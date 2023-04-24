module L = List
open StdLabels
open Pa_ppx_parsetree_helpers

let convert_down_list_expr f e =
  let rec crec acc = function
      {%expression| [] |} -> List.rev acc
    | {%expression| $h$ :: $tl$ |} ->
       crec (f h :: acc) tl
    | _ -> failwith Fmt.(str "convert_down_list_expr: malformed list-expression %a"
                           Std_derivers.pp_expression e)
  in
  crec [] e

let convert_up_list_expr loc el =
  Stdlib.List.fold_right (fun e rhs -> {%expression| $e$ :: $rhs$ |}) el {%expression| [] |}

module SplitAttributes = struct
  open Parsetree
  let core_type ct =
    { ct with ptyp_attributes = [] }, ct.ptyp_attributes
end

module OrigLocation = Location
open Ppxlib
open Asttypes
(* open Parsetree *)
open Ast_builder.Default

let ( --> ) lhs rhs = case ~guard:None ~lhs ~rhs

let wrap_runtime ~loc decls =
  [%expr let open! Ppx_jsobject_conv_runtime in [%e decls]]

let mk_ep_var ~loc n = evar ~loc n, pvar ~loc n

let input_evar ~loc = evar ~loc "v"
let input_pvar ~loc = pvar ~loc "v"

let unref ~loc var =
  let u = evar ~loc "!" in
  eapply ~loc u [var]

let unref_apply ~loc var args =
  let unref_var = unref ~loc var in
  eapply ~loc unref_var args

let ref_ ~loc var =
  let r = evar ~loc "ref" in
  eapply ~loc r [var]

let mk_recent core =
  core ^ "_most_recent"

let mk_recent_ep_var ~loc core =
  mk_ep_var ~loc (mk_recent core)

let mk_default core =
  core ^ "_default"

module Attrs = struct
  let name =
    Attribute.declare "jsobject.name"
                      Attribute.Context.constructor_declaration
                      (Ast_pattern.single_expr_payload
                         (Ast_pattern.estring Ast_pattern.__))
                      (fun x -> x)

  let constructor_name cd  =
    match Attribute.get name cd with
    | Some(v) -> v
    | None -> cd.pcd_name.txt

  let key =
    Attribute.declare "jsobject.key"
                      Attribute.Context.label_declaration
                      (Ast_pattern.single_expr_payload
                         (Ast_pattern.estring Ast_pattern.__))
                      (fun x -> x)
  let field_name ld =
    match Attribute.get key ld with
    | Some(v) -> v
    | None -> ld.pld_name.txt

  let drop_none =
    Attribute.declare "jsobject.drop_none"
      Attribute.Context.label_declaration
      Ast_pattern.(pstr nil)
      ()
  let should_drop_none ld =
    match Attribute.get drop_none ld with
    | Some(_) ->
       (* Some sanity check: [@drop_none] make sense only with option types *)
       let err () = Location.raise_errorf
                      ~loc:ld.pld_name.loc
                      "ppx_jsobject_conv: drop_none only makes sense with fields of option type"
       in
       let () = match ld.pld_type.ptyp_desc with
         | Ptyp_constr (id, _) ->
            (match id.txt with
             | {%longident_t| option |} -> ()
             | {%longident_t| $lid:_$ |} | {%longident_t| $longid:_$ . $lid:_$ |}
               | {%extended_module_path| $longid:_$ ( $longid:_$ ) |} -> err ())
         | Ptyp_tuple (_) | Ptyp_variant (_)
           | Ptyp_object (_) | Ptyp_class (_)
           | Ptyp_package(_) | Ptyp_any | Ptyp_var(_) | Ptyp_arrow(_)
           | Ptyp_alias(_) | Ptyp_poly(_) | Ptyp_extension(_) -> err ()
       in true
    | None -> false

  let default_on_error =
    let open! Ast_pattern in
    Attribute.declare "jsobject.default_on_error"
                      Attribute.Context.label_declaration
                      (Ast_pattern.pstr (pstr_eval __ nil ^:: nil))
                      (fun x -> x)

  let default =
    let open! Ast_pattern in
    Attribute.declare "jsobject.default"
                      Attribute.Context.label_declaration
                      (Ast_pattern.pstr (pstr_eval __ nil ^:: nil))
                      (fun x -> x)

  let error_default ld =
    match (Attribute.get default_on_error ld), (Attribute.get default ld) with
    | Some _, Some _ ->
       Location.raise_errorf
         ~loc:ld.pld_name.loc "ppx_jsobject_conv: default_on_error and default attrs can't be used together"
    | Some _ as v, _ ->
       v
    | None, _ -> None

  let field_default ld =
    match Attribute.get default ld with
    | Some(_) as v ->
       (* Some sanity check: [@default] doesn't make much sense with option types *)
       let () = match ld.pld_type.ptyp_desc with
         | Ptyp_constr (id, _) ->
            (match id.txt with
             | {%longident_t| option |} ->
                Location.raise_errorf
                  ~loc:ld.pld_name.loc "ppx_jsobject_conv: default attr doesn't make sense with fields of option type"
             | {%longident_t| $lid:_$ |} | {%longident_t| $longid:_$ . $lid:_$ |}
               | {%extended_module_path| $longid:_$ ( $longid:_$ ) |} -> ())
         | Ptyp_tuple (_) | Ptyp_variant (_)
           | Ptyp_object (_) | Ptyp_class (_)
           | Ptyp_package(_) | Ptyp_any | Ptyp_var(_) | Ptyp_arrow(_)
           | Ptyp_alias(_) | Ptyp_poly(_) | Ptyp_extension(_) -> ()
       in v
    | None -> None

  type sum_type_conversion = [`Regular | `AsObject | `AsEnum | `AsTagless]
  let sum_type_as =
    Attribute.declare "jsobject.sum_type_as"
                      Attribute.Context.constructor_declaration
                      (Ast_pattern.single_expr_payload
                         (Ast_pattern.estring Ast_pattern.__))
                      (fun x -> x)

  let define_constructor_as cd  =
    match Attribute.get sum_type_as cd with
    | Some("object") -> `AsObject
    | Some("enum") -> `AsEnum
    | Some("tagless") -> `AsTagless
    | Some("regular") -> `Regular
    | Some(b) -> Location.raise_errorf ~loc:cd.pcd_loc "ppx_jsobject_conv: sum_type_as only accepts object/enum/tagless/regular, got %s" b
    | None -> `Regular

  let define_sum_type_as cds =
    let conversions = List.map ~f:define_constructor_as cds in
    let uniq = L.sort_uniq compare conversions in
    let special = List.filter ~f:(function
                                  | `Regular -> false
                                  | _ -> true) uniq in
    match special with
    | [] -> `Regular
    | [n] -> n
    | _ -> Location.raise_errorf
             ~loc:((List.hd cds).pcd_loc)
             "ppx_jsobject_conv: sum type should have at most one distinct sum_type_as attribute"
end

(* Courtesy of ppx_sexp_conv *)
module Fun_or_match = struct
  type t =
    | Fun   of expression
    | Match of case list

  let expr ~loc t =
    match t with
    | Fun f       -> f
    | Match cases -> pexp_function ~loc cases

  let unroll ~loc e t =
    match t with
    | Fun f       -> eapply ~loc f [e]
    | Match cases -> pexp_match ~loc e cases

  (** For list of expressions returns triple (bindings, pvars, evars)
      where bindings is list of `let v_i =`;
            pvars is list of `v_i` for patterns, and
            evars is list of expressions applied to corresponding temp var
   *)
  let map_tmp_vars ~loc ts =
    let vars = List.mapi ts ~f:(fun i _ -> "v" ^ string_of_int i) in
    let bindings =
      List.map2 vars ts
                ~f:(fun var t ->
                  let e, p = mk_ep_var ~loc var in
                  let expr = unroll ~loc e t in
                  value_binding ~loc ~pat:p ~expr)
    in
    (bindings,
     List.map vars ~f:(pvar ~loc),
     List.map vars ~f:(evar ~loc))
end

(* XXX: Temporary workaround, while ppx_core is fixing exception there *)
exception Stop
let type_is_recursive_repl short_circuit type_names =
  object(self)
    inherit Ast_traverse.iter as super

    method! type_declaration td =
      (match td with
      | {%type_decl| $list:_$ $lid:_$ = $priv:_$ .. $list:_$ $itemattrs:_$ |} -> raise_notrace Stop
      | _ -> super#type_declaration td) [@ocaml.warning "-4"]

    method! core_type ctyp =
      match short_circuit ctyp with
      | Some false -> ()
      | Some true  -> raise_notrace Stop
      | None ->
         (match ctyp with
         | {%core_type| $list:_$ $lid:id$ $algattrs:_$ |} when List.mem id ~set:type_names ->
            raise Stop
         | _ -> super#core_type ctyp) [@ocaml.warning "-4"]

    method! label_declaration {%label_declaration| $mutable:_$ $lid:_$ : $ty$ $algattrs:_$ |} =
      self#core_type ty

    method! constructor_declaration cd =
      (* Don't recurse through cd.pcd_res *)
      match cd with
      | {%constructor_declaration| $uid:_$ : $list:_$ . $list:args$ $opt:_$ $algattrs:_$ |} -> List.iter ~f:(fun ty -> self#core_type ty) args
      | {%constructor_declaration| $uid:_$ : $list:_$ . { $list:fields$ } $opt:_$ $algattrs:_$ |} ->
         List.iter ~f:(fun ld -> self#label_declaration ld) fields
  end

let types_are_recursive_repl ?(stop_on_functions = true)
                        ?(short_circuit = fun _ -> None)
                        tds =
  let type_names = List.map ~f:(fun td -> td.ptype_name.txt) tds in
  let short_circuit =
    if stop_on_functions then
      fun ty ->
      (match ty.ptyp_desc with
       | Ptyp_arrow _ -> Some false
      | _ -> short_circuit ty) [@ocaml.warning "-4"]
    else short_circuit
  in
  let check = (type_is_recursive_repl short_circuit type_names)#type_declaration in
  try
    List.iter ~f:(fun td -> check td) tds;
    false
  with Stop ->
    true

let really_recursive rec_flag tds =
  match rec_flag with
  | Recursive    -> if types_are_recursive_repl tds then Recursive else Nonrecursive
  | Nonrecursive -> Nonrecursive

let constrained_function_binding = fun
  (* placing a suitably polymorphic or rigid type constraint on the pattern or body *)
    ~(loc:Location.t) ?constraint_
    ~(func_name:string) (body:expression) ->
  let pre_pat = pvar ~loc func_name in
  let pat = match constraint_ with
    | Some ct -> ppat_constraint ~loc pre_pat ct
    | None -> pre_pat
  in
  value_binding ~loc ~pat ~expr:body

module Jsobject_of_expander = struct
  let mk_type td =
    combinator_type_of_type_declaration
      td ~f:(fun ~loc ty ->
        [%type: [%t ty] -> Js_of_ocaml.Js.Unsafe.any Js_of_ocaml.Js.t])

  let mk_ref_type td =
    combinator_type_of_type_declaration
      td ~f:(fun ~loc ty ->
        [%type: ([%t ty] -> Js_of_ocaml.Js.Unsafe.any Js_of_ocaml.Js.t) ref])


  let name_of_tdname name = match name with
    | "t" -> "jsobject_of"
    | tn  -> "jsobject_of_" ^ tn

  let name_of_td td = name_of_tdname td.ptype_name.txt
  let name_of_te te = name_of_tdname @@ Longident.last_exn te.ptyext_path.txt
  let full_name_of_te te =
    let names = List.rev @@ Longident.flatten_exn te.ptyext_path.txt in
    match names with
    | [] -> Location.raise_errorf "name_of_te: assert"
    | (fn::rest) ->
       let func_name = name_of_tdname fn in
       let names' = List.rev (func_name::rest) in
       String.concat ~sep:"." names'

  let jsobject_of_std_type ~loc (id : Longident.t) =
    let mark, txt =
      match id with
      | {%longident_t| $lid:s$ |} ->
         `Fold, {%longident_t| $lid:(name_of_tdname s)$ |}
      | {%longident_t| Js . t |} ->
         `FullStop, {%longident_t| jsobject_of_jst |}
      | {%longident_t| Js . Unsafe . any|} ->
         `FullStop, {%longident_t| jsobject_of_jsany |}
      | {%longident_t| $longid:p$ . $lid:s$ |} ->
         `Fold, {%longident_t| $longid:p$ . $lid:name_of_tdname s$ |}
      | {%extended_module_path| $longid:_$ ( $longid:_$ ) |} ->
         failwith "ppx_jsobject_conv: jsobject_std_type"
    in
    let expr = {%expression| $longlid:txt$ |} in
    match mark with
    | `Fold -> `Fold expr
    | `FullStop -> `FullStop expr

  let rec jsobject_of_type
            (tparams : (string * (Parsetree.expression * Parsetree.pattern)) list)
            (typ: core_type) : Fun_or_match.t =
    match SplitAttributes.core_type typ with
    | {%core_type.loc| $list:args$ $longlid:cid$ |},_ ->
       let type_expr = match jsobject_of_std_type ~loc cid with
         | `FullStop expr -> expr
         | `Fold init -> List.fold_left
                           args
                           ~init
                           ~f:(fun exp1 tp2 ->
                             let exp2 = Fun_or_match.expr
                                          ~loc (jsobject_of_type tparams tp2) in
                             {%expression| $exp1$ $exp2$ |})
       in
       Fun_or_match.Fun type_expr
    | {%core_type.loc| $tuplelist:tps$ |},_ ->
       Fun_or_match.Match [jsobject_of_tuple ~loc tparams tps]
    | {%core_type.loc| [ $closedflag:_$ $list:row_fields$ $opt:_$ ] |},_ ->
       jsobject_of_variant ~loc tparams row_fields
    | {%core_type| ' $lid:a$ |},_ ->
       let etp, _ = List.assoc a tparams in
       Fun_or_match.Fun etp
    | {ptyp_desc=Ptyp_object(_) | Ptyp_class(_);_},_ ->
       Location.raise_errorf ~loc:typ.ptyp_loc "ppx_jsobject_conv: jsobject_of_type -- classes & objects are not supported yet"
    | {ptyp_desc=Ptyp_package(_);_},_ ->
       Location.raise_errorf ~loc:typ.ptyp_loc "ppx_jsobject_conv: jsobject_of_type -- modules are not supported yet"
    | {ptyp_desc=Ptyp_any | Ptyp_arrow(_) | Ptyp_alias(_)
      | Ptyp_poly(_) | Ptyp_extension(_);_},_ ->
       Location.raise_errorf ~loc:typ.ptyp_loc "ppx_jsobject_conv: jsobject_of_type -- Unsupported type"
    | {%core_type| $_$ $algattrs:(_::_)$ |},_ -> assert false
  (* Conversion of tuples *)
  and jsobject_of_tuple ~loc tparams tps =
    let fps = List.map ~f:(jsobject_of_type tparams) tps in
    let bindings, pvars, evars = Fun_or_match.map_tmp_vars ~loc fps in
    let in_expr = {%expression| to_js_array $elist ~loc evars$ |} in
    let expr = pexp_let ~loc Nonrecursive bindings in_expr in
    ppat_tuple ~loc pvars --> expr

  (* Conversion of variant types *)
  and jsobject_of_variant ~loc tparams row_fields =
    let make_final_expr cnstr args  =
      let ecnstr = estring ~loc cnstr in
      let cnstr_expr = [%expr jsobject_of_string [%e ecnstr]] in
      let full = elist ~loc (cnstr_expr::args) in
      [%expr to_js_array [%e full]]
    in
    let item = function
      | Rtag (cnstr, true, []) ->
         ppat_variant ~loc cnstr.txt None -->
           (make_final_expr cnstr.txt [] )
      | Rtag (cnstr, false, [tp]) ->
        let var, patt = mk_ep_var ~loc "v0" in
        let cnstr_arg = Fun_or_match.unroll
                          ~loc var (jsobject_of_type tparams tp) in
        let expr = make_final_expr cnstr.txt [cnstr_arg] in
        ppat_variant ~loc cnstr.txt (Some patt) --> expr
      | Rtag (_) | Rinherit(_) ->
         Location.raise_errorf ~loc "ppx_jsobject_conv: unsupported jsobject_of_variant"
    in
    let desc_item = fun rf -> item rf.prf_desc
    in Fun_or_match.Match (List.map ~f:desc_item row_fields)

  (* Conversion of sum types *)
  let rec jsobject_of_sum tparams cds =
    let conversion = Attrs.define_sum_type_as cds in
    let make_final_expr ~loc scnstr args =
      match conversion, args with
      | `Regular, [] ->
         [%expr to_js_array [jsobject_of_string [%e scnstr]]]
      | `Regular, vars ->
         let cnstr_expr = [%expr (jsobject_of_string [%e scnstr])] in
         [%expr to_js_array [%e elist ~loc (cnstr_expr :: vars)]]
      | `AsObject, [var] ->
         let pair = pexp_tuple ~loc [scnstr; var] in
         let pairs = Ast_helper.Exp.array ~loc [pair] in
         [%expr make_jsobject [%e pairs]]
      | `AsTagless, [var] ->
         var
      | `AsEnum, [] ->
         [%expr jsobject_of_string [%e scnstr]]
      | `AsEnum, _ ->
         Location.raise_errorf ~loc "ppx_jsobject_conv: when using sum_type_as enum, all constructors must be nullary"
      | `AsObject, _ ->
         Location.raise_errorf ~loc "ppx_jsobject_conv: when using sum_type_as object, all constructors must be unary"
      | `AsTagless, _ ->
         Location.raise_errorf ~loc "ppx_jsobject_conv: when using sum_type_as tagless, all constructors must be unary"
    in
    let item cd =
      let loc = cd.pcd_loc in
      let lid = Located.map lident cd.pcd_name in
      let scnstr = estring ~loc (Attrs.constructor_name cd) in
      match cd.pcd_args with
      | Pcstr_tuple [] ->
         ppat_construct ~loc lid None -->
           make_final_expr ~loc scnstr []
      | Pcstr_tuple args ->
         let jsobject_of_args = List.map
                                  ~f:(jsobject_of_type tparams) args in
         let bindings, patts, vars = Fun_or_match.map_tmp_vars
                                       ~loc jsobject_of_args in
         let patt =
           match patts with
           | [patt] -> patt
           | _ -> ppat_tuple ~loc patts
         in
         ppat_construct ~loc lid (Some patt) -->
           pexp_let ~loc
                    Nonrecursive
                    bindings
                    (make_final_expr ~loc scnstr vars)
      | Pcstr_record fields ->
         let patt, expr = mk_rec_conv ~loc tparams fields in
         ppat_construct ~loc lid (Some patt) -->
           make_final_expr ~loc scnstr [expr]

    in
    Fun_or_match.Match (List.map ~f:item cds)

  (* Conversion of record types *)
  and mk_rec_patt loc patt name =
    let p =
      OrigLocation.mkloc (Longident.Lident name) loc ,
      pvar ~loc ("v_" ^ name)
    in
    patt @ [p]

  and mk_rec_conv ~loc tparams fields =
    let item (patts, exprs) = function
      | {pld_name = {txt=name; loc}; pld_type = tp; _ } as ld ->
         let patts = mk_rec_patt loc patts name in
         let vname = evar ~loc ("v_" ^ name) in
         let field_name = estring ~loc (Attrs.field_name ld) in
         let cnv = Fun_or_match.unroll
                     ~loc vname (jsobject_of_type tparams tp) in
         let expr = if Attrs.should_drop_none ld
                    then [%expr (match [%e vname] with
                                 | Some _ -> Some ([%e field_name], [%e cnv])
                                 | None -> None)]
                    else [%expr
                             (Some ([%e field_name], [%e cnv]))]
         in
         patts, expr::exprs
    in
    let patts, exprs = List.fold_left ~f:item ~init:([], []) fields in
    let expr = Ast_helper.Exp.array ~loc (List.rev exprs) in
    let patt = ppat_record ~loc patts Closed in
    (patt, [%expr make_jsobject_of_some [%e expr]])

  and jsobject_of_record ~loc tparams fields =
    let patt, expr = mk_rec_conv ~loc tparams fields in
    Fun_or_match.Match [patt --> expr]

  let jsobject_of_td td =
    let {ptype_name = {txt = type_name; loc = _}; ptype_loc = loc; _} = td in
    let tparams = List.map td.ptype_params
                           ~f:(fun tp ->
                             let n = (get_type_param_name tp).txt in
                             let e, p = mk_ep_var ~loc ("_of_" ^ n) in
                             (n, (e, p))) in
    let func_name = name_of_td td in
    let body, sitems =
      match td.ptype_kind with
      | Ptype_abstract -> begin
          match td.ptype_manifest with
          | Some ty -> jsobject_of_type tparams ty, []
          | None -> Location.raise_errorf ~loc "ppx_jsobject_conv: fully abstract types are not supported"
        end
      | Ptype_variant cds -> jsobject_of_sum tparams cds, []
      | Ptype_record fields -> jsobject_of_record ~loc tparams fields, []
      | Ptype_open ->
         (* Create default conversion for open type*)
         let stype_name = estring ~loc type_name in
         let default_name = mk_default func_name in
         let recent_evar, recent_pvar = mk_recent_ep_var ~loc func_name in
         let default_func_body =
           [%expr fun _ ->
                  throw_js_error
                    ("ppx_jsobject_conv: Maybe a [@@deriving jsobject] is missing when extending the type " ^
                       [%e stype_name])
           ] in
         let default_func =
           let _, eps = List.split tparams in
           let _, patts = List.split eps in
           let fb = eabstract ~loc patts @@ wrap_runtime ~loc default_func_body in
           let constraint_ = mk_type td in
           constrained_function_binding ~loc ~constraint_
                                        ~func_name:default_name fb
         in
         let most_recent =
           let expr = ref_ ~loc (evar ~loc default_name) in
           value_binding ~loc ~pat:recent_pvar ~expr
         in
         let body =
           let ei, pi = mk_ep_var ~loc "i" in
           let application = unref_apply ~loc recent_evar [ei] in
           Fun_or_match.Match [pi --> application] in
         body, [default_func; most_recent]
    in
    let body' = match body with
      | Fun_or_match.Fun fun_expr -> [%expr fun [%p input_pvar ~loc] ->
                                            [%e fun_expr] [%e input_evar ~loc]]
      | Fun_or_match.Match matchings -> pexp_function ~loc matchings
    in
    let body'' =
      let _, eps = List.split tparams in
      let _, patts = List.split eps in
      eabstract ~loc patts @@ wrap_runtime ~loc body'
    in
    List.append sitems [constrained_function_binding ~loc ~func_name body'']


  let str_type_decl ~loc ~path:_ (rec_flag, tds) =
    let rec_flag = really_recursive rec_flag tds in
    let bindings = List.map tds ~f:jsobject_of_td |> List.concat in
    [pstr_value ~loc rec_flag bindings]

  let sig_type_decl ~loc:_ ~path:_ (_rf, tds) =
    List.concat
    @@ List.map
         tds
         ~f:(fun td ->
           let type_ = mk_type td in
           let func_name = name_of_td td in
           let loc = td.ptype_loc in
           let type_func = psig_value ~loc
                                      (value_description
                                         ~loc
                                         ~name:{ td.ptype_name
                                               with txt = func_name }
                                         ~type_ ~prim:[]) in
           match td.ptype_kind with
           | Ptype_open ->
              let default_name = { td.ptype_name with
                                   txt = mk_default func_name } in
              let default_sig = psig_value ~loc
                                           (value_description
                                              ~loc
                                              ~name:default_name
                                              ~type_
                                              ~prim:[]) in
              let recent_name = { td.ptype_name with
                                  txt = mk_recent func_name } in
              let ref_sig = psig_value ~loc
                                       (value_description
                                          ~loc
                                          ~name:recent_name
                                          ~type_:(mk_ref_type td)
                                          ~prim:[]) in
              [default_sig; ref_sig; type_func]
           | Ptype_abstract | Ptype_variant _ | Ptype_record _ ->
              [type_func])

  let str_type_ext ~loc ~path:_ te =
    let constructors = te.ptyext_constructors in
    let make_cd = function
      | {pext_kind; pext_name; pext_loc; pext_attributes } ->
         (match pext_kind with
          | Pext_decl (vars, cons_args, ctyp) ->
             {
               pcd_name = pext_name;
               pcd_args = cons_args;
               pcd_vars = vars;
               pcd_res = ctyp;
               pcd_loc = pext_loc;
               pcd_attributes = pext_attributes;
             }
          | Pext_rebind _ ->
             Location.raise_errorf ~loc "ppx_jsobject_conv: rebinds are not supported in type extensions!"
         )
    in
    let cds = List.map constructors ~f:make_cd in
    let tparams = List.map te.ptyext_params
                           ~f:(fun tp ->
                             let n = (get_type_param_name tp).txt in
                             let e, p = mk_ep_var ~loc ("_of_" ^ n) in
                             (n, (e, p))) in
    let func_name = name_of_te te in
    let previous_evar, previous_pvar = mk_ep_var ~loc
                                       @@ func_name ^ "_previous" in
    (* body of function, responsible for converting newly introduced
       variant constructors; unknown constructors will be redirected
       to previously defined function *)
    let body = jsobject_of_sum tparams cds in
    let body' = match body with
      | Fun_or_match.Match matchings ->
         let ev, pv = mk_ep_var ~loc "wildcard" in
         let wild_match = pv -->
                            eapply ~loc previous_evar [ev] in
         pexp_function ~loc (List.append matchings [wild_match])
      | Fun_or_match.Fun _ ->
         Location.raise_errorf ~loc "ppx_jsobject_conv: impossible state"
    in
    let body'' =
      let _, eps = List.split tparams in
      let _, patts = List.split eps in
      eabstract ~loc patts @@ wrap_runtime ~loc body'
    in
    (* statement for saving previously defined function: it is used in
       wildcard pattern above *)
    let recent_evar, _recent_pvar = mk_recent_ep_var ~loc
                                   @@ full_name_of_te te in
    let previous_body =
      let expr = unref ~loc recent_evar in
      value_binding ~loc ~pat:previous_pvar ~expr
    in
    (* update most recent definition with our function *)
    let recent_body =
      let pat = punit ~loc in
      let assign_var = evar ~loc ":=" in
      let efunc = evar ~loc func_name in
      let expr = eapply ~loc assign_var [recent_evar; efunc] in
      value_binding ~loc ~pat ~expr
    in
    let rec_bindings = [
        previous_body;
        constrained_function_binding ~loc ~func_name body''] in
    let bindings = [recent_body] in
    [pstr_value ~loc Recursive rec_bindings;
     pstr_value ~loc Nonrecursive bindings]

  let core_type ty =
    jsobject_of_type [] ty |> Fun_or_match.expr ~loc:ty.ptyp_loc

end

module Jsobject_of_expander_2 = struct
  open Stdlib
  open Parsetree
  [@@@ocaml.warning "-8"]
  let name_of_tdname name = match name with
    | "t" -> "jsobject_of"
    | tn  -> "jsobject_of_" ^ tn

  let name_of_td td = name_of_tdname td.ptype_name.txt
  let name_of_te te = name_of_tdname @@ Longident.last_exn te.ptyext_path.txt

  let converter_type ty : core_type =
    let loc = match ty with {%core_type.noattr.loc| $_$ |} -> loc in
    {%core_type| $ty$ -> Js_of_ocaml.Js.Unsafe.any Js_of_ocaml.Js.t |}

  let td_to_fun_type td =
    let (loc,  pl, tname) =
      match td with
        {%type_decl.noattr.loc| $list:pl$ $lid:tname$ |} -> (loc, pl, tname)
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ |} -> (loc, pl, tname)
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $constructorlist:_$ |} -> (loc, pl, tname)
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = { $list:_$ } |} -> (loc, pl, tname)
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ = $constructorlist:_$ |} -> (loc, pl, tname)
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ = { $list:_$ } |} -> (loc, pl, tname)
    in
    let rhs_t = converter_type {%core_type| $list:List.map fst pl$ $lid:tname$ |} in
    List.fold_right (fun (pv, _) rhs_t ->
        {%core_type| $converter_type pv$ -> $rhs_t$ |})
      pl rhs_t

  let sig_type_decl ~loc:_ ~path:_ (_rf, tds) =
    tds
    |> List.concat_map (fun td ->
           let fun_type = td_to_fun_type td in
           let func_name = name_of_td td in
           let loc = td.ptype_loc in
           [{%signature_item| val $lid:func_name$ : $fun_type$ |}])

  let do_wrap_body cid e =
    let rec wraprec = function
        {%expression.noattr.loc| let $recflag:rf$ $list:bl$ in $e$ |} ->
        let e = wraprec e in
        {%expression.noattr| let $recflag:rf$ $list:bl$ in $e$ |}
      | {%expression.noattr.loc| $_$ |} as e ->
         {%expression| to_js_array [jsobject_of_string $string:cid$ ; $e$ ] |}
    in
    wraprec e

  let do_prepend_body cid e =
    let rec wraprec = function
        {%expression.noattr.loc| let $recflag:rf$ $list:bl$ in $e$ |} ->
        let e = wraprec e in
        {%expression.noattr| let $recflag:rf$ $list:bl$ in $e$ |}
      | {%expression.noattr.loc| to_js_array $exprs_list$ |} ->
         {%expression| to_js_array (( jsobject_of_string $string:cid$ ) :: $exprs_list$ ) |}
    in
    wraprec e

  [@@@ocaml.warning "-39-27"]
  let rec core_type_to_jsobject_of_fun loc rho ty =
    let cases = core_type_to_jsobject_of rho ty in
    {%expression| function $list:cases$ |}

  and core_type_to_jsobject_of ?prepend_pattern ?wrap_body ?prepend_body rho ty : case list =
    let cases = match ty with
        {%core_type.noattr.loc| ' $lid:v$ |} ->
        let f = match List.assoc v rho with
            exception Not_found ->
             failwith Fmt.(str "core_type_to_jsobject_of: unknown type-var %a" Std_derivers.pp_core_type ty)
          | x -> x in
         [{%case| v -> $f$ v |}]

      | {%core_type.noattr.loc| int |} ->
         [{%case| v -> jsobject_of_int v |}]

      | {%core_type.noattr.loc| bool |} ->
         [{%case| v -> jsobject_of_bool v |}]

      | {%core_type.noattr.loc| string |} ->
         [{%case| v -> jsobject_of_string v |}]

      | {%core_type.noattr.loc| $ty$ array |} ->
         let cases = core_type_to_jsobject_of rho ty in
         [{%case| v -> jsobject_of_array (function $list:cases$) v |}]

      | {%core_type.noattr.loc| $ty$ list |} ->
         let cases = core_type_to_jsobject_of rho ty in
         [{%case| v -> jsobject_of_list (function $list:cases$) v |}]

      | {%core_type.noattr.loc| $ty$ option |} ->
         let cases = core_type_to_jsobject_of rho ty in
         [{%case| v -> jsobject_of_option (function $list:cases$) v |}]

      | {%core_type.noattr.loc| $lid:tname$ |} ->
         let fname = name_of_tdname tname in
         [{%case| v -> $lid:fname$ v |}]

      | {%core_type.noattr.loc| $longid:li$ . $lid:tname$ |} ->
         let fname = name_of_tdname tname in
         [{%case| v -> $longid:li$ . $lid:fname$ v |}]

      | {%core_type.noattr.loc| $list:tyl$ $lid:tname$ |} ->
         let fname = name_of_tdname tname in
         let params = List.map (core_type_to_jsobject_of_fun loc rho) tyl in
         let params = List.map (fun e -> (Asttypes.Nolabel,e)) params in
         [{%case| v -> ($lid:fname$ $list:params$) v |}]

      | {%core_type.noattr.loc| $list:tyl$ $longid:li$ . $lid:tname$ |} ->
         let fname = name_of_tdname tname in
         let params = List.map (core_type_to_jsobject_of_fun loc rho) tyl in
         let params = List.map (fun e -> (Asttypes.Nolabel,e)) params in
         [{%case| v -> ( $longid:li$ . $lid:fname$ $list:params$ ) v |}]

      | {%core_type.noattr.loc| $tuplelist:tyl$ |} ->
         let convert1 i ty =
           let var = Printf.sprintf "v_%d" i in
           let patt = {%pattern| $lid:var$ |} in
           let expr = {%expression| $lid:var$ |} in
           let conv =
             let cases = core_type_to_jsobject_of rho ty in
             {%expression| function $list:cases$ |} in
           (var,patt,expr,conv) in
         let var_patt_expr_conv_list = List.mapi convert1 tyl in
         let patts = var_patt_expr_conv_list |> List.map (fun (_,p,_,_) -> p) in
         let patt = {%pattern| $tuplelist:patts$ |} in
         let exprs = var_patt_expr_conv_list |> List.map (fun (_,_,e,_) -> e) in
         let exprs_list = convert_up_list_expr loc exprs in
         let rhs = {%expression| to_js_array $exprs_list$ |} in
         let body = List.fold_right (fun (var,patt,expr,conv) rhs ->
                        {%expression| let $lid:var$ = $conv$ $lid:var$ in $rhs$ |})
                      var_patt_expr_conv_list rhs in
         [{%case| $patt$ -> $body$ |}]
      | ct ->
         failwith Fmt.(str "core_type_to_jsobject_of: unhandled core_type: %a" Std_derivers.pp_core_type ct)

    in
    cases
    |>  List.map (function
              {%case.noattr.loc| $patt$ -> $body$ |} ->
              let loc = match patt with {%pattern.noattr.loc| $_$ |} -> loc in
              let patt = match prepend_pattern with
                  None -> patt
                | Some cid -> {%pattern| $uid:cid$ $patt$ |} in
              let body = match (wrap_body, prepend_body) with
                  (None, None) -> body
                | (Some cid, None) -> do_wrap_body cid body
                | (None, Some cid) -> do_prepend_body cid body
                | (Some _, Some _) -> assert false in
              {%case.noattr.loc| $patt$ -> $body$ |}) 

  let record_type_to_jsobject_of ~loc rho ll =
    let field_name_var_longid_patt_conv_list =
      ll
      |> List.map (function
               {%label_declaration.noattr.loc| $mutable:_$ $lid:fldname$ : $fldty$ |} as ld ->
               let var = Printf.sprintf "v_%s" fldname in
               let longid = OrigLocation.mkloc {%longident_t| $lid:fldname$ |} loc in
               let patt = {%pattern| $lid:var$ |} in
               let conv = core_type_to_jsobject_of rho fldty in
               let jsfldname = Attrs.field_name ld in
               (jsfldname, var, longid, patt, conv)) in
    let pattfields = 
      field_name_var_longid_patt_conv_list
      |> List.map (fun (_,_,li,p,_) -> (li,p)) in
    let patt = {%pattern| { $list:pattfields$ } |} in
    let jstuples =
      field_name_var_longid_patt_conv_list
      |> List.map (fun (jsfldname,var,_,_,conv) ->
             {%expression| Some ($string:jsfldname$, ((function $list:conv$) $lid:var$)) |}) in
    [{%case| $patt$ -> make_jsobject_of_some [| $list:jstuples$ |] |}]

  let td_to_jsobject_of = function
    {%type_decl.noattr.loc| $list:pl$ $lid:tname$ |} -> []
  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $ty$ |} ->
     let fname = name_of_tdname tname in
     let rho = pl |>  List.map (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) ->
                          let fname = Printf.sprintf "_of_%s" v in
                          (v, {%expression| $lid:fname$ |})) in
     let cases = core_type_to_jsobject_of rho ty in
     let rhs = {%expression| function $list:cases$ |} in
     let rhs = List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
                   let fname = Printf.sprintf "_of_%s" v in
                   {%expression| fun $lid:fname$ -> $rhs$ |})
                 pl rhs in
     [{%value_binding| $lid:fname$ = $rhs$ |}]

  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $constructorlist:cl$ |} when Attrs.define_sum_type_as cl = `Regular ->
     let fname = name_of_tdname tname in
     let rho = pl |>  List.map (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) ->
                          let fname = Printf.sprintf "_of_%s" v in
                          (v, {%expression| $lid:fname$ |})) in
     let cases =
       cl
       |> List.concat_map (function cd ->
              let jscid = Attrs.constructor_name cd in
              match cd with
                {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
                 [{%case| $uid:cid$ -> to_js_array [jsobject_of_string $string:jscid$] |}]
              | {%constructor_declaration.noattr.loc| $uid:cid$ of $ty$ |} ->
                 core_type_to_jsobject_of ~prepend_pattern:cid ~wrap_body:jscid rho ty
              | {%constructor_declaration.noattr.loc| $uid:cid$ of $list:tyl$ |} ->
                 core_type_to_jsobject_of ~prepend_pattern:cid ~prepend_body:jscid rho {%core_type| $tuplelist:tyl$ |})
     in
     let rhs = {%expression| function $list:cases$ |} in
     let rhs = List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
                   let fname = Printf.sprintf "_of_%s" v in
                   {%expression| fun $lid:fname$ -> $rhs$ |})
                 pl rhs in
     [{%value_binding| $lid:fname$ = $rhs$ |}]

  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $constructorlist:cl$ |} when Attrs.define_sum_type_as cl = `AsTagless ->
     let fname = name_of_tdname tname in
     let rho = pl |>  List.map (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) ->
                          let fname = Printf.sprintf "_of_%s" v in
                          (v, {%expression| $lid:fname$ |})) in
     let cases =
       cl
       |> List.concat_map (function
                {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
                 failwith Fmt.(str "core_type_to_jsobject_of: cannot tagless-ly marshal nullary constructor: %s" cid)
              | {%constructor_declaration.noattr.loc| $uid:cid$ of $ty$ |} ->
                 core_type_to_jsobject_of ~prepend_pattern:cid rho ty
              | {%constructor_declaration.noattr.loc| $uid:cid$ of $list:tyl$ |} ->
                 core_type_to_jsobject_of ~prepend_pattern:cid rho {%core_type| $tuplelist:tyl$ |})
     in
     let rhs = {%expression| function $list:cases$ |} in
     let rhs = List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
                   let fname = Printf.sprintf "_of_%s" v in
                   {%expression| fun $lid:fname$ -> $rhs$ |})
                 pl rhs in
     [{%value_binding| $lid:fname$ = $rhs$ |}]


  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = { $list:ll$ } |} ->
     let fname = name_of_tdname tname in
     let rho = pl |>  List.map (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) ->
                          let fname = Printf.sprintf "_of_%s" v in
                          (v, {%expression| $lid:fname$ |})) in
     let cases = record_type_to_jsobject_of ~loc rho ll in
     let rhs = {%expression| function $list:cases$ |} in
     let rhs = List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
                   let fname = Printf.sprintf "_of_%s" v in
                   {%expression| fun $lid:fname$ -> $rhs$ |})
                 pl rhs in
     [{%value_binding| $lid:fname$ = $rhs$ |}]
     

  let str_type_decl ~loc ~path:_ (rec_flag, tds) =
    let rec_flag = really_recursive rec_flag tds in
    let bindings = tds |> List.concat_map td_to_jsobject_of in
    let bindings =
      bindings
      |> List.map (fun
               {%value_binding.noattr.loc| $lid:fname$ = $e$ |} ->
             let e = {%expression| let open! Ppx_jsobject_conv_runtime in $e$ |} in
             {%value_binding.noattr.loc| $lid:fname$ = $e$ |}) in
    [{%structure_item| let $recflag:rec_flag$ $list:bindings$ |}]

end

module Jsobject_of = struct
  let str_type_decl =
    Ppxlib.Deriving.Generator.make_noarg
      Jsobject_of_expander_2.str_type_decl
      ~attributes:[Attribute.T Attrs.name;
                   Attribute.T Attrs.key;
                   Attribute.T Attrs.sum_type_as;
                   Attribute.T Attrs.drop_none;
                  ]

  let sig_type_decl =
    Ppxlib.Deriving.Generator.make_noarg Jsobject_of_expander_2.sig_type_decl

  let str_type_ext =
    Ppxlib.Deriving.Generator.make_noarg Jsobject_of_expander.str_type_ext

  let name = "jsobject_of"

  let deriver =
    Ppxlib.Deriving.add name
      ~str_type_decl
      ~sig_type_decl
      ~str_type_ext
end

module Of_jsobject_expander = struct
  (* Helpers for creating good error messages *)
  let mk_index ~loc i =
    let ei = eint ~loc i in
    let es = estring ~loc @@ string_of_int i in
    (ei, es)

  let mk_err_expander ~loc path_comp =
    [%expr (fun emsg -> concat_error_messages [%e path_comp] emsg)]

  let mk_type td =
    combinator_type_of_type_declaration
      td ~f:(fun ~loc ty ->
        [%type: Js_of_ocaml.Js.Unsafe.any Js_of_ocaml.Js.t -> ([%t ty], string) result ])

  let mk_ref_type td =
    combinator_type_of_type_declaration
      td ~f:(fun ~loc ty ->
        [%type: (Js_of_ocaml.Js.Unsafe.any Js_of_ocaml.Js.t -> ([%t ty], string) result) ref ])

  let eok ~loc v = pexp_construct
                     ~loc (Located.lident ~loc "Ok") (Some v)
  let err_simple ~loc s = pexp_construct
                            ~loc (Located.lident ~loc "Error")
                            (Some (estring ~loc s))
  let err_var ~loc s var =
    let base = estring ~loc s in
    let full = [%expr [%e base] ^ [%e var]] in
    pexp_construct ~loc (Located.lident ~loc "Error") (Some full)

  let name_of_tdname name = match name with
    | "t" -> "of_jsobject"
    | tn  -> tn ^ "_of_jsobject"

  let name_of_td td = name_of_tdname td.ptype_name.txt
  let name_of_te te = name_of_tdname @@ Longident.last_exn te.ptyext_path.txt
  let full_name_of_te te =
    let names = List.rev @@ Longident.flatten_exn te.ptyext_path.txt in
    match names with
    | [] -> Location.raise_errorf "name_of_te: assert"
    | (fn::rest) ->
       let func_name = name_of_tdname fn in
       let names' = List.rev (func_name::rest) in
       String.concat ~sep:"." names'

  let std_type_of_jsobject id =
    let mark, txt =
      match id.txt with
      | Longident.Lident s ->
         `Fold, Longident.Lident (name_of_tdname s)
      | Longident.Ldot (Longident.Lident "Js", "t") ->
         `FullStop, Longident.Lident "jst_of_jsobject"
      | Longident.Ldot (Longident.Ldot
                          (Longident.Lident "Js", "Unsafe"), "any") ->
         `FullStop, Longident.Lident "jsany_of_jsobject"
      | Longident.Ldot (p, s) ->
         `Fold, Longident.Ldot (p, name_of_tdname s)
      | Longident.Lapply _    -> failwith "ppx_jsobject_conv: type_id_of_jsobject"
    in
    let expr = pexp_ident ~loc:id.loc { id with txt } in
    match mark with
    | `Fold -> `Fold expr
    | `FullStop -> `FullStop expr

  let rec type_of_jsobject tparams typ =
    let loc = typ.ptyp_loc in
    match typ.ptyp_desc with
    | Ptyp_constr (cid, args) ->
       let type_expr = match std_type_of_jsobject cid with
         | `FullStop expr -> expr
         | `Fold init ->
            let args = List.map
                         args
                         ~f:(fun arg ->
                           Fun_or_match.expr
                             ~loc
                             (type_of_jsobject tparams arg)) in
            eapply ~loc init args
       in
       Fun_or_match.Fun type_expr
    | Ptyp_tuple tps -> tuple_of_jsobject ~loc tparams tps
    | Ptyp_variant(row_fields, _, _) ->
       variant_of_jsobject ~loc tparams row_fields
    | Ptyp_var a ->
       let etp, _ = List.assoc a tparams in
       Fun_or_match.Fun etp
    | Ptyp_object(_) | Ptyp_class(_) ->
       Location.raise_errorf ~loc "ppx_jsobject_conv: type_of_jsobject -- classes & objects are not supported yet"
    | Ptyp_package(_) ->
       Location.raise_errorf ~loc "ppx_jsobject_conv: type_of_jsobject -- modules are not supported yet"
    | Ptyp_any  | Ptyp_arrow(_) | Ptyp_alias(_)
      | Ptyp_poly(_) | Ptyp_extension(_) ->
       Location.raise_errorf ~loc "ppx_jsobject_conv: type_of_jsobject -- Unsupported type"
  and tuple_of_jsobject ~loc tparams tps =
    let fps = List.map ~f:(type_of_jsobject tparams) tps in
    let efps = List.map ~f:(Fun_or_match.expr ~loc) fps in
    let _, pvars, evars = Fun_or_match.map_tmp_vars ~loc fps in
    let iefps = List.mapi ~f:(fun i fp -> (i, fp)) efps in
    let inner_expr = eok ~loc (pexp_tuple ~loc evars) in
    let earr, parr = mk_ep_var ~loc "arr" in
    let body = List.fold_right2
                 ~init: inner_expr
                 ~f:(fun pvar (i, fp) acc ->
                   let ei, es = mk_index ~loc i in
                   [%expr
                       array_get_ind [%e earr] [%e ei]
                       >>= [%e fp]
                       >*= [%e mk_err_expander ~loc es]
                       >>= (fun [%p pvar ] ->
                                [%e acc])])
                 pvars iefps
    in
    let num = List.length fps in
    let outer_expr = [%expr
                         (fun t ->
                           is_array_of_size_n
                             t [%e eint ~loc num]
                           >>= (fun [%p parr] -> [%e body]))
                     ] in
    Fun_or_match.Fun outer_expr

  and variant_of_jsobject ~loc tparams row_fields =
    let earr, parr = mk_ep_var ~loc "arr" in
    let item = function
      (* p. variant constructor w/o arguments*)
      | Rtag (cnstr, true , []) ->
         let ecnstr = Ast_helper.Exp.variant ~loc cnstr.txt None in
         (pstring ~loc cnstr.txt -->
            [%expr [%e eok ~loc ecnstr]],
          cnstr.txt)
      (* p. variant constructor w argument *)
      | Rtag (cnstr, false, [tp]) ->
         let ev, pv = mk_ep_var ~loc "v0" in
         let cnstr_fun =
           Fun_or_match.expr ~loc
                             (type_of_jsobject tparams tp) in
         let ecnstr = Ast_helper.Exp.variant ~loc cnstr.txt (Some ev) in
         let ei, es = mk_index ~loc 1 in
         let exp = pstring ~loc cnstr.txt -->
                     [%expr
                         array_get_ind [%e earr] [%e ei]
                      >>= [%e cnstr_fun]
                      >*= [%e mk_err_expander ~loc es]
                      >>= (fun [%p pv] ->
                        [%e eok ~loc ecnstr]
                     )] in
         (exp, cnstr.txt)
      | Rtag(_) | Rinherit(_) ->
         Location.raise_errorf "ppx_jsobject_conv: unsupported variant_of_jsobject"
    in
    let desc_item = fun rf -> item rf.prf_desc in
    let matches, varnames = List.split @@ List.map ~f:desc_item row_fields in
    let unknown_match =
      let allowed = String.concat ~sep:"/" varnames in
      let msg = Printf.sprintf "0: expected one of the %s, got " allowed in
      [pvar ~loc "unknown" -->
         err_var ~loc msg (evar ~loc "unknown")]
    in
    let match_expr = Fun_or_match.expr ~loc @@
                 Fun_or_match.Match (matches @ unknown_match) in
    let outer_expr = [%expr
                         (fun pv ->
                           is_array pv >>=
                             (fun [%p parr] ->
                               array_get_ind [%e earr] 0
                               >>= string_of_jsobject
                               >>= [%e match_expr]))]
    in Fun_or_match.Fun outer_expr


  let rec sum_of_jsobject ~loc tparams cds =
    let conversion = Attrs.define_sum_type_as cds in
    match conversion with
    | `Regular -> sum_of_jsobject_as_array tparams ~loc cds
    | `AsObject -> sum_of_jsobject_as_object tparams ~loc cds
    | `AsEnum -> sum_of_jsobject_as_enum ~loc cds
    | `AsTagless -> sum_of_jsobject_as_tagless ~loc tparams cds

  and mk_unary_cons ~loc tparams cd argname msg =
    let is_constructed, tp_conv = match cd.pcd_args with
      | Pcstr_tuple [a] ->
         false, type_of_jsobject tparams a
      | Pcstr_tuple _ -> Location.raise_errorf ~loc "ppx_jsobject_conv: %s" msg
      | Pcstr_record fields ->
         true, record_of_jsobject ~loc ?inline_of:(Some cd) tparams fields
    in
    let econ = if is_constructed (* Will be wrapped with constructor in
                                      conversion func (inlined records) *)
               then argname
               else (* Can be wrapped here *)
                 econstruct cd (Some(pexp_tuple ~loc [argname]))
    in
    let eres = eok ~loc econ in
    (eres, tp_conv)

  and sum_of_jsobject_as_tagless ~loc tparams cds =
    let eobj, pobj = mk_ep_var ~loc "tagless_obj" in
    let inner_expr =
      let errnames = List.map
                       cds
                       ~f:(fun cd ->
                         let e = evar ~loc ("emsg_" ^ cd.pcd_name.txt) in
                         [%expr "(" ^ [%e e] ^ ")"]) in
      let errlist = elist ~loc errnames in
      let errcon = eapply ~loc [%expr String.concat "; "] [errlist] in
      err_var ~loc "_: neither of possible tagless conversions applicable, possible errors " errcon
    in
    let item acc cd =
      let vanila_name = cd.pcd_name.txt in
      let eca, pca = mk_ep_var ~loc ("a_" ^ vanila_name) in
      let perr = pvar ~loc ("emsg_" ^ vanila_name) in
      let error_msg = "when using as_tagless, all constructors must be unary" in
      let eres, tp_conv = mk_unary_cons ~loc tparams cd eca error_msg in
      let cnv = Fun_or_match.expr ~loc tp_conv in
      [%expr
          [%e cnv] [%e eobj]
          |> (function
              | Ok([%p pca]) -> [%e eres]
              | Error([%p perr]) -> [%e acc])]
    in
    let body = List.fold_left ~init:inner_expr
                              ~f:item
                              cds in
    let outer_expr = [%expr (fun [%p pobj] -> [%e body])] in
    Fun_or_match.Fun outer_expr

  and sum_of_jsobject_as_enum ~loc cds =
    let item cd =
      let cname = (Attrs.constructor_name cd) in
      let pcnstr = pstring ~loc cname in
      (pcnstr -->
         [%expr [%e eok ~loc (econstruct cd None)]],
       cname)
    in
    let matches, cnames = List.split @@ List.map ~f:item cds in
    let unknown_match =
      let allowed = String.concat ~sep:"/" cnames in
      let msg = Printf.sprintf "expected one of the %s, got " allowed in
      [pvar ~loc "unknown" -->
         err_var ~loc msg (evar ~loc "unknown")] in
    let match_expr  = Fun_or_match.expr ~loc @@
                        Fun_or_match.Match (matches @ unknown_match) in
    let outer_expr = [%expr
                         (fun s ->
                           defined_or_error s
                           >>= string_of_jsobject
                           >>= [%e match_expr])]
    in Fun_or_match.Fun outer_expr

  and sum_of_jsobject_as_object ~loc tparams cds =
    let eobj, pobj = mk_ep_var ~loc "obj" in
    let item cd =
      let cname = (Attrs.constructor_name cd) in
      let pcnstr = pstring ~loc cname in
      let field_name = estring ~loc cname in
      let vanila_name = cd.pcd_name.txt in
      let eca, pca = mk_ep_var ~loc ("a_" ^ vanila_name) in
      let vname, pname = mk_ep_var ~loc ("v_" ^ vanila_name) in
      let error_msg = "when using as_object, all constructors must be unary" in
      let eres, tp_conv = mk_unary_cons ~loc tparams cd eca error_msg in
      let conv = Fun_or_match.expr ~loc tp_conv in
      let final_conv = [%expr
                           object_get_key [%e eobj] [%e field_name]
                         >>= (fun [%p pname] ->
                              [%e conv] [%e vname]
                              >*= [%e mk_err_expander ~loc field_name]
                              >>= (fun [%p pca] -> [%e eres]))
                       ]
      in (pcnstr --> final_conv, cname)
    in
    let matches, cnames = List.split @@ List.map ~f:item cds in
    let unknown_match =
      let allowed = String.concat ~sep:"/" cnames in
      let msg = Printf.sprintf "object should contain one key of the %s, got " allowed in
      [pvar ~loc "unknown" -->
         err_var ~loc msg (evar ~loc "unknown")] in
    let match_expr  = Fun_or_match.expr ~loc @@
                        Fun_or_match.Match (matches @ unknown_match) in
    let outer_expr = [%expr
                         (fun r ->
                           is_object r
                           >>= (fun [%p pobj] ->
                            object_get_sole_key [%e eobj]
                            >>= [%e match_expr]))
                     ]
    in
    Fun_or_match.Fun outer_expr

  and sum_of_jsobject_as_array ~loc tparams cds =
    let earr, parr = mk_ep_var ~loc "arr" in
    let item cd =
      let cname = (Attrs.constructor_name cd) in
      let pcnstr = pstring ~loc cname in
      let conv = match cd.pcd_args with
      | Pcstr_tuple [] ->
         [%expr [%e eok ~loc (econstruct cd None)]]
      | Pcstr_tuple args ->
         let fargs = List.map ~f:(type_of_jsobject tparams) args in
         let efargs = List.map ~f:(Fun_or_match.expr ~loc) fargs in
         let _, pvars, evars = Fun_or_match.map_tmp_vars ~loc fargs in
         (* first element is constructor name *)
         let iefargs = List.mapi ~f:(fun i fp -> (i + 1, fp)) efargs in
         let econstr = econstruct cd (Some (pexp_tuple ~loc evars)) in
         let inner_expr = eok ~loc econstr in
         (* (fun [%p input_pvar ~loc ] -> [%e fa] v)
            not very good, maybe generate randomized "input_vars"
            and pass them from the top?
          *)
         List.fold_right2
           ~init: inner_expr
           ~f:(fun pvar (i, fa) acc ->
             let ei, es = mk_index ~loc i in
             [%expr
                 array_get_ind [%e earr] [%e ei]
              >>= [%e fa]
              >*= [%e mk_err_expander ~loc es]
              >>= (fun [%p pvar ] ->
                [%e acc])])
           pvars iefargs
      | Pcstr_record fields ->
         let ei, es = mk_index ~loc 1 in
         let rec_conv = Fun_or_match.expr ~loc @@
                          record_of_jsobject ~loc ?inline_of:(Some cd) tparams fields in
         [%expr
             array_get_ind [%e earr] [%e ei]
             >>= [%e rec_conv]
             >*= [%e mk_err_expander ~loc es]
         ]
      in
      (pcnstr --> conv, cname)
    in
    let matches, cnames = List.split @@ List.map ~f:item cds in
    let unknown_match =
      let allowed = String.concat ~sep:"/" cnames in
      let msg = Printf.sprintf "0: expected one of the %s, got " allowed in
      [pvar ~loc "unknown" -->
         err_var ~loc msg (evar ~loc "unknown")] in
    let match_expr  = Fun_or_match.expr ~loc @@
                        Fun_or_match.Match (matches @ unknown_match) in
    let outer_expr = [%expr
                         (fun s ->
                           is_array s >>=
                             (fun [%p parr] ->
                               array_get_ind [%e earr] 0
                               >>= string_of_jsobject
                               >>= [%e match_expr]))]
    in Fun_or_match.Fun outer_expr

  and mk_rec_details tparams = function
    | {pld_name = {txt=name; loc}; pld_type = tp; _ } as ld ->
       let vname, pname = mk_ep_var ~loc ("v_" ^ name) in
       let field_name = estring ~loc (Attrs.field_name ld) in
       let cnv = Fun_or_match.expr ~loc (type_of_jsobject tparams tp) in
       let cnv' = match Attrs.field_default ld, Attrs.error_default ld with
         | Some _, Some _ ->
            (* this should be handled during attrs parsing *)
            Location.raise_errorf
              ~loc "ppx_jsobject_conv: default_on_error and default attrs can't be used together"
         | Some v, None ->
            [%expr defined_or_default [%e cnv] [%e v]]
         | None, Some v ->
            [%expr convert_or_default [%e cnv] [%e v]]
         | None, None -> cnv
       in
       let lid = Located.lident ~loc name in
       ((lid, vname), (pname, field_name, cnv'))

  and record_of_jsobject ~loc ?inline_of tparams fields =
    let rec_details = List.map ~f:(mk_rec_details tparams) fields in
    let lidexprs, pfc = List.split rec_details in
    let erec = (Ast_helper.Exp.record ~loc lidexprs None) in
    let eres = match inline_of with (* This record is inlined, so it has to be
                                       wrapped with constructor here *)
      | Some cd -> econstruct cd (Some erec)
      | None -> erec
    in
    let inner_expr = eok ~loc eres in
    let eobj, pobj = mk_ep_var ~loc "obj" in
    let item (pname, field_name, cnv) acc =
      [%expr
          object_get_key [%e eobj] [%e field_name]
       >>= [%e cnv]
       >*= [%e mk_err_expander ~loc field_name]
       >>= (fun [%p pname] ->
         [%e acc])]
    in
    let body = List.fold_right ~init: inner_expr ~f:item pfc in
    let outer_expr = [%expr
                         (fun r ->
                           is_object r >>=
                             (fun [%p pobj] ->
                               [%e body]))] in
    Fun_or_match.Fun outer_expr


  let td_of_jsobject td =
    let {ptype_name = {loc = _; txt = type_name}; ptype_loc = loc; _} = td in
    let is_private = (match td.ptype_private with Private -> true | Public -> false) in
    if is_private
    then Location.raise_errorf ~loc "of_jsobject is not supported for private types";
    let tparams = List.map td.ptype_params
                           ~f:(fun tp ->
                             let n = (get_type_param_name tp).txt in
                             let e, p = mk_ep_var ~loc ("_of_" ^ n) in
                             (n, (e, p))) in
    let func_name = name_of_td td in
    let body, sitems =
      match td.ptype_kind with
      | Ptype_abstract -> begin
          match td.ptype_manifest with
          | Some ty -> type_of_jsobject tparams ty, []
          | _ -> Location.raise_errorf ~loc "ppx_jsobject_conv: fully abstract types are not supported"
        end
      | Ptype_variant cds -> sum_of_jsobject ~loc tparams cds, []
      | Ptype_record fields -> record_of_jsobject ~loc tparams fields, []
      | Ptype_open ->
         let stype_name = estring ~loc type_name in
         let default_name = mk_default func_name in
         let recent_evar, recent_pvar = mk_recent_ep_var ~loc func_name in
         let default_func_body =
           [%expr fun _ ->
                  Error
                    ("ppx_jsobject_conv: can't convert, maybe a [@@deriving jsobject] is missing when extending the type " ^
                       [%e stype_name])] in
         let default_func =
           let _, eps = List.split tparams in
           let _, patts = List.split eps in
           let fb = eabstract ~loc patts @@ wrap_runtime ~loc default_func_body in
           let constraint_ = mk_type td in
           constrained_function_binding ~loc ~constraint_
                                        ~func_name:default_name fb
         in
         let most_recent =
           let expr = ref_ ~loc (evar ~loc default_name) in
           value_binding ~loc ~pat:recent_pvar ~expr
         in
         let body =
           let ei, pi = mk_ep_var ~loc "i" in
           let application = unref_apply ~loc recent_evar [ei] in
           Fun_or_match.Match [pi --> application] in
         body, [default_func; most_recent]
    in
    let body' = match body with
      | Fun_or_match.Fun fun_expr -> [%expr fun [%p input_pvar ~loc] ->
                                            [%e fun_expr] [%e input_evar ~loc]]
      | Fun_or_match.Match matchings -> pexp_function ~loc matchings
    in
    let body'' =
      let _, eps = List.split tparams in
      let _, patts = List.split eps in
      eabstract ~loc patts @@ wrap_runtime ~loc body'
    in
    List.append sitems [constrained_function_binding ~loc ~func_name body'']

  let str_type_decl ~loc ~path:_ (rec_flag, tds) =
    let rec_flag = really_recursive rec_flag tds in
    let bindings = List.map tds ~f:td_of_jsobject |> List.concat in
    [pstr_value ~loc rec_flag bindings]


  let sig_type_decl ~loc:_ ~path:_ (_rf, tds) =
    List.concat
    @@ List.map
         tds
         ~f:(fun td ->
           let type_ = mk_type td in
           let func_name = name_of_td td in
           let loc = td.ptype_loc in
           let type_func = psig_value ~loc
                                      (value_description
                                         ~loc ~name:{ td.ptype_name
                                                    with txt = func_name }
                                         ~type_ ~prim:[]) in
           match td.ptype_kind with
           | Ptype_open ->
              let default_name = { td.ptype_name with
                                   txt = mk_default func_name } in
              let default_sig = psig_value ~loc
                                           (value_description
                                              ~loc
                                              ~name:default_name
                                              ~type_
                                              ~prim:[]) in
              let recent_name = { td.ptype_name with
                                  txt = mk_recent func_name } in
              let ref_sig = psig_value ~loc
                                       (value_description
                                          ~loc
                                          ~name:recent_name
                                          ~type_:(mk_ref_type td)
                                          ~prim:[]) in
              [default_sig; ref_sig; type_func]
           | Ptype_abstract | Ptype_variant _ | Ptype_record _ ->
              [type_func])


  let str_type_ext ~loc ~path:_ te =
    let constructors = te.ptyext_constructors in
    let make_cd = function
      | {pext_kind; pext_name; pext_loc; pext_attributes } ->
         (match pext_kind with
          | Pext_decl (vars, cons_args, ctyp) ->
             {
               pcd_name = pext_name;
               pcd_args = cons_args;
               pcd_vars = vars;
               pcd_res = ctyp;
               pcd_loc = pext_loc;
               pcd_attributes = pext_attributes;
             }
          | Pext_rebind _ ->
             Location.raise_errorf ~loc "ppx_jsobject_conv: rebinds are not supported in type extensions!"
         )
    in
    let cds = List.map constructors ~f:make_cd in
    let tparams = List.map te.ptyext_params
                           ~f:(fun tp ->
                             let n = (get_type_param_name tp).txt in
                             let e, p = mk_ep_var ~loc ("_of_" ^ n) in
                             (n, (e, p))) in
    let func_name = name_of_te te in
    let previous_evar, previous_pvar = mk_ep_var ~loc
                                       @@ func_name ^ "_previous" in
    let body = sum_of_jsobject ~loc tparams cds in
    (* body of function, responsible for converting newly introduced
       variant constructors; unknown constructors will be redirected
       to previously defined function *)
    let body' = match body with
      | Fun_or_match.Fun fun_expr ->
         let previous_definition = eapply ~loc previous_evar [input_evar ~loc] in
         [%expr fun [%p input_pvar ~loc] ->
                match [%e fun_expr] [%e input_evar ~loc] with
                | Error _ -> [%e previous_definition]
                | asis -> asis
         ]
      | Fun_or_match.Match _ ->
         Location.raise_errorf ~loc "ppx_jsobject_conv: impossible state"
    in
    let body'' =
      let _, eps = List.split tparams in
      let _, patts = List.split eps in
      eabstract ~loc patts @@ wrap_runtime ~loc body'
    in
    (* statement for saving previously defined function: it is used in
       wildcard pattern above *)
    let recent_evar, _recent_pvar = mk_recent_ep_var ~loc
                                   @@ full_name_of_te te in
    let previous_body =
      let expr = unref ~loc recent_evar in
      value_binding ~loc ~pat:previous_pvar ~expr
    in
    (* update most recent definition with our function *)
    let recent_body =
      let pat = punit ~loc in
      let assign_var = evar ~loc ":=" in
      let efunc = evar ~loc func_name in
      let expr = eapply ~loc assign_var [recent_evar; efunc] in
      value_binding ~loc ~pat ~expr
    in
    let rec_bindings = [
        previous_body;
        constrained_function_binding ~loc ~func_name body''] in
    let bindings = [recent_body] in
    [pstr_value ~loc Recursive rec_bindings;
     pstr_value ~loc Nonrecursive bindings]

  let core_type ty =
    (* Conserned about empty type_name *)
    type_of_jsobject [] ty |> Fun_or_match.expr ~loc:ty.ptyp_loc

end

module Of_jsobject_expander_2 = struct
  open Stdlib
  open Parsetree
  [@@@ocaml.warning "-8"]

  let name_of_tdname name = match name with
    | "t" -> "of_jsobject"
    | tn  -> tn ^ "_of_jsobject"

  let name_of_td td = name_of_tdname td.ptype_name.txt
  let name_of_te te = name_of_tdname @@ Longident.last_exn te.ptyext_path.txt

  let converter_type ty : core_type =
    let loc = match ty with {%core_type.noattr.loc| $_$ |} -> loc in
    {%core_type| Js_of_ocaml.Js.Unsafe.any Js_of_ocaml.Js.t -> ($ty$, string) result |}


  let td_to_fun_type td =
    let (loc,  pl, tname) =
      match td with
        {%type_decl.noattr.loc| $list:pl$ $lid:tname$ |} -> (loc, pl, tname)
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ |} -> (loc, pl, tname)
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $constructorlist:_$ |} -> (loc, pl, tname)
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = { $list:_$ } |} -> (loc, pl, tname)
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ = $constructorlist:_$ |} -> (loc, pl, tname)
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ = { $list:_$ } |} -> (loc, pl, tname)
    in
    let rhs_t = converter_type {%core_type| $list:List.map fst pl$ $lid:tname$ |} in
    List.fold_right (fun (pv, _) rhs_t ->
        {%core_type| $converter_type pv$ -> $rhs_t$ |})
      pl rhs_t

  let sig_type_decl ~loc:_ ~path:_ (_rf, tds) =
    tds
    |> List.concat_map (fun td ->
           let fun_type = td_to_fun_type td in
           let func_name = name_of_td td in
           let loc = td.ptype_loc in
           [{%signature_item| val $lid:func_name$ : $fun_type$ |}])

  [@@@ocaml.warning "-39-27"]
  let rec core_type_to_of_jsobject ?offset ?wrap_body rho ty =
    match ty with
        {%core_type.noattr.loc| ' $lid:v$ |} ->
        let f = match List.assoc v rho with
            exception Not_found ->
             failwith Fmt.(str "core_type_to_jsobject_of: unknown type-var %a" Std_derivers.pp_core_type ty)
          | x -> x in
         f

      | {%core_type.noattr.loc| int |} ->
         {%expression|int_of_jsobject|}

      | {%core_type.noattr.loc| bool |} ->
         {%expression|bool_of_jsobject|}

      | {%core_type.noattr.loc| string |} ->
         {%expression|string_of_jsobject|}

      | {%core_type.noattr.loc| $ty$ array |} ->
         let conv = core_type_to_of_jsobject rho ty in
         {%expression| array_of_jsobject $conv$ |}

      | {%core_type.noattr.loc| $ty$ list |} ->
         let conv = core_type_to_of_jsobject rho ty in
         {%expression| list_of_jsobject $conv$ |}

      | {%core_type.noattr.loc| $ty$ option |} ->
         let conv = core_type_to_of_jsobject rho ty in
         {%expression| option_of_jsobject $conv$ |}

      | {%core_type.noattr.loc| $lid:tname$ |} ->
         let fname = name_of_tdname tname in
         {%expression| $lid:fname$ |}

      | {%core_type.noattr.loc| $longid:li$ . $lid:tname$ |} ->
         let fname = name_of_tdname tname in
         {%expression| $longid:li$ . $lid:fname$ |}

      | {%core_type.noattr.loc| $list:tyl$ $lid:tname$ |} ->
         let fname = name_of_tdname tname in
         let params = List.map (core_type_to_of_jsobject rho) tyl in
         let params = List.map (fun e -> (Asttypes.Nolabel,e)) params in
         {%expression| ($lid:fname$ $list:params$) |}

      | {%core_type.noattr.loc| $list:tyl$ $longid:li$ . $lid:tname$ |} ->
         let fname = name_of_tdname tname in
         let params = List.map (core_type_to_of_jsobject rho) tyl in
         let params = List.map (fun e -> (Asttypes.Nolabel,e)) params in
         {%expression| ( $longid:li$ . $lid:fname$ $list:params$ ) |}

      | {%core_type.noattr.loc| $tuplelist:tyl$ |} ->
         let len = List.length tyl in
         let convert1 i ty =
           let var = Printf.sprintf "v_%d" i in
           let patt = {%pattern| $lid:var$ |} in
           let expr = {%expression| $lid:var$ |} in
           let conv = core_type_to_of_jsobject rho ty in
           let offset_plus_i = match offset with None -> i | Some j -> i+j in
           (string_of_int offset_plus_i, var,patt,expr,conv) in
         let ind_var_patt_expr_conv_list = List.mapi convert1 tyl in
         let exprs = ind_var_patt_expr_conv_list |> List.map (fun (_,_,_,e,_) -> e) in
         let rhs = match wrap_body with
             None -> {%expression| Ok ( $tuplelist:exprs$ ) |}
           | Some cid -> {%expression| Ok ( $uid:cid$ ( $tuplelist:exprs$ ) ) |}
         in
         let rhs =
           List.fold_right (fun (i,v,p,e,conv) rhs ->
               {%expression|
                (((array_get_ind arr $int:i$) >>= $conv$)
                 >*= (fun emsg -> concat_error_messages $string:i$ emsg))
                >>= (fun $lid:v$ -> $rhs$) |})
             ind_var_patt_expr_conv_list rhs
         in
         let offset_plus_len = match offset with None -> len | Some j -> len+j in
         {%expression| fun v ->
           (is_array_of_size_n v $int:string_of_int offset_plus_len$) >>=
             (fun arr -> $rhs$) |}

      | ct ->
         failwith Fmt.(str "core_type_to_of_jsobject: unhandled core_type: %a" Std_derivers.pp_core_type ct)

  let record_type_to_of_jsobject ~loc rho ll =
    let field_name_jsfldname_var_longid_expr_conv_list =
      ll
      |> List.map (function
               {%label_declaration.noattr.loc| $mutable:_$ $lid:fldname$ : $fldty$ |} as ld ->
               let var = Printf.sprintf "v_%s" fldname in
               let longid = OrigLocation.mkloc {%longident_t| $lid:fldname$ |} loc in
               let expr = {%expression| $lid:var$ |} in
               let conv = core_type_to_of_jsobject rho fldty in
               let jsfldname = Attrs.field_name ld in
               (fldname, jsfldname, var, longid, expr, conv)) in
    let exprfields = 
      field_name_jsfldname_var_longid_expr_conv_list
      |> List.map (fun (_,_,_,li,e,_) -> (li,e)) in
    let rhs = {%expression| Ok { $list:exprfields$ } |} in
    let rhs = List.fold_right (fun (fldname,  jsfldname,var,li,e,conv) rhs ->
                  {%expression|
                   (((object_get_key obj $string:jsfldname$) >>= $conv$) >*=
                      (fun emsg -> concat_error_messages $string:fldname$ emsg))
                   >>= (fun $lid:var$ -> $rhs$)
                   |}
                )
                field_name_jsfldname_var_longid_expr_conv_list rhs in
    {%expression| fun r -> (is_object r) >>= (fun obj -> $rhs$) |}

  let td_to_of_jsobject = function
    {%type_decl.noattr.loc| $list:pl$ $lid:tname$ |} -> []
  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $ty$ |} ->
     let fname = name_of_tdname tname in
     let rho = pl |>  List.map (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) ->
                          let fname = Printf.sprintf "_of_%s" v in
                          (v, {%expression| $lid:fname$ |})) in
     let rhs = core_type_to_of_jsobject rho ty in
     let rhs = List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
                   let fname = Printf.sprintf "_of_%s" v in
                   {%expression| fun $lid:fname$ -> $rhs$ |})
                 pl rhs in
     [{%value_binding| $lid:fname$ = $rhs$ |}]


  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $constructorlist:cl$ |} when Attrs.define_sum_type_as cl = `Regular ->
     let fname = name_of_tdname tname in
     let rho = pl |>  List.map (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) ->
                          let fname = Printf.sprintf "_of_%s" v in
                          (v, {%expression| $lid:fname$ |})) in
     let cases =
       cl
       |> List.map (function cd ->
              let jscid = Attrs.constructor_name cd in
              match cd with
                {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
                 let rhs = {%expression| Ok $uid:cid$ |} in
                 (jscid, rhs)
              | {%constructor_declaration.noattr.loc| $uid:cid$ of $ty$ |} ->
                 let rhs = core_type_to_of_jsobject rho ty in
                 let rhs = {%expression|
                            (((array_get_ind arr 1) >>= $rhs$) >*=
                            (fun emsg -> concat_error_messages "1" emsg))
                            >>= (fun v0 -> Ok ($uid:cid$ v0))
                  |} in
                 (jscid, rhs)
              | {%constructor_declaration.noattr.loc| $uid:cid$ of $list:tyl$ |} ->
                 let rhs = core_type_to_of_jsobject ~offset:1 ~wrap_body:cid rho {%core_type| $tuplelist:tyl$ |} in
                 let rhs = {%expression| $rhs$ v |} in
                 (jscid, rhs))
       |> List.map (fun (cid, rhs) ->
              {%case| $string:cid$ -> $rhs$ |}
            ) in
     let cases = cases @ [
           let cids =
             cl
             |> List.map (function {%constructor_declaration.noattr| $uid:cid$ of $list:_l$ |} -> cid) in
           let msg = Fmt.(str "0: expected one of the %a, got " (list ~sep:(const string  "/") string) cids) in
           {%case| unknown -> Error ($string:msg$ ^ unknown) |}
         ]
     in
     let rhs = {%expression| function $list:cases$ |} in
     let rhs = {%expression|
                fun v -> (is_array v) >>=
                  (fun arr ->
                    ((array_get_ind arr 0) >>= string_of_jsobject) >>= $rhs$ ) |} in

     let rhs = List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
                   let fname = Printf.sprintf "_of_%s" v in
                   {%expression| fun $lid:fname$ -> $rhs$ |})
                 pl rhs in
     [{%value_binding| $lid:fname$ = $rhs$ |}]

  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $constructorlist:cl$ |} when Attrs.define_sum_type_as cl = `AsTagless ->
     let fname = name_of_tdname tname in
     let rho = pl |>  List.map (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) ->
                          let fname = Printf.sprintf "_of_%s" v in
                          (v, {%expression| $lid:fname$ |})) in
     let cases =
       cl
       |> List.map (function
                {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
                 failwith Fmt.(str "core_type_to_jsobject_of: cannot tagless-ly demarshal nullary constructor: %s" cid)
              | {%constructor_declaration.noattr.loc| $uid:cid$ of $ty$ |} ->
                 let rhs = core_type_to_of_jsobject rho ty in
                 (cid, rhs)
              | {%constructor_declaration.noattr.loc| $uid:cid$ of $list:tyl$ |} ->
                 failwith Fmt.(str "core_type_to_jsobject_of: can only tagless-ly demarshal single-argument constructor: %s" cid)
            ) in
     let fallthru = {%expression| Error emsg |} in
     let rhs = List.fold_right (fun (cid, demarsh) rhs ->
                   {%expression|
                    ($demarsh$ v)
                    |> (function
                        | Ok v1 -> Ok ($uid:cid$ v1)
                        | Error msg1 ->
                           let emsg = emsg ^ "("^msg1^"); " in
                           $rhs$)
                    |})
                 cases fallthru in
     let rhs = {%expression|
                fun v ->
                let emsg = "_: neither of possible tagless conversions applicable, possible errors: " in
                $rhs$ |} in

     let rhs = List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
                   let fname = Printf.sprintf "_of_%s" v in
                   {%expression| fun $lid:fname$ -> $rhs$ |})
                 pl rhs in
     [{%value_binding| $lid:fname$ = $rhs$ |}]

  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = { $list:ll$ } |} ->
     let fname = name_of_tdname tname in
     let rho = pl |>  List.map (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) ->
                          let fname = Printf.sprintf "_of_%s" v in
                          (v, {%expression| $lid:fname$ |})) in
     let rhs = record_type_to_of_jsobject ~loc rho ll in
     let rhs = List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
                   let fname = Printf.sprintf "_of_%s" v in
                   {%expression| fun $lid:fname$ -> $rhs$ |})
                 pl rhs in
     [{%value_binding| $lid:fname$ = $rhs$ |}]

  let str_type_decl ~loc ~path:_ (rec_flag, tds) =
    let rec_flag = really_recursive rec_flag tds in
    let bindings = tds |> List.concat_map td_to_of_jsobject in
    let bindings =
      bindings
      |> List.map (fun
               {%value_binding.noattr.loc| $lid:fname$ = $e$ |} ->
             let e = {%expression| let open! Ppx_jsobject_conv_runtime in $e$ |} in
             {%value_binding.noattr.loc| $lid:fname$ = $e$ |}) in
    [{%structure_item| let $recflag:rec_flag$ $list:bindings$ |}]

end

module Of_jsobject = struct
  let str_type_decl =
    Ppxlib.Deriving.Generator.make_noarg
      Of_jsobject_expander_2.str_type_decl
      ~attributes:[Attribute.T Attrs.name;
                   Attribute.T Attrs.key;
                   Attribute.T Attrs.sum_type_as;
                   Attribute.T Attrs.default;
                   Attribute.T Attrs.default_on_error;
                  ]

  let sig_type_decl =
    Ppxlib.Deriving.Generator.make_noarg Of_jsobject_expander_2.sig_type_decl

  let str_type_ext =
    Ppxlib.Deriving.Generator.make_noarg Of_jsobject_expander.str_type_ext

  let name = "of_jsobject"

  let deriver =
    Ppxlib.Deriving.add name
      ~str_type_decl
      ~sig_type_decl
      ~str_type_ext
end


let () =
  Ppxlib.Deriving.add_alias "jsobject"
                      [Jsobject_of.deriver ;
                       Of_jsobject.deriver
                      ]
                      ~sig_exception:[Jsobject_of.deriver]
                      ~str_exception:[Jsobject_of.deriver]
  |> Ppxlib.Deriving.ignore;;
