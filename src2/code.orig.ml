open Syntax

open Stdlib
open OurSyntax.Ast
module Longident = Ppxlib.Longident
open Parsetree
open Location

let convFromLib_type_decls (rec_flag,tds) =
  let loc = Location.none in
  (match ConvFromLib.copy_structure LibSyntax.Ast.[{%structure_item| type $nonrecflag:rec_flag$ $list:tds$ |}] with
     OurSyntax.Ast.([{%structure_item| type $nonrecflag:rec_flag$ $list:tds$ |}]) ->  (rec_flag, tds))[@ocaml.warning "-8"]

module LocOf = struct
  let constructor_declaration cd = cd.pcd_loc
  let label_declaration ld = ld.pld_loc
  let attribute a = a.attr_loc
end

module Attribute = struct
  module Context = struct
    let constructor_declaration cd = cd.pcd_attributes
    let label_declaration ld  = ld.pld_attributes
  end

  let attr_names name =
    let parts = String.split_on_char '.' name in
    let rec nrec l = match l with
        [] -> []
      | _::t ->
         (String.concat "." l)::(nrec t) in
    nrec parts

  let declare name ctxt conv =
    let names = attr_names name in
    (names, ctxt, conv)

  let get (names, ctxt, conv) it =
    let l = ctxt it in
    match l |> List.filter (fun a -> List.mem a.attr_name.txt names) with
      [] ->  None
    | h::_ -> Some (conv h)
end

module Attrs = struct
  let name = Attribute.declare "jsobject.name"
               Attribute.Context.constructor_declaration
               (function
                  {%attribute| [@ $attrid:_$ $string:s$ ] |} -> s
                | a ->
                   Location.raise_errorf
                     ~loc:(LocOf.attribute a) "ppx_jsobject_conv: malformed attribute jsobject.name")

  let constructor_name cd  =
    match Attribute.get name cd with
    | Some(v) -> v
    | None -> cd.pcd_name.txt

  let key = Attribute.declare "jsobject.key"
               Attribute.Context.label_declaration
               (function
                  {%attribute| [@ $attrid:_$ $string:s$ ] |} -> s
                | a ->
                   Location.raise_errorf
                     ~loc:(LocOf.attribute a) "ppx_jsobject_conv: malformed attribute jsobject.key")

  let field_name ld =
    match Attribute.get key ld with
    | Some(v) -> v
    | None -> ld.pld_name.txt

  let drop_none = Attribute.declare "jsobject.drop_none"
               Attribute.Context.label_declaration
               (function
                  {%attribute| [@ $attrid:_$ ] |} -> ()
                | a ->
                   Location.raise_errorf
                     ~loc:(LocOf.attribute a) "ppx_jsobject_conv: malformed attribute jsobject.drop_none")

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

  let default_on_error = Attribute.declare "jsobject.default_on_error"
               Attribute.Context.label_declaration
               (function
                  {%attribute| [@ $attrid:_$ $expr:e$ ] |} -> e
                | a ->
                   Location.raise_errorf
                     ~loc:(LocOf.attribute a) "ppx_jsobject_conv: malformed attribute jsobject.default_on_error")

  let default = Attribute.declare "jsobject.default"
               Attribute.Context.label_declaration
               (function
                  {%attribute| [@ $attrid:_$ $expr:e$ ] |} -> e
                | a ->
                   Location.raise_errorf
                     ~loc:(LocOf.attribute a) "ppx_jsobject_conv: malformed attribute jsobject.default")

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

  let sum_type_as = Attribute.declare "jsobject.sum_type_as"
               Attribute.Context.constructor_declaration
               (function
                  {%attribute| [@ $attrid:_$ $string:s$ ] |} -> s
                | a ->
                   Location.raise_errorf
                     ~loc:(LocOf.attribute a) "ppx_jsobject_conv: malformed attribute jsobject.sum_type_as")

  let define_constructor_as cd  =
    match Attribute.get sum_type_as cd with
    | Some("object") -> `AsObject
    | Some("enum") -> `AsEnum
    | Some("tagless") -> `AsTagless
    | Some("regular") -> `Regular
    | Some(b) -> Location.raise_errorf ~loc:(LocOf.constructor_declaration cd) "ppx_jsobject_conv: sum_type_as only accepts object/enum/tagless/regular, got %s" b
    | None -> `Regular

  let define_sum_type_as cds =
    let conversions = List.map define_constructor_as cds in
    let uniq = List.sort_uniq Stdlib.compare conversions in
    let special = List.filter (function
                                  | `Regular -> false
                                  | _ -> true) uniq in
    match special with
    | [] -> `Regular
    | [n] -> n
    | _ -> Location.raise_errorf
             ~loc:((List.hd cds).pcd_loc)
             "ppx_jsobject_conv: sum type should have at most one distinct sum_type_as attribute"
end

let convert_down_list_expr f e =
  let rec crec acc = function
      {%expression| [] |} -> List.rev acc
    | {%expression| $h$ :: $tl$ |} ->
       crec (f h :: acc) tl
    | _ -> failwith Fmt.(str "convert_down_list_expr: malformed list-expression %a"
                           pp_expression e)
  in
  crec [] e

let convert_up_list_expr loc el =
  List.fold_right (fun e rhs -> {%expression| $e$ :: $rhs$ |}) el {%expression| [] |}

let suppress_unused_rec bindings =
  match bindings with
    [] ->  assert false
  | {%value_binding.noattr.loc| $patt$ = $expr$ |}::t ->
     {%value_binding.loc| $patt$ = $expr$ [@@ocaml.warning "-39"] |}::t

module Jsobject_of_expander = struct
  [@@@ocaml.warning "-8"]
  let name_of_tdname name = match name with
    | "t" -> "jsobject_of"
    | tn  -> "jsobject_of_" ^ tn

  let name_of_td td = name_of_tdname td.ptype_name.txt
  let name_of_te te = name_of_tdname @@ Longident.last_exn te.ptyext_path.txt

  let converter_type ty =
    let loc = match ty with {%core_type.noattr.loc| $_$ |} -> loc in
    {%core_type| $ty$ -> Js_of_ocaml.Js.Unsafe.any Js_of_ocaml.Js.t |}

  let fun_type ~loc pl tname =
    let rhs_t = converter_type {%core_type| $list:List.map fst pl$ $lid:tname$ |} in
    let ftype =
      List.fold_right (fun (pv, _) rhs_t ->
          {%core_type| $converter_type pv$ -> $rhs_t$ |})
        pl rhs_t in
    let tvl = List.map (fun ({%core_type.noattr| ' $lid:v$ |}, _) -> Location.{txt=v; loc=loc}) pl in
    (tvl, ftype)

  let td_to_sig_items td =
      match td with
        {%type_decl.noattr.loc| $list:pl$ $lid:tname$ |}
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ |}
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $constructorlist:_$ |}
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = { $list:_$ } |}
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ = $constructorlist:_$ |}
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ = { $list:_$ } |} ->
         let (_tvl,ftype) = fun_type ~loc pl tname in
         let func_name = name_of_tdname tname in
         [{%signature_item| val $lid:func_name$ : (* $list:tvl$ . *) $ftype$ |}]

      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = .. |} ->
         let (tvl, ftype) = fun_type ~loc pl tname in
         let func_name = name_of_tdname tname in
         let default_fname = func_name^"_default" in
         let ref_type_name = func_name^"_ref_t" in
         let ref_name = func_name^"_ref" in
         [
           {%signature_item| type $lid:ref_type_name$ = { mutable $lid:func_name$ : $list:tvl$ . $ftype$ }|}
         ; {%signature_item| val $lid:default_fname$ : (* $list:tvl$ . *) $ftype$ |}
         ; {%signature_item| val $lid:ref_name$ : $lid:ref_type_name$ |}
         ; {%signature_item| val $lid:func_name$ : (* $list:tvl$ . *) $ftype$ |}
         ]

  let sig_type_decl ~loc:_ ~path:_ (_rf, tds) =
    tds
    |> List.concat_map td_to_sig_items

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

  let polyvariant_pattern ~loc cid patt =
    {%pattern| ` $id:cid$ $patt$ |}
  let constructor_pattern ~loc cid patt =
    {%pattern| $uid:cid$ $patt$ |}

  let modify_pattern ~polyvariant ~loc cid =
    if polyvariant then
      polyvariant_pattern ~loc cid
    else 
      constructor_pattern ~loc cid

  [@@@ocaml.warning "-39-27"]
  let rec core_type_to_jsobject_of_fun loc rho ty =
    let cases = core_type_to_jsobject_of rho ty in
    {%expression| function $list:cases$ |}

  and core_type_to_jsobject_of ?(modify_pattern = (fun x -> x)) ?(modify_body=(fun x -> x)) rho ty =
    let cases = match ty with
        {%core_type.noattr.loc| ' $lid:v$ |} ->
        let f = match List.assoc v rho with
            exception Not_found ->
             failwith Fmt.(str "core_type_to_jsobject_of: unknown type-var %a" pp_core_type ty)
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

      | {%core_type.noattr.loc| [ $list:rfl$ ] |} ->
         let cl =
           rfl
           |> List.map (function
                    {%row_field| $_$ |} ->
                     failwith Fmt.(str "jsobject_of: variant cannot include inheritance: %a" pp_core_type ty)
                  | {%row_field.noattr.loc| ` $id:cid$ |} ->
                     {%constructor_declaration| $uid:cid$ |}
                  | {%row_field.noattr.loc| ` $id:cid$ of $ty$ |} ->
                     {%constructor_declaration| $uid:cid$ of $ty$ |}
                  | rf ->
                     failwith Fmt.(str "jsobject_of: unrecognized row_field in type %a" pp_core_type ty)
                ) in
         variant_type_to_jsobject_of ~loc ~polyvariant:true rho cl

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
         failwith Fmt.(str "core_type_to_jsobject_of: unhandled core_type: %a" pp_core_type ct)

    in
    cases
    |>  List.map (function
              {%case.noattr.loc| $patt$ -> $body$ |} ->
              let patt = modify_pattern patt in
              let body = modify_body body in
              {%case.noattr.loc| $patt$ -> $body$ |}) 

  and record_type_to_jsobject_of ?(modify_pattern = (fun x -> x)) ~loc rho ll =
    let field_name_var_longid_patt_conv_dropnone_list =
      ll
      |> List.map (function
               {%label_declaration.noattr.loc| $mutable:_$ $lid:fldname$ : $fldty$ |} as ld ->
               let var = Printf.sprintf "v_%s" fldname in
               let longid = Location.mkloc {%longident_t| $lid:fldname$ |} loc in
               let patt = {%pattern| $lid:var$ |} in
               let conv = core_type_to_jsobject_of rho fldty in
               let jsfldname = Attrs.field_name ld in
               let drop_none = Attrs.should_drop_none ld in
               (jsfldname, var, longid, patt, conv, drop_none)) in
    let pattfields = 
      field_name_var_longid_patt_conv_dropnone_list
      |> List.map (fun (_,_,li,p,_,_) -> (li,p)) in
    let patt = {%pattern| { $list:pattfields$ } |} in
    let patt = modify_pattern patt in
    let jstuples =
      field_name_var_longid_patt_conv_dropnone_list
      |> List.map (fun (jsfldname,var,_,_,conv,dropnone) ->
             if dropnone then
               {%expression|
                (match $lid:var$ with
                 | Some _ ->
                    Some ($string:jsfldname$, ((function $list:conv$) $lid:var$))
                 | None -> None)
                |}
             else
               {%expression| Some ($string:jsfldname$, ((function $list:conv$) $lid:var$)) |}
           ) in
    {%case| $patt$ -> make_jsobject_of_some [| $list:jstuples$ |] |}

  and variant_type_to_jsobject_of ~loc ?(polyvariant=false) rho cl =
    if Attrs.define_sum_type_as cl = `Regular then
       cl
       |> List.concat_map (function cd ->
              let jscid = Attrs.constructor_name cd in
              match cd with
                {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
                 let patt =
                   if polyvariant then
                     {%pattern| ` $id:cid$ |}
                   else
                     {%pattern| $uid:cid$ |} in
                 [{%case| $patt$ -> to_js_array [jsobject_of_string $string:jscid$] |}]

              | {%constructor_declaration.noattr.loc| $uid:cid$ of $ty$ |} ->
                 core_type_to_jsobject_of
                   ~modify_pattern:(modify_pattern ~polyvariant ~loc cid)
                   ~modify_body:(do_wrap_body jscid) rho ty

              | {%constructor_declaration.noattr.loc| $uid:cid$ of { $list:ll$ } |} ->
                 (match record_type_to_jsobject_of ~loc ~modify_pattern:(modify_pattern ~polyvariant:false ~loc cid) rho ll with
                    {%case| $patt$ -> $expr$ |} ->
                     [{%case| $patt$ ->  let v = $expr$ in to_js_array [jsobject_of_string $string:jscid$; v] |}]
                 )

              | {%constructor_declaration.noattr.loc| $uid:cid$ of $list:tyl$ |} ->
                 core_type_to_jsobject_of
                   ~modify_pattern:(modify_pattern ~polyvariant ~loc cid)
                   ~modify_body:(do_prepend_body jscid) rho {%core_type| $tuplelist:tyl$ |})
    else if Attrs.define_sum_type_as cl = `AsTagless then
     cl
     |> List.concat_map (function
              {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
               failwith Fmt.(str "core_type_to_jsobject_of: cannot tagless-ly marshal nullary constructor: %s" cid)

            | {%constructor_declaration.noattr.loc| $uid:cid$ of $ty$ |} ->
               core_type_to_jsobject_of
                 ~modify_pattern:(modify_pattern ~polyvariant ~loc cid)
                 rho ty

              | {%constructor_declaration.noattr.loc| $uid:cid$ of { $list:ll$ } |} ->
                 [record_type_to_jsobject_of ~loc ~modify_pattern:(modify_pattern ~polyvariant:false ~loc cid) rho ll]

            | {%constructor_declaration.noattr.loc| $uid:cid$ of $list:tyl$ |} ->
               core_type_to_jsobject_of
                 ~modify_pattern:(modify_pattern ~polyvariant ~loc cid)
                 rho {%core_type| $tuplelist:tyl$ |})

    else if Attrs.define_sum_type_as cl = `AsObject then
     cl
     |> List.map (function cd ->
            let jscid = Attrs.constructor_name cd in
            match cd with
              {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
               {%case| $uid:cid$ -> make_jsobject [|($string:jscid$, to_js_array [])|] |}

            | {%constructor_declaration.noattr.loc| $uid:cid$ of $ty$ |} ->
               let conv_cases = core_type_to_jsobject_of rho ty in
               let conv = {%expression| function $list:conv_cases$ |} in
               {%case| $uid:cid$ v -> let v = $conv$ v in make_jsobject [|($string:jscid$, v)|] |}

            | {%constructor_declaration.noattr.loc| $uid:cid$ of { $list:ll$ } |} ->
               (match record_type_to_jsobject_of ~loc ~modify_pattern:(modify_pattern ~polyvariant:false ~loc cid) rho ll with
                  {%case| $patt$ -> $expr$ |} ->
                  {%case|
                   $patt$ -> let v = $expr$ in make_jsobject [|($string:jscid$, v)|] |})

            | {%constructor_declaration.noattr.loc| $uid:cid$ of $list:tyl$ |} ->
               failwith Fmt.(str "variant type as_object only with nullary/unary constructors: %s" cid)
          )

    else if Attrs.define_sum_type_as cl = `AsEnum then
     cl
     |> List.map (function cd ->
            let jscid = Attrs.constructor_name cd in
            match cd with
              {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
               {%case| $uid:cid$ -> jsobject_of_string $string:jscid$ |}

            | _ ->
               failwith Fmt.(str "variant type as_enum only with nullary constructors")
          )

    else assert false

  let wrapper_with_fun_type ~loc pl tname = function
      {%value_binding| $lid:f$ = $e$ |} ->
      let (tvl, ftype) = fun_type ~loc pl tname in
      {%value_binding| $lid:f$ : $list:tvl$ . $ftype$ = $e$ |} 

  let wrapper_with_newtype ~loc pl rhs =
    List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
        Parsetree.{pexp_desc=Pexp_newtype(Location.{txt=v;loc=loc}, rhs);
                   pexp_loc=loc;
                   pexp_loc_stack=[];
                   pexp_attributes=[]})
      pl rhs

  let build_rho pl =
    pl |>  List.map (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) ->
               let fname = Printf.sprintf "_of_%s" v in
               (v, {%expression| $lid:fname$ |}))

  let prepend_params pl rhs =
    List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
        let fname = Printf.sprintf "_of_%s" v in
        let argty = converter_type {%core_type| $lid:v$ |} in
        {%expression| fun ( $lid:fname$ : $argty$ ) -> $rhs$ |})
      pl rhs

  let td_to_jsobject_of = function
    {%type_decl.noattr.loc| $list:pl$ $lid:tname$ |} -> ([],[])
  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $ty$ |} ->
     let fname = name_of_tdname tname in
     let rho = build_rho pl in
     let cases = core_type_to_jsobject_of rho ty in
     let rhs = {%expression| function $list:cases$ |} in
     let rhs = prepend_params pl rhs in
     let rhs = wrapper_with_newtype ~loc pl rhs in
     ([],
      [wrapper_with_fun_type ~loc pl tname
         {%value_binding| $lid:fname$ v = let open! Ppx_jsobject_conv_runtime in $rhs$ v |}])

  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $constructorlist:cl$ |} ->
     let fname = name_of_tdname tname in
     let rho = build_rho pl in
     let cases = variant_type_to_jsobject_of ~loc rho cl in
     let rhs = {%expression| function $list:cases$ |} in
     let rhs = prepend_params pl rhs in
     let rhs = wrapper_with_newtype ~loc pl rhs in
     ([],
      [wrapper_with_fun_type ~loc pl tname
         {%value_binding| $lid:fname$ = let open! Ppx_jsobject_conv_runtime in $rhs$ |}])

  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = { $list:ll$ } |} ->
     let fname = name_of_tdname tname in
     let rho = build_rho pl in
     let case = record_type_to_jsobject_of ~loc rho ll in
     let rhs = {%expression| function $list:[case]$ |} in
     let rhs = prepend_params pl rhs in
     let rhs = wrapper_with_newtype ~loc pl rhs in
     ([],
      [wrapper_with_fun_type ~loc pl tname
         {%value_binding| $lid:fname$ = let open! Ppx_jsobject_conv_runtime in $rhs$ |}])
     
  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = .. |} ->
     let fname = name_of_tdname tname in
     let (tvl, fty) = fun_type ~loc pl tname in
     let default_fname = fname^"_default" in
     let ref_type_name = fname^"_ref_t" in
     let ref_name = fname^"_ref" in
     let default_expr =
       {%expression|
        fun _ ->
        throw_js_error
          ("ppx_jsobject_conv: Maybe a [@@deriving jsobject] is missing when extending the type "
           ^ $string:tname$)
        |} in
     let default_expr = prepend_params pl default_expr in
     let default_expr = wrapper_with_newtype ~loc pl default_expr in
     ([{%structure_item| type $lid:ref_type_name$ = { mutable $lid:fname$ : $list:tvl$ . $fty$ }|}],
      [
        {%value_binding|
         $lid:default_fname$ : $list:tvl$ . $fty$ =
           let open! Ppx_jsobject_conv_runtime in 
           $default_expr$ |}
      ; {%value_binding| $lid:ref_name$ = let open! Ppx_jsobject_conv_runtime in
          { $lid:fname$ =  $lid:default_fname$ } |}
      ; {%value_binding| $lid:fname$ =
                                let open! Ppx_jsobject_conv_runtime in 
                                function | i -> $lid:ref_name$ . $lid:fname$ i
                                         |}
      ])
     
  let str_type_decl ~loc ~path:_ (rec_flag, tds) =
    let l = tds |> List.map td_to_jsobject_of in
    let stril = List.concat_map fst l in
    let bindings = List.concat_map snd l in
    let bindings = suppress_unused_rec bindings in
    stril@[{%structure_item| let $recflag:rec_flag$ $list:bindings$ |}]

  let str_type_ext ~loc ~path:_ te =
    match te with
      {%str_type_extension.noattr.loc| type $list:pl$ $longid:modli$ . $lid:tname$ += $list:exconl$ |} ->
      let fname = name_of_tdname tname in
      let ref_name = fname^"_ref" in
      let previous_fname = fname^"_previous" in
      let cl =
        exconl
        |> List.map (function
                 {%extension_constructor.loc| $uid:s$ of $list:tyl$ $algattrs:attrs$ |} ->
                  {%constructor_declaration| $uid:s$ of $list:tyl$ $algattrs:attrs$ |}
               | {%extension_constructor.loc| $uid:s$ of { $list:ll$ } $algattrs:attrs$ |} ->
                  {%constructor_declaration| $uid:s$ of { $list:ll$ } $algattrs:attrs$ |}
             ) in
      let rho = build_rho pl in
      let cases = variant_type_to_jsobject_of ~loc rho cl in
      let fallback =
        List.fold_left (fun f (_,arg) -> {%expression| $f$ $arg$ |})
          {%expression| $lid:previous_fname$ |} rho in
      let cases = cases @ [
            {%case| wildcard -> $fallback$ wildcard |}
          ] in
      let fbody = {%expression| function $list:cases$ |} in
      let fbody = prepend_params pl fbody in
      let fbody = wrapper_with_newtype ~loc pl fbody in
      [
        {%structure_item|
         let () =
         let $lid:previous_fname$ = $longid:modli$ . $lid:ref_name$ . $lid:fname$ in
           $longid:modli$ . $lid:ref_name$ . $lid:fname$ <- 
           let open! Ppx_jsobject_conv_runtime in
           $fbody$
         |}
      ]

end

module Of_jsobject_expander = struct
  open Stdlib
  [@@@ocaml.warning "-8"]

  let name_of_tdname name = match name with
    | "t" -> "of_jsobject"
    | tn  -> tn ^ "_of_jsobject"

  let name_of_td td = name_of_tdname td.ptype_name.txt
  let name_of_te te = name_of_tdname @@ Longident.last_exn te.ptyext_path.txt

  let converter_type ty =
    let loc = match ty with {%core_type.noattr.loc| $_$ |} -> loc in
    {%core_type| Js_of_ocaml.Js.Unsafe.any Js_of_ocaml.Js.t -> ($ty$, string) result |}

  let fun_type ~loc pl tname =
    let rhs_t = converter_type {%core_type| $list:List.map fst pl$ $lid:tname$ |} in
    let ftype =
      List.fold_right (fun (pv, _) rhs_t ->
          {%core_type| $converter_type pv$ -> $rhs_t$ |})
        pl rhs_t in
    let tvl = List.map (fun ({%core_type.noattr| ' $lid:v$ |}, _) -> Location.{txt=v; loc=loc}) pl in
    (tvl, ftype)

  let td_to_sig_items td =
    match td with
        {%type_decl.noattr.loc| $list:pl$ $lid:tname$ |}
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ |}
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $constructorlist:_$ |}
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = { $list:_$ } |}
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ = $constructorlist:_$ |}
      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $_$ = { $list:_$ } |} ->
         let (_tvl, ftype) = fun_type ~loc pl tname in
         let func_name = name_of_tdname tname in
         [{%signature_item| val $lid:func_name$ : (* $list:tvl$ . *) $ftype$ |}]

      | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = .. |} ->
         let (tvl, ftype) = fun_type ~loc pl tname in
         let func_name = name_of_tdname tname in
         let default_fname = func_name^"_default" in
         let ref_type_name = func_name^"_ref_t" in
         let ref_name = func_name^"_ref" in
         [
           {%signature_item| type $lid:ref_type_name$ = { mutable $lid:func_name$ : $list:tvl$ . $ftype$ }|}
         ; {%signature_item| val $lid:default_fname$ : (* $list:tvl$ . *) $ftype$ |}
         ; {%signature_item| val $lid:ref_name$ : $lid:ref_type_name$ |}
         ; {%signature_item| val $lid:func_name$ : (* $list:tvl$ . *) $ftype$ |}
         ]

  let sig_type_decl ~loc:_ ~path:_ (_rf, tds) =
    tds
    |> List.concat_map td_to_sig_items

  let wrap_polyvariant ~loc cid body =
    {%expression| ` $id:cid$ $body$ |}

  let wrap_constructor ~loc cid body =
    {%expression| $uid:cid$ $body$ |}

  [@@@ocaml.warning "-39-27"]
  let rec core_type_to_of_jsobject ?(offset = 0) ?(modify_body = (fun x -> x)) rho ty =
    match ty with
        {%core_type.noattr.loc| ' $lid:v$ |} ->
        let f = match List.assoc v rho with
            exception Not_found ->
             failwith Fmt.(str "core_type_to_jsobject_of: unknown type-var %a" pp_core_type ty)
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

      | {%core_type.noattr.loc| [ $list:rfl$ ] |} ->
         let cl =
           rfl
           |> List.map (function
                    {%row_field| $_$ |} ->
                     failwith Fmt.(str "of_jsobject: variant cannot include inheritance: %a" pp_core_type ty)
                  | {%row_field.noattr.loc| ` $id:cid$ |} ->
                     {%constructor_declaration| $uid:cid$ |}
                  | {%row_field.noattr.loc| ` $id:cid$ of $ty$ |} ->
                     {%constructor_declaration| $uid:cid$ of $ty$ |}
                  | rf ->
                     failwith Fmt.(str "of_jsobject: unrecognized row_field of %a" pp_core_type ty)
                ) in
         let cases = variant_type_to_of_jsobject ~loc ~polyvariant:true rho cl in
         {%expression| function $list:cases$ |}

      | {%core_type.noattr.loc| $tuplelist:tyl$ |} ->
         let len = List.length tyl in
         let convert1 i ty =
           let var = Printf.sprintf "v_%d" i in
           let patt = {%pattern| $lid:var$ |} in
           let expr = {%expression| $lid:var$ |} in
           let conv = core_type_to_of_jsobject rho ty in
           (string_of_int (offset + i), var,patt,expr,conv) in
         let ind_var_patt_expr_conv_list = List.mapi convert1 tyl in
         let exprs = ind_var_patt_expr_conv_list |> List.map (fun (_,_,_,e,_) -> e) in
         let rhs = {%expression| $tuplelist:exprs$ |} in
         let rhs = modify_body rhs in
         let rhs = {%expression| Ok $rhs$ |} in
         let rhs =
           List.fold_right (fun (i,v,p,e,conv) rhs ->
               {%expression|
                (((array_get_ind arr $int:i$) >>= $conv$)
                 >*= (fun emsg -> concat_error_messages $string:i$ emsg))
                >>= (fun $lid:v$ -> $rhs$) |})
             ind_var_patt_expr_conv_list rhs
         in
         {%expression| fun v ->
           (is_array_of_size_n v $int:string_of_int (offset + len)$) >>=
             (fun arr -> $rhs$) |}

      | ct ->
         failwith Fmt.(str "core_type_to_of_jsobject: unhandled core_type: %a" pp_core_type ct)

  and record_type_to_of_jsobject ~loc ?(modify_body = (fun x -> x)) rho ll =
    let field_name_jsfldname_var_longid_expr_conv_list =
      ll
      |> List.map (function
               {%label_declaration.noattr.loc| $mutable:_$ $lid:fldname$ : $fldty$ |} as ld ->
               let var = Printf.sprintf "v_%s" fldname in
               let longid = Location.mkloc {%longident_t| $lid:fldname$ |} loc in
               let expr = {%expression| $lid:var$ |} in
               let conv = core_type_to_of_jsobject rho fldty in
               let conv = match Attrs.field_default ld, Attrs.error_default ld with
                   Some _, Some _ -> 
                   (* this should be handled during attrs parsing *)
                   Location.raise_errorf
                     ~loc "ppx_jsobject_conv: default_on_error and default attrs can't be used together"
                 | Some v, None ->
                    {%expression| defined_or_default $conv$ $v$ |}
                 | None, Some v ->
                    {%expression| convert_or_default $conv$ $v$ |}
                 | None, None -> conv in
               let jsfldname = Attrs.field_name ld in
               (fldname, jsfldname, var, longid, expr, conv)) in
    let exprfields = 
      field_name_jsfldname_var_longid_expr_conv_list
      |> List.map (fun (_,_,_,li,e,_) -> (li,e)) in
    let rhs = {%expression| { $list:exprfields$ } |} in
    let rhs = modify_body rhs in
    let rhs = {%expression| Ok $rhs$ |} in
    let rhs = List.fold_right (fun (fldname,  jsfldname,var,li,e,conv) rhs ->
                  {%expression|
                   (((object_get_key obj $string:jsfldname$) >>= $conv$) >*=
                      (fun emsg -> concat_error_messages $string:fldname$ emsg))
                   >>= (fun $lid:var$ -> $rhs$)
                   |}
                )
                field_name_jsfldname_var_longid_expr_conv_list rhs in
    {%expression| fun r -> (is_object r) >>= (fun obj -> $rhs$) |}

  and variant_type_to_of_jsobject ?(polyvariant=false) ~loc rho cl =
    if Attrs.define_sum_type_as cl = `Regular then
      let cases =
        cl
        |> List.map (function cd ->
            let jscid = Attrs.constructor_name cd in
            match cd with
              {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
               let rhs =
                 if polyvariant then
                   {%expression| Ok ( ` $id:cid$ ) |}
                 else
                   {%expression| Ok $uid:cid$ |} in
               (jscid, rhs)
            | {%constructor_declaration.noattr.loc| $uid:cid$ of $ty$ |} ->
               let rhs = core_type_to_of_jsobject rho ty in
               let rhs =
                 let body =
                   if polyvariant then
                     {%expression| ` $id:cid$ v0 |}
                   else
                     {%expression| $uid:cid$ v0 |}
                 in
                 {%expression|
                  (((array_get_ind arr 1) >>= $rhs$) >*=
                     (fun emsg -> concat_error_messages "1" emsg))
                  >>= (fun v0 -> Ok ($body$))
                  |} in
               (jscid, rhs)

            | {%constructor_declaration.noattr.loc| $uid:cid$ of { $list:ll$ } |} ->
               let rhs = record_type_to_of_jsobject ~modify_body:(wrap_constructor ~loc cid) ~loc rho ll in
               let rhs = {%expression|
                  (((array_get_ind arr 1) >>= $rhs$) >*=
                     (fun emsg -> concat_error_messages "1" emsg))
                  |} in
               (jscid, rhs)

            | {%constructor_declaration.noattr.loc| $uid:cid$ of $list:tyl$ |} ->
               let modify_body =
                 if polyvariant then
                   wrap_polyvariant ~loc cid
                 else
                   wrap_constructor ~loc cid in
               let rhs = core_type_to_of_jsobject ~offset:1 ~modify_body rho {%core_type| $tuplelist:tyl$ |} in
               let rhs = {%expression| $rhs$ v |} in
               (jscid, rhs))
        |> List.map (fun (cid, rhs) ->
               {%case| $string:cid$ -> $rhs$ |}
             ) in
      let cases = cases @ [
            let cids =
              cl
              |> List.map (function
                       {%constructor_declaration.noattr| $uid:cid$ of $list:_l$ |} -> cid
                     | {%constructor_declaration.noattr| $uid:cid$ of { $list:_l$ } |} -> cid
                   ) in
            let msg = Fmt.(str "0: expected one of the %a, got " (list ~sep:(const string  "/") string) cids) in
            {%case| unknown -> Error ($string:msg$ ^ unknown) |}
          ]
      in
     let rhs = {%expression| function $list:cases$ |} in
     [{%case| v -> (is_array v) >>=
                  (fun arr ->
                    ((array_get_ind arr 0) >>= string_of_jsobject) >>= $rhs$ ) |}]

    else if Attrs.define_sum_type_as cl = `AsTagless then
      let cases =
        cl
       |> List.map (function
                {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
                 failwith Fmt.(str "core_type_to_jsobject_of: cannot tagless-ly demarshal nullary constructor: %s" cid)
              | {%constructor_declaration.noattr.loc| $uid:cid$ of $ty$ |} ->
                 let rhs = core_type_to_of_jsobject rho ty in
                 ((wrap_constructor ~loc cid), rhs)

            | {%constructor_declaration.noattr.loc| $uid:cid$ of { $list:ll$ } |} ->
               let rhs = record_type_to_of_jsobject ~modify_body:(wrap_constructor ~loc cid) ~loc rho ll in
               ((fun x -> x),rhs)

              | {%constructor_declaration.noattr.loc| $uid:cid$ of $list:tyl$ |} ->
                 failwith Fmt.(str "core_type_to_jsobject_of: can only tagless-ly demarshal single-argument constructor: %s" cid)
            ) in
     let fallthru = {%expression| Error emsg |} in
     let rhs = List.fold_right (fun (modifier, demarsh) rhs ->
                   let body = modifier {%expression| v1 |} in
                   {%expression|
                    ($demarsh$ v)
                    |> (function
                        | Ok v1 -> Ok $body$
                        | Error msg1 ->
                           let emsg = emsg ^ "("^msg1^"); " in
                           $rhs$)
                    |})
                 cases fallthru in
     [{%case| v -> let emsg = "_: neither of possible tagless conversions applicable, possible errors: " in
                $rhs$ |}]

    else if Attrs.define_sum_type_as cl = `AsObject then
      let jscid_rhs_list =
        cl
        |> List.map (function cd ->
            let jscid = Attrs.constructor_name cd in
            match cd with
              {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
               let rhs =
                 if polyvariant then
                   {%expression| Ok ( ` $id:cid$ ) |}
                 else
                   {%expression| Ok $uid:cid$ |} in
               (jscid, rhs)

            | {%constructor_declaration.noattr.loc| $uid:cid$ of $ty$ |} ->
               let conv = core_type_to_of_jsobject rho ty in
               let body =
                 if polyvariant then
                   {%expression| ` $id:cid$ v0 |}
                 else
                   {%expression| $uid:cid$ v0 |}
               in
               let rhs = {%expression|
                (object_get_key obj $string:jscid$) >>=
                  ((fun v ->
                    (($conv$ v) >*=
                       (fun emsg ->
                         concat_error_messages $string:jscid$ emsg))
                    >>= (fun v0 -> Ok $body$)))
                |} in
               (jscid, rhs)

            | {%constructor_declaration.noattr.loc| $uid:cid$ of { $list:ll$ } |} ->
               let conv = record_type_to_of_jsobject ~modify_body:(wrap_constructor ~loc cid) ~loc rho ll in
               let rhs = {%expression|
                (object_get_key obj $string:jscid$) >>=
                  ((fun v ->
                    (($conv$ v) >*=
                       (fun emsg ->
                         concat_error_messages $string:jscid$ emsg))
                    >>= (fun v0 -> Ok v0)))
                |} in
               (jscid, rhs)

            | {%constructor_declaration.noattr.loc| $uid:cid$ of $list:tyl$ |} ->
               failwith Fmt.(str "variant type as_object only with nullary/unary constructors %s" cid)
             ) in
      let cases = 
        jscid_rhs_list
        |> List.map (fun (jscid, rhs) ->
               {%case| $string:jscid$ -> $rhs$ |}
             ) in
      let jscids = List.map fst jscid_rhs_list in
      let cases = cases @ [
            let msg = Fmt.(str "object should contain one key of the %a, got " (list ~sep:(const string  "/") string) jscids) in
            {%case| unknown -> Error ($string:msg$ ^ unknown) |}
          ]
      in
     let rhs = {%expression| function $list:cases$ |} in
     [{%case|
       v ->
       (is_object v) >>=
         (fun obj ->
           (object_get_sole_key obj) >>= $rhs$)
       |}]

    else if Attrs.define_sum_type_as cl = `AsEnum then
      let jscid_rhs_list =
        cl
        |> List.map (function cd ->
            let jscid = Attrs.constructor_name cd in
            match cd with
              {%constructor_declaration.noattr.loc| $uid:cid$ |} ->
               let rhs =
                 if polyvariant then
                   {%expression| Ok ( ` $id:cid$ ) |}
                 else
                   {%expression| Ok $uid:cid$ |} in
               (jscid, rhs)
            | _ ->
               failwith Fmt.(str "variant type as_enum only with nullary constructors")
             ) in
      let cases = 
        jscid_rhs_list
        |> List.map (fun (jscid, rhs) ->
               {%case| $string:jscid$ -> $rhs$ |}
             ) in
      let jscids = List.map fst jscid_rhs_list in
      let cases = cases @ [
            let msg = Fmt.(str "expected one of the %a, got " (list ~sep:(const string  "/") string) jscids) in
            {%case| unknown -> Error ($string:msg$ ^ unknown) |}
          ]
      in
      let rhs = {%expression| function $list:cases$ |} in
      [{%case|
        v ->
             ((defined_or_error v) >>= string_of_jsobject) >>=
               $rhs$
        |}]

  else assert false

  let wrapper_with_fun_type ~loc pl tname = function
      {%value_binding| $lid:f$ = $e$ |} ->
      let (tvl,ftype) = fun_type ~loc pl tname in
      {%value_binding| $lid:f$ : $list:tvl$ . $ftype$ = $e$ |} 

  let wrapper_with_newtype ~loc pl rhs =
    List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
        Parsetree.{pexp_desc=Pexp_newtype(Location.{txt=v;loc=loc}, rhs);
                   pexp_loc=loc;
                   pexp_loc_stack=[];
                   pexp_attributes=[]})
      pl rhs

  let build_rho pl =
    pl |>  List.map (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) ->
               let fname = Printf.sprintf "_of_%s" v in
               (v, {%expression| $lid:fname$ |}))

  let prepend_params pl rhs =
    List.fold_right (fun ({%core_type.noattr.loc| ' $lid:v$ |}, _) rhs ->
        let fname = Printf.sprintf "_of_%s" v in
        let argty = converter_type {%core_type| $lid:v$ |} in
        {%expression| fun ( $lid:fname$ : $argty$ ) -> $rhs$ |})
      pl rhs

  let td_to_of_jsobject = function
    {%type_decl.noattr.loc| $list:pl$ $lid:tname$ |} -> ([],[])
  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $ty$ |} ->
     let fname = name_of_tdname tname in
     let rho = build_rho pl in
     let rhs = core_type_to_of_jsobject rho ty in
     let rhs = {%expression| fun v -> $rhs$ v |} in
     let rhs = prepend_params pl rhs in
     let rhs = wrapper_with_newtype ~loc pl rhs in
     ([],
      [wrapper_with_fun_type ~loc pl tname
         {%value_binding| $lid:fname$ =  let open! Ppx_jsobject_conv_runtime in $rhs$ |}])


  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = $constructorlist:cl$ |} ->
     let fname = name_of_tdname tname in
     let rho = build_rho pl in
     let cases = variant_type_to_of_jsobject ~loc rho cl in
     let rhs = {%expression| function $list:cases$ |} in
     let rhs = prepend_params pl rhs in
     let rhs = wrapper_with_newtype ~loc pl rhs in
     ([],
      [wrapper_with_fun_type ~loc pl tname
         {%value_binding| $lid:fname$ = let open! Ppx_jsobject_conv_runtime in $rhs$ |}])

  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = { $list:ll$ } |} ->
     let fname = name_of_tdname tname in
     let rho = build_rho pl in
     let rhs = record_type_to_of_jsobject ~loc rho ll in
     let rhs = prepend_params pl rhs in
     let rhs = wrapper_with_newtype ~loc pl rhs in
     ([],
      [{%value_binding| $lid:fname$ = let open! Ppx_jsobject_conv_runtime in $rhs$ |}])

  | {%type_decl.noattr.loc| $list:pl$ $lid:tname$ = .. |} ->
     let fname = name_of_tdname tname in
     let (tvl, fty) = fun_type ~loc pl tname in
     let default_fname = fname^"_default" in
     let ref_type_name = fname^"_ref_t" in
     let ref_name = fname^"_ref" in
     let default_expr =
       {%expression|
        fun _ ->
        Error
          ("ppx_jsobject_conv: can't convert, maybe a [@@deriving jsobject] is missing when extending the type "
           ^ $string:tname$)
        |} in
     let default_expr = prepend_params pl default_expr in
     let default_expr = wrapper_with_newtype ~loc pl default_expr in
     ([{%structure_item| type $lid:ref_type_name$ = { mutable $lid:fname$ : $list:tvl$ . $fty$ }|}],
      [
        {%value_binding|
         $lid:default_fname$ : $list:tvl$ . $fty$ =
                                 let open! Ppx_jsobject_conv_runtime in 
                                 $default_expr$
         |}
      ; {%value_binding| $lid:ref_name$ = let open! Ppx_jsobject_conv_runtime in
          { $lid:fname$ =  $lid:default_fname$ } |}
      ; {%value_binding| $lid:fname$ =
                                let open! Ppx_jsobject_conv_runtime in 
                                function | i -> $lid:ref_name$ . $lid:fname$ i
                                         |}
     ])

  let str_type_decl ~loc ~path:_ (rec_flag, tds) =
    let l = tds |> List.map td_to_of_jsobject in
    let stril = List.concat_map fst l in
    let bindings = List.concat_map snd l in
    let bindings = suppress_unused_rec bindings in
    stril@[{%structure_item| let $recflag:rec_flag$ $list:bindings$ |}]

  let str_type_ext ~loc ~path:_ te =
    match te with
      {%str_type_extension.noattr.loc| type $list:pl$ $longid:modli$ . $lid:tname$ += $list:exconl$ |} ->
     let fname = name_of_tdname tname in
     let ref_name = fname^"_ref" in
     let previous_fname = fname^"_previous" in
     let cl =
       exconl
       |> List.map (function
                {%extension_constructor.loc| $uid:s$ of $list:tyl$ $algattrs:attrs$ |} ->
                {%constructor_declaration| $uid:s$ of $list:tyl$ $algattrs:attrs$ |}
              | {%extension_constructor.loc| $uid:s$ of { $list:ll$ } $algattrs:attrs$ |} ->
                 {%constructor_declaration| $uid:s$ of { $list:ll$ } $algattrs:attrs$ |}
            ) in
     let rho = build_rho pl in
      let fallback =
        List.fold_left (fun f (_,arg) -> {%expression| $f$ $arg$ |})
          {%expression| $lid:previous_fname$ |} rho in
     let fbody = variant_type_to_of_jsobject ~loc rho cl in
     let fbody = {%expression|
                  fun v ->
                  match (function $list:fbody$) v
                  with
                  | Error _ -> $fallback$ v
                  | asis -> asis
                  |} in
     let fbody = prepend_params pl fbody in
     let fbody = wrapper_with_newtype ~loc pl fbody in
     let fbody = {%expression|
                  let open! Ppx_jsobject_conv_runtime in
                  $fbody$ |} in
    [
      {%structure_item|
         let () =
           let $lid:previous_fname$ = $longid:modli$ . $lid:ref_name$ . $lid:fname$ in
           $longid:modli$ . $lid:ref_name$ . $lid:fname$ <- $fbody$
         |}
    ]

end
