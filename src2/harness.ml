open Syntax
module OrigList = List
open StdLabels

open Ppxlib
(* open Asttypes *)
(* open Parsetree *)


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
             | Longident.Lident "option" -> ()
             | Longident.Lident (_) | Longident.Ldot (_)
               | Longident.Lapply (_) -> err ())
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
             | Longident.Lident "option" ->
                Location.raise_errorf
                  ~loc:ld.pld_name.loc "ppx_jsobject_conv: default attr doesn't make sense with fields of option type"
             | Longident.Lident (_) | Longident.Ldot (_)
               | Longident.Lapply (_) -> ())
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
    let uniq = OrigList.sort_uniq compare conversions in
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

module Jsobject_of = struct

  let str_type_decl_wrapped ~loc ~path x =
    x
    |> Code.convFromLib_type_decls
    |> Code.Jsobject_of_expander.str_type_decl ~loc ~path
    |> ConvToLib.copy_structure


  let str_type_decl =
    Ppxlib.Deriving.Generator.make_noarg
      str_type_decl_wrapped
      ~attributes:[Attribute.T Attrs.name;
                   Attribute.T Attrs.key;
                   Attribute.T Attrs.sum_type_as;
                   Attribute.T Attrs.drop_none;
                  ]

let sig_type_decl_wrapped ~loc ~path x =
  x
  |> Code.convFromLib_type_decls
  |> Code.Jsobject_of_expander.sig_type_decl ~loc ~path
  |> ConvToLib.copy_signature

  let sig_type_decl =
    Ppxlib.Deriving.Generator.make_noarg sig_type_decl_wrapped

let str_type_ext_wrapped ~loc ~path te =
  te
  |> ConvFromLib.copy_type_extension
  |> Code.Jsobject_of_expander.str_type_ext ~loc ~path
  |> ConvToLib.copy_structure

  let str_type_ext =
    Ppxlib.Deriving.Generator.make_noarg str_type_ext_wrapped

  let name = "jsobject_of"

  let deriver =
    Ppxlib.Deriving.add name
      ~str_type_decl
      ~sig_type_decl
      ~str_type_ext
end

module Of_jsobject = struct
  let str_type_decl_wrapped ~loc ~path x =
    x
    |> Code.convFromLib_type_decls
    |> Code.Of_jsobject_expander.str_type_decl ~loc ~path
    |> ConvToLib.copy_structure
  let str_type_decl =
    Ppxlib.Deriving.Generator.make_noarg
      str_type_decl_wrapped
      ~attributes:[Attribute.T Attrs.name;
                   Attribute.T Attrs.key;
                   Attribute.T Attrs.sum_type_as;
                   Attribute.T Attrs.default;
                   Attribute.T Attrs.default_on_error;
                  ]

let sig_type_decl_wrapped ~loc ~path x =
  x
  |> Code.convFromLib_type_decls
  |> Code.Of_jsobject_expander.sig_type_decl ~loc ~path
  |> ConvToLib.copy_signature

  let sig_type_decl =
    Ppxlib.Deriving.Generator.make_noarg sig_type_decl_wrapped

let str_type_ext_wrapped ~loc ~path te =
  te
  |> ConvFromLib.copy_type_extension
  |> Code.Of_jsobject_expander.str_type_ext ~loc ~path
  |> ConvToLib.copy_structure

  let str_type_ext =
    Ppxlib.Deriving.Generator.make_noarg str_type_ext_wrapped

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
