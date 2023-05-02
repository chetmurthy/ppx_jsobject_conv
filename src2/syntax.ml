open Ppxlib

module LibSyntax = Ppxlib_ast__.Versions.OCaml_414
module OurSyntax = Ppxlib_ast__.Versions.OCaml_410

module ConvToLib = Ppxlib_ast__.Versions.Convert(OurSyntax) (LibSyntax)
module ConvFromLib = Ppxlib_ast__.Versions.Convert(LibSyntax)(OurSyntax)

let pp_expression pps e = Pprintast.expression pps (ConvToLib.copy_expression e)
let pp_core_type pps e = Pprintast.core_type pps (ConvToLib.copy_core_type e)
