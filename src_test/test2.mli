
type xx1 = int [@@deriving jsobject]
type xx1b = int * bool * string [@@deriving jsobject]

type ('a, 'b) choice = Left of 'a | Right of 'b [@@deriving jsobject]
type xx4 = (int, string) choice [@@deriving jsobject]
type xx4b = (int, (string * bool)) choice [@@deriving jsobject]

type xx2 = Foo0 | Foo1 of int | Foo2 of bool | Foo3 of bool * int | Foo4 of (bool * int) [@@deriving jsobject]
type xx3 = Bar1 of int | Bar2 of bool | Bar3 of (bool * int) [@jsobject.sum_type_as "tagless"] [@@deriving jsobject]
type rec1 = { x : int } [@@deriving jsobject]
type rec2 = { y : int ; z:string } [@@deriving jsobject]
type simple_tuple = int * string * int [@@deriving jsobject]
type simple_enum = Af | Bf of string | Cf of int * string * int [@@deriving jsobject]
type variant_rename = Gt [@name "$gt"]
                    | Lt of string [@name "$lt"]
                    | Eq of simple_tuple [@name "$eq"] [@@deriving jsobject]
type inline_tuple = D of (int * string)
                    | E of (string * int) [@@deriving jsobject]
type field_rename = {
    field_name: string [@key "FieldName"]
  } [@@deriving jsobject]
type maybe_int = int option [@@deriving jsobject]
(*
type arr_float = float array [@@deriving jsobject]
type string_list = string list [@@deriving jsobject]
type status = [`Created |
               `Registered of int * string |
               `Deleted of int] [@@deriving jsobject]
type user = {
    age: int;
    name: string;
    status: status
  } [@@deriving jsobject]
module NullableUser : sig
  type t = {
      age: int option;
      name: string option;
      status: status option
    } [@@deriving jsobject]
end
type outside_of_module = Something of NullableUser.t [@@deriving jsobject]
type condition = Gt of int | Lt of int [@@deriving jsobject]
type query = {amount: float; condition: condition} [@@deriving jsobject]
type basket = {name: string; query: query} [@@deriving jsobject]
type message = Basket of basket | Nop [@@deriving jsobject]
type command = {message: message} [@@deriving jsobject]
type with_defaults = {def_cond: condition [@default Gt(32)];
                      enabled: bool [@default true];
                      kind: string [@default "integer"]} [@@deriving jsobject]
type err_default = {something: float [@jsobject.default_on_error 0.0];
                    query: query option [@jsobject.default_on_error None]
                   } [@@deriving jsobject]
module Email : sig
  type t = string [@@deriving jsobject]
  val show : 'a ->  'a
end
type email_info = {email: Email.t} [@@deriving jsobject]
type variant_as_object = Gtn of int [@name "$gt"] [@jsobject.sum_type_as "object"]
                       | Ltn of int [@name "$lt"]  [@@deriving jsobject]
type enum = Var1 [@name "var1"] | Var2 | Var3 [@sum_type_as "enum"] [@@deriving jsobject]
type enum_info = {enum: enum} [@@deriving jsobject]
type ('a,'b) type_parameters = {data: 'a; ident: 'b; kind: string} [@@deriving jsobject]
type some_detais = {details: string} [@@deriving jsobject]
type some_ident = string [@@deriving jsobject]
type parametrized = (some_detais, some_ident) type_parameters [@@deriving jsobject]
type tagless =  U2 of {inlinef: float; inlines: string}
              | U1 of user [@jsobject.sum_type_as "tagless"]
                           [@@deriving jsobject]
type drop_none = {some: string option [@jsobject.drop_none]}
                   [@@deriving jsobject]
module ForOpen : sig
  type open_type = .. [@@deriving jsobject]
end
type ForOpen.open_type += OpV1 (* [@@deriving jsobject] *)
type ForOpen.open_type += OpV2 (* [@@deriving jsobject] *)

 *)
