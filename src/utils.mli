(** Utility functions *)

(** Explode a list into all its characters. *)
val explode : string -> char list

(** Inverse of [explode]. *)
val implode : char list -> string

(** Create a string with only one character. *)
val string_of_char : char -> string

(* Type of the host extern val store *)
module StringMap : Map.S with type key = string