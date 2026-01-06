(** Utility functions *)

(** Create a string with only one character. *)
val string_of_char : char -> string

(* Type of the host extern val store *)
module StringMap : Map.S with type key = string