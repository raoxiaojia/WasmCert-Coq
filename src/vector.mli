open CCVector

val length : 'a vector -> int

val app : 'a vector -> 'a vector -> 'a vector

val nth_error : 'a vector -> int -> 'a option

val nth : int -> 'a vector -> 'a -> 'a

val rev : 'a vector -> 'a vector

val in_dec : ('a -> 'a -> bool) -> 'a -> 'a vector -> bool

val vec_eq_dec : ('a -> 'a -> bool) -> 'a vector -> 'a vector -> bool

val flatten : ('a vector) vector -> 'a vector

val map : ('a -> 'b) -> 'a vector -> 'b vector

val firstn : 'a vector -> int -> 'a vector

val skipn : 'a vector -> int -> 'a vector

val nodup : ('a -> 'a -> bool) -> 'a vector -> 'a vector

val repeat : int -> 'a -> 'a vector

val rcons : 'a vector -> 'a -> 'a vector

val unrcons : 'a vector -> ('a vector * 'a) option

val set_nth : 'a -> 'a vector -> int -> 'a -> 'a vector