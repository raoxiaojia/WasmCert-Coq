type 'a t
val length  : 'a t -> Extracted_z.extracted_z
val get     : 'a t -> Extracted_z.extracted_z -> 'a
val set     : 'a t -> Extracted_z.extracted_z -> 'a -> 'a t

val set_gen : 'a t -> Extracted_z.extracted_z -> Extracted_z.extracted_z -> (Extracted_z.extracted_z -> 'a) -> 'a t
(** [set_gen p start_pos block_len generator] returns a new persistent array
    based on [p] where the range of length [block_len] starting at [start_pos]
    is updated by calling [generator] for each index 0 to [block_len - 1].
    [block_len] must be greater than 0. *)

val default : 'a t -> 'a
val make    : Extracted_z.extracted_z -> 'a -> 'a t
val make_copy    : Extracted_z.extracted_z -> 'a -> 'a t -> Extracted_z.extracted_z -> 'a t
val copy    : 'a t -> 'a t