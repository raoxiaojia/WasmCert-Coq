(* TODO: more tests *)
Require Import leb128.
Require Import Ascii Coq.Init.Byte.
Require Import NArith.BinNat.
From parseque Require Import Running Induction.
Require Import check_toks.

Definition plop n :=
  List.map (fun x => byte_of_ascii x) (encode_unsigned n).

(* Test from Wikipedia article: https://en.wikipedia.org/wiki/LEB128#Unsigned_LEB128
   This is the representation of the number [624485]. *)
Definition test_wikipedia : list byte :=
  xe5 :: x8e :: x26 :: nil.

Definition encode_unsigned_check (k : N) :=
  Singleton (plop k).

Lemma test_wikipedia_correct :
  encode_unsigned_check 624485 = Singleton test_wikipedia.
Proof.
  vm_compute. reflexivity.
Qed.

Definition test_wikipedia_decode :
  check_toks test_wikipedia unsigned_ = Singleton 624485%N.
Proof.
  vm_compute. reflexivity.
Qed.
