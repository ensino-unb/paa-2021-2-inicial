(** * Projeto e Análise de Algoritmos  *)

(** ** O algoritmo de ordenação por inserção
*)

Require Import List.
Require Import Arith.

(**
   Definição da função de inserção
*)

Fixpoint insere x l :=
  match l with
  | nil => x :: nil 
  | h :: tl => if (x <=? h) then x :: l else h :: (insere x tl)
  end.

Eval compute in (insere 3 (1::2::nil)).

Eval compute in (insere 3 (2::1::nil)).

Fixpoint ord_insercao l :=
  match l with
  | nil => nil
  | h :: tl => insere h (ord_insercao tl)
  end.

Eval compute in (ord_insercao (3::2::1::nil)).

Print list.




Theorem correcao_ord_insercao: forall l, ordenada (ord_insercao l) /\ permutacao l (ord_insercao l).
