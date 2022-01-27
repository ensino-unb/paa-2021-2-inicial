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

Inductive sorted: list nat -> Prop :=
| sorted_nil: sorted nil
| sorted_one: forall x, sorted (x::nil)
| sorted_all: forall l x y, x <=? y = true -> sorted (y::l) -> sorted (x::y::l).

Lemma insere_preserva_ordem: forall l x, sorted l -> sorted (insere x l).
Proof.
  induction l. (* A prova é por indução em l... *)
  - intro x. 
    intro H. 
    simpl.
    apply sorted_one.
  - intros x H.
    simpl.
    destruct (x <=? a) eqn:Hle.
    + apply sorted_all.
      * assumption.
      * exact H.
    + generalize dependent l.
      intro l. case l.
      * intros IH H.
        simpl.
        apply sorted_all.
        ** clear IH H.
           apply Nat.leb_gt in Hle.
           apply Nat.leb_le.
           apply Nat.lt_le_incl.
           assumption.
        ** apply sorted_one.
      * Admitted.

Print insere_preserva_ordem.
  
Fixpoint ord_insercao l :=
  match l with
  | nil => nil
  | h :: tl => insere h (ord_insercao tl)
  end.

Eval compute in (ord_insercao (3::2::1::nil)).

Print list.




Theorem correcao_ord_insercao: forall l, sorted (ord_insercao l) /\ permutacao l (ord_insercao l).
