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
      * intros n l' IH H.
        simpl in *.
        destruct (x <=? n) eqn:Hle'.
        ** apply sorted_all.
           *** apply Nat.leb_gt in Hle.
               apply Nat.leb_le.
               apply Nat.lt_le_incl.
               assumption.
           *** apply sorted_all.
               **** assumption.
               **** inversion H; subst.
                    assumption.
        ** inversion H; subst.
           apply sorted_all.
           *** assumption.
           ***specialize (IH x).
              rewrite Hle' in IH.
              apply IH.
           assumption.
Qed.

Fixpoint ord_insercao l :=
  match l with
  | nil => nil
  | h :: tl => insere h (ord_insercao tl)
  end.

Eval compute in (ord_insercao (3::2::1::nil)).

Lemma ord_insercao_preserva_ordem: forall l, sorted (ord_insercao l).
Proof.
  induction l.
  - simpl.
    apply sorted_nil.
  - simpl.
    apply insere_preserva_ordem.
    apply IHl.
Qed.

(*
Inductive Permutation': list nat -> list nat -> Prop :=
    perm'_nil : Permutation' nil nil
  | perm'_skip : forall (x : nat) (l l' : list nat),
                Permutation' l l' -> Permutation' (x :: l) (x :: l')
  | perm'_swap : forall (x y : nat) (l : list nat),
                Permutation' (y :: x :: l) (x :: y :: l)
  | perm'_trans : forall l l' l'' : list nat,
                 Permutation' l l' ->
                 Permutation' l' l'' -> Permutation' l l''.


Lemma Permutation'_refl: forall l, Permutation' l l.
Proof.
  induction l.
  - apply perm'_nil.
  - apply perm'_skip.
    apply IHl.
Qed.
  
Lemma Permutation'_insere: forall l a, Permutation' (a :: l) (insere a l).
Proof.
  induction l.
  - intro a.
    simpl.
    apply Permutation'_refl.
  - intros a'.
    simpl.
    destruct (a' <=? a).
    + apply Permutation'_refl.
    + apply perm'_trans with (a::a'::l).
      * apply perm'_swap.
      * apply perm'_skip.
        apply IHl.
Qed.
  
Lemma Permutation'_insere_diff: forall l l' a, Permutation' l l' -> Permutation' (a :: l) (insere a l').
Proof.
  intros l l' a H. 
  apply perm'_skip with (x := a) in H.
  apply perm'_trans with (a::l').
  - assumption.
  - apply Permutation'_insere.
Qed.
*)

Require Import Permutation.
Print Permutation.


Lemma Permutation_insere: forall l a, Permutation (a :: l) (insere a l).
Proof.  
  induction l.
  - intro a.
    simpl.
    apply Permutation_refl.
  - intros a'.
    simpl.
    destruct (a' <=? a).
    + apply Permutation_refl.
    + apply perm_trans with (a::a'::l).
      * apply perm_swap.
      * apply perm_skip.
        apply IHl.
Qed.
  
Lemma Permutation_insere_diff: forall l l' a, Permutation l l' -> Permutation (a :: l) (insere a l').
Proof.
  intros l l' a H.
  rewrite H.
  apply Permutation_insere.
Qed.

Lemma ord_insercao_Permutation: forall l, Permutation l (ord_insercao l).
Proof.
  induction l.
  - simpl.
    apply perm_nil.
  - simpl.
    apply Permutation_insere_diff.
    apply IHl.
Qed.
  
Theorem correcao_ord_insercao: forall l, sorted (ord_insercao l) /\ Permutation l (ord_insercao l).
Proof.
  intro l; split.
  - apply ord_insercao_preserva_ordem.
  - apply ord_insercao_Permutation.
Qed.

Fixpoint num_oc x l := match l with
                       | nil => 0
                       | h::tl => if (x =? h) then S(num_oc x tl) else num_oc x tl
                       end.

Eval compute in (num_oc 2 (1::2::3::2::2::nil)).

Definition perm' l l' := forall x, num_oc x l = num_oc x l'.

Lemma num_oc_insere: forall l l' x a, perm' l l' -> (if x =? a then S (num_oc x l) else num_oc x l) =
  num_oc x (insere a l').
Proof.
Admitted.

(* Abordagem alternativa:

Lemma num_oc_insere_eq: num_oc a (insere a l) = S(num_oc a l)

Lemma num_oc_insere_diff: x <> a ->  num_oc x (insere a l)
  *)  

Lemma ord_insercao_perm': forall l, perm' l (ord_insercao l).
Proof.
  induction l.
  - simpl.
    unfold perm'.
    intro x.
    reflexivity.
  - simpl.
    unfold perm' in *.
    intro x.
    simpl.
    apply num_oc_insere.
    unfold perm'.
    intro x'.
    apply IHl.
Qed.

