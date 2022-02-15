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
(* begin hide *)
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
(* end hide *)
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

(** * Equivalência entre Permutation e perm' *)

(** Exercício: (4 pontos) prazo: 23h59 da segunda, dia 14. *)
Lemma Permutation_implica_perm': forall l l', Permutation l l' -> perm' l l'.
Proof.
  induction 1.
(*  intros l l' H.
  induction H. *)
Admitted.

(** Desafio: pontuação extra: 10 pontos - primeiro grupo. Prazo: até 13 de março de 2022. *)
Lemma perm'_nil: forall l, perm' nil l -> l = nil.
Proof.
  Admitted.

(* Ideia que pode não ser a melhor. *)
Lemma perm'_exists: forall l l' a, perm' (a :: l) l' -> exists l1 l2, l' = l1++a::l2.
Proof.
  Admitted.
  
Lemma perm'_implica_Permutation: forall l l', perm' l l' -> Permutation l l'.
Proof.
  induction l.
  - intros l' H.
    apply perm'_nil in H.
    subst.
    apply perm_nil.
  - intros l' H.
    assert (H' := H). (* cópia da hipótese H no contexto *)
    apply perm'_exists in H'.
    destruct H' as [l1 [l2 H']].
    subst.
Admitted.

Theorem Permutation_equiv_perm': forall l l', Permutation l l' <-> perm' l l'.
Proof.
  intros l l'.
  split.
  - apply Permutation_implica_perm'.
  - apply perm'_implica_Permutation.
Qed.
    
(** * Análise da complexidade do algoritmo de ordenação por inserção *)

Fixpoint T_insere (x: nat) (l: list nat) : nat :=
match l with
| nil => 0
| h :: tl => if (x <=? h) then 1 else S (T_insere x tl)
end.

Require Import Lia.

Lemma T_insere_linear: forall l x, T_insere x l <= length l.
Proof.
  induction l.
  - intros x.
    simpl.
    auto.
  - intros x.
    simpl.
    destruct (x <=? a).
    + apply le_n_S.
      lia.
    + apply le_n_S.
      apply IHl.
Qed.

Fixpoint T_is (l: list nat) : nat :=
match l with
| nil => 0
| h::tl => (T_is tl) + (T_insere h (ord_insercao tl))
end.

Lemma ord_insercao_length: forall l, length (ord_insercao l) = length l.
Proof.
  Admitted.

Lemma T_is_quad: forall l, T_is l <= (length l)*(length l).
Proof.
  induction l.
  - simpl.
    auto.
  - simpl.
    apply le_trans with ((length l)*(length l) + length (ord_insercao l)).
    + apply Nat.add_le_mono.
      * apply IHl.
      * apply T_insere_linear.
    + rewrite ord_insercao_length.
      lia.
Qed.

(** ** Análise do pior caso *)

Fixpoint Tw_insere (n:nat) :=
  match n with
  | 0 => 0
  | S k => S (Tw_insere k)
  end.

Lemma Tw_insere_linear: forall n, Tw_insere n = n.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Fixpoint Tw_is (n: nat) :=
  match n with
  | 0 => 0
  | S k => k + Tw_is k
  end.

(* Exercício (2 pontos)  - prazo: 23h59 de 21/02 *)
Theorem Tw_is_quad: forall n, 2 * Tw_is (S n) = n * (S n).
Proof.
  Admitted.
