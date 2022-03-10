(** * Projeto e Análise de Algoritmos *)

Require Import Arith List Recdef.
Require Import Lia.

Definition len (p: list nat * list nat) :=
   length (fst p) + length (snd p).

Function merge (p: list nat * list nat) {measure len p} :=
match p with
  | (nil, l2) => l2
  | (l1, nil) => l1
  | ((hd1 :: tl1) as l1, (hd2 :: tl2) as l2) =>
if hd1 <=? hd2 then hd1 :: merge (tl1, l2)
      else hd2 :: merge (l1, tl2)
   end.
Proof.
  - intros p l1 l2 hd1 tl1 H1 hd2 tl2 H2 H3 H4.
    unfold len.
    simpl.
    lia.
  - intros p l1 l2 hd1 tl1 H1 hd2 tl2 H2 H3 H4.
    unfold len.
    simpl.
    lia.
Qed.
  
Function mergesort (l: list nat) {measure length l}:=
  match l with
  | nil => nil
  | h :: nil => l
  | h :: tl =>
     let n := length(l) / 2 in
     let l1 := firstn n l in
     let l2 := skipn n l in
     let sorted_l1 := mergesort(l1) in
     let sorted_l2 := mergesort(l2) in
     merge (sorted_l1, sorted_l2)
  end.
Proof.
  - intros l h tl n l' H1 H2.
    rewrite skipn_length.
    simpl length.
    apply Nat.sub_lt.
    + apply Nat.lt_le_incl.
      rewrite <- Nat.div2_div.
      apply Nat.lt_div2.
      lia.
    + apply Nat.div_str_pos.
      lia.
  - Admitted. (** Exercício *)

Require Import paa_2021_2_coq.

(** Prova da correção *)

Theorem mergesort_sorts: forall l, sorted (mergesort l).
Proof.
 Admitted.


Require Import Permutation.


Theorem mergesort_is_perm: forall l, Permutation l (mergesort l).
Proof.
 Admitted.

Theorem mergesort_is_correct: forall l, Permutation l (mergesort l) /\ sorted (mergesort l).
Proof.
  intro l; split.
  - apply mergesort_is_perm.
  - apply mergesort_sorts.
Qed.

(** Prova da complexidade *)

Function T_merge (p: list nat * list nat) {measure len p} : nat :=
  match p with
  | (nil, l2) => 0
  | (l1, nil) => 0
  | ((hd1 :: tl1) as l1, (hd2 :: tl2) as l2) =>
    if hd1 <=? hd2 then S(T_merge (tl1, l2))
    else S(T_merge (l1, tl2))
  end.
Proof.
Admitted.

(** Exercício: Enunciar o lema que estabelece a complexidade linear de merge. *)

Function T_mergesort (l: list nat) {measure length l} : nat :=
  if (length l <=? 1) then 0 else
    let n := length(l) / 2 in
    let l1 := firstn n l in
    let l2 := skipn n l in
    T_mergesort(l1) + T_mergesort(l2) + T_merge (mergesort l1, mergesort l2).
Proof.
Admitted.

Theorem T_mergesort_complexity: forall l k, length l = 2^k -> T_mergesort l <= k * 2^k.
Proof.
Admitted.
