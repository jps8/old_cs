(* Implementation and correctness proof for insertion sort.
  Andrew W. Appel, January 2010. *)

Require Import Permutation.
Require Import List.
Require Import Compare_dec.


Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Locate le.
Print le.

Locate le_lt_dec.
Check le_lt_dec.

Print le_lt_dec.
Print sumbool.

Lemma le_lt_dec': forall n m, {n<=m}+{m<n}.
Proof.
induction n; destruct m; intros.
left. apply le_n.
left. apply le_S.
    induction m. apply le_n. apply le_S. auto.
right. clear. unfold lt. apply Le.le_n_S.
   apply Le.le_0_n.
destruct (IHn m).
left. apply Le.le_n_S. auto.
right. apply Lt.lt_n_S. auto.
Defined.

Locate le_lt_dec.
Print le_lt_dec'.
Print le_lt_dec.

Fixpoint select (i: nat) (l: list nat) : nat * list nat :=
match l with
|  nil => (i, nil)
|  h::t => if le_lt_dec i h 
               then let (j, l') := select i t in (j, h::l')
               else let (j,l') := select h t in (j, i::l')
end.

Fixpoint selsort l n :=
match l, n with
| i::r, S n' => let (j,r') := select i r
               in j :: selsort r' n'
| _, _ => nil
end.

Definition selection_sort l := selsort l (length l).


Example sort_pi: selection_sort [3,1,4,1,5,9,2,6,5,3,5] = [1,1,2,3,3,4,5,5,5,6,9].
Proof.
unfold selection_sort.
simpl.
reflexivity.
Qed.

Lemma select_perm: forall i l, 
  let (j,r) := select i l in
   Permutation (i::l) (j::r).
Proof.
intros i l; revert i.
induction l; intros; simpl in *.
apply Permutation_refl.
destruct (le_lt_dec i a).
specialize (IHl i).
destruct (select i l).
eapply perm_trans.
apply perm_swap.
apply Permutation_sym.
eapply perm_trans.
apply perm_swap.
apply Permutation_cons.
apply Permutation_sym.
apply IHl.
specialize (IHl a).
destruct (select a l).
apply Permutation_sym.
eapply perm_trans.
apply perm_swap.
apply Permutation_cons.
apply Permutation_sym.
apply IHl.
Qed.

Ltac inv H := inversion H; clear H; subst.

Lemma selsort_perm:
  forall n l, length l = n -> Permutation l (selsort l n).
Proof.
induction n; destruct l; intros; inv H.
simpl. apply Permutation_refl.
simpl.
assert (SP := select_perm n0 l).
destruct (select n0 l) as [j r].
eapply Permutation_trans; [ apply SP | ].
apply Permutation_cons.
apply IHn.
apply Permutation_length in SP.
simpl in SP.
inv SP.
auto.
Qed.

Theorem selection_sort_perm:
  forall l, Permutation l (selection_sort l).
Proof.
unfold selection_sort.
intro.
apply selsort_perm.
reflexivity.
Qed.

(* NOTE!  Proving that a sort function is correct has two parts:
  1.  The output is a permutation of the input
  2.  The output is in increasing order
 Only part 1 has been proved here.  The specification
  and proof of part 2 is missing.

*)

