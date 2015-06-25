(* Selection sort.  Andrew W. Appel, March 2013.
  Selection sort is rarely the right sort to use:
   it's not as fast as insertion sort (if you want
  a simple O(n^2) sorting algorithm), and its
  proof is (slightly) more difficult too.  We use it here
  only to show some proof techniques. *)				        
 
Require Import Permutation.
Require Import SfLib.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Theorem ble_nat_i: forall n m, n <= m -> ble_nat n m = true.
Proof.
induction n as [|n']; intros; simpl; auto.
destruct m.
elimtype False.
omega.
apply IHn'.
omega.
Qed.

Theorem false_ble_nat_i:  forall n m, n > m -> ble_nat n m = false.
Proof.
intros.
remember (ble_nat n m) as p; destruct p; auto.
symmetry in Heqp; apply ble_nat_true in Heqp; elimtype False; omega.
Qed.

Theorem false_ble_nat_e: forall n m, ble_nat n m = false -> n > m.
Proof.
intros.
assert (n <= m \/ n > m) by omega.
destruct H0; auto.
apply ble_nat_i in H0.
rewrite H0 in H.
inversion H.
Qed.

(* PART I.   Prove correctness of functional program for selection sort  *)

Fixpoint select (i: nat) (l: list nat) : nat * list nat :=
match l with
|  nil => (i, nil)
|  h::t => if ble_nat i h 
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
destruct (ble_nat i a).
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

Lemma selsort_perm:
  forall n, 
  forall l, length l = n -> Permutation l (selsort l n).
Proof.
intros.
rewrite <- H.
clear n H.
induction l.
simpl.
constructor.
simpl.
assert (H0 := select_perm a l).
destruct (select a l).
eapply Permutation_trans.
apply H0.
constructor.
assert (length l0 = length l). {
  clear - H.
  revert a n0 l0 H; induction l; intros; destruct l0; simpl in *; auto.
  destruct (ble_nat a a0).
  destruct (select a l) eqn:?; inversion H.
  destruct (select a0 l) eqn:?; inversion H.
  replace (length l) with (length l0); auto.
  destruct (ble_nat a a0).
  destruct (select a l) eqn:?. inversion H. subst. auto.
  destruct (select a0 l) eqn:?. invversion H. subst. clear H H1. auto.
  inversion H.

}



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
