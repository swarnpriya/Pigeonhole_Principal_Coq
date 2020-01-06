
(*Add LoadPath "/Users/swarnpriya/Desktop/Purdue_research/COQ/cs541_sf/".*)
Require Export List.
Require Export Setoid.
Require Export PeanoNat.
Require Export Lt.
Require Export Compare_dec.
Require Export Arith.
Require Export Omega.

Definition pigeon := Set.

(* A container is a list of pigeon as a container might contain more than one pigeon *)
Definition container := list pigeon.

(* Containers is a list of container which resembles the pigeon holes *)
Definition containers := list container.

Definition number_of_containers (c : containers) := length c.

Definition number_of_pigeons_in_a_container (c : container) := length c.

Fixpoint total_number_of_pigeons_in_containers (c : containers) : nat := 
match c with
| nil => O
| cons x l => (number_of_pigeons_in_a_container x + total_number_of_pigeons_in_containers l)
end.

Definition good_container (c : container) : Prop :=
 number_of_pigeons_in_a_container c <= 1.


Inductive good_containers : containers -> bool -> Prop :=
| nil_case_cs : good_containers nil true
| cons_case_cs : forall x l,
                 good_container x ->
                 good_containers l true ->
                 good_containers (cons x l) true.

(* Contrapositive *)
Theorem contrapositive_ph : forall c : containers,
good_containers c true ->
total_number_of_pigeons_in_containers c <= number_of_containers c.
Proof.
intros.
induction c.
- (* case : no containers *)
simpl. intuition.
- (* case : more than one containers *) 
induction a.
 + (* case : first container is empty *)
  simpl. apply le_S. apply IHc. inversion H. subst. assumption.
 + (* case : first container has one or more than one thing *) 
  induction a0. simpl. apply le_n_S. apply IHc. inversion H. subst.
  assumption. inversion H. subst. inversion H2. subst.
  inversion H1.
Qed.

Lemma not_good_containers : forall c,
    total_number_of_pigeons_in_containers c > number_of_containers c ->
    good_containers c true -> False.
Proof.
intros.
unfold not. intros.
apply le_not_lt in H. unfold not in H.
apply H. apply le_n_S. apply contrapositive_ph.
assumption.
Qed.

Lemma good_containers_p : forall a c,
good_container a ->
good_containers c true ->
total_number_of_pigeons_in_containers c <=
     number_of_containers c ->
good_containers (a :: c)%list true.
Proof.
intros.
apply cons_case_cs.
assumption.
assumption.
Qed.

Lemma container_good_or_not_dec : forall c,
      {good_container c} + {~ good_container c}.
Proof.
intros.
apply le_dec. 
Qed.

(* Proving contrapositive of contrapositive_ph theorem *)
Theorem pigeon_hole : forall c,
(good_containers c true  ->
total_number_of_pigeons_in_containers c <= number_of_containers c) ->
(not (total_number_of_pigeons_in_containers c <= number_of_containers c) ->
not (good_containers c true)).
Proof.
intros c.
intros H.
unfold not.
intros H1.
intros H3.
apply H1.
apply H.
apply H3.
Qed.

Lemma gt_S : forall n m,
    (S n) > (S m) <-> n > m.
Proof.
  intros. unfold gt. split; omega.
Qed.

Lemma gt_S' : forall n m,
    n > (S m) -> n > m.
Proof.
  intros. unfold gt. omega.  
Qed.

(* I think this hypothesis is true but the good proof should include the 
proof of this hypothesis as well *)
Lemma lemma0 : forall a c,
total_number_of_pigeons_in_containers (cons a c) > number_of_containers (cons a c) ->
good_container a ->
total_number_of_pigeons_in_containers c > number_of_containers c.
Proof.
unfold good_container. induction c; intros.
- inversion H.
+ rewrite -> plus_comm in H2. simpl in H2.
rewrite <- H2 in H0. inversion H0. inversion H3.
+ rewrite -> plus_comm in H1. simpl in H1. rewrite <- H1 in H0.
inversion H0; subst. inversion H2. inversion H4.
- simpl in H. inversion H0.
+ rewrite H2 in H. simpl in H. apply -> gt_S in H. simpl. assumption.
+ subst. inversion H2. rewrite -> H3 in H. simpl in H. apply gt_S' in H.
simpl. assumption.
Qed.


Theorem pigeon_hole' : forall (c : containers),
total_number_of_pigeons_in_containers c > number_of_containers c ->
exists c', In c' c /\ ~ good_container c'.
Proof.
intro c.
intros H.
induction c.
(* case : no containers *)
exists nil. split. simpl. inversion H.
unfold not. intros. inversion H.
(* Not getting two cases either the head of the list if faulty or there may be 
an element in the tail that is faulty *)
destruct (container_good_or_not_dec) with a.
induction IHc.
(* x is in the tail *) 
exists x. split. destruct H0. simpl. right.
assumption.
destruct H0. assumption. apply lemma0 with a.
assumption. assumption.
(* head is faulty *)
exists a. split. simpl. left.
reflexivity. assumption.
Qed.





