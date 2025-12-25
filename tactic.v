From LF Require Export poly.
(* The commands to compile
rocq makefile -f _CoqProject *.v -o Makefile
make. *)

Theorem silly1 : forall (n m : nat),
n = m -> n = m.
Proof.
    intros n m eq.
apply eq. Qed.

Theorem silly2 : forall (n m o p : nat),
n = m -> (n = m -> [n;o] = [m;p]) -> [n;o] = [m;p].
Proof. 
    intros n m o p eq1 eq2.
apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
(n,n) = (m,m) -> (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) -> [n] = [m].
Proof.
    intros n m eq1 eq2.
apply eq2. apply eq1. Qed.

Theorem silly_ex : forall p,
(forall n, even n = true -> even (S n) = false) ->
(forall n, even n = false -> odd n = true) ->
even p = true -> odd (S p) = true.
Proof.
    intros p eq1 eq2 eq3.
    apply eq2.
    apply eq1.
    apply eq3.
Qed.

Theorem silly3 : forall (n m : nat),
n = m -> m = n.
Proof.
    intros n m H.
symmetry. apply H. Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
l = rev l' -> l' = rev l.
Proof.
    intros l l' H.
    rewrite -> H.
    symmetry.
    apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
[a;b] = [c;d] ->
[c;d] = [e;f] ->
[a;b] = [e;f].
Proof.
    intros a b c d e f eq1 eq2.
rewrite -> eq1. apply eq2. Qed.

Theorem trans_eq : forall (X:Type) (x y z : X),
x = y -> y = z -> x = z.
Proof.
    intros X x y z eq1 eq2. rewrite -> eq1. rewrite -> eq2.
reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
intros a b c d e f eq1 eq2.
apply trans_eq with (y:=[c;d]).
apply eq1. apply eq2. Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
intros a b c d e f eq1 eq2.
transitivity [c;d].
apply eq1. apply eq2. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
    intros n m o p eq1 eq2.
    transitivity m.
    apply eq2.
    apply eq1.
Qed.

Theorem S_injective : forall (n m : nat),
S n = S m ->  n = m.
Proof.
    intros n m H1.
    assert (H2 : n = pred (S n)). { reflexivity. }
    rewrite H2. rewrite -> H1. simpl. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
S n = S m -> n = m.
Proof.
    intros n m H.
    injection H as Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
[n;m] = [o;o] ->
n = m.
Proof.
    intros n m o H.
    injection H as H1 H2.
    rewrite H1. rewrite H2. reflexivity.
Qed.

(*There should be an easier way to prove this.*)
Example injection_ex3 : forall (X : Type) (x y z : X)
(l j : list X),
x :: y :: l = z :: j ->
j = z :: l ->
x = y.
Proof.
    intros X x y z l j H1 H2.
    injection H1 as H1' H1''.
    assert (H3 : y :: l = z :: l).
    - rewrite H1''. rewrite <- H2.
    reflexivity.
    - assert (H4 : y = z).
    injection H3 as H5.
    apply H5.
    rewrite H4.
    apply H1'.
Qed.

Theorem discriminate_ex1 : forall (n m : nat),
false = true -> n = m.
Proof.
intros n m contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n : nat),
S n = O -> 2 + 2 = 5.
Proof.
intros n contra. discriminate contra. Qed.

Example discriminate_ex3 : forall (X : Type)
(x y z : X) (l j : list X),
x :: y :: l = [] -> x = z.
Proof.
    intros X x y z l j contra.
discriminate contra. Qed.

Theorem eqb_0_1 : forall n,
0 =? n = true -> n = 0.
Proof.
    intros n.
    destruct n as [| n'] eqn:E.
    - intros H. reflexivity.
    - simpl. intros H. discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B)
(x y : A), x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
n = m -> S (S n) = S (S m).
Proof. intros n m H. f_equal. f_equal. apply H. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
((S n) =? (S m)) = b ->
(n =? m) = b.
Proof.
intros n m b H. simpl in H. apply H. Qed.

Theorem silly4 : forall (n m p q : nat),
(n = m -> p = q) ->
m = n ->
q = p.
Proof.
    intros n m p q EQ H.
    symmetry in H. apply EQ in H. symmetry in H.
apply H. Qed.

Theorem specialize_example : forall n,
(forall m, m * n = 0)
-> n = 0.
Proof.
    intros n H.
    specialize H with (m := 1).
    rewrite mult_1_1 in H.
apply H. Qed.

Example trans_eq_example''' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
intros a b c d e f eq1 eq2.
specialize trans_eq with (y:=[c;d]) as H.
apply H.
apply eq1.
apply eq2. Qed.

(*Introduce n and m early on then do induction on n
means that we want to prove a statement involving 
every n but just a particular m, whereas when done
correctly here, we leave m universally quantified
and we are proving a statement for every n and m.*)
Theorem double_injective : forall n m,
double n = double m -> n = m.
Proof.
    intros n. induction n as [| n' IHn'].
    - simpl. intros m eq. destruct m as [| m'] eqn:E.
        + reflexivity.
        + discriminate eq.
    - intros m eq. destruct m as [| m'] eqn:E.
    + discriminate eq.
    + f_equal. apply IHn'. simpl in eq. 
    injection eq as goal. apply goal.
Qed.

Theorem eqb_true : forall n m,
n =? m = true -> n = m.
Proof.
    intros n. induction n as [| n' IHn'].
    - simpl. intros m eq. destruct m as [| m'] eqn:E.
        + reflexivity.
        + discriminate eq.
    - intros m eq. destruct m as [| m'] eqn:E.
        + discriminate eq.
        + f_equal. apply IHn'. simpl in eq.
        apply eq.
Qed.

(*Leave m generic and destruct it later on because
we get stuck if we introduce n and m together.*)
Theorem plus_n_n_injective : forall n m,
n + n = m + m -> n = m.
Proof.
    intros n. induction n as [| n' IHn'].
    - simpl. intros m eq. destruct m as [| m'] eqn:E.
        + reflexivity.
        + discriminate eq.
    - intros m eq. destruct m as [| m'] eqn:E.
        + discriminate eq.
        + f_equal. apply IHn'. 
        injection eq as goal.
        rewrite <- plus_n_Sm in goal.
        rewrite <- plus_n_Sm in goal.
        injection goal as goal2.
        apply goal2.
Qed.