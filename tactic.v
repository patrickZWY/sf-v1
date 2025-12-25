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
