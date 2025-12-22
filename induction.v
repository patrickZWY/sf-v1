From LF Require Export rocqFunc.

Theorem add_0_r_firsttry : forall n:nat,
n + 0 = n.
Proof.
    intros n. induction n as [| n' IHn'].
    - reflexivity.
- simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem minus_n_n : forall n,
minus n n = 0.
Proof.
intros n. induction n as [| n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mul_0_r : forall n:nat,
n * 0 = 0.
Proof.
intros n. induction n as [| n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
    intros n m. induction n as [| n' IHn'].
    simpl. reflexivity.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
    n + m = m + n.
    Proof.
        intros n m.
        induction n as [| n' IHn'].
        simpl.
        rewrite -> add_0_r_firsttry.
        reflexivity.
        simpl.
        rewrite -> IHn'.
        rewrite -> plus_n_Sm.
        reflexivity.
    Qed.

Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
    Proof.
        intros n m p.
        induction m as [| n' IHn'].
        simpl.
        rewrite -> add_0_r_firsttry.
        reflexivity.
        simpl.
        rewrite <- plus_n_Sm.
        rewrite -> IHn'.
        rewrite -> add_comm.
        rewrite <- plus_n_Sm.
        rewrite -> plus_n_Sm.
        rewrite <- add_comm.
        reflexivity.
    Qed.

Fixpoint double (n:nat) :=
    match n with
    | O => O
    | S n' => S (S (double n'))
    end.

Lemma double_plus : forall n, double n = n + n.
Proof.
    intros n.
    induction n as [| n' IHn'].
    simpl.
    reflexivity.
    simpl.
    rewrite -> IHn'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
(n =? n) = true.
Proof.
    intros n. induction n as [| n' IHn'].
    simpl. reflexivity.
    simpl. rewrite -> IHn'. 
reflexivity. Qed.

Theorem even_S : forall n : nat,
even (S n) = negb (even n).
Proof.
    intros n. induction n as [| n' IHn'].
    simpl. reflexivity.
    rewrite -> IHn'.
    simpl.
    rewrite -> negb_involutive.
    reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
    (n + 0 + 0) * m = n * m.
    Proof.
        intros n m.
        replace (n + 0 + 0) with n.
        - reflexivity.
        - rewrite add_comm. simpl. rewrite add_comm. reflexivity.
    Qed.

Theorem plus_rearrange : forall n m p q : nat,
(n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    replace (n + m) with (m + n).
    - reflexivity.
    - rewrite add_comm. reflexivity.
Qed.

Theorem add_shuffle3 : forall n m p : nat,
    n + (m + p) = m + (n + p).
    Proof.
        intros n m p.
        rewrite -> add_assoc.
        rewrite -> add_assoc.
        replace (n + m) with (m + n).
        reflexivity.
        rewrite -> add_comm.
        reflexivity.
    Qed.

Theorem mul_dist : forall m n o : nat,
    m * (n + o) = m * n + m * o.
Proof.
    intros m n o.
    induction m as [| n' IHn'].
    reflexivity.
    simpl. rewrite -> IHn'.
    rewrite -> add_shuffle3.
    rewrite -> plus_rearrange.
    rewrite -> add_assoc.
    rewrite -> add_assoc.
    rewrite -> add_assoc.
    reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
    m * n = n * m.
Proof.
    intros m n.
    induction m as [| n' IHn'].
    simpl. rewrite -> mul_0_r. reflexivity.
    simpl.
    replace (n + n' * n) with (n * (1 + n')).
    simpl. reflexivity.
    rewrite -> IHn'.
    rewrite -> mul_dist.
    rewrite -> mult_n_1.
    reflexivity.
Qed.

Theorem leb_refl : forall n:nat,
(n <=? n) = true.
Proof.
    intros n.
    induction n as [| n' IHn'].
    simpl. reflexivity.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
0 =? (S n) = false.
Proof.
    intros n.
    induction n as [|n' IHn'].
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
andb b false = false.
Proof.
    intros b.
    destruct b.
    reflexivity.
    reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
(S n) =? 0 = false.
Proof.
    intros n.
    reflexivity.
Qed.

Theorem mult_1_1 : forall n:nat, 1 * n = n.
Proof.
    intros n.
    induction n as [| n' IHn'].
    reflexivity.
    rewrite <- mul_comm.
    rewrite <- mult_n_1.
    reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
orb (andb b c) 
    (orb (negb b) 
        (negb c)) = true.
Proof.
    intros b c.
    destruct b.
    simpl.
    destruct c.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
(n + m) * p = (n * p) + (m * p).
Proof.
    intros n m p.
    rewrite -> mul_comm.
    rewrite -> mul_dist.
    rewrite -> mul_comm.
    replace (p * m) with (m * p).
    reflexivity.
    rewrite -> mul_comm.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
Proof.
    intros n m p.
    induction n as [| n' IHn'].
    reflexivity.
    simpl.
    rewrite -> IHn'.
    rewrite <- mult_plus_distr_r.
reflexivity. Qed.



