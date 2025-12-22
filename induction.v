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

Theorem bin_to_nat_pres_incr : forall b : bin,
bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
    intros b.
    induction b.
    reflexivity.
    reflexivity.
    simpl.
    rewrite -> IHb.
    simpl.
    replace (bin_to_nat b + S (bin_to_nat b + 0)) with
    (S (bin_to_nat b + (bin_to_nat b + 0))).
    reflexivity.
    rewrite -> add_0_r_firsttry.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
match n with
| 0 => Z
| S n' => incr (nat_to_bin n')
end.

Theorem nat_bin_nat : 
forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
intros n.
induction n as [| n' IHn'].
simpl. reflexivity.
simpl.
rewrite -> bin_to_nat_pres_incr.
simpl.
rewrite -> IHn'.
reflexivity.
Qed.

Lemma double_incr : 
forall n : nat, double (S n) = S (S (double n)).
Proof.
    intros n.
    simpl.
    reflexivity.
Qed.

Definition double_bin (b:bin) : bin  :=
match b with
| Z => Z
| B0 n' => B0 (B0 n')
| B1 n' => B0 (B1 n')
end.

Example double_bin_zero : double_bin Z = Z.
Proof. reflexivity. Qed.

Example double_bin_one : double_bin (B1 Z) = (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.

Example double_bin_two : double_bin (B0 (B1 Z)) = (B0 (B0 (B1 Z))).
Proof. simpl. reflexivity. Qed.

Example double_bin_three : double_bin (B1 (B1 Z)) = (B0 (B1 (B1 Z))).
Proof. reflexivity. Qed.

Lemma double_incr_bin : forall b,
double_bin (incr b) = incr (incr (double_bin b)).
Proof.
    intros b.
    destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Fixpoint normalize (b:bin) : bin :=
match b with
| Z => Z
| B0 n' => let temp := normalize n' in
    match temp with
    | Z => Z
    | B0 n0 => double_bin (B0 n0)
    | B1 n0 => double_bin (B1 n0)
    end
| B1 n' => B1 (normalize n')
end.

Lemma nat_to_bin_double :
forall n, nat_to_bin (n + n) =
match nat_to_bin n with
| Z => Z
| b => double_bin b 
end.
Proof.
    intros n.
    induction n as [| n' IHn'].
    reflexivity.
    simpl.
    rewrite <- plus_n_Sm.
    simpl.
    rewrite -> IHn'.
    simpl.
    destruct (nat_to_bin n') as [| b' | b'] eqn:E.
    reflexivity.
    reflexivity.
    reflexivity.
Qed.

Theorem bin_nat_bin :
forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
    intros b.
    induction b as [| b IH | b IH].
    reflexivity.
    simpl.
    rewrite -> add_0_r_firsttry.
    rewrite -> nat_to_bin_double.
    rewrite -> IH.
    reflexivity.
    simpl.
    rewrite -> add_0_r_firsttry.
    rewrite -> nat_to_bin_double.
    rewrite -> IH.
    destruct (normalize b).
    reflexivity.
    reflexivity.
    reflexivity.
Qed.