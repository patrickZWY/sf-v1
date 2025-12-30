From LF Require Export tactic.

Check (forall n m : nat, n + m = m + n) : Prop.

Check 2 = 2 : Prop.
Check 3 = 2 : Prop.
Check forall n : nat, n = 2 : Prop.

Theorem plus_2_2_is_4 :
2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
plus_claim.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
n = 3.
Check is_three : nat -> Prop.

Definition injective {A B} (f : A -> B) : Prop :=
forall x y : A, f x = f y -> x = y.
Lemma succ_inj : injective S.
Proof.
intros x y H. injection H as H1. apply H1.
Qed.

Check @eq : forall A : Type, A -> A -> Prop.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
    split.
    - reflexivity.
    - reflexivity.
Qed.

Check @conj : forall A B : Prop, A -> B -> A /\ B.
Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
    apply conj.
    - reflexivity.
    - reflexivity.
Qed.

Example plus_is_O :
forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
    intros n m H.
    apply conj.
    destruct n.
    reflexivity.
    simpl in H. discriminate H.
    destruct m.
    reflexivity.
    destruct n in H.
    simpl in H.
    discriminate H.
    discriminate H.
Qed.

Lemma and_example2 :
    forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
intros n m H.
destruct H as [Hn Hm].
rewrite Hn. rewrite Hm.
reflexivity.
Qed.

Lemma and_example2' :
    forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
    intros n m [Hn Hm].
    rewrite Hn. rewrite Hm.
    reflexivity.
Qed.

Lemma and_example2'' :
    forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
    intros n m Hn Hm.
    rewrite Hn. rewrite Hm.
    reflexivity.
Qed.

Lemma and_example3 :
    forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
    intros n m H.
    apply plus_is_O in H.
    destruct H as [Hn Hm].
    rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
    P /\ Q -> P.
Proof.
    intros P Q HPQ.
    destruct HPQ as [HP _].
    apply HP. Qed.

Lemma proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
    intros P Q eq.
    destruct eq as [_ HQ].
    apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
    intros P Q [HP HQ].
    split.
    - apply HQ.
    - apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
    intros P Q R [HP [HQ HR]].
    split.
    split.
    apply HP. apply HQ. apply HR.
Qed.

Lemma factor_is_O:
    forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
    intros n m [Hn | Hm].
    - rewrite Hn. reflexivity.
    - rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
    intros A B HA.
    left.
    apply HA.
Qed.

Lemma zero_or_succ : 
forall n : nat, n = 0 \/ n = S (pred n).
Proof.
    intros [| n'].
    - left. reflexivity.
    - right. reflexivity.
Qed.

Lemma mult_is_O :
forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
    intros n m H.
    destruct n as [| n'].
    - left. reflexivity.
    - right. destruct m as [| m'].
    + reflexivity.
    + simpl in H. discriminate H.
Qed.

Theorem or_commut : forall P Q : Prop,
P \/ Q -> Q \/ P.
Proof.
    intros P Q [HP | HQ].
    right. apply HP.
    left. apply HQ.
Qed.

Definition not (P:Prop) := P -> False.

Check not : Prop -> Prop.

Notation "~ x" := (not x) : type_scope.

Theorem ex_falso_quodlibet : forall (P:Prop),
False -> P.
Proof.
    intros P contra.
    destruct contra.
Qed.

Theorem not_implies_our_not : forall (P:Prop),
~ P -> (forall (Q:Prop), P -> Q).
Proof.
    unfold not.
    intros P Q eq eq2.
    apply ex_falso_quodlibet.
    apply Q.
    apply eq2.
Qed.

Notation "x <> y" := (~(x = y)) : type_scope.

Theorem zero_not_one : 0 <> 1.
Proof.
    unfold not.
    intros contra.
    discriminate contra.
Qed.

Theorem not_False :
~ False.
Proof.
    unfold not. intros H. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
(P /\ ~P) -> Q.
Proof.
    intros P Q [HP HNP]. unfold not in HNP.
    apply HNP in HP. destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
P -> ~~P.
Proof.
    intros P H. unfold not. intros G. apply G. apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
(P -> Q) -> (~Q -> ~P).
Proof.
    intros P Q eq eq2.
    unfold not. unfold not in eq2.
    intros H.
    apply eq2. apply eq. apply H.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
~ (P /\ ~P).
Proof.
    intros P [HP HNP].
    unfold not in HNP.
    apply HNP. apply HP.
Qed.

Theorem de_morgan_not_or : forall (P Q : Prop),
~ (P \/ Q) -> ~P /\ ~Q.
Proof.
    intros P Q.
    unfold not.
    split.
    intros H1.
    apply H.
    left.
    apply H1.
    intros H1.
    apply H.
    right.
    apply H1.
Qed.

Lemma not_S_pred_n : ~(forall n : nat, S (pred n) = n).
Proof.
    unfold not.
    intros H.
    unfold pred in H.
    specialize (H 0).
    simpl in H.
    discriminate H.
Qed.

Theorem not_true_is_false : forall b : bool,
b <> true -> b = false.
Proof.
    intros [] H.
    - unfold not in H.
    exfalso.
    apply H. reflexivity.
    - reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Definition disc_fn (n : nat) : Prop :=
    match n with
    | O => True
    | S _ => False
    end.

Theorem disc_example : forall n, ~ (O = S n).
Proof.
    intros n contra.
    assert (H : disc_fn O). { simpl. apply I. }
    rewrite contra in H. simpl in H. apply H.
Qed.

Definition disc_fn' {X : Type} (n : list X) : Prop :=
    match n with
    | nil => True
    | _ :: _ => False
    end.

Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x :: xs).
Proof.
    intros X x xs contra.
    assert (H : disc_fn' (@nil X)). { simpl. apply I. }
    rewrite contra in H. simpl in H. apply H.
Qed.

Theorem iff_sym : forall P Q : Prop,
(P <-> Q) -> (Q <-> P).
Proof.
    intros P Q [HAB HBA].
    split.
    - apply HBA.
    - apply HAB.
Qed.

Lemma not_true_iff_false : forall b,
b <> true <-> b = false.
Proof.
    intros b. split.
    - apply not_true_is_false.
    - intros H. rewrite H. intros H'. discriminate H'.
Qed.

Lemma apply_iff_example1:
    forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
    intros P Q R Hiff H HP. apply H. apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
    forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
    intros P Q R Hiff H HQ. apply H. apply Hiff. apply HQ.
Qed.

Theorem iff_refl : forall P : Prop,
    P <-> P.
Proof.
    intros P.
    split.
    intros H.
    apply H.
    intros H.
    apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
(P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros P Q R H1 H2.
    split.
    intros H3.
    apply H2. apply H1. apply H3.
    intros H3.
    apply H1.
    apply H2.
    apply H3.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
    intros P Q R.
    split.
    intros H.
    split.
    destruct H as [H1 | H2] eqn:Ed.
    left. apply H1. destruct H2. right. apply q.
    destruct H as [H1 | H2] eqn:Ed.
    left. apply H1. destruct H2. right. apply r.
    intros H.
    destruct H as [H1 H2] eqn:E1.
    destruct H1 as [H3 | H4] eqn:E2.
    left. apply H3.
    destruct H2 as [H5 | H6].
    left. apply H5.
    right. split.
    apply H4. apply H6.
Qed. 

From Stdlib Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
    intros n m.
    split.
    - apply mult_is_O.
    - apply factor_is_O.
Qed.

Theorem or_assoc :
    forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
    intros P Q R. split.
    - intros [H | [H | H]].
        + left. left. apply H.
        + left. right. apply H.
        + right. apply H.
    - intros [[H | H] | H].
        + left. apply H.
        + right. left. apply H.
        + right. right. apply H.
Qed.

Lemma mul_eq_0_ternary :
    forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
    intros n m p.
    rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
    reflexivity.
Qed.

Definition Even x := exists n : nat, x = double n.
Check Even : nat -> Prop.

Lemma four_is_Even : Even 4.
Proof.
    unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
(exists m, n = 4 + m) ->
(exists o, n = 2 + o).
Proof.
    intros n [m Hm].
    exists (2 + m).
    apply Hm.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
(forall x, P x) -> ~ (exists x, ~ P x).
Proof.
    intros X P H1 H2.
    destruct H2 as [x E].
    unfold not in E.
    apply E.
    apply H1.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
(exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
    intros X P Q.
    split.
    intros H1.
    destruct H1 as [x [goal | goal2]].
    left.
    exists x.
    apply goal.
    right.
    exists x.
    apply goal2.
    intros H2.
    destruct H2 as [ [x H1] | [y H2]].
    exists x.
    left. apply H1.
    exists y.
    right.
    apply H2.
Qed.







