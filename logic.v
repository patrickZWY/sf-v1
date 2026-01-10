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

Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x,
m = n + x.
Proof.
    intros n.
    induction n as [| n' IH].
    - intros m _.
    exists m.
    simpl.
    reflexivity.
    - intros m H.
    destruct m as [| m'].
    + simpl in H.
    discriminate.
    + simpl in H.
    apply IH in H.
    destruct H as [x Hx].
    exists x.
    simpl.
    rewrite Hx.
    reflexivity.
Qed.

Theorem plus_exists_leb : forall n m, (exists x, m = n + x) ->
n <=? m = true.
Proof.
    intros n.
    induction n as [| n' IH].
    intros m _.
    simpl. reflexivity.
    intros m [x Hx].
    destruct m as [| m'].
    + simpl in Hx.
    discriminate.
    + simpl. apply IH.
    exists x.
    simpl in Hx.
    injection Hx as Hx'.
    apply Hx'.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
    match l with
    | [] => False
    | x' :: l' => x' = x \/ In x l'
    end.

Example In_example_1 : In 4 [1;2;3;4;5].
Proof.
    simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
forall n, In n [2; 4] -> exists n', n = 2 * n'.
Proof.
    simpl.
    intros n [H | [H | []]].
    - exists 1. rewrite <- H. reflexivity.
    - exists 2. rewrite <- H. reflexivity.
Qed.

Theorem In_map :
forall (A B : Type) (f : A -> B) (l : list A) (x : A),
In x l -> In (f x) (map f l).
Proof.
    intros A B f l x.
    induction l as [| x' l' IHl'].
    simpl. intros [].
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Theorem In_map_iff :
forall (A B : Type) (f : A -> B) (l : list A) (y : B),
In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
    intros A B f l y. split.
    - induction l as [| x l' IHl'].
    simpl. intros [].
    simpl. intros [H | H].
    + exists x. split. apply H.
    left. reflexivity.
    + destruct (IHl' H) as [x' [Hx' Hin']].
    exists x'. split.
    apply Hx'.
    right. apply Hin'.
    - intros [x [Hfx Hin]].
    induction l as [| a l' IHl'].
    + simpl in Hin. simpl. apply Hin.
    + simpl in Hin. simpl.
    destruct Hin as [Hin1 | Hin2].
    left. rewrite <- Hfx. rewrite -> Hin1. reflexivity.
    right. apply IHl'. apply Hin2.
Qed.

Theorem In_app_iff : forall A l l' (a:A),
    In a (l++l') <-> In a l \/ In a l'.
Proof.
    intros A l. induction l as [| a' l IH].
    - intros l' a. simpl. split.
    + intros H. right. apply H.
    + intros H. destruct H as [H | H].
    * exfalso. apply H.
    * apply H.
    - intros l1' a. simpl. split.
    + intros H. destruct H as [H | H].
    left. left. apply H.
    destruct (IH l a) as [IH3 IH4].
    apply or_assoc.
    right. apply IH.
    apply H.
    + intros H. destruct H as [H | H].
    destruct H as [H1 | H1].
    left. apply H1. right. apply IH. left.
    apply H1. right. apply IH. right. apply H.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
    match l with
    | [] => True
    | x' :: l' => (P x') /\ (All P l')
    end.

(*See a false hypothesis, do exfalso*)
Theorem All_In :
    forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
    intros T P l. induction l as [| a l' IHl'].
    split. simpl. intros x. apply I.
    simpl. intros x. intros x0. intros H. exfalso. apply H.
    split. simpl. intros H. destruct IHl'.
    split. apply H. left. reflexivity.
    apply H0. intros x. intros H5.
    apply H. right. apply H5.
    simpl. intros H x HIn.
    destruct H as [Ha Hall].
    destruct HIn as [Hx | HIn'].
    * rewrite <- Hx. apply Ha.
    * apply IHl'.
    apply Hall. apply HIn'.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
    fun x => (odd x = true -> Podd x) /\ (odd x = false -> Peven x).

Theorem combine_odd_even_intro :
    forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
    intros Po Pe n.
    intros H1 H2.
    unfold combine_odd_even.
    split. apply H1. apply H2.
Qed.

Theorem combine_odd_even_elim_odd :
    forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true -> Podd n.
Proof.
    intros Po Pe n.
    intros H1 H2.
    unfold combine_odd_even in H1.
    destruct H1.
    apply H. apply H2.
Qed.

Theorem combine_odd_even_elim_even :
    forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
    intros Po Pe n.
    intros H1 H2.
    destruct H1.
    apply H0.
    apply H2.
Qed.

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

Check add_comm : forall n m : nat, n + m = m + n.
Check plus_id_example : forall n m : nat, n = m -> n + n = m + m.

Lemma add_comm3 :
forall x y z, x + (y + z) = (z + y) + x.
Proof.
    intros x y z.
    rewrite (add_comm x (y + z)).
    rewrite (add_comm y z).
    reflexivity.
Qed.

Theorem in_not_nil :
    forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
    intros A x l H. unfold not. intro Hl.
    rewrite Hl in H. simpl in H. apply H.
Qed.

Lemma in_not_nil_42 :
forall l : list nat, In 42 l -> l <> [].
Proof.
    intros l H.
    apply (in_not_nil nat 42). apply H.
Qed.

Lemma in_not_nil_42' :
forall l : list nat, In 42 l -> l <> [].
Proof.
    intros l H.
    apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
forall {n : nat} {ns : list nat},
In n (map (fun m => m * 0) ns) ->
n = 0.
Proof.
    intros n ns H.
    destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
    as [m [Hm _]].
    rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
    intros k. induction k as [|k' IHk'].
    - reflexivity.
    - simpl. apply IHk'.
Qed.

Lemma even_double_conv : forall n, exists k,
n = if even n then double k else S (double k).
Proof.
    intros n. induction n as [| n' IHn'].
    simpl. exists 0. simpl. reflexivity.
    destruct IHn' as [k Hk].
    destruct (even n') eqn:Hev.
    exists k. rewrite Hk in Hev. rewrite Hk.
    rewrite even_S. rewrite Hev. simpl. reflexivity.
    exists (S k).
    rewrite even_S. rewrite Hev. simpl. rewrite -> Hk.
    reflexivity.
Qed.

Theorem even_bool_prop : forall n,
even n = true <-> Even n.
Proof.
    intros n. split.
    - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
    - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
n1 =? n2 = true <-> n1 = n2.
Proof.
    intros n1 n2. split.
    - apply eqb_true.
    - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

Example even_1000 : Even 1000.

Proof. unfold Even. exists 500. reflexivity. Qed.

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001 : even 1001 = false.
Proof.
    reflexivity.
Qed.


Example not_even_1001' : ~(Even 1001).
Proof.
    unfold not.
    rewrite <- even_bool_prop.
    simpl.
    intro H.
    discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
    intros n m p H.
    rewrite eqb_eq in H.
    rewrite H.
    rewrite eqb_eq.
    reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2 : bool,
b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
    intros b1 b2.
    split. intro H.
    split. destruct b1. destruct b2.
    reflexivity. reflexivity. destruct b2.
    simpl in H. discriminate H. simpl in H. discriminate H.
    destruct b2. reflexivity. destruct b1. simpl in H. discriminate H.
    simpl in H. discriminate H.
    intro H.
    destruct H.
    rewrite H. rewrite H0. simpl. reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
    split. destruct b1. destruct b2. simpl. left. apply H.
    simpl. left. apply H. destruct b2. simpl. right. apply H.
    simpl. right. apply H. destruct b1. destruct b2.
    intros H. simpl. reflexivity.
    simpl. intro H. reflexivity.
    simpl. intro H. destruct b2.
    reflexivity. destruct H.
    apply H. apply H.
Qed.

Theorem eqb_neq : forall x y : nat,
x =? y = false <-> x <> y.
Proof.
    split.
    destruct x. destruct y. simpl. intro H. discriminate H.
    simpl. unfold not. intro H. intro H2. symmetry in H2.
    discriminate H2.
    unfold not. destruct y.
    simpl. intro H. intro H2. discriminate H2.
    simpl. intro H. intro H2. injection H2 as H3.
    rewrite H3 in H. rewrite eqb_refl in H. discriminate H.
    unfold not. intro H. apply not_true_iff_false. unfold not.
    intro H2. apply H. destruct x. destruct y. reflexivity.
    apply eqb_true in H2. apply H2.
    apply eqb_true in H2. apply H2.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
(l1 l2 : list A) : bool :=
match l1, l2 with
| [], [] => true
| [], _ => false
| _, [] => false
| x1 :: xs1, x2 :: xs2 => eqb x1 x2 && eqb_list eqb xs1 xs2 
end.

Theorem eqb_list_true_iff :
forall A (eqb : A -> A -> bool),
(forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
    intros A eqb. intros Heq.
    induction l1 as [| x1 xs1 IH].
    intro l2.
    split. destruct l2 as [| x2 xs2].
    intro useless. reflexivity.
    simpl. intro H. discriminate H.
    intro H. rewrite <- H. simpl. reflexivity.
    split.
    destruct l2 as [| x2 xs2].
    simpl. intro H. discriminate H.
    simpl. intro H. apply andb_true_iff in H as [Hhd Htl].
    apply Heq in Hhd. apply IH in Htl.
    rewrite Hhd. rewrite Htl. reflexivity.
    intro H. rewrite <- H. simpl.
    apply andb_true_iff. split.
    apply Heq. reflexivity.
    apply IH. reflexivity.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) 
(l : list X) : bool :=
match l with
| nil => true
| x :: xs => if test x then forallb test xs else false
end.

Theorem forallb_true_iff : forall X test (l : list X),
    forallb test l = true <-> All (fun x => test x = true) l.
Proof.
    intros X test l.
    induction l as [| x xs IH].
    simpl. split. intro H. apply I. intro H. reflexivity.
    simpl. split. intro H. split.
    destruct (test x). reflexivity. discriminate H.
    apply IH. destruct (test x) in H.
    apply H. discriminate H.
    intro H.
    destruct (test x).
    apply IH. destruct H.
    apply H0.
    destruct H. apply H.
Qed.

Example function_equality_ex1 :
    (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Example function_equality_ex2 :
    (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
    Fail reflexivity. Fail rewrite add_comm.
Abort.

Axiom functional_extensionality : forall {X Y : Type} {f g : X -> Y},
(forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
    (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
    apply functional_extensionality. intros x.
    apply add_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
    match l1 with
    | [] => l2
    | x :: l1' => rev_append l1' (x :: l2)
    end.

Definition tr_rev {X} (l : list X) : list X :=
    rev_append l [].

Lemma helper1 : forall {X : Type} (l1 : list X), l1 = [] -> tr_rev l1 = rev l1.
Proof.
    intros X l1 H.
    rewrite H. simpl. unfold tr_rev. simpl. reflexivity.
Qed.

Lemma helper2 : forall {X : Type} (l1 : list X) (x : X) , l1 = [x] -> tr_rev l1 = rev l1.
Proof.
    intros X l1 x H.
    rewrite H.
    simpl.
    reflexivity.
Qed.

Lemma helper4 : forall {X : Type} (xs acc: list X), rev_append xs acc = rev xs ++ acc.
Proof.
    intros X xs.
    induction xs as [| a xs IH].
    intro acc. simpl. reflexivity.
    intro acc. simpl. rewrite IH.
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma helper3 : forall {X : Type} (l1 : list X), tr_rev l1 = rev l1.
Proof.
    intros X l1.
    induction l1 as [| x xs IH].
    apply helper1. reflexivity.
    simpl.
    unfold tr_rev. simpl. apply helper4.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
    intro X.
    apply functional_extensionality.
    apply helper3.
Qed.
    

