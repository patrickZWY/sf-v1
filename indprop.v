Set Warnings "-notation-overriden".
From LF Require Export logic.

Fixpoint div2 (n : nat) : nat :=
    match n with
    0 => 0
    | 1 => 0 
    | S (S n) => S (div2 n)
    end.

Definition csf (n : nat) : nat :=
    if even n then div2 n 
    else (3 * n) + 1.

Inductive Collatz_holds_for : nat -> Prop :=
    | Chf_one : Collatz_holds_for 1
    | Chf_even (n : nat) : even n = true ->
                            Collatz_holds_for (div2 n) ->
                            Collatz_holds_for n
    | Chf_odd (n : nat) : even n = false ->
                            Collatz_holds_for ((3 * n) + 1) ->
                            Collatz_holds_for n.


Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
    apply Chf_even. reflexivity. simpl.
    apply Chf_even. reflexivity. simpl.
    apply Chf_odd. reflexivity. simpl.
    apply Chf_even. reflexivity. simpl.
    apply Chf_odd. reflexivity. simpl.
    apply Chf_even. reflexivity. simpl.
    apply Chf_even. reflexivity. simpl.
    apply Chf_even. reflexivity. simpl.
    apply Chf_even. reflexivity. simpl.
    apply Chf_one.
Qed.

Conjecture collatz : forall n, n <> 0 -> Collatz_holds_for n.

Inductive le : nat -> nat -> Prop :=
    | le_n (n : nat) : le n n
    | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof.
apply le_S. apply le_S. apply le_n. Qed.

Inductive clos_trans {X : Type} (R : X->X->Prop) : X->X->Prop :=
    | t_step (x y : X) :
        R x y -> 
        clos_trans R x y
    | t_trans (x y z : X) :
        clos_trans R x y -> 
        clos_trans R y z -> 
        clos_trans R x z.

Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
    po_SC : parent_of Sage Cleo 
    | po_SR : parent_of Sage Ridley
    | po_CM : parent_of Cleo Moss.

Definition ancestor_of : Person -> Person -> Prop :=
    clos_trans parent_of.

Example ancestor_of_ex : ancestor_of Sage Moss.
Proof.
    unfold ancestor_of. apply t_trans with Cleo.
    - apply t_step. apply po_SC.
- apply t_step. apply po_CM. Qed.


Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
    | rt_step (x y : X) :
        R x y ->
        clos_refl_trans R x y
    | rt_refl (x : X) :
        clos_refl_trans R x x
    | rt_trans (x y z : X) :
        clos_refl_trans R x y ->
        clos_refl_trans R y z ->
        clos_refl_trans R x z.

Definition cs (n m : nat) : Prop := csf n = m.

Definition cms n m := clos_refl_trans cs n m.
Conjecture collatz' : forall n, n <> 0 -> cms n 1.


Inductive clos_refl_trans_sym {X: Type} (R: X->X->Prop) : X->X->Prop :=
    | rts_step (x y : X) :
        R x y ->
        clos_refl_trans_sym R x y
    | rts_refl (x : X) :
        clos_refl_trans_sym R x x
    | rts_trans (x y z : X) :
        clos_refl_trans_sym R x y ->
        clos_refl_trans_sym R y z ->
        clos_refl_trans_sym R x z
    | rts_sym (x y : X) :
        clos_refl_trans_sym R x y ->
        clos_refl_trans_sym R y x.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
    | perm3_swap12 (a b c : X) :
        Perm3 [a;b;c] [b;a;c]
    | perm3_swap23 (a b c : X) :
        Perm3 [a;b;c] [a;c;b]
    | perm3_trans (l1 l2 l3 : list X) :
        Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(*if ev n is even then ev (S (S n)) is also even*)
Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS (n : nat) (H : ev n) : ev (S (S n)).


Check ev_0 : ev 0.
Check ev_SS : forall (n : nat), ev n -> ev (S (S n)).

Module EvPlayground.

Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS : forall (n : nat), ev n -> ev (S (S n)).

End EvPlayground.

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
    intros n. simpl. intros Hn. apply ev_SS. apply ev_SS. apply Hn.
Qed.

(*No idea how to deal with n after expansion, you are not using inductive hypo!*)
Theorem ev_double : forall n,
ev (double n).
Proof.
    intros n. induction n.
    simpl. apply ev_0.
    simpl. apply ev_SS. apply IHn.
Qed. 

Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Proof.
    apply perm3_trans with (l2:=[2;3;1]).
    - apply perm3_trans with (l2:=[2;1;3]).
        + apply perm3_swap12.
        + apply perm3_swap23.
    - apply perm3_swap12.
Qed.

Lemma Perm3_rev' : Perm3 [1;2;3] [3;2;1].
Proof.
    apply (perm3_trans _ [2;3;1] _ 
        (perm3_trans _ [2;1;3] _ 
            (perm3_swap12 _ _ _) 
            (perm3_swap23 _ _ _))
        (perm3_swap12 _ _ _)).
Qed.

Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
    apply perm3_trans with (l2:=[2;1;3]).
    apply perm3_swap12.
    apply perm3_swap23.
Qed.

Lemma Perm3_refl : forall (X : Type) (a b c : X),
    Perm3 [a;b;c] [a;b;c].
Proof.
    intros X a b c. apply perm3_trans with (l2:=[b;a;c]).
    apply perm3_swap12. apply perm3_swap12.
Qed.

(*inversion lemma*)
Lemma ev_inversion : forall (n : nat),
ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
    intros n E. destruct E as [ | n' E'] eqn:EE.
    - left. reflexivity.
    - right. exists n'. split. reflexivity. apply E'.
Qed.

Lemma le_inversion : forall (n m : nat),
    le n m -> (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
    intros n m E. destruct E as [| n' E'] eqn:EE.
    left. reflexivity.
    right. exists E'.
    split. reflexivity.
    apply l.
Qed.

(* since we are arguing for the inverted version of one of ev's definition*)
(* recall in type theory the structural induction used inversion too and there *)
(* it was about the only path that could lead to the conclusion, we are in this*)
(* situation too because these are the only ways ev can be*)
(* therefore we do an inversion and get rid of the cases we don't need and use*)
(* the case we need to solve it*)
Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
    intros n E. apply ev_inversion in E. destruct E as [H0|H1].
    - discriminate H0.
    - destruct H1 as [n' [Hnn' E']]. injection Hnn' as Hnn'.
    rewrite Hnn'. apply E'.
Qed.

Theorem evSS_ev' : forall n,
ev (S (S n)) -> ev n.
Proof.
    intros n E. inversion E as [| n' E' Hnn'].
    apply E'.
Qed.

(* apply inversion to obviously contradictory statement*)
Theorem one_not_even : ~ ev 1.
Proof.
    intros H. apply ev_inversion in H. destruct H as [| [m [Hm _]]].
    - discriminate H.
    - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof. intros H. inversion H. Qed.

Theorem SSSSev_even : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
    intros n H.
    inversion H as [| n' E' H'].
    inversion E' as [| n'' E'' H''].
    apply E''.
Qed.

Theorem SSSSev_even' : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
    intros n H.
    apply ev_inversion in H. destruct H as [H1|H2].
    - discriminate H1.
    - destruct H2 as [n' [Ha Hb]].
    injection Ha as Ha'.
    apply ev_inversion in Hb.
    destruct Hb as [H1 | [k [A B]]].
    rewrite H1 in Ha'. discriminate Ha'.
    rewrite A in Ha'. injection Ha' as Hm.
    rewrite Hm.
    apply B.
Qed.










    
