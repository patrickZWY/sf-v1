From LF Require Export induction.
Module NatList.

Inductive natprod : Type :=
    | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3, 5)).

Definition fst' (p : natprod) : nat :=
    match p with 
    | (x, y) => x
    end.
Definition snd' (p : natprod) : nat :=
    match p with 
    | (x, y) => y
    end.
Definition swap_pair (p : natprod) : natprod :=
    match p with 
    | (x, y) => (y, x)
    end.

Fixpoint minus (n m : nat) : nat :=
match n, m with
| O , _ => O
| S _, O => n
| S n', S m' => minus n' m'
end.

Theorem surjective_pairing : forall (p : natprod),
p = (fst p, snd p).
Proof.
intros p. destruct p as [n m]. simpl. reflexivity. 
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
(snd p, fst p) = swap_pair p.
Proof.
    intros p. destruct p as [n m]. simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
fst (swap_pair p) = snd p.
Proof.
    intros p. destruct p as [n m]. simpl. reflexivity.
Qed.





