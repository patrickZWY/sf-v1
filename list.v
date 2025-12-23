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

Inductive natlist : Type :=
    | nil
    | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                    (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil 
    | S count' => n :: (repeat n count')
    end.

Fixpoint length (l:natlist) : nat :=
    match l with
    | nil => O
    | h :: t => S (length t)
end.

Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
end.

Notation "x ++ y" := (app x y)
                        (right associativity, at level 60).
Example test_app1 : [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2 : nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3 : [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.


Definition hd (default : nat) (l : natlist) : nat :=
match l with
| nil => default
| h :: t => h
end.

Definition tl (l : natlist) : natlist :=
match l with
| nil => nil
| h :: t => t
end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
match l with
| nil => nil
| 0 :: t => nonzeros t
| n :: t => n :: nonzeros t
end.

Example test_nonzeros:
nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
match l with
| nil => nil
| n :: t => if (odd n) then n :: (oddmembers t) else oddmembers t
end.

Example test_oddmembers:
oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat := length (oddmembers l).

Example test_countoddmembers1:
countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2:
countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
match l1, l2 with
| nil, _ => l2
| _, nil => l1
| n :: t1, m :: t2 => n :: m :: (alternate t1 t2)
end.

Example test_alternate1:
alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:
alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:
alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
match s with
| x :: xs => if x =? v then 1 + (count v xs) else count v xs
| nil => O
end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
alternate.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
app [v] s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
match s with
| x :: xs => if x =? v then true else member v xs
| nil => false
end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
match s with
| x :: xs => if v =? x then xs else x :: remove_one v xs
| nil => nil
end.

Example test_remove_one1:
count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
count 5 (remove_one 5 [2;1;4;1]) = 0.

Proof. reflexivity. Qed.

Example test_remove_one3:
count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
match s with
| x :: xs => if x =? v then remove_all v xs else x :: remove_all v xs
| nil => nil
end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
match s1, s2 with
| x :: xs, y => 
    if member x y then included xs (remove_one x y) 
    else false
| nil, n => true 
end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem add_inc_count : forall (m : bag) (v : nat),
count v (app [v] m) = S (count v m).
Proof. 
    intros m v.
    induction m as [| n' IHn'].
    simpl. rewrite -> eqb_refl. reflexivity.
    simpl. rewrite -> eqb_refl. reflexivity.
Qed.

Theorem nil_app : forall l : natlist,
[] ++ l = l.
Proof. reflexivity. Qed.
    
Theorem tl_length_pred : forall l:natlist,
pred (length l) = length (tl l).
Proof.
intros l. destruct l as [| n l'].
-
    reflexivity.
-
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
    - reflexivity.
- simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem repeat_plus: forall c1 c2 n : nat,
repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Proof.
    intros c1 c2 n.
    induction c1 as [| c1' IHcl'].
    - simpl. reflexivity.
    - simpl.
    rewrite <- IHcl'.
    reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => rev t ++ [h]
    end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length_S : forall l n,
length (l ++ [n]) = S (length l).
Proof.
    intros l n. induction l as [| m l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite IHl'.
    reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
length (rev l) = length l.
Proof.
    intros l. induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> app_length_S.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
    intros l1 l2. induction l1 as [| n l1' IHl1'].
    - reflexivity.
- simpl. rewrite -> IHl1'. reflexivity. Qed.

Search rev.

Search (_ + _ = _ + _) inside induction.

Search (?x + ?y = ?y + ?x).

Theorem app_nil_r : forall l : natlist,
l ++ [] = l.
Proof.
    intros l.
    induction l as [| n l' IHl'].
    reflexivity.
    simpl. rewrite -> IHl'.
reflexivity. Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros l1 l2.
    induction l1 as [| n l1' IHl1'].
    simpl. rewrite -> app_nil_r. reflexivity.
    simpl. rewrite -> IHl1'. rewrite app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
rev (rev l) = l.
Proof.
    intros l.
    induction l as [| n l' IHl'].
    reflexivity.
    simpl. rewrite -> rev_app_distr.
    simpl. rewrite -> IHl'.
    reflexivity.
Qed. 

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
    intros l1 l2 l3 l4.
    rewrite -> app_assoc.
    rewrite -> app_assoc.
    reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
    intros l1 l2.
    induction l1 as [| n l' IHl'].
    reflexivity.
    simpl.
    rewrite -> IHl'.
    destruct n.
    - reflexivity.
    - simpl.
    reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
match l1, l2 with
| nil, nil => true
| _, nil => false
| nil, _ => false
| x :: xs, y :: ys => if x =? y then eqblist xs ys else false
end.

Example test_eqblist1 :
(eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 :
eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
true = eqblist l l.
Proof.
    intros l.
    induction l as [| n l' IHl'].
    reflexivity.
    simpl. rewrite -> eqb_refl.
    rewrite IHl'.
    reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
1 <=? (count 1 (1 :: s)) = true.
Proof.
    intros s.
simpl. reflexivity. Qed.

Theorem leb_n_Sn : forall n,
n <=? (S n) = true.
Proof.
    intros n. induction n as [| n' IHn'].
    - simpl. reflexivity.
- simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_one_does_not_increase_count :
forall (s : bag), (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
    intros s. induction s as [| n' IHn'].
    simpl. reflexivity.
    simpl. destruct n'.
    simpl. rewrite leb_n_Sn. reflexivity.
    simpl. rewrite -> IHIHn'.
    reflexivity.
Qed.

Theorem count_sum_equal :
forall (s1 : bag) (s2 : bag) (a : nat),
(count a s1) + (count a s2) = (count a (sum s1 s2)).
Proof.
    intros s1 s2 a.
    unfold sum.
    revert s2.
    induction s1 as [| x xs IH].
    intros s2.
    - simpl. reflexivity.
    - destruct s2 as [| y ys].
    simpl. rewrite add_0_r_firsttry.
    reflexivity.
    simpl.
    destruct (x =? a) eqn:Ex.
    destruct (y =? a) eqn:Ey.
    simpl. rewrite <- plus_n_Sm.
    rewrite IH. reflexivity.
    simpl. 
    rewrite IH. reflexivity.
    destruct (y =? a) eqn:Ey.
    rewrite <- plus_n_Sm.
    rewrite IH.
    reflexivity.
    rewrite IH.
    reflexivity.
Qed.

Theorem involution_injective : forall (f : nat -> nat),
(forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
    intros f n'.
    intros n1 n2 H.
    rewrite -> n'.
    rewrite <- H.
    rewrite <- n'.
    reflexivity.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist),
rev l1 = rev l2 -> l1 = l2.
Proof.
    intros l1 l2.
    intros H.
    rewrite <- rev_involutive.
    rewrite <- H.
    rewrite -> rev_involutive.
    reflexivity.
Qed.

Inductive natoption : Type :=
    | Some (n : nat)
    | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
match l with
| nil => None
| a :: l' => match n with
            | O => Some a
            | S n' => nth_error l' n'
            end 
end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
match o with 
| Some n' => n'
| None => d
end.

Definition hd_error (l : natlist) : natoption :=
match l with
| nil => None
| x :: xs => Some x
end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
hd default l = option_elim default (hd_error l).
Proof.
    intros l default.
    induction l as [| n l' IHl'].
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

End NatList.

Inductive id : Type :=
| Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
    match x1, x2 with
    | Id n1, Id n2 => n1 =? n2
    end.

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
    intros x.
    destruct x.
    simpl. rewrite eqb_refl. reflexivity.
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
| empty 
| record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map) (x : id)
(value : nat) : partial_map :=
record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
match d with
| empty => None
| record y v d' => if eqb_id x y then Some v else find x d'
end.

Theorem update_eq :
forall (d : partial_map) (x : id) (v : nat),
find x (update d x v) = Some v.
Proof.
    intros d x v.
    simpl. rewrite -> eqb_id_refl.
    reflexivity.
Qed.

Theorem update_neq :
forall (d : partial_map) (x y : id) (o : nat),
eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
    intros d x y o.
    intros H.
    simpl.
    rewrite -> H.
    reflexivity.
Qed.

End PartialMap.