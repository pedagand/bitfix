Require Import Coq.Lists.List.

Require Import Algebra.

Require Cols.
Require Rows.
Require Slice8.
Require Double.

Require Import Skinny.Base.
Require Skinny.Spec.
Require Skinny.Bitslice.

(* =to_bitslice= *)
Definition to_bitslice {A} (s0: Spec.cube A)(s1: Spec.cube A): Bitslice.cube2 A :=
  reindex (F := Double.T)
    (init (fun i =>
             match i with
             | Double.Fst => reindex (G := Slice8.T) s0
             | Double.Snd => reindex (G := Slice8.T) s1
             end)).
(* =end= *)

(* =invariant_bitslice= *)
Definition R {A} (s0: Spec.cube A)(s1: Spec.cube A)(s: Bitslice.cube2 A): Prop :=
  to_bitslice s0 s1 = s.
(* =end= *)

Proposition correct_subcells:
  forall s0 s1 s,
    R s0 s1 s ->
    R (Spec.subcells s0)
      (Spec.subcells s1)
      (Bitslice.subcells s).
Proof.
  intros s0 s1 s <-; reflexivity.
Qed.

Proposition correct_shiftrows:
  forall s0 s1 s,
    R s0 s1 s ->
    R (Spec.shiftrows s0)
      (Spec.shiftrows s1)
      (Bitslice.shiftrows s).
Proof.
  intros s0 s1 s <-; reflexivity.
Qed.

Proposition correct_mixcolumns:
  forall s0 s1 s,
    R s0 s1 s ->
    R (Spec.mixcolumns s0)
      (Spec.mixcolumns s1)
      (Bitslice.mixcolumns s).
Proof.
  intros s0 s1 s <-; reflexivity.
Qed.

Proposition correct_add_round_key:
  forall constkey0 constkey1 constkey,
    R constkey0 constkey1 constkey ->
    forall s0 s1 s,
      R s0 s1 s ->
      R (Spec.add_round_key constkey0 s0)
        (Spec.add_round_key constkey1 s1)
        (Bitslice.add_round_key constkey s).
Proof.
  intros constkey0 constkey1 constkey <-
         s0 s1 s <-;
         reflexivity.
Qed.


Proposition correct_round:
  forall constkey0 constkey1 constkey,
    R constkey0 constkey1 constkey ->
    forall s0 s1 s,
      R s0 s1 s ->
  R (Spec.round s0 constkey0)
    (Spec.round s1 constkey1)
    (Bitslice.round Bitslice.permbits s constkey).
Proof.
  intros constkey0 constkey1 constkey HR_constkey
    s0 s1 s HR.
  apply correct_mixcolumns.
  apply correct_shiftrows.
  apply correct_add_round_key; auto.
  apply correct_subcells; auto.
Qed.

Inductive Forall3 {A B C} (R : A -> B -> C -> Prop)
  : list A -> list B -> list C -> Prop :=
    Forall3_nil : Forall3 R nil nil nil
  | Forall3_cons : forall (x : A)
                     (y : B)(z : C) (l : list A)
                     (l' : list B)(l'' : list C),
                   R x y z ->
                   Forall3 R l l' l'' ->
                   Forall3 R
                     (x :: l) (y :: l') (z :: l'').

Proposition correct_skinny:
  forall constkeys0 constkeys1 constkeys,
    Forall3 R constkeys0 constkeys1 constkeys ->
    forall s0 s1 s,
      R s0 s1 s ->
      R (Spec.skinny constkeys0 s0)
        (Spec.skinny constkeys1 s1)
        (Bitslice.skinny constkeys s).
Proof.
  intros constkeys0 constkeys1 constkeys HR_constkeys.
  induction HR_constkeys as [|constkeys0 constkeys1 constkeys constkey0 constkey1 constkey HR_constkey HR_constkeys IH]; auto.
  intros s0 s1 s HR.
  apply IH.
  apply correct_round; assumption.
Qed.


Theorem correct_bitsliced_skinny:
  forall constkeys s0 s1,
(* =theorem= *)
    let constkeys0 := List.map fst constkeys in
    let constkeys1 := List.map snd constkeys in
    to_bitslice
      (Spec.skinny constkeys0 s0)
      (Spec.skinny constkeys1 s1)
    = Bitslice.skinny
        (List.map (fun '(x, y) => to_bitslice x y) constkeys)
        (to_bitslice s0 s1).
(* =end= *)
Proof.
  intros.
  eapply correct_skinny; try reflexivity.
  induction constkeys as [|[x y] xs IH]; constructor; simpl; [ reflexivity | apply IH].
Qed.

Print Assumptions correct_bitsliced_skinny.

