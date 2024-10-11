Require Import Coq.Lists.List.

Require Import Algebra.

Require Gift.Spec.
Require Gift.Bitslice.

Definition uvconsts_to_bitslice {A}
 (uvconsts0: Cols.T (Rows.T A) * Cols.T (Rows.T A) * Cols.T (Rows.T A))
 (uvconsts1: Cols.T (Rows.T A) * Cols.T (Rows.T A) * Cols.T (Rows.T A)):
  Bitslice.reg32 A *
    Bitslice.reg32 A *
    Bitslice.reg32 A :=
  let '(x0, y0, z0) := uvconsts0 in
  let '(x1, y1, z1) := uvconsts1 in
  let x := Double.Build_T x0 x1 in
  let y := Double.Build_T y0 y1 in
  let z := Double.Build_T z0 z1 in
  (reindex (G := fun X => Cols.T (Rows.T X)) x,
    reindex (G := fun X => Cols.T (Rows.T X)) y,
    reindex (G := fun X => Cols.T (Rows.T X)) z).

Definition R_uvconsts
  (uvconsts0: Cols.T (Rows.T bool) * Cols.T (Rows.T bool) * Cols.T (Rows.T bool))
  (uvconsts1: Cols.T (Rows.T bool) * Cols.T (Rows.T bool) * Cols.T (Rows.T bool))
  (uvconsts: Bitslice.reg32 bool *
                Bitslice.reg32 bool *
                Bitslice.reg32 bool): Prop :=
  uvconsts_to_bitslice uvconsts0 uvconsts1 = uvconsts.

Definition to_bitslice {A} (s0: Spec.cube A)(s1: Spec.cube A): Bitslice.cube2 A :=
  reindex (F := Double.T)
    (Double.Build_T
       (reindex (G := Slice4.T) s0)
       (reindex (G := Slice4.T) s1)).

(*
Definition from_bitslice {A} (s: Bitslice.cube2 A): GiftSpec.cube A * GiftSpec.cube A :=
  let s := reindex (G := Double.T) s in
  (reindex (F := Slice4.T) s.(Double.fst),
    reindex (F := Slice4.T) s.(Double.snd)).
*)

(*
Proposition to_bitslice_inv: forall {A} s0 s1,
    from_bitslice (A := A) (to_bitslice s0 s1) = (s0, s1).
Admitted.

Proposition from_bitslice_inv: forall {A} s,
    let '(s0, s1) := from_bitslice (A := A) s in
    to_bitslice s0 s1 = s.
Admitted.
*)

Definition R {A} (s0: Spec.cube A)(s1: Spec.cube A)(s: Bitslice.cube2 A): Prop :=
  to_bitslice s0 s1 = s.

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

Proposition correct_subcells:
  forall s0 s1 s,
    R s0 s1 s ->
    R (Spec.subcells s0)
      (Spec.subcells s1)
      (Bitslice.subcells s).
Proof.
  intros s0 s1 s <-; reflexivity.
Qed.

Proposition correct_permbits:
  forall s0 s1 s,
    R s0 s1 s ->
    R (Spec.permbits s0)
      (Spec.permbits s1)
      (Bitslice.permbits s).
Proof.
  intros s0 s1 s <-; reflexivity.
Qed.

Proposition correct_add_round_key:
  forall uvconst0 uvconst1 uvconst,
    R_uvconsts uvconst0 uvconst1 uvconst ->
    forall s0 s1 s,
      R s0 s1 s ->
  R (let '(us0, vs0, consts0) := uvconst0 in
     Spec.add_round_key us0 vs0 consts0 s0)
    (let '(us1, vs1, consts1) := uvconst1 in
     Spec.add_round_key us1 vs1 consts1 s1)
    (let '(us, vs, consts) := uvconst in
     Bitslice.add_round_key us vs consts s).
Proof.
  intros [[us0 vs0] consts0]
         [[us1 vs1] consts1]
         uvconst <- s0 s1 s <-;
         reflexivity.
Qed.

Proposition correct_round:
  forall uvconst0 uvconst1 uvconst,
    R_uvconsts uvconst0 uvconst1 uvconst ->
    forall s0 s1 s,
      R s0 s1 s ->
  R (Spec.round s0 uvconst0)
    (Spec.round s1 uvconst1)
    (Bitslice.round Bitslice.permbits s
       uvconst).
Proof.
  intros uvconst0 uvconst1 uvconst HR_uvconst s0 s1 s HR.
  apply correct_add_round_key; auto.
  apply correct_permbits.
  apply correct_subcells; auto.
Qed.

Proposition correct_gift:
  forall uvconsts0 uvconsts1 uvconsts,
    Forall3 R_uvconsts uvconsts0 uvconsts1 uvconsts ->
    forall s0 s1 s,
      R s0 s1 s ->
      R (Spec.gift uvconsts0 s0)
        (Spec.gift uvconsts1 s1)
        (Bitslice.gift uvconsts s).
Proof.
  intros uvconsts0 uvconsts1 uvconsts HR_uvconsts.
  induction HR_uvconsts as [|uvconsts0 uvconsts1 uvconsts uvconst0 uvconst1 uvconst HR_uvconst HR_uvconsts IH]; auto.
  intros s0 s1 s HR.
  eapply IH.
  eapply correct_round; auto.
Qed.

Theorem correct_bitsliced_gift:
  forall uvconsts s0 s1,
    let uvconsts0 := List.map fst uvconsts in
    let uvconsts1 := List.map snd uvconsts in
    to_bitslice
      (Spec.gift uvconsts0 s0)
      (Spec.gift uvconsts1 s1)
    = Bitslice.gift
        (List.map (fun '(x, y) => uvconsts_to_bitslice x y) uvconsts)
        (to_bitslice s0 s1).
Proof.
  intros.
  eapply correct_gift; try reflexivity.
  induction uvconsts as [|[x y] xs IH]; constructor; simpl; [ reflexivity | apply IH].
Qed.

Print Assumptions correct_bitsliced_gift.
