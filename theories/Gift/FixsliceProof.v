Require Import Coq.Lists.List.
Import ListNotations.

Require Import Algebra.

Require Import Gift.Base.
Require Gift.Bitslice.
Require Gift.Fixslice.

Definition R_mod0 {A}
  (s: Cols.T (Rows.T A))
  (f_s: Cols.T (Rows.T A)): Prop :=
  s = f_s.
(* = sigma^{4} s *)

Definition R_mod1 {A}
  (s: Cols.T (Rows.T A))
  (f_s: Cols.T (Rows.T A)): Prop :=
  s = sigma f_s.

Definition R_mod2 {A}
  (s: Cols.T (Rows.T A))
  (f_s: Cols.T (Rows.T A)): Prop :=
  s = sigma (sigma f_s).

Definition R_mod3 {A}
  (s: Cols.T (Rows.T A))
  (f_s: Cols.T (Rows.T A)): Prop :=
  s = sigma (sigma (sigma f_s)).


Definition R_uvconsts_mod0 {A}
  (uvconst: (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)))
  (f_uvconst: (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)) * (Cols.T (Rows.T A))): Prop :=
  let '(us, vs, consts) := uvconst in
  let '(f_us, f_vs, f_consts) := f_uvconst in
  R_mod1 us f_us /\
    R_mod1 vs f_vs /\
    R_mod1 consts f_consts.

Definition R_uvconsts_mod1 {A}
  (uvconst: (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)))
  (f_uvconst: (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)) * (Cols.T (Rows.T A))): Prop :=
  let '(us, vs, consts) := uvconst in
  let '(f_us, f_vs, f_consts) := f_uvconst in
  R_mod2 us f_us /\
    R_mod2 vs f_vs /\
    R_mod2 consts f_consts.

Definition R_uvconsts_mod2 {A}
  (uvconst: (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)))
  (f_uvconst: (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)) * (Cols.T (Rows.T A))): Prop :=
  let '(us, vs, consts) := uvconst in
  let '(f_us, f_vs, f_consts) := f_uvconst in
  R_mod3 us f_us /\
    R_mod3 vs f_vs /\
    R_mod3 consts f_consts.

Definition R_uvconsts_mod3 {A}
  (uvconst: (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)))
  (f_uvconst: (Cols.T (Rows.T A)) * (Cols.T (Rows.T A)) * (Cols.T (Rows.T A))): Prop :=
  let '(us, vs, consts) := uvconst in
  let '(f_us, f_vs, f_consts) := f_uvconst in
  R_mod0 us f_us /\
    R_mod0 vs f_vs /\
    R_mod0 consts f_consts.

Inductive R_uvconsts:
  list (Bitslice.reg32 bool *
          Bitslice.reg32 bool *
          Bitslice.reg32 bool) ->
  list
    (Fixslice.reg32 bool *
       Fixslice.reg32 bool *
       Fixslice.reg32 bool *
       (Fixslice.reg32 bool *
          Fixslice.reg32 bool *
          Fixslice.reg32 bool) *
       (Fixslice.reg32 bool *
          Fixslice.reg32 bool *
          Fixslice.reg32 bool) *
       (Fixslice.reg32 bool *
          Fixslice.reg32 bool *
          Fixslice.reg32 bool)) -> Prop :=
| R_nil: R_uvconsts [] []
| R_cons: forall uvconst_mod0 uvconst_mod1 uvconst_mod2 uvconst_mod3
                 f_uvconst_mod0 f_uvconst_mod1 f_uvconst_mod2 f_uvconst_mod3
                 xs f_xs,
    R_uvconsts_mod0 uvconst_mod0 f_uvconst_mod0 ->
    R_uvconsts_mod1 uvconst_mod1 f_uvconst_mod1 ->
    R_uvconsts_mod2 uvconst_mod2 f_uvconst_mod2 ->
    R_uvconsts_mod3 uvconst_mod3 f_uvconst_mod3 ->
    R_uvconsts xs f_xs ->
    R_uvconsts (uvconst_mod0 ::
                  uvconst_mod1 ::
                  uvconst_mod2 ::
                  uvconst_mod3 :: xs)
               ((f_uvconst_mod0,
                 f_uvconst_mod1,
                  f_uvconst_mod2,
                  f_uvconst_mod3) :: f_xs).

Proposition correct_add_round_key_mod0:
  forall us vs consts f_us f_vs f_consts,
    R_uvconsts_mod3
      (us, vs, consts)
      (f_us, f_vs, f_consts) ->
    forall s f_s,
      Slice4.Forall2 R_mod0 s f_s ->
      Slice4.Forall2 R_mod0
        (Bitslice.add_round_key us vs consts s)
        (Bitslice.add_round_key f_us f_vs f_consts f_s).
Proof.
  intros us vs consts ? ? ? [<- [<- <-]] [s0 s1 s2 s3] [fs0 fs1 fs2 fs3] [H0 H1 H2 H3]; simpl in *.
  rewrite <-H0, <-H1, <-H2, <-H3.
  repeat split.
Qed.

Proposition correct_add_round_key_mod1:
  forall us vs consts f_us f_vs f_consts,
    R_uvconsts_mod0
      (us, vs, consts)
      (f_us, f_vs, f_consts) ->
    forall s f_s,
      Slice4.Forall2 R_mod1 s f_s ->
      Slice4.Forall2 R_mod1
        (Bitslice.add_round_key us vs consts s)
        (Bitslice.add_round_key f_us f_vs f_consts f_s).
Proof.
  intros ? ? ? f_us f_vs f_consts [-> [-> ->]]
    [s0 s1 s2 s3]
    [fs0 fs1 fs2 fs3]
    [H0 H1 H2 H3]; simpl in *.
  rewrite H0, H1, H2, H3.
  repeat split.
Qed.

Proposition correct_add_round_key_mod2:
  forall us vs consts f_us f_vs f_consts,
    R_uvconsts_mod1
      (us, vs, consts)
      (f_us, f_vs, f_consts) ->
    forall s f_s,
      Slice4.Forall2 R_mod2 s f_s ->
      Slice4.Forall2 R_mod2
        (Bitslice.add_round_key us vs consts s)
        (Bitslice.add_round_key f_us f_vs f_consts f_s).
Proof.
  intros ? ? ? f_us f_vs f_consts [-> [-> ->]]
    [s0 s1 s2 s3]
    [fs0 fs1 fs2 fs3]
    [H0 H1 H2 H3]; simpl in *.
  rewrite H0, H1, H2, H3.
  repeat split.
Qed.

Proposition correct_add_round_key_mod3:
  forall us vs consts f_us f_vs f_consts,
    R_uvconsts_mod2
      (us, vs, consts)
      (f_us, f_vs, f_consts) ->
    forall s f_s,
      Slice4.Forall2 R_mod3 s f_s ->
      Slice4.Forall2 R_mod3
        (Bitslice.add_round_key us vs consts s)
        (Bitslice.add_round_key f_us f_vs f_consts f_s).
Proof.
  intros ? ? ? f_us f_vs f_consts [-> [-> ->]]
    [s0 s1 s2 s3]
    [fs0 fs1 fs2 fs3]
    [H0 H1 H2 H3]; simpl in *.
  rewrite H0, H1, H2, H3.
  repeat split.
Qed.

Proposition correct_permbits_mod0:
    forall s f_s,
      Slice4.Forall2 R_mod0 s f_s ->
      Slice4.Forall2 R_mod1
        (Bitslice.permbits s)
        (Fixslice.permbits_mod0 f_s).
Proof.
  intros
    [? ? ? ?]
    [f_s0 f_s1 f_s2 f_s3]
    [H0 H1 H2 H3];
    simpl in *.
  rewrite H0, H1, H2, H3.
  constructor; reflexivity.
Qed.

Proposition correct_permbits_mod1:
    forall s f_s,
      Slice4.Forall2 R_mod1 s f_s ->
      Slice4.Forall2 R_mod2
        (Bitslice.permbits s)
        (Fixslice.permbits_mod1 f_s).
Proof.
  intros
    [? ? ? ?]
    [f_s0 f_s1 f_s2 f_s3]
    [H0 H1 H2 H3];
    simpl in *.
  rewrite H0, H1, H2, H3.
  constructor;
    unfold R_mod2; simpl;
    rewrite inv_inv_sigma; auto.
Qed.

Proposition correct_permbits_mod2:
    forall s f_s,
      Slice4.Forall2 R_mod2 s f_s ->
      Slice4.Forall2 R_mod3
        (Bitslice.permbits s)
        (Fixslice.permbits_mod2 f_s).
Proof.
  intros
    [? ? ? ?]
    [f_s0 f_s1 f_s2 f_s3]
    [H0 H1 H2 H3];
    simpl in *.
  rewrite H0, H1, H2, H3.
  constructor;
    unfold R_mod3; simpl;
    rewrite !inv_inv_sigma; auto.
Qed.

Proposition correct_permbits_mod3:
    forall s f_s,
      Slice4.Forall2 R_mod3 s f_s ->
      Slice4.Forall2 R_mod0
        (Bitslice.permbits s)
        (Fixslice.permbits_mod3 f_s).
Proof.
  intros
    [? ? ? ?]
    [f_s0 f_s1 f_s2 f_s3]
    [H0 H1 H2 H3];
    simpl in *.
  rewrite H0, H1, H2, H3.
  constructor;
    unfold R_mod0; simpl;
    unfold inv_sigma; rewrite !idemp_sigma4; auto.
Qed.

Proposition correct_subcells_mod0:
    forall s f_s,
      Slice4.Forall2 R_mod0 s f_s ->
      Slice4.Forall2 R_mod0
        (Bitslice.subcells s)
        (Bitslice.subcells f_s).
Proof.
  intros
    [s0 s1 s2 s3]
    [f_s0 f_s1 f_s2 f_s3]
    [H0 H1 H2 H3]; simpl in *.
  rewrite <-H0, <-H1, <-H2, <-H3.
  repeat split.
Qed.

Proposition correct_subcells_mod1:
    forall s f_s,
      Slice4.Forall2 R_mod1 s f_s ->
      Slice4.Forall2 R_mod1
        (Bitslice.subcells s)
        (Bitslice.subcells f_s).
Proof.
  intros
    [s0 s1 s2 s3]
    [f_s0 f_s1 f_s2 f_s3]
    [H0 H1 H2 H3]; simpl in *.
  rewrite H0, H1, H2, H3.
  repeat split.
Qed.

Proposition correct_subcells_mod2:
    forall s f_s,
      Slice4.Forall2 R_mod2 s f_s ->
      Slice4.Forall2 R_mod2
        (Bitslice.subcells s)
        (Bitslice.subcells f_s).
Proof.
  intros
    [s0 s1 s2 s3]
    [f_s0 f_s1 f_s2 f_s3]
    [H0 H1 H2 H3]; simpl in *.
  rewrite H0, H1, H2, H3.
  repeat split.
Qed.

Proposition correct_subcells_mod3:
    forall s f_s,
      Slice4.Forall2 R_mod3 s f_s ->
      Slice4.Forall2 R_mod3
        (Bitslice.subcells s)
        (Bitslice.subcells f_s).
Proof.
  intros
    [s0 s1 s2 s3]
    [f_s0 f_s1 f_s2 f_s3]
    [H0 H1 H2 H3]; simpl in *.
  rewrite H0, H1, H2, H3.
  repeat split.
Qed.

Proposition correct_round_mod0:
  forall uvconst f_uvconst,
    R_uvconsts_mod0 uvconst f_uvconst ->
  forall s f_s,
    Slice4.Forall2 R_mod0 s f_s ->
    Slice4.Forall2 R_mod1
      (Bitslice.round Bitslice.permbits s uvconst)
      (Fixslice.round Fixslice.permbits_mod0 f_s f_uvconst).
Proof.
  intros [[us vs] consts] [[f_us f_vs] f_consts] HR_uvconsts s f_s HR.
  apply correct_add_round_key_mod1; auto.
  apply correct_permbits_mod0.
  apply correct_subcells_mod0.
  auto.
Qed.

Proposition correct_round_mod1:
  forall uvconst f_uvconst,
    R_uvconsts_mod1 uvconst f_uvconst ->
  forall s f_s,
    Slice4.Forall2 R_mod1 s f_s ->
    Slice4.Forall2 R_mod2
      (Bitslice.round Bitslice.permbits s uvconst)
      (Fixslice.round Fixslice.permbits_mod1 f_s f_uvconst).
Proof.
  intros [[us vs] consts] [[f_us f_vs] f_consts] HR_uvconsts s f_s HR.
  apply correct_add_round_key_mod2; auto.
  apply correct_permbits_mod1.
  apply correct_subcells_mod1.
  auto.
Qed.

Proposition correct_round_mod2:
  forall uvconst f_uvconst,
    R_uvconsts_mod2 uvconst f_uvconst ->
  forall s f_s,
    Slice4.Forall2 R_mod2 s f_s ->
    Slice4.Forall2 R_mod3
      (Bitslice.round Bitslice.permbits s uvconst)
      (Fixslice.round Fixslice.permbits_mod2 f_s f_uvconst).
Proof.
  intros [[us vs] consts] [[f_us f_vs] f_consts] HR_uvconsts s f_s HR.
  apply correct_add_round_key_mod3; auto.
  apply correct_permbits_mod2.
  apply correct_subcells_mod2.
  auto.
Qed.

Proposition correct_round_mod3:
  forall uvconst f_uvconst,
    R_uvconsts_mod3 uvconst f_uvconst ->
  forall s f_s,
    Slice4.Forall2 R_mod3 s f_s ->
    Slice4.Forall2 R_mod0
      (Bitslice.round Bitslice.permbits s uvconst)
      (Fixslice.round Fixslice.permbits_mod3 f_s f_uvconst).
Proof.
  intros [[us vs] consts] [[f_us f_vs] f_consts] HR_uvconsts s f_s HR.
  apply correct_add_round_key_mod0; auto.
  apply correct_permbits_mod3.
  apply correct_subcells_mod3.
  auto.
Qed.

Proposition correct_gift:
  forall uvconsts f_uvconsts,
    R_uvconsts uvconsts f_uvconsts ->
    forall s f_s,
      Slice4.Forall2 R_mod0 s f_s ->
      Slice4.Forall2 R_mod0
        (Bitslice.gift uvconsts s)
        (Fixslice.gift f_uvconsts f_s).
Proof.
  intros uvconsts f_uvconsts HR_uvconsts.
  induction HR_uvconsts
    as [|uvconst_mod0 uvconst_mod1 uvconst_mod2 uvconst_mod3
         f_uvconst_mod0 f_uvconst_mod1 f_uvconst_mod2 f_uvconst_mod3
         xs f_xs HR_mod0 HR_mod1 HR_mod2 HR_mod3 HR_uvconsts IH]; auto.
  intros s f_s HR; simpl.
  apply IH.
  apply correct_round_mod3; auto.
  apply correct_round_mod2; auto.
  apply correct_round_mod1; auto.
  apply correct_round_mod0; auto.
Qed.

Proposition eta_Slice4R_mod0 {A}:
  forall (s: Slice4.T (Cols.T (Rows.T A))) s',
    Slice4.Forall2 R_mod0 s s' -> s = s'.
Proof.
  intros
    [s0 s1 s2 s3]
    [s0' s1' s2' s3']
    [H0 H1 H2 H3].
  simpl in *.
  rewrite H0, H1, H2, H3; auto.
Qed.

Fixpoint flatten_uvconsts {A} l :=
  match l with
  | [] => []
  | ((u_mod0, v_mod0, const_mod0),
      (u_mod1, v_mod1, const_mod1),
      (u_mod2, v_mod2, const_mod2),
      (u_mod3, v_mod3, const_mod3)) :: l =>
      (sigma (A := A) u_mod0,
        sigma (A := A) v_mod0,
        sigma (A := A) const_mod0) ::
        (sigma (sigma u_mod1),
          sigma (sigma v_mod1),
          sigma (sigma const_mod1)) ::
        (sigma (sigma (sigma u_mod2)),
          sigma (sigma (sigma v_mod2)),
          sigma (sigma (sigma const_mod2))) ::
        (u_mod3, v_mod3, const_mod3) ::
        flatten_uvconsts l
  end.

Lemma R_uvconsts_flatten_uvconsts:
  forall l, R_uvconsts (flatten_uvconsts l) l.
Proof.
  intro l; induction l; try constructor.
  destruct a as [[[[[u0 v0] const0]
                   [[u1 v1] const1]]
                   [[u2 v2] const2]]
                   [[u3 v3] const3]].
  constructor; auto.
  - repeat split.
  - repeat split;
    unfold R_mod2;
    rewrite !inv_inv_sigma; auto.
  - repeat split;
    unfold R_mod3;
    rewrite !inv_inv_sigma; auto.
  - repeat split;
    unfold R_mod0;
    rewrite !inv_inv_sigma; auto.
Qed.

Theorem correct_fixsliced_gift:
  forall f_uvconsts s,
    let uvconsts := flatten_uvconsts f_uvconsts in
    Bitslice.gift uvconsts s
    = Fixslice.gift f_uvconsts s.
Proof.
  intros f_uvconsts s.
  apply eta_Slice4R_mod0.
  apply correct_gift; repeat constructor.
  apply R_uvconsts_flatten_uvconsts.
Qed.

Print Assumptions correct_fixsliced_gift.
