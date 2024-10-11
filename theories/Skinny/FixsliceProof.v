Require Import Coq.Lists.List.
Import ListNotations.

Require Import Algebra.

Require Import Skinny.Base.
Require Skinny.Bitslice.
Require Skinny.Fixslice.

Lemma inv_inv_phi {A}: forall rs: Rows.T (Cols.T A),
    inv_phi_ (phi_ rs) = rs.
Proof.
  intros [[? ? ? ?]
          [? ? ? ?]
          [? ? ? ?]
          [? ? ? ?]];
  reflexivity.
Qed.

Lemma inv_phi_phi {A}: forall rs: Rows.T (Cols.T A),
    phi_ (inv_phi_ rs) = rs.
Proof.
  intros [[? ? ? ?]
          [? ? ? ?]
          [? ? ? ?]
          [? ? ? ?]];
  reflexivity.
Qed.

Lemma equiv_phi_explicit_ {A}: forall rs: Rows.T (Cols.T A),
    phi_ rs = phi_explicit_ rs.
Proof.
  intros rs; reflexivity.
Qed.

Import Fixslice.

Lemma tau_phi4_id {A}:
  forall (rs: Rows.T (Cols.T A)), 
(* =tau_phi4= *)
    tau_ (iter 4 phi_ rs) = rs.
(* =end= *)
Proof. reflexivity. Qed.

Proposition mixcolumns_spec: forall {B} `(Boolean B) (rs: Rows.T (Cols.T B)),
    mixcolumns_spec_ rs = mixcolumns_ rs.
Proof. intros; reflexivity. Qed.

Proposition split_mixcolumns_shiftrows:
  (* =split_phi_sigma= *)
  forall {B} `(Boolean B) (rs: Rows.T (Cols.T B)),
    mixcolumns_ (app shiftrows_ rs) = phi_ (sigma_ rs).
(* =end= *)
Proof. intros; reflexivity. Qed.


Definition R_mod0 {A}
  (s: Rows.T (Cols.T A))
  (f_s: Rows.T (Cols.T A)): Prop :=
  s = f_s.
(* = tau (phi_^{4} s) *)

Definition R_mod1 {A}
  (s: Rows.T (Cols.T A))
  (f_s: Rows.T (Cols.T A)): Prop :=
  s = phi_ f_s.

Definition R_mod2 {A}
  (s: Rows.T (Cols.T A))
  (f_s: Rows.T (Cols.T A)): Prop :=
  s = phi_ (phi_ f_s).

Definition R_mod3 {A}
  (s: Rows.T (Cols.T A))
  (f_s: Rows.T (Cols.T A)): Prop :=
  s = phi_ (phi_ (phi_ f_s)).

Definition R_mod4 {A}
  (s: Rows.T (Cols.T A))
  (f_s: Rows.T (Cols.T A)): Prop :=
  s = phi_ (phi_ (phi_ (phi_ f_s))).

Inductive R_constkeys:
  list Bitslice.state ->
  list (Bitslice.state * Bitslice.state * Bitslice.state * Bitslice.state) -> Prop :=
| R_nil: R_constkeys [] []
| R_cons: forall constkey_mod0 constkey_mod1 constkey_mod2 constkey_mod3
                 f_constkey_mod0 f_constkey_mod1 f_constkey_mod2 f_constkey_mod3
                 xs f_xs,
    Slice8.Forall2 R_mod0 constkey_mod0 f_constkey_mod0 ->
    Slice8.Forall2 R_mod1 constkey_mod1 f_constkey_mod1 ->
    Slice8.Forall2 R_mod2 constkey_mod2 f_constkey_mod2 ->
    Slice8.Forall2 R_mod3 constkey_mod3 f_constkey_mod3 ->
    R_constkeys xs f_xs ->
    R_constkeys (constkey_mod0 ::
                  constkey_mod1 ::
                  constkey_mod2 ::
                  constkey_mod3 :: xs)
               ((f_constkey_mod0,
                 f_constkey_mod1,
                  f_constkey_mod2,
                  f_constkey_mod3) :: f_xs).

Lemma rewrite_R_mod0 {A}: forall (constkey: Slice8.T (Rows.T (Cols.T A))) f_constkey,
    Slice8.Forall2 R_mod0 constkey f_constkey -> constkey = f_constkey.
Proof.
  intros [c0 c1 c2 c3 c4 c5 c6 c7] 
           [f0 f1 f2 f3 f4 f5 f6 f7]
           [H0 H1 H2 H3 H4 H5 H6 H7];
  simpl in *;
  congruence.
Qed.

Lemma rewrite_R_mod1 {A}: forall (constkey: Slice8.T (Rows.T (Cols.T A))) f_constkey,
    Slice8.Forall2 R_mod1 constkey f_constkey -> constkey = map phi_ f_constkey.
Proof.
  intros [c0 c1 c2 c3 c4 c5 c6 c7] 
           [f0 f1 f2 f3 f4 f5 f6 f7]
           [H0 H1 H2 H3 H4 H5 H6 H7];
  simpl in *;
  congruence.
Qed.

Lemma rewrite_R_mod2 {A}: forall (constkey: Slice8.T (Rows.T (Cols.T A))) f_constkey,
    Slice8.Forall2 R_mod2 constkey f_constkey -> constkey = map phi_ (map phi_ f_constkey).
Proof.
  intros [c0 c1 c2 c3 c4 c5 c6 c7] 
           [f0 f1 f2 f3 f4 f5 f6 f7]
           [H0 H1 H2 H3 H4 H5 H6 H7];
  simpl in *;
  congruence.
Qed.


Lemma rewrite_R_mod3 {A}: forall (constkey: Slice8.T (Rows.T (Cols.T A))) f_constkey,
    Slice8.Forall2 R_mod3 constkey f_constkey -> constkey = map phi_ (map phi_ (map phi_ f_constkey)).
Proof.
  intros [c0 c1 c2 c3 c4 c5 c6 c7] 
           [f0 f1 f2 f3 f4 f5 f6 f7]
           [H0 H1 H2 H3 H4 H5 H6 H7];
  simpl in *;
  congruence.
Qed.

Lemma rewrite_R_mod4 {A}: forall (constkey: Slice8.T (Rows.T (Cols.T A))) f_constkey,
    Slice8.Forall2 R_mod4 constkey f_constkey -> constkey = map phi_ (map phi_ (map phi_ (map phi_ f_constkey))).
Proof.
  intros [c0 c1 c2 c3 c4 c5 c6 c7] 
           [f0 f1 f2 f3 f4 f5 f6 f7]
           [H0 H1 H2 H3 H4 H5 H6 H7];
  simpl in *;
  congruence.
Qed.

(*
Definition eta_Rows {A}: forall (x y: Rows.T A),
    x.(Rows.r0) = y.(Rows.r0) ->
    x.(Rows.r1) = y.(Rows.r1) ->
    x.(Rows.r2) = y.(Rows.r2) ->
    x.(Rows.r3) = y.(Rows.r3) ->
    x = y.
Admitted.

Definition eta_Cols {A}: forall (x y: Cols.T A),
    x.(Cols.c0) = y.(Cols.c0) ->
    x.(Cols.c1) = y.(Cols.c1) ->
    x.(Cols.c2) = y.(Cols.c2) ->
    x.(Cols.c3) = y.(Cols.c3) ->
    x = y.
Admitted.


Definition eta_Double {A}: forall (x y: Double.T A),
    x.(Double.fst) = y.(Double.fst) ->
    x.(Double.snd) = y.(Double.snd) ->
    x = y.
Admitted.

Definition eta_Slice8 {A}: forall (x y: Slice8.T A),
    x.(Slice8.s0) = y.(Slice8.s0) ->
    x.(Slice8.s1) = y.(Slice8.s1) ->
    x.(Slice8.s2) = y.(Slice8.s2) ->
    x.(Slice8.s3) = y.(Slice8.s3) ->
    x.(Slice8.s4) = y.(Slice8.s4) ->
    x.(Slice8.s5) = y.(Slice8.s5) ->
    x.(Slice8.s6) = y.(Slice8.s6) ->
    x.(Slice8.s7) = y.(Slice8.s7) ->
    x = y.
Admitted.
*)

Proposition commute_phi_add_round_key:
  (* =comm_phi_add_round_key= *)
  forall B `(Boolean B) (s constkey: Rows.T (Cols.T B)),
    add_round_key_ (phi_ s) constkey
    = phi_ (add_round_key_ s (inv_phi_ constkey)).
  (* =end= *)
Proof.
  intros ? ? s constkey;
  vm_compute; reflexivity.
Qed.

Proposition correct_add_round_key_mod0:
  forall constkey f_constkey,
    Slice8.Forall2 R_mod0 constkey f_constkey ->
    forall s f_s,
      Slice8.Forall2 R_mod0 s f_s ->
      Slice8.Forall2 R_mod0
        (Bitslice.add_round_key constkey s)
        (Bitslice.add_round_key f_constkey f_s).
Proof.
  intros constkey f_constkey
    R_constkey
    [s0 s1 s2 s3 s4 s5 s6 s7]
    [fs0 fs1 fs2 fs3 fs4 fs5 fs6 fs7]
    [H0 H1 H2 H3 H4 H5 H6 H7].
  rewrite (rewrite_R_mod0 _ _ R_constkey).
  rewrite H0, H1, H2, H3, H4, H5, H6, H7.
  constructor; vm_compute; reflexivity.
Qed.


Proposition correct_add_round_key_mod1:
  forall constkey f_constkey,
    Slice8.Forall2 R_mod1 constkey f_constkey ->
    forall s f_s,
      Slice8.Forall2 R_mod1 s f_s ->
      Slice8.Forall2 R_mod1
        (Bitslice.add_round_key constkey s)
        (Bitslice.add_round_key f_constkey f_s).
Proof.
  intros constkey f_constkey
    R_constkey
    s f_s R_s.
  rewrite (rewrite_R_mod1 _ _ R_constkey).
  rewrite (rewrite_R_mod1 _ _ R_s).
  constructor; vm_compute; reflexivity.
Qed.

Proposition correct_add_round_key_mod2:
  forall constkey f_constkey,
    Slice8.Forall2 R_mod2 constkey f_constkey ->
    forall s f_s,
      Slice8.Forall2 R_mod2 s f_s ->
      Slice8.Forall2 R_mod2
        (Bitslice.add_round_key constkey s)
        (Bitslice.add_round_key f_constkey f_s).
Proof.
  intros constkey f_constkey R_constkey
    s f_s R_s.
  rewrite (rewrite_R_mod2 _ _ R_constkey).
  rewrite (rewrite_R_mod2 _ _ R_s).
  constructor; vm_compute; reflexivity.
Qed.

Proposition correct_add_round_key_mod3:
  forall constkey f_constkey,
    Slice8.Forall2 R_mod3 constkey f_constkey ->
    forall s f_s,
      Slice8.Forall2 R_mod3 s f_s ->
      Slice8.Forall2 R_mod3
        (Bitslice.add_round_key constkey s)
        (Bitslice.add_round_key f_constkey f_s).
Proof.
  intros constkey f_constkey R_constkey
    s f_s R_s.
  rewrite (rewrite_R_mod3 _ _ R_constkey).
  rewrite (rewrite_R_mod3 _ _ R_s).
  constructor; vm_compute; reflexivity.
Qed.

Proposition absorb_phi_sigma:
  (* =absorb_phi_sigma= *)
  forall B `(Boolean B) n (s: Rows.T (Cols.T B)),
    mixcolumns_ (app shiftrows_ (iter n phi_ s))
    = iter (1 + n) phi_ (mixcolumns_mod n s).
  (* =end= *)
Proof.
  intros ? ? n.
  intro s.
  rewrite split_mixcolumns_shiftrows.
  revert s.
  unfold mixcolumns_mod.
  induction n; try reflexivity.
  intro s. simpl; rewrite IHn.
  simpl.
  rewrite iter_S with (f := inv_phi_), inv_phi_phi.
  reflexivity.
Qed.

Proposition absorb_phi_sigma1:
  (* =absorb_phi_sigma1= *)
  forall B `(Boolean B) (s: Rows.T (Cols.T B)),
    mixcolumns_ (app shiftrows_ (phi_ s))
    = phi_ (phi_ (inv_phi_ (sigma_ (phi_ s)))).
  (* =end= *)
Proof.
  intros.
  eapply absorb_phi_sigma with (n := 1).
Qed.


Proposition correct_shiftrows_mixcolumns_mod0:
    forall s f_s,
      Slice8.Forall2 R_mod0 s f_s ->
      Slice8.Forall2 R_mod1
        (Bitslice.permbits s)
        (map Fixslice.mixcolumns_mod0 f_s).
Proof.
  intros
    [? ? ? ? ? ? ? ?]
    [f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7]
    [H0 H1 H2 H3 H4 H5 H6 H7];
    simpl in *.
  rewrite H0, H1, H2, H3, H4, H5, H6, H7.
  constructor; reflexivity.
Qed.

Proposition correct_shiftrows_mixcolumns_mod1:
    forall s f_s,
      Slice8.Forall2 R_mod1 s f_s ->
      Slice8.Forall2 R_mod2
        (Bitslice.permbits s)
        (map Fixslice.mixcolumns_mod1 f_s).
Proof.
  intros
    [? ? ? ? ? ? ? ?]
    [f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7]
    [H0 H1 H2 H3 H4 H5 H6 H7];
    simpl in *.
  rewrite H0, H1, H2, H3, H4, H5, H6, H7.
  constructor; reflexivity.
Qed.

Proposition correct_shiftrows_mixcolumns_mod2:
    forall s f_s,
      Slice8.Forall2 R_mod2 s f_s ->
      Slice8.Forall2 R_mod3
        (Bitslice.permbits s)
        (map Fixslice.mixcolumns_mod2 f_s).
Proof.
  intros
    [? ? ? ? ? ? ? ?]
    [f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7]
    [H0 H1 H2 H3 H4 H5 H6 H7];
    simpl in *.
  rewrite H0, H1, H2, H3, H4, H5, H6, H7.
  constructor; reflexivity.
Qed.

Proposition correct_shiftrows_mixcolumns_mod3:
    forall s f_s,
      Slice8.Forall2 R_mod3 s f_s ->
      Slice8.Forall2 R_mod4
        (Bitslice.permbits s)
        (map Fixslice.mixcolumns_mod3 f_s).
Proof.
  intros
    [? ? ? ? ? ? ? ?]
    [f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7]
    [H0 H1 H2 H3 H4 H5 H6 H7];
    simpl in *.
  rewrite H0, H1, H2, H3, H4, H5, H6, H7.
  constructor; reflexivity.
Qed.

Proposition correct_tau:
    forall s f_s,
      Slice8.Forall2 R_mod4 s f_s ->
      Slice8.Forall2 R_mod0
        s
        (Fixslice.tau f_s).
  intros s f_s R_s.
  rewrite (rewrite_R_mod4 _ _ R_s).
  constructor; vm_compute; reflexivity.
Qed.

Proposition commute_phi_subcells:
  (* =comm_phi_subcells= *)
  forall {B} `{Boolean B} (s: Slice8.T (Rows.T (Cols.T B))),
    subcells_ (map phi_ s) = map phi_ (subcells_ s).
  (* =end= *)
Proof.
  intros ? ?
    [s0 s1 s2 s3 s4 s5 s6 s7];
  vm_compute; reflexivity.
Qed.

Proposition correct_subcells_mod0:
    forall s f_s,
      Slice8.Forall2 R_mod0 s f_s ->
      Slice8.Forall2 R_mod0
        (Bitslice.subcells s)
        (Bitslice.subcells f_s).
Proof.
  intros
    [s0 s1 s2 s3 s4 s5 s6 s7]
    [f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7]
    [H0 H1 H2 H3 H4 H5 H6 H7]; simpl in *.
  rewrite <-H0, <-H1, <-H2, <-H3,
    <-H4, <-H5, <-H6, <-H7.
  repeat split.
Qed.

Proposition correct_subcells_mod1:
    forall s f_s,
      Slice8.Forall2 R_mod1 s f_s ->
      Slice8.Forall2 R_mod1
        (Bitslice.subcells s)
        (Bitslice.subcells f_s).
Proof.
  intros
    [s0 s1 s2 s3 s4 s5 s6 s7]
    [f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7]
    [H0 H1 H2 H3 H4 H5 H6 H7]; simpl in *.
  rewrite H0, H1, H2, H3,
    H4, H5, H6, H7.
  constructor; vm_compute; reflexivity.
Qed.

Proposition correct_subcells_mod2:
    forall s f_s,
      Slice8.Forall2 R_mod2 s f_s ->
      Slice8.Forall2 R_mod2
        (Bitslice.subcells s)
        (Bitslice.subcells f_s).
Proof.
  intros
    [s0 s1 s2 s3 s4 s5 s6 s7]
    [f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7]
    [H0 H1 H2 H3 H4 H5 H6 H7]; simpl in *.
  rewrite H0, H1, H2, H3,
    H4, H5, H6, H7.
  constructor; vm_compute; reflexivity.
Qed.

Proposition correct_subcells_mod3:
    forall s f_s,
      Slice8.Forall2 R_mod3 s f_s ->
      Slice8.Forall2 R_mod3
        (Bitslice.subcells s)
        (Bitslice.subcells f_s).
Proof.
  intros
    [s0 s1 s2 s3 s4 s5 s6 s7]
    [f_s0 f_s1 f_s2 f_s3 f_s4 f_s5 f_s6 f_s7]
    [H0 H1 H2 H3 H4 H5 H6 H7]; simpl in *.
  rewrite H0, H1, H2, H3,
    H4, H5, H6, H7.
  constructor; vm_compute; reflexivity.
Qed.


Proposition correct_round_mod0:
  forall constkey f_constkey,
    Slice8.Forall2 R_mod0 constkey f_constkey ->
  forall s f_s,
    Slice8.Forall2 R_mod0 s f_s ->
    Slice8.Forall2 R_mod1
      (Bitslice.round Bitslice.permbits s constkey)
      (Fixslice.round (map Fixslice.mixcolumns_mod0) f_s f_constkey).
Proof.
  intros
    constkey f_constkey HR_constkey
    s f_s HR.
  apply correct_shiftrows_mixcolumns_mod0.
  apply correct_add_round_key_mod0; auto.
  apply correct_subcells_mod0.
  auto.
Qed.

Proposition correct_round_mod1:
  forall constkey f_constkey,
    Slice8.Forall2 R_mod1 constkey f_constkey ->
  forall s f_s,
    Slice8.Forall2 R_mod1 s f_s ->
    Slice8.Forall2 R_mod2
      (Bitslice.round Bitslice.permbits s constkey)
      (Fixslice.round (map Fixslice.mixcolumns_mod1) f_s f_constkey).
Proof.
  intros
    constkey f_constkey HR_constkey
    s f_s HR.
  apply correct_shiftrows_mixcolumns_mod1.
  apply correct_add_round_key_mod1; auto.
  apply correct_subcells_mod1.
  auto.
Qed.

Proposition correct_round_mod2:
  forall constkey f_constkey,
    Slice8.Forall2 R_mod2 constkey f_constkey ->
  forall s f_s,
    Slice8.Forall2 R_mod2 s f_s ->
    Slice8.Forall2 R_mod3
      (Bitslice.round Bitslice.permbits s constkey)
      (Fixslice.round (map Fixslice.mixcolumns_mod2) f_s f_constkey).
Proof.
  intros
    constkey f_constkey HR_constkey
    s f_s HR.
  apply correct_shiftrows_mixcolumns_mod2.
  apply correct_add_round_key_mod2; auto.
  apply correct_subcells_mod2.
  auto.
Qed.

Proposition correct_round_mod3:
  forall constkey f_constkey,
    Slice8.Forall2 R_mod3 constkey f_constkey ->
  forall s f_s,
    Slice8.Forall2 R_mod3 s f_s ->
    Slice8.Forall2 R_mod4
      (Bitslice.round Bitslice.permbits s constkey)
      (Fixslice.round (map Fixslice.mixcolumns_mod3) f_s f_constkey).
Proof.
  intros
    constkey f_constkey HR_constkey
    s f_s HR.
  apply correct_shiftrows_mixcolumns_mod3.
  apply correct_add_round_key_mod3; auto.
  apply correct_subcells_mod3.
  auto.
Qed.

Proposition correct_skinny:
  forall constkeys f_constkeys,
    R_constkeys constkeys f_constkeys ->
    forall s f_s,
      Slice8.Forall2 R_mod0 s f_s ->
      Slice8.Forall2 R_mod0
        (Bitslice.skinny constkeys s)
        (Fixslice.skinny f_constkeys f_s).
Proof.
  intros constkeys f_constkeys HR_constkeys.
  induction HR_constkeys
    as [|constkey_mod0 constkey_mod1 constkey_mod2 constkey_mod3
         f_constkey_mod0 f_constkey_mod1 f_constkey_mod2 f_constkey_mod3
         xs f_xs HR_mod0 HR_mod1 HR_mod2 HR_mod3 HR_constkeys IH]; auto.
  intros s f_s HR.
  apply IH.
  apply correct_tau.
  apply correct_round_mod3; auto.
  apply correct_round_mod2; auto.
  apply correct_round_mod1; auto.
  apply correct_round_mod0; auto.
Qed.

Proposition eta_Slice8_R_mod0 {A}:
  forall s s',
    Slice8.Forall2 (R_mod0 (A := A)) s s' -> s = s'.
Proof.
  intros
    [s0 s1 s2 s3 s4 s5 s6 s7]
    [s0' s1' s2' s3' s4' s5' s6' s7']
    [H0 H1 H2 H3 H4 H5 H6 H7].
  simpl in *.
  rewrite H0, H1, H2, H3, H4, H5, H6, H7; auto.
Qed.

Definition state := Bitslice.state.

Fixpoint flatten_constkeys (l: list (state * state * state * state)): list state :=
  match l with
  | [] => []
  | (constkey_mod0,
      constkey_mod1,
      constkey_mod2, 
      constkey_mod3) :: l =>
      constkey_mod0
        :: map phi_ constkey_mod1
        :: map phi_ (map phi_ constkey_mod2)
        :: map phi_ (map phi_ (map phi_ constkey_mod3))
        :: flatten_constkeys l
  end.

Lemma R_constkeys_flatten_constkeys:
  forall l, R_constkeys (flatten_constkeys l) l.
Proof.
  intro l;
    induction l as 
    [ | [[[constkey0 constkey1] constkey2] constkey3] constkeys IH];
    try constructor; repeat split; auto.
Qed.

Theorem correct_fixsliced_skinny:
(* =theorem= *)
  forall f_constkeys s,
    let constkeys := flatten_constkeys f_constkeys in
    Bitslice.skinny constkeys s
    = Fixslice.skinny f_constkeys s.
(* =end= *)
Proof.
  intros f_constkeys s.
  apply eta_Slice8_R_mod0.
  apply correct_skinny; repeat constructor.
  apply R_constkeys_flatten_constkeys.
Qed.

Print Assumptions correct_fixsliced_skinny.
