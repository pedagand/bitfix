Require Import Coq.Lists.List.

Require Import Algebra.
Require Cols.
Require Rows.
Require Slice4.
Require Double.

Require Import Gift.Base.
Require Gift.Bitslice.

Definition reg32 A := Bitslice.reg32 A.
Definition cube2 A := Bitslice.cube2 A.
Definition state := Bitslice.state.

Definition round:
  forall (permbits: state -> state)
         (s: state)
         (uvconsts: reg32 bool * reg32 bool * reg32 bool), state :=
  Bitslice.round.

Definition permbits_mod0 (s: state): state :=
  app rols s.

Definition permbits_mod1 (s: state): state :=
  map inv_sigma (app rols (map sigma s)).

Definition indices_R : Slice4.T Rows.Ix :=
  init (fun s =>
          match s with
            | Slice4.S0 => Rows.R0
            | Slice4.S1 => Rows.R1
            | Slice4.S2 => Rows.R2
            | Slice4.S3 => Rows.R3
          end).

Definition permbits_mod1_explicit (s: state): state :=
  let p : Rows.Ix -> reg32 bool -> reg32 bool :=
      fun i crs => map (rol (F := Rows.T) i) crs
  in
  app (map p indices_R) s.

Lemma equiv_permbits_mod1: forall s, permbits_mod1 s = permbits_mod1_explicit s.
Proof.
  intros s; reflexivity.
Qed.

Definition permbits_mod2 (s: state): state :=
    map inv_sigma (map inv_sigma (app rols (map sigma (map sigma s)))).

Definition permbits_mod2_explicit (s: state): state :=
  app (map (ror (F := Cols.T)) indices_C) s.

Lemma equiv_permbits_mod2: forall s, permbits_mod2 s = permbits_mod2_explicit s.
Proof.
  intros s; reflexivity.
Qed.


Definition permbits_mod3 (s: state): state :=
  map inv_sigma
      (map inv_sigma
           (map inv_sigma
                (app rols
                     (map sigma
                          (map sigma
                               (map sigma s)))))).

Definition permbits_mod3_explicit (s: state): state :=
  let p : Rows.Ix -> reg32 bool -> reg32 bool :=
      fun i crs => map (ror (F := Rows.T) i) crs
  in
  app (map p indices_R) s.

Lemma equiv_permbits_mod3: forall s, permbits_mod3 s = permbits_mod3_explicit s.
Proof.
  intros s; reflexivity.
Qed.

Definition round_mod (s: state) uvconsts :=
  let '(uvconsts0, uvconsts1, uvconsts2, uvconsts3) :=
    uvconsts in
  let s := round permbits_mod0 s uvconsts0 in
  let s := round permbits_mod1 s uvconsts1 in
  let s := round permbits_mod2 s uvconsts2 in
  round permbits_mod3 s uvconsts3.

Definition gift uvconsts (s: state): state :=
  fold_left round_mod uvconsts s.

