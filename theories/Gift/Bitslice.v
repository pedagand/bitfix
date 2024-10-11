Require Import Coq.Lists.List.

Require Import Algebra.

Require Cols.
Require Rows.
Require Slice4.
Require Double.

Require Import Gift.Base.

Definition reg32 A := Cols.T (Rows.T (Double.T A)).
Definition cube2 A := Slice4.T (reg32 A).
Definition state := cube2 bool.

Definition subcells (s: state): state :=
  subcells_ s.

Definition permbits (s: state): state :=
  app permbits_ s.

Definition add_round_key
  (us: reg32 bool)
  (vs: reg32 bool)
  (consts: reg32 bool)
  (s: state): state :=
  add_round_key_ us vs consts s.

Definition round (permbits: state -> state)(s: state)(uvconsts: reg32 bool * reg32 bool * reg32 bool): state :=
  let s := subcells s in
  let s := permbits s in
  let '(us, vs, consts) := uvconsts in
  add_round_key us vs consts s.

Definition gift (uvconsts: list (reg32 bool * reg32 bool * reg32 bool))(s: state): state :=
  fold_left (round permbits) uvconsts s.
