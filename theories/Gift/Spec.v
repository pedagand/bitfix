Require Import Coq.Lists.List.

Require Import Algebra.
Require Cols.
Require Rows.
Require Slice4.
Require Double.

Require Import Gift.Base.

Definition cube A := Cols.T (Rows.T (Slice4.T A)).
Definition state := cube bool.

Definition subcells (s: state): state :=
  map subcells_ s.

Definition permbits (s: state): state :=
  let s := reindex (G := Slice4.T) s in
  let s := app permbits_ s in
  let s := reindex (F := Slice4.T) s in
  s.

Definition add_round_key
  (us: Cols.T (Rows.T bool))
  (vs: Cols.T (Rows.T bool))
  (consts: Cols.T (Rows.T bool))
  (s: state): state :=
  app (app (app (map add_round_key_ us) vs) consts) s.

Definition round (s: state)(uvconsts: Cols.T (Rows.T bool) * (Cols.T (Rows.T bool)) * (Cols.T (Rows.T bool))): state :=
  let s := subcells s in
  let s := permbits s in
  let '(us, vs, consts) := uvconsts in
  add_round_key us vs consts s.

Definition gift (uvconsts: list (Cols.T (Rows.T bool) * Cols.T (Rows.T bool) * Cols.T (Rows.T bool)))(s: state): state :=
  fold_left round uvconsts s.
