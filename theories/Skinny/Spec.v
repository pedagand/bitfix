Require Import Coq.Lists.List.

Require Import Algebra.
Require Cols.
Require Rows.
Require Slice8.
Require Double.

Require Import Skinny.Base.

(* =state= *)
Definition cube A := Rows.T (Cols.T (Slice8.T A)).
Definition state := cube bool.
(* =end= *)

Definition subcells (s: state): state :=
  map subcells_ s.

Definition add_round_key (constkey: state)(s: state): state :=
  add_round_key_ constkey s.

Definition shiftrows (s: state): state :=
  app shiftrows_ s.

Definition mixcolumns (s: state): state :=
  mixcolumns_ s.

Definition permbits (s: state): state :=
  let s := shiftrows s in
  mixcolumns s.

(* =round= *)
Definition round (s: state)(constkey: state): state :=
  let s := map subcells_ s in
  let s := add_round_key_ constkey s in
  let s := app shiftrows_ s in
  mixcolumns_ s.
(* =end= *)

(* =skinny= *)
Definition skinny (constkeys: list state)(s: state): state :=
  fold_left round constkeys s.
(* =end= *)
