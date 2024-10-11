Require Import Coq.Lists.List.

Require Import Algebra.

Require Cols.
Require Rows.
Require Slice8.
Require Double.

Require Import Skinny.Base.

(* =state= *)
Definition reg32 A := Rows.T (Cols.T (Double.T A)).
Definition cube2 A := Slice8.T (reg32 A).
Definition state := cube2 bool.
(* =end= *)

Definition subcells (s: state): state :=
  subcells_ s.

Definition add_round_key (constkey: state)(s: state): state :=
  map2 add_round_key_ constkey s.

Definition shiftrows (s: state): state :=
  map (F := Slice8.T) (app shiftrows_) s.

Definition mixcolumns (s: state): state :=
  map mixcolumns_ s.

Definition permbits (s: state): state :=
  let s := shiftrows s in
  mixcolumns s.

(* =round= *)
Definition round (s: state)(constkey: state): state :=
  let s := subcells_ s in
  let s := add_round_key_ constkey s in
  let s := map (F := Slice8.T) (app shiftrows_) s in
  map mixcolumns_ s.
(* =end= *)

(* =round= *)
Definition skinny (constkeys: list state)(s: state): state :=
  fold_left round constkeys s.
(* =end= *)

Reset round. 
(* That was for show, let's have some software engineering to ease the
   proof. *)

Section Round.
  Variable permbits: state -> state.

  Definition round (s: state)(constkey: state): state :=
    let s := subcells s in
    let s := add_round_key constkey s in
    permbits s.

End Round.

Definition skinny (constkeys: list state)(s: state): state :=
  fold_left (round permbits) constkeys s.
