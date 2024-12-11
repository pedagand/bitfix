Require Import Algebra.
Require Cols.
Require Rows.
Require Slice8.
Require Double.

Section Subcells.

  (* =perms= *)
  Variable B: Type.

  Definition bperm (xs: Slice8.T B): Slice8.T B :=
    perm (fun s => match s with
                   | Slice8.S7 => Slice8.S2 | Slice8.S6 => Slice8.S1
                   | Slice8.S5 => Slice8.S7 | Slice8.S4 => Slice8.S6
                   | Slice8.S3 => Slice8.S4 | Slice8.S2 => Slice8.S0
                   | Slice8.S1 => Slice8.S3 | Slice8.S0 => Slice8.S5
                   end) xs.

  Definition bperm_out (xs: Slice8.T B): Slice8.T B  :=
    perm (fun s => match s with
                   | Slice8.S0 => Slice8.S0 | Slice8.S1 => Slice8.S2
                   | Slice8.S2 => Slice8.S1 | Slice8.S3 => Slice8.S3
                   | Slice8.S4 => Slice8.S4 | Slice8.S5 => Slice8.S5
                   | Slice8.S6 => Slice8.S6 | Slice8.S7 => Slice8.S7
                   end) xs.
  (* =end= *)

  (* =s8= *)
  Context `(Boolean B).

  Definition gate x y z := xor x (not (or y z)).

  Definition s8 (xs: Slice8.T B): Slice8.T B :=
    let b0 := lookup xs Slice8.S0 in
    let b2 := lookup xs Slice8.S2 in
    let b4 := lookup xs Slice8.S4 in
    let b6 := lookup xs Slice8.S6 in
    let b7 := lookup xs Slice8.S7 in

    let b0' := gate b0 b2 b2 in
    let b4' := gate b4 b6 b7 in
    init (fun i => match i with
                   | Slice8.S0 => b0'
                   | Slice8.S4 => b4'
                   | i => lookup xs i
                   end).
  (* =end= *)

  (* =subcells= *)
  Definition subcells_ (xs: Slice8.T B): Slice8.T B :=
    let xs := bperm (s8 xs) in
    let xs := bperm (s8 xs) in
    let xs := bperm (s8 xs) in
    bperm_out (s8 xs).
  (* =end= *)

End Subcells.

Arguments subcells_ {B _} xs.

Section TestSubcells.

End TestSubcells.

Section AddRoundKey.
  (* =addroundkey= *)
  Variable B: Type.
  Context `(Boolean B).

  Definition add_round_key_ (constkey: B)(s: B): B :=
    xor s constkey.
  (* =end= *)

End AddRoundKey.

Arguments add_round_key_ {B _} constkey s.

Section ShiftRows.

  (* =indices_C= *)
  Definition reindex_R (i: Rows.Ix): Cols.Ix :=
    match i with
    | Rows.R0 => Cols.C0
    | Rows.R1 => Cols.C1
    | Rows.R2 => Cols.C2
    | Rows.R3 => Cols.C3
    end.

  Definition indices_C: Rows.T Cols.Ix :=
    map reindex_R (indices Rows.Ix).
  (* =end= *)

  (* =shiftrows= *)
  Variable A: Type.

  Definition shiftrows_: Rows.T (Cols.T A -> Cols.T A) :=
    map ror indices_C.
  (* =end= *)

  (* =phi= *)
  Definition phi_ (rs: Rows.T (Cols.T A)): Rows.T (Cols.T A) :=
    ror Rows.R1 (app shiftrows_ rs).
  (* =end= *)

  (* =inv_phi= *)
  Definition inv_phi_ (rs: Rows.T (Cols.T A)): Rows.T (Cols.T A) :=
    let rs := rol Rows.R1 rs in
    app (map rol indices_C) rs.
  (* =end= *)

  Definition phi_explicit_ (rs: Rows.T (Cols.T A)): Rows.T (Cols.T A) :=
    let r0 := lookup rs Rows.R0 in
    let r1 := lookup rs Rows.R1 in
    let r2 := lookup rs Rows.R2 in
    let r3 := lookup rs Rows.R3 in
    init (fun r => match r with
                   | Rows.R0 => ror Cols.C3 r3
                   | Rows.R1 => ror Cols.C0 r0
                   | Rows.R2 => ror Cols.C1 r1
                   | Rows.R3 => ror Cols.C2 r2
                   end).

  (* =tau= *)
  Definition tau_ (rs: Rows.T (Cols.T A)): Rows.T (Cols.T A) :=
    map (ror Cols.C2) rs.
  (* =end= *)

End ShiftRows.

Arguments shiftrows_ {A}.
Arguments phi_ {A} rs.
Arguments phi_explicit_ {A} rs.
Arguments inv_phi_ {A} rs.
Arguments tau_ {A} rs.

Section MixColumns.
  (* =psi= *)
  Variable B: Type.
  Context `(Boolean B).

  Definition psi_ (s: Rows.T B): Rows.T B :=
    let r0 := lookup s Rows.R0 in
    let r1 := lookup s Rows.R1 in
    let r2 := lookup s Rows.R2 in
    let r3 := lookup s Rows.R3 in
    let r1' := xor r2 r1 in
    let r2' := xor r0 r2 in
    let r3' := xor r2' r3 in
    init (fun r => match r with
                   | Rows.R0 => r0
                   | Rows.R1 => r1'
                   | Rows.R2 => r2'
                   | Rows.R3 => r3'
                   end).
  (* =end= *)

  (* =mixcolumns= *)
  Definition mixcolumns_ (rs: Rows.T B): Rows.T B :=
    ror Rows.R1 (psi_ rs).
  (* =end= *)

  Definition mixcolumns_spec_ (rs: Rows.T B): Rows.T B :=
    let r0 := lookup rs Rows.R0 in
    let r1 := lookup rs Rows.R1 in
    let r2 := lookup rs Rows.R2 in
    let r3 := lookup rs Rows.R3 in
    let r1' := xor r2 r1 in
    let r2' := xor r0 r2 in
    let r3' := xor r2' r3 in
    init (fun r => match r with
                     | Rows.R0 => r3'
                     | Rows.R1 => r0
                     | Rows.R2 => r1'
                     | Rows.R3 => r2'
                   end).

  (* =sigma= *)
  Definition sigma_ (s: Rows.T (Cols.T B)): Rows.T (Cols.T B) :=
    let r0 := lookup s Rows.R0 in
    let r1 := lookup s Rows.R1 in
    let r2 := lookup s Rows.R2 in
    let r3 := lookup s Rows.R3 in
    let r0' := r0 in
    let r1' := xor (ror Cols.C1 r2) r1 in
    let r2' := xor (ror Cols.C2 r0) r2 in
    let r3' := xor (ror Cols.C3 r2') r3 in
    init (fun r => match r with
                   | Rows.R0 => r0'
                   | Rows.R1 => r1'
                   | Rows.R2 => r2'
                   | Rows.R3 => r3'
                   end).
  (* =end= *)

End MixColumns.

Arguments mixcolumns_ {B _} rs.
Arguments mixcolumns_spec_ {B _} rs.
Arguments psi_ {B _} s.
Arguments sigma_ {B _} s.

Print Implicit subcells_.
Print Implicit add_round_key_.
Print Implicit shiftrows_.
Print Implicit mixcolumns_.
