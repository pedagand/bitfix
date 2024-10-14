Require Import Coq.Lists.List.
Import ListNotations.

Require Import Algebra.
Require Cols.
Require Rows.
Require Slice4.
Require Double.

Section Subcells.
  (* =subcells= *)
  Variable B: Type.
  Context `(Boolean B).

  Definition gate x y z := xor x (and y z).

  Definition subcells_ (xs: Slice4.T B): Slice4.T B :=
    let x0 := lookup xs Slice4.S0 in
    let x1 := lookup xs Slice4.S1 in
    let x2 := lookup xs Slice4.S2 in
    let x3 := lookup xs Slice4.S3 in
    let x1' := gate x1 x0 x2 in
    let x0' := gate x0 x1' x3 in
    let x2' := xor x2 (or x0' x1') in
    let x3' := xor x3 x2' in
    let x1'' := xor x1' x3' in
    let x3'' := not x3' in
    let x2'' := gate x2' x0' x1'' in
    init (fun i => match i with
                   | Slice4.S0 => x3''
                   | Slice4.S1 => x1''
                   | Slice4.S2 => x2''
                   | Slice4.S3 => x0'
                   end).
  (* =end= *)

End Subcells.

Arguments subcells_ {B _} xs.

Section SubcellsTest.

  Proposition correct_subcells_:
    List.map (fun n => subcells_ (Slice4.of_int n))
      (List.seq 0 16)
    = (* https://eprint.iacr.org/2017/622.pdf
         Table 3 *)
      List.map Slice4.of_int
        [ 1; 10; 4; 12
        ; 6; 15; 3; 9
        ; 2; 13; 11; 7
        ; 5; 0; 8; 14 ].
  Proof. cbv. reflexivity. Qed.

End SubcellsTest.

Section Permbits.

  Definition reverse {A} (xs: Cols.T A): Cols.T A :=
    perm (fun i => match i with
                   | Cols.C0 => Cols.C3
                   | Cols.C1 => Cols.C2
                   | Cols.C2 => Cols.C1
                   | Cols.C3 => Cols.C0
                   end) xs.

  Definition reindex_R (i: Rows.Ix): Cols.Ix :=
    match i with
    | Rows.R0 => Cols.C0
    | Rows.R1 => Cols.C1
    | Rows.R2 => Cols.C2
    | Rows.R3 => Cols.C3
    end.

  Definition reindex_C (j: Cols.Ix): Rows.Ix :=
    match j with
    | Cols.C0 => Rows.R0
    | Cols.C1 => Rows.R1
    | Cols.C2 => Rows.R2
    | Cols.C3 => Rows.R3
    end.

  Definition transpose {A} (m: Cols.T (Rows.T A)): Rows.T (Cols.T A) :=
    init (fun j =>
    init (fun i =>
    lookup (lookup m (reindex_R j)) (reindex_C i))).

  Definition rotate {A} (m: Cols.T (Rows.T A)): Cols.T (Rows.T A) :=
    reindex (transpose m).

  Definition sigma {A} (m: Cols.T (Rows.T A)): Cols.T (Rows.T A) :=
    let m := reverse m in
    let m := ror Cols.C1 m in
    rotate m.

  Proposition idemp_sigma4 {A}: forall (m: Cols.T (Rows.T A)), sigma (sigma (sigma (sigma m))) = m.
  Proof.
    intros [[? ? ? ?]
            [? ? ? ?]
            [? ? ? ?]
            [? ? ? ?]];
    reflexivity.
  Qed.

  Definition inv_sigma {A} (m: Cols.T (Rows.T A)): Cols.T (Rows.T A) := sigma (sigma (sigma m)).

  Proposition inv_inv_sigma {A}: forall (m: Cols.T (Rows.T A)), sigma (inv_sigma m) = m.
  Proof. apply idemp_sigma4. Qed.

  Definition indices_C: Slice4.T Cols.Ix :=
    init (fun i =>
            match i with
            | Slice4.S0 => Cols.C0
            | Slice4.S1 => Cols.C1
            | Slice4.S2 => Cols.C2
            | Slice4.S3 => Cols.C3
            end).

  Definition rols {A} : Slice4.T (Cols.T A -> Cols.T A) :=
    map rol indices_C.

  Definition permbits_ {A} : Slice4.T (Cols.T (Rows.T A) -> Cols.T (Rows.T A)) :=
    map (fun p xs => sigma (p xs)) rols.

End Permbits.

Section PermbitsTest.
  Definition in_m: Cols.T (Rows.T (Cols.Ix * Rows.Ix)) := indices (Cols.Ix * Rows.Ix)%type.

  Lemma correct_rotate:
    rotate in_m
    = Cols.Build_T
        (Rows.Build_T
           (Cols.C0, Rows.R0)
           (Cols.C1, Rows.R0)
           (Cols.C2, Rows.R0)
           (Cols.C3, Rows.R0))
        (Rows.Build_T
           (Cols.C0, Rows.R1)
           (Cols.C1, Rows.R1)
           (Cols.C2, Rows.R1)
           (Cols.C3, Rows.R1))
        (Rows.Build_T
           (Cols.C0, Rows.R2)
           (Cols.C1, Rows.R2)
           (Cols.C2, Rows.R2)
           (Cols.C3, Rows.R2))
        (Rows.Build_T
           (Cols.C0, Rows.R3)
           (Cols.C1, Rows.R3)
           (Cols.C2, Rows.R3)
           (Cols.C3, Rows.R3)).
  Proof. reflexivity. Qed.

  Lemma correct_reverse:
    reverse (indices Cols.Ix) =
      Cols.Build_T Cols.C3 Cols.C2 Cols.C1 Cols.C0.
  Proof. reflexivity. Qed.

  Lemma correct_ror1:
    ror Cols.C1 (indices Cols.Ix) =
      Cols.Build_T Cols.C3 Cols.C0 Cols.C1 Cols.C2.
  Proof. reflexivity. Qed.

  Proposition correct_sigma: 
    sigma in_m = 
    Cols.Build_T
      (Rows.Build_T
         (Cols.C0, Rows.R0)
         (Cols.C3, Rows.R0)
         (Cols.C2, Rows.R0)
         (Cols.C1, Rows.R0))
      (Rows.Build_T
         (Cols.C0, Rows.R1)
         (Cols.C3, Rows.R1)
         (Cols.C2, Rows.R1)
         (Cols.C1, Rows.R1))
      (Rows.Build_T
         (Cols.C0, Rows.R2)
         (Cols.C3, Rows.R2)
         (Cols.C2, Rows.R2)
         (Cols.C1, Rows.R2))
      (Rows.Build_T
         (Cols.C0, Rows.R3)
         (Cols.C3, Rows.R3)
         (Cols.C2, Rows.R3)
         (Cols.C1, Rows.R3)).
  Proof. reflexivity. Qed.

  Definition in_slice0 := Cols.Build_T
                            (Rows.Build_T 0 16 32 48)
                            (Rows.Build_T 4 20 36 52)
                            (Rows.Build_T 8 24 40 56)
                            (Rows.Build_T 12 28 44 60).

  Definition out_slice0 := Cols.Build_T
                            (Rows.Build_T 0 12 8 4)
                            (Rows.Build_T 16 28 24 20)
                            (Rows.Build_T 32 44 40 36)
                            (Rows.Build_T 48 60 56 52).

  Definition in_slice1 := Cols.Build_T
                            (Rows.Build_T 1 17 33 49)
                            (Rows.Build_T 5 21 37 53)
                            (Rows.Build_T 9 25 41 57)
                            (Rows.Build_T 13 29 45 61).

  Definition out_slice1 := Cols.Build_T
                            (Rows.Build_T 5 1 13 9)
                            (Rows.Build_T 21 17 29 25)
                            (Rows.Build_T 37 33 45 41)
                            (Rows.Build_T 53 49 61 57).

  Definition in_slice2 := Cols.Build_T
                            (Rows.Build_T 2 18 34 50)
                            (Rows.Build_T 6 22 38 54)
                            (Rows.Build_T 10 26 42 58)
                            (Rows.Build_T 14 30 46 62).

  Definition out_slice2 := Cols.Build_T
                            (Rows.Build_T 10 6 2 14)
                            (Rows.Build_T 26 22 18 30)
                            (Rows.Build_T 42 38 34 46)
                            (Rows.Build_T 58 54 50 62).

  Definition in_slice3 := Cols.Build_T
                            (Rows.Build_T 3 19 35 51)
                            (Rows.Build_T 7 23 39 55)
                            (Rows.Build_T 11 27 43 59)
                            (Rows.Build_T 15 31 47 63).

  Definition out_slice3 := Cols.Build_T
                            (Rows.Build_T 15 11 7 3)
                            (Rows.Build_T 31 27 23 19)
                            (Rows.Build_T 47 43 39 35)
                            (Rows.Build_T 63 59 55 51).

  Definition in_s := Slice4.Build_T in_slice0 in_slice1 in_slice2 in_slice3.
  Definition out_s := Slice4.Build_T out_slice0 out_slice1 out_slice2 out_slice3.

  Proposition correct_permbits: app permbits_ in_s = out_s.
  Proof. reflexivity. Qed.


(*
     i 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
P64(i) 0 17 34 51 48 1 18 35 32 49 2 19 16 33 50 3
     i 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
P64(i) 4 21 38 55 52 5 22 39 36 53 6 23 20 37 54 7
     i 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47
P64(i) 8 25 42 59 56 9 26 43 40 57 10 27 24 41 58 11
     i 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63
P64(i) 12 29 46 63 60 13 30 47 44 61 14 31 28 45 62 15 *)

End PermbitsTest.

Section AddRoundKey.
  Variable B: Type.
  Context `(Boolean B).

  Definition add_round_key_ (u v const: B)(xs: Slice4.T B): Slice4.T B :=
    let uvconst :=
      init (fun s => match s with
                     | Slice4.S0 => v
                     | Slice4.S1 => u
                     | Slice4.S2 => ff
                     | Slice4.S3 => const
                     end) in
    map2 xor uvconst xs.

End AddRoundKey.

Arguments add_round_key_ {B _} u v const xs.
