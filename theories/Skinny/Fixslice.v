Require Import Coq.Lists.List.

Require Import Algebra.

Require Cols.
Require Rows.
Require Slice8.
Require Double.

Require Import Skinny.Base.
Require Skinny.Bitslice.

Definition reg32 A := Bitslice.reg32 A.
Definition cube2 A := Bitslice.cube2 A.
Definition state := Bitslice.state.

Definition round:
  forall (permbits: state -> state)
         (s: state)
         (constkey: state), state :=
  Bitslice.round.

Fixpoint iter {A} (n: nat)(f: A -> A)(x: A): A :=
  match n with
  | 0 => x
  | S n => iter n f (f x)
  end.

Proposition iter_S:
  forall A (f: A -> A) (n: nat)(a: A),
    iter n f (f a) = f (iter n f a).
Proof.
  intros A f n.
  induction n as [|n IHn]; try reflexivity.
  intro a; simpl; rewrite IHn; reflexivity.
Qed.

Section MixColumns.
  Variable B: Type.
  Context `(Boolean B).

  (* =mixcolumns_mod= *)
  Definition mixcolumns_mod i (s: Rows.T (Cols.T B)): Rows.T (Cols.T B) :=
    iter i inv_phi_ (sigma_ (iter i phi_ s)).
  (* =end= *)

  Definition mixcolumns_mod0 (s: Rows.T (Cols.T B)): Rows.T (Cols.T B) :=
    mixcolumns_mod 0 s.

  Definition mixcolumns_mod1 (s: Rows.T (Cols.T B)): Rows.T (Cols.T B) :=
    mixcolumns_mod 1 s.

  Definition mixcolumns_mod1_explicit (s: Rows.T (Cols.T B)): Rows.T (Cols.T B) :=
    let r0 := lookup s Rows.R0 in
    let r1 := lookup s Rows.R1 in
    let r2 := lookup s Rows.R2 in
    let r3 := lookup s Rows.R3 in
    let r0' := map2 xor (ror Cols.C2 r1) r0 in
    let r1' := map2 xor r3 r1 in
    let r2' := map2 xor (ror Cols.C2 r1') r2 in
    init (fun r => match r with
                   | Rows.R0 => r0'
                   | Rows.R1 => r1'
                   | Rows.R2 => r2'
                   | Rows.R3 => r3
                   end).

  (* =mixcolumns_mod2= *)
  Definition mixcolumns_mod2 (s: Rows.T (Cols.T B)): Rows.T (Cols.T B) :=
    mixcolumns_mod 2 s.
  (* =end= *)

  Definition mixcolumns_mod2_explicit (s: Rows.T (Cols.T B)): Rows.T (Cols.T B) :=
    let r0 := lookup s Rows.R0 in
    let r1 := lookup s Rows.R1 in
    let r2 := lookup s Rows.R2 in
    let r3 := lookup s Rows.R3 in
    let r3' := map2 xor (ror Cols.C3 r0) r3 in
    let r0' := map2 xor (ror Cols.C2 r2) r0 in
    let r1' := map2 xor (ror Cols.C1 r0') r1 in
    init (fun r => match r with
                   | Rows.R0 => r0'
                   | Rows.R1 => r1'
                   | Rows.R2 => r2
                   | Rows.R3 => r3'
                   end).

  Definition mixcolumns_mod3 (s: Rows.T (Cols.T B)): Rows.T (Cols.T B) :=
    mixcolumns_mod 3 s.

  Definition mixcolumns_mod3_explicit (s: Rows.T (Cols.T B)): Rows.T (Cols.T B) :=
    let r0 := lookup s Rows.R0 in
    let r1 := lookup s Rows.R1 in
    let r2 := lookup s Rows.R2 in
    let r3 := lookup s Rows.R3 in
    let r2' := map2 xor r3 r2 in
    let r3' := map2 xor r1 r3 in
    let r0' := map2 xor r3' r0 in
    init (fun r => match r with
                   | Rows.R0 => r0'
                   | Rows.R1 => r1
                   | Rows.R2 => r2'
                   | Rows.R3 => r3'
                   end).

End MixColumns.

Arguments mixcolumns_mod {B _} i s.
Arguments mixcolumns_mod0 {B _} s.
Arguments mixcolumns_mod1 {B _} s.
Arguments mixcolumns_mod2 {B _} s.
Arguments mixcolumns_mod3 {B _} s.
Arguments mixcolumns_mod1_explicit {B _} s.
Arguments mixcolumns_mod2_explicit {B _} s.
Arguments mixcolumns_mod3_explicit {B _} s.

Lemma rol1_init {A}: forall (f: Rows.Ix -> A),
  rol Rows.R1 (init f)
  = init (fun r => match r with
                   | Rows.R0 => f Rows.R1
                   | Rows.R1 => f Rows.R2
                   | Rows.R2 => f Rows.R3
                   | Rows.R3 => f Rows.R0
                   end).
Proof. reflexivity. Qed.

Lemma ror1_init: forall A (f: Rows.Ix -> A),
  ror Rows.R1 (init f)
  = init (fun r => match r with
                   | Rows.R0 => f Rows.R3
                   | Rows.R1 => f Rows.R0
                   | Rows.R2 => f Rows.R1
                   | Rows.R3 => f Rows.R2
                   end).
Proof. reflexivity. Qed.

Lemma app_init_init {A B}: forall (f: Rows.Ix -> A -> B)(g: Rows.Ix -> A),
  app (init f) (init g) = init (fun i => f i (g i)).
Proof. reflexivity. Qed.

Lemma eta_Rows {A}:
  forall (cs0 cs1: Rows.T A),
           lookup cs0 Rows.R0 = lookup cs1 Rows.R0 ->
           lookup cs0 Rows.R1 = lookup cs1 Rows.R1 ->
           lookup cs0 Rows.R2 = lookup cs1 Rows.R2 ->
           lookup cs0 Rows.R3 = lookup cs1 Rows.R3 ->
           cs0 = cs1.
Admitted.

Lemma lookup_init : forall A (f: Rows.Ix -> A)(i: Rows.Ix),
    lookup (init f) i = f i.
Proof. intros A f i; destruct i; reflexivity. Qed.

(*
Definition eta_Rows {A}: forall (x y: Rows.T A),
    x.(Rows.r0) = y.(Rows.r0) ->
    x.(Rows.r1) = y.(Rows.r1) ->
    x.(Rows.r2) = y.(Rows.r2) ->
    x.(Rows.r3) = y.(Rows.r3) ->
    x = y.
Admitted.
*)
Lemma app_init: forall A B (f: Rows.Ix -> A -> B)(s: Rows.T A),
    (app (init f) s) = init (fun i => f i (lookup s i)).
Proof.
intros; reflexivity.
Qed.

(*
Lemma ror_Z: forall A (s: Cols.T A), Cols.ror1 s = Cols.ror s 1.
Proof. reflexivity. Qed. 

Lemma rol_Z: forall A (s: Cols.T A), Cols.rol1 s = Cols.rol s 1.
Proof. reflexivity. Qed. 
*)

(*
Lemma ror_S: forall A (s: Cols.T A) m n, ror m (ror n s) = ror (Cols.add m n) s.
Proof. Admitted. (* reflexivity. Qed.  *)

Lemma rol_S: forall A (s: Cols.T A) m n, rol m (Cols.rol n s) = Cols.rol (Cols.add m n) s.
Proof. Admitted. (* reflexivity. Qed.  *)
*)
(*
Lemma ror_mod4 {A}: forall (s: Cols.T A) n, Cols.ror s (3 + n) = Cols.ror s n.
Proof. Admitted.

Lemma ror_n {A}: forall (s: Cols.T A) m n, Cols.ror (Cols.ror s m) n = Cols.ror s (m + n).
Proof. Admitted.  (* reflexivity. Qed. *)

Lemma ror_0 {A}: forall (s: Cols.T A), Cols.ror s 0 = s.
Proof. reflexivity. Qed.

Lemma rol_n {A}: forall (s: Cols.T A) n, Cols.rol (Cols.rol s n) 1 = Cols.rol s (1 + n).
Proof. reflexivity. Qed.

Lemma rol_0 {A}: forall (s: Cols.T A), Cols.rol s 0 = s.
Proof. reflexivity. Qed.

Lemma ror_rol {A}: forall (s: Cols.T A)(n: nat), Cols.ror (Cols.rol s n) n = s.
Proof. induction n; try reflexivity. simpl.
Admitted.

Lemma rol_ror {A}: forall (s: Cols.T A)(n: nat), Cols.rol (Cols.ror s n) n = s.
Proof. induction n; try reflexivity. simpl.
Admitted.


Lemma ror_S_rol {A}: forall (s: Cols.T A)(m n: nat), Cols.ror (Cols.rol s n) (m + n) = Cols.ror s m.
Proof.
induction m; simpl.
- apply ror_rol.
- intro. erewrite IHm. reflexivity.
Qed.

Lemma ror_rol_S {A}: forall (s: Cols.T A)(m n: nat), Cols.ror (Cols.rol s (m + n)) n = Cols.rol s m.
Proof.
Admitted.

Lemma rol_ror_S {A}: forall (s: Cols.T A)(m n: nat), Cols.rol (Cols.ror s (m + n)) n = Cols.ror s m.
Proof.
Admitted.

Lemma rol_xor {B}`{Boolean B}: forall (s0 s1: Cols.T B)(n: nat), Cols.rol (xor s0 s1) n = xor (Cols.rol s0 n) (Cols.rol s1 n).
Admitted.
*)

(*
Lemma rol1_xor: forall B `(Boolean B) (s0 s1: Cols.T B) m, Cols.rol m (xor s0 s1) = xor (Cols.rol m s0) (Cols.rol m s1).
Proof. Admitted. (*reflexivity. Qed.*)

Lemma ror1_xor: forall  B `(Boolean B) (s0 s1: Cols.T B) m, Cols.ror m (xor s0 s1) = xor (Cols.ror m s0) (Cols.ror m s1).
Proof. Admitted. (*reflexivity. Qed.*)
*)
(*
Lemma ror1_idemp: forall A (s: Cols.T A),
    Cols.ror (Cols.ror1 (Cols.ror1 (Cols.ror1 (s)))) = s.
Proof. reflexivity. Qed.
*)

(*
Lemma ror1_rol1: forall A (s: Cols.T A) m n, Cols.ror (Cols.rol s m) n = Cols.ror s (Cols.sub m n).
Proof. Admitted. (* XXX *) (* reflexivity. Qed. *)

Lemma rol1_ror1: forall A (s: Cols.T A), Cols.rol1 (Cols.ror1 s) = s.
Proof. reflexivity. Qed.
*)

#[local]
Hint Rewrite
  lookup_init
  app_init
  ror1_init
  (*
    rol1_xor
  ror1_xor
  ror_S
  rol_S *)
(*
  ror1_idemp
  ror1_rol1
  rol1_ror1 *) : simplifier.

(*
#[local]
Hint Rewrite
(*  ror_Z
  rol_Z *)
 : folder.
*)

(*
Lemma equiv_mixcolumns_mod1 {B} `{Boolean B}:
  forall (s: Rows.T (Cols.T B)),
    mixcolumns_mod1 s = mixcolumns_mod1_explicit s.
Proof.
intro s.
unfold mixcolumns_mod1, phi_, sigma_, inv_phi_, shiftrows_.
Opaque app init Cols.rol Cols.ror Rows.rol lookup xor.
rewrite rol1_init, app_init_init.
eapply eta_Rows; simpl;
  autorewrite with simplifier;
  set (s0 := lookup s Rows.R0);
  set (s1 := lookup s Rows.R1);
  set (s2 := lookup s Rows.R2);
  set (s3 := lookup s Rows.R3);
  (* autorewrite with folder *). 
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.
*)

Lemma equiv_mixcolumns_mod2 {B} `{Boolean B}:
  forall (s: Rows.T (Cols.T B)),
    mixcolumns_mod2 s = mixcolumns_mod2_explicit s.
Proof.
  intros s; reflexivity.
Qed.

Lemma equiv_mixcolumns_mod3 {B} `{Boolean B}:
  forall (s: Rows.T (Cols.T B)),
    mixcolumns_mod3 s = mixcolumns_mod3_explicit s.
Proof.
  intros s; reflexivity.
Qed.

Definition tau (s: state): state := 
  map tau_ s.

(* =round= *)
Definition round_mod (s: state) constkeys :=
  let '(constkey0, constkey1, constkey2, constkey3) :=
    constkeys in
  let s := round (map (mixcolumns_mod 0)) s constkey0 in
  let s := round (map (mixcolumns_mod 1)) s constkey1 in
  let s := round (map (mixcolumns_mod 2)) s constkey2 in
  let s := round (map (mixcolumns_mod 3)) s constkey3 in
  map tau_ s.
(* =end= *)

Definition skinny constkeys (s: state): state :=
  fold_left round_mod constkeys s.
