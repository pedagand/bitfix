Require Import Algebra.

#[projections(primitive)]
 Record T (A : Type) :=
  { r0: A; r1: A; r2: A; r3: A }.

Arguments Build_T {_} r0 r1 r2 r3.
Arguments r0 {_}.
Arguments r1 {_}.
Arguments r2 {_}.
Arguments r3 {_}.

(* =Ix= *)
Inductive Ix := R0 | R1 | R2 | R3.
(* =end= *)

#[global]
  Instance Functor_T: Functor T :=
  { map := fun _ _ f d =>
             Build_T
               (f d.(r0)) (f d.(r1))
               (f d.(r2)) (f d.(r3)) }. 

(*
#[global, program]
  Instance FunctorLaws_T: FunctorLaws Functor_T.
Next Obligation. Admitted.
Next Obligation. Admitted.
*)

#[global]
  Instance Naperian_T: Naperian Functor_T Ix :=
  { lookup := fun _ xs i =>
                match i with
                | R0 => xs.(r0)
                | R1 => xs.(r1)
                | R2 => xs.(r2)
                | R3 => xs.(r3)
                end
  ; init := fun _ f => Build_T (f R0) (f R1) (f R2) (f R3) }.

(*
#[global, program]
  Instance NaperianLaws_T: NaperianLaws Naperian_T.
Next Obligation. Admitted.
Next Obligation. Admitted.
*)

#[global]
  Instance Foldable_T: Foldable Functor_T.
Admitted.
(*
  { foldM := fun _ _ xs => append xs.(fst) xs.(snd) }. *)

(*
#[program, global]
  Instance FoldableLaws_T: FoldableLaws Foldable_T.
*)

(* XXX: temporary hack. Delete *)

Definition add (b: Ix)(c: Ix): Ix :=
  match c with
  | R0 => b
  | R1 => match b with
          | R0 => R1
          | R1 => R2
          | R2 => R3
          | R3 => R0
          end
  | R2 => match b with
          | R0 => R2
          | R1 => R3
          | R2 => R0
          | R3 => R1
          end
  | R3 => match b with
          | R0 => R3
          | R1 => R0
          | R2 => R1
          | R3 => R2
          end
  end.


Definition sub (b: Ix)(c: Ix): Ix :=
  match c with
  | R0 => b
  | R1 => match b with
          | R0 => R3
          | R1 => R0
          | R2 => R1
          | R3 => R2
          end
  | R2 => match b with
          | R0 => R2
          | R1 => R3
          | R2 => R0
          | R3 => R1
          end
  | R3 => match b with
          | R0 => R1
          | R1 => R2
          | R2 => R3
          | R3 => R0
          end
  end.

(* =rol_sig= *)
Definition rol {A} (i: Ix)(xs: T A): T A
(* =end= *)
  := perm (fun j => add j i) xs.

(* =ror_sig= *)
Definition ror {A} (i: Ix)(xs: T A): T A
(* =end= *)
  := perm (fun j => sub j i) xs.

(*
Definition ror1 {A} (xs: T A): T A :=
  perm (fun i => match i with
                 | R0 => R3
                 | R1 => R0
                 | R2 => R1
                 | R3 => R2
                 end) xs.

Fixpoint ror {A} (xs: T A)(i: Ix): T A :=
  match i with
  | R0 => xs
  |  => ror1 (ror xs i)
  end.
*)

(*
Definition rol1 {A} (xs: T A): T A :=
  perm (fun i => match i with
                 | R0 => R1
                 | R1 => R2
                 | R2 => R3
                 | R3 => R0
                 end) xs.

Fixpoint rol {A} (xs: T A)(i: nat): T A :=
  match i with
  | 0 => xs
  | S i => rol1 (rol xs i)
  end.
*)

Definition xs : T Ix := indices Ix.

Example rol1_xs: rol R1 xs = Build_T R1 R2 R3 R0.
Proof. reflexivity. Qed.

Example rol3_xs: rol R3 xs = Build_T R3 R0 R1 R2.
Proof. reflexivity. Qed.

Example ror1_xs: ror R1 xs = Build_T R3 R0 R1 R2.
Proof. reflexivity. Qed.

Example ror3_xs: ror R3 xs = Build_T R1 R2 R3 R0.
Proof. reflexivity. Qed.
