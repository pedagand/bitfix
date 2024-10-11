Require Import Algebra.

#[projections(primitive)]
 Record T (A : Type) :=
  { c0: A; c1: A; c2: A; c3: A }.

Arguments Build_T {_} c0 c1 c2 c3.
Arguments c0 {_}.
Arguments c1 {_}.
Arguments c2 {_}.
Arguments c3 {_}.

(* =Ix= *)
Inductive Ix := C0 | C1 | C2 | C3.
(* =end= *)

#[global]
  Instance Functor_T: Functor T :=
  { map := fun _ _ f d =>
             Build_T
               (f d.(c0)) (f d.(c1))
               (f d.(c2)) (f d.(c3)) }. 

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
                | C0 => xs.(c0)
                | C1 => xs.(c1)
                | C2 => xs.(c2)
                | C3 => xs.(c3)
                end
  ; init := fun _ f => Build_T (f C0) (f C1) (f C2) (f C3) }.

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
  | C0 => b
  | C1 => match b with
          | C0 => C1
          | C1 => C2
          | C2 => C3
          | C3 => C0
          end
  | C2 => match b with
          | C0 => C2
          | C1 => C3
          | C2 => C0
          | C3 => C1
          end
  | C3 => match b with
          | C0 => C3
          | C1 => C0
          | C2 => C1
          | C3 => C2
          end
  end.


Definition sub (b: Ix)(c: Ix): Ix :=
  match c with
  | C0 => b
  | C1 => match b with
          | C0 => C3
          | C1 => C0
          | C2 => C1
          | C3 => C2
          end
  | C2 => match b with
          | C0 => C2
          | C1 => C3
          | C2 => C0
          | C3 => C1
          end
  | C3 => match b with
          | C0 => C1
          | C1 => C2
          | C2 => C3
          | C3 => C0
          end
  end.

Definition rol {A} (i: Ix)(xs: T A): T A :=
  perm (fun j => add j i) xs.

Definition ror {A} (i: Ix)(xs: T A): T A :=
  perm (fun j => sub j i) xs.

(*
Definition ror1 {A} (xs: T A): T A :=
  perm (fun i => match i with
                 | C0 => C3
                 | C1 => C0
                 | C2 => C1
                 | C3 => C2
                 end) xs.

Fixpoint ror {A} (xs: T A)(i: nat): T A :=
  match i with
  | 0 => xs
  | S i => ror1 (ror xs i)
  end.

Definition rol1 {A} (xs: T A): T A :=
  perm (fun i => match i with
                 | C0 => C1
                 | C1 => C2
                 | C2 => C3
                 | C3 => C0
                 end) xs.

Fixpoint rol {A} (xs: T A)(i: nat): T A :=
  match i with
  | 0 => xs
  | S i => rol1 (rol xs i)
  end.
*)
