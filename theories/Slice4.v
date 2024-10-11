Require Import Algebra.

#[projections(primitive)]
 Record T (A: Type) :=
  { s0: A; s1: A; s2: A; s3: A}.

Arguments Build_T {_} s0 s1 s2 s3.
Arguments s0 {_}.
Arguments s1 {_}.
Arguments s2 {_}.
Arguments s3 {_}.

Definition of_int n :=
  match n with
  | 0 => Build_T false false false false
  | 1 => Build_T true false false false
  | 2 => Build_T false true false false
  | 3 => Build_T true true false false
  | 4 => Build_T false false true false
  | 5 => Build_T true false true false
  | 6 => Build_T false true true false
  | 7 => Build_T true true true false
  | 8 => Build_T false false false true
  | 9 => Build_T true false false true
  | 10 => Build_T false true false true
  | 11 => Build_T true true false true
  | 12 => Build_T false false true true
  | 13 => Build_T true false true true
  | 14 => Build_T false true true true
  | 15 => Build_T true true true true
  | _ => Build_T false false false true
  end.

Inductive Ix := S0 | S1 | S2 | S3.

Record Forall2 {A B}(R: A -> B -> Prop)(xs: T A)(ys: T B): Prop :=
  { p0: R xs.(s0) ys.(s0);
    p1: R xs.(s1) ys.(s1);
    p2: R xs.(s2) ys.(s2);
    p3: R xs.(s3) ys.(s3) }.

#[global]
  Instance Functor_T: Functor T :=
  { map := fun _ _ f d =>
             Build_T
               (f d.(s0)) (f d.(s1))
               (f d.(s2)) (f d.(s3)) }.

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
                | S0 => xs.(s0)
                | S1 => xs.(s1)
                | S2 => xs.(s2)
                | S3 => xs.(s3)
                end
  ; init := fun _ f => Build_T (f S0) (f S1) (f S2) (f S3) }.

(*
#[global, program]
  Instance NaperianLaws_T: NaperianLaws Naperian_T.
Next Obligation. Admitted.
Next Obligation. Admitted.
*)

(*
#[global]
  Instance Foldable_T: Foldable Functor_T.
Admitted.
*)
(*
  { foldM := fun _ _ xs => append xs.(fst) xs.(snd) }. *)

(*
#[program, global]
  Instance FoldableLaws_T: FoldableLaws Foldable_T.
*)
