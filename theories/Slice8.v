Require Import Algebra.

Record T (A: Type) :=
  { s0: A; s1: A; s2: A; s3: A
  ; s4: A; s5: A; s6: A; s7: A }.

Arguments Build_T {_} s0 s1 s2 s3 s4 s5 s6 s7.
Arguments s0 {_}.
Arguments s1 {_}.
Arguments s2 {_}.
Arguments s3 {_}.
Arguments s4 {_}.
Arguments s5 {_}.
Arguments s6 {_}.
Arguments s7 {_}.

(* =Ix= *)
Inductive Ix :=
  | S0 | S1 | S2 | S3
  | S4 | S5 | S6 | S7.
(* =end= *)

Record Forall2 {A B}(R: A -> B -> Prop)(xs: T A)(ys: T B): Prop :=
  { p0: R xs.(s0) ys.(s0);
    p1: R xs.(s1) ys.(s1);
    p2: R xs.(s2) ys.(s2);
    p3: R xs.(s3) ys.(s3);
    p4: R xs.(s4) ys.(s4);
    p5: R xs.(s5) ys.(s5);
    p6: R xs.(s6) ys.(s6);
    p7: R xs.(s7) ys.(s7) }.

#[global]
  Instance Functor_T: Functor T :=
  { map := fun _ _ f d =>
             Build_T
               (f d.(s0)) (f d.(s1))
               (f d.(s2)) (f d.(s3))
               (f d.(s4)) (f d.(s5))
               (f d.(s6)) (f d.(s7)) }.

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
                | S4 => xs.(s4)
                | S5 => xs.(s5)
                | S6 => xs.(s6)
                | S7 => xs.(s7)
                end
  ; init := fun _ f => Build_T (f S0) (f S1) (f S2) (f S3)
                         (f S4) (f S5) (f S6) (f S7) }.

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
