Require Import Algebra.

#[projections(primitive)]
 Record T (A : Type) := { fst: A ; snd: A }.

Arguments Build_T {A} fst snd.
Arguments fst {A}.
Arguments snd {A}.

Inductive Ix := Fst | Snd.


#[global] Instance Functor_Double: Functor T :=
  { map := fun _ _ f d =>
             Build_T (f d.(fst)) (f d.(snd)) }.

(*
#[global, program] Instance FunctorLaws_Double: FunctorLaws Functor_Double.
Next Obligation. auto. Qed.
Next Obligation. destruct xs; auto. Qed.
*)

#[global] Instance Naperian_Double: Naperian Functor_Double Ix :=
  { lookup := fun _ xs i =>
                match i with
                | Fst => xs.(fst)
                | Snd => xs.(snd)
                end
  ; init := fun _ f => Build_T (f Fst) (f Snd) }.

(*
#[global, program] Instance NaperianLaws_Double: NaperianLaws Naperian_Double.
Next Obligation. destruct xs; auto. Qed.
Next Obligation. intros ? ? i; case i; auto. Qed.
*)

#[global]
  Instance Foldable_Double: Foldable Functor_Double :=
  { foldM := fun _ _ xs => append xs.(fst) xs.(snd) }. 

(*
#[program, global]
  Instance FoldableLaws_Double: FoldableLaws Foldable_Double.
*)
