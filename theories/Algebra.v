(* =boolean= *)
Class Boolean (T: Type) :=
  { tt: T
  ; ff: T
  ; and: T -> T -> T
  ; or: T -> T -> T
  ; not: T -> T
  ; xor : T -> T -> T }.
(* =end= *)

(*
Class BooleanLaws {T} `(Boolean T) :=
  { assoc_or: forall a b c, or a (or b c) = or (or a b) c
  ; assoc_and: forall a b c, and a (and b c) = and (and a b) c
  ; comm_or: forall a b, or a b = or b a
  ; comm_and: forall a b, and a b = and b a
  ; abs_or_and: forall a b, or a (and a b) = a
  ; abs_and_or: forall a b, and a (or a b) = a
  ; id_or: forall a, or a ff = a
  ; id_and: forall a, and a tt = a
  ; distr_or_and: forall a b c, or a (and b c) = and (or a b) (or a c)
  ; distr_and_or: forall a b c, and a (or b c) = or (and a b) (and a c)
  ; compl_or: forall a, or a (not a) = tt
  ; compl_and: forall a, and a (not a) = ff }.
*)

(*
Definition xor {T} `{Boolean T} (x y: T): T :=
  and (or x y) (or (not x) (not y)).
*)

#[global]
  Instance Boolean_bool: Boolean bool :=
  { tt := true
  ; ff := false
  ; and := andb
  ; or := orb
  ; not := negb
  ; xor := xorb }.

(*
#[global,program]
  Instance BooleanLaws_bool : BooleanLaws Boolean_bool.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
*)

(* ******************************** *)

Implicit Type A B C: Type.
Implicit Type F: Type -> Type.

(* =Functor= *)
Class Functor F :=
  { map: forall A B, (A -> B) -> F A -> F B }.
(* =end= *)

Arguments map {F}{_}{A}{B} f fa.

(*
Class FunctorLaws {F} `(Functor F) :=
  { map_compose: forall A B C (f: B -> C)(g: A -> B) xs,
      map f (map g xs) = map (fun x => f (g x)) xs
  ; map_id: forall A (xs: F A),
      map (fun x => x) xs = xs }.
*)

#[global]
  Instance Functor_Comp {F G} `(Functor F, Functor G): Functor (fun X => F (G X)) :=
  { map := fun _ _ f fgs =>
             map (F := F) (map (F := G) f) fgs }.

(*
#[program,global]
  Instance FunctorLaws_Comp {F G}
  `(F_: Functor F,  G_: Functor G,
        FunctorLaws F, FunctorLaws G): FunctorLaws (Functor_Comp F_ G_).
Next Obligation.
Admitted.
Next Obligation.
Admitted.
*)

(* ******************************** *)

Implicit Type Ix: Type.

(* =Naperian= *)
Class Naperian {F} `(Functor F) Ix :=
  { lookup: forall A, F A -> Ix -> A
  ; init: forall A, (Ix -> A) -> F A }.
(* =end= *)

Arguments lookup {F}{_}{Ix}{_}{A} fa i.
Arguments init {F}{_}{Ix}{_}{A} f.

Section Derived.
  Variable A: Type.

  (* =indices= *)
  Variable Ix: Type.
  Variable F : Type -> Type.
  Context `{Naperian F Ix}.

  Definition indices: F Ix := init (fun ix => ix).
  (* =end= *)

  (* =perm= *)
  Definition perm (sigma: Ix -> Ix)(xs: F A): F A :=
    init (fun ix => lookup xs (sigma ix)).
  (* =end= *)

(*
  Definition swap (i j: Ix)(xs: F A): F A.
    (* XXX: need decidable equality on Ix. *)
  Admitted.
*)
End Derived.

Arguments indices Ix {F _ _}.
Arguments perm {A Ix F _ _} sigma xs.
(* Arguments swap {A Ix F _ _} i j xs. *)


(* =NaperianLaws= *)
Class NaperianLaws {F Ix} `(Naperian F Ix) :=
  { init_lookup: forall A (xs: F A),
      init (lookup xs) = xs
  ; lookup_init: forall A (f: Ix -> A)(ix: Ix),
      lookup (init f) ix = f ix }.
(* =end= *)


#[global]
  Instance Naperian_Comp {F G FIx GIx}
  `(F_: Functor F, G_: Functor G,
        Naperian F FIx, Naperian G GIx): Naperian (Functor_Comp F_ G_) (FIx * GIx) :=
  { lookup := fun _ xs '(i , j) =>
                lookup (F := G) (lookup (F := F) xs i) j
  ; init := fun _ f =>
              init (fun i =>
              init (F := G) (fun j =>
              f (i, j)))
  }.

(*
#[program, global]
  Instance NaperianLaws_Comp {F G FIx GIx}
  `(F_: Functor F, G_: Functor G,
    FN: Naperian F FIx,  GN: Naperian G GIx,
    NaperianLaws F FIx, NaperianLaws G GIx):
  NaperianLaws (Naperian_Comp F_ G_ FN GN).
Next Obligation. Admitted.
Next Obligation. Admitted.
*)

Section Derived.
  (* =reindex= *)
  Variables A FIx GIx: Type.
  Variable F G : Type -> Type.
  Context `{Naperian F FIx} `{Naperian G GIx}.

  Definition reindex (fgs : F (G A)): G (F A) :=
    init (fun j =>
    init (fun i =>
    lookup (lookup fgs i) j)).
  (* =end= *)

End Derived.

Arguments reindex {A}{FIx}{GIx}{F}{G}{_}{_}{_}{_} fgs.

Lemma idemp_reindex {A FIx GIx F G} `{Naperian F FIx} `{Naperian G GIx}:
  forall xs: F (G A),
    reindex (reindex xs) = xs.
Proof.
Admitted.

(* ******************************** *)

(* =Applicative= *)
Class Applicative {F} `(Functor F) :=
  { pure: forall A, A -> F A
  ; app: forall A B, F (A -> B) -> F A -> F B}.
(* =end= *)

Arguments pure {F _ _ A} a.
Arguments app {F _ _ A B} fs xs.

Section Derived.
  Variable F: Type -> Type.
  Context `{Functor F}.
  Context `{Applicative F}.

  Definition map2 {A B C} (f: A -> B -> C)(xs: F A)(ys: F B): F C :=
    app (app (pure f) xs) ys.

  Definition pair {A B} (xs: F A)(ys: F B): F (A * B) :=
    map2 (fun x y => (x, y)) xs ys.

End Derived.

Arguments map2 {F _ _ A B C} f xs ys.
Arguments pair {F _ _ A B} xs ys.

(*
Class ApplicativeLaws {F} `(Applicative F) :=
  (* XXX: check online *)
  { app_id: forall A (xs: F A),
      app (pure (fun x => x)) xs = xs
  ; pure_app: forall A B (f: A -> B)(xs: A),
      app (pure f) (pure xs) = pure (f xs)
  ; assoc: forall A B C (f: F (A -> B))(g: F (B -> C))(xs: F A),
      app (map2 (fun f g x => f (g x)) g f) xs = app g (app f xs)
  ; interchange: forall A B (y: A)(fs: F (A -> B)),
      app fs (pure y) = app (pure (fun f => f y)) fs }.
*)

#[global]
  Instance Applicative_Naperian {Ix F} `{F_: Functor F}`(Naperian F Ix): Applicative F_ :=
  { pure := fun _ a => init (fun _ => a)
  ; app := fun _ _ fs xs => init (fun i => lookup fs i (lookup xs i)) }.

(*
#[program, global]
  Instance ApplicativeLaws_Naperian {Ix F} `{Functor F}`(F_: Naperian F Ix): ApplicativeLaws (Applicative_Naperian F_).
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
*)

(*
Class CommutativeApplicativeLaws {F} `{F_: Applicative F}  `(ApplicativeLaws F) :=
  { commutative: forall {A B C} (f: A -> B -> C)(xs: F A)(ys: F B),
      map2 f xs ys = map2 (fun x y => f y x) ys xs
  }.
*)

(*
#[program, global]
  Instance CommutativeApplicativeLaws_Naperian {Ix F} `{Functor F}`(F_: Naperian F Ix): CommutativeApplicativeLaws (ApplicativeLaws_Naperian F_).
Next Obligation. Admitted.
*)

Section BooleanCommutativeApplicative.
  Variable B: Type.
  Context `{Boolean B}.
  Variable F: Type -> Type.
  Context `{F_ : Applicative F}.
(*  Context `{ApplicativeLaws F}. *)
  (* Context `{CommutativeApplicativeLaws F}. *)

  #[global]
    Instance Boolean_CommutativeApplicative: Boolean (F B) :=
    { tt := pure tt
    ; ff := pure ff
    ; and := map2 and
    ; or := map2 or
    ; not := map not
    ; xor := map2 xor }.

(*
  #[program, global]
    Instance BooleanLaws_CommutativeApplicative: BooleanLaws Boolean_CommutativeApplicative.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
*)

End BooleanCommutativeApplicative.

(* ******************************** *)

Implicit Type M : Type.


(* =Foldable= *)
Class Monoid M :=
  { nil : M
  ; append : M -> M -> M }.

Class Foldable {F} `(Functor F) :=
  { foldM: forall {M} `{M_ : Monoid M}, F M -> M }.
(* =end= *)

#[global]
  Instance Monoid_List {A}: Monoid (list A) :=
  { nil := Datatypes.nil
  ; append := fun xs ys => Datatypes.app xs ys }.

Section Derived.
  Variable F: Type -> Type.
  Context `{Foldable F}.

  Definition to_list {A} (xs: F A): list A :=
    foldM
      (map (fun x => cons x nil) xs).

(*
  Variable Ix: Type.
  Context `{Naperian F Ix}.

  Definition ror {A}(n: nat)(xs: F A): F A :=
    let ixs := indices Ix in
    let seqs := List.seq 0 (List.length (to_list ixs)) in
    let list_ixs := List.combine (to_list ixs)  in
    init (fun i => lookup xs i).

  Definition rol {A}(i: nat)(xs: F A): F A.
  Admitted.
*)

End Derived.

Arguments to_list {F _ _ A} xs.


(*
Class FoldableLaws {F} `(Foldable F).
  (* XXX: to be done *)

*)


(* ******************************** *)

(* =Circulant= *)
Class Circulant {F} `(Functor F) :=
  { circulant: forall A, F A -> F (F A)
  ; anticirculant: forall A, F A -> F (F A) }.
(* =end= *)

Arguments circulant {F _ _ A} xs.
Arguments anticirculant {F _ _ A} xs.

Section Derived.
  Variable F: Type -> Type.
  Variable Ix: Type.
  Context `(Circulant F).
  Context `(Naperian F Ix).

  (* =ror_rol_sig= *)
  Definition ror {A} (ix: Ix)(xs: F A): F A :=
    lookup (circulant xs) ix.
  Definition rol {A} (ix: Ix)(xs: F A): F A :=
    lookup (anticirculant xs) ix.
  (* =end= *)

End Derived.

Arguments rol {F Ix _ _ _ _ A} ix xs.
Arguments ror {F Ix _ _ _ _ A} ix xs.
