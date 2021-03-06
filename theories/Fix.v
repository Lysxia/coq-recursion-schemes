Require Import Coq.Lists.List.
Import ListNotations.

Require Import RecursionSchemes.Indexed.

Polymorphic Definition algebra {n : nat} (ts : telescope n)
           (f : (ts *-> Type) -> (ts *-> Type))
           (g :  ts *-> Type ) : Type :=
  foralls xs : ts, uncurry (f g) xs -> uncurry g xs.

(* Least fixed-point of a functor [f] in the category of
   [ts0 *-> Type]. *)
Polymorphic Definition mu {n : nat} (ts : telescope n)
           (f : (ts *-> Type) -> (ts *-> Type)) :
  ts *-> Type :=
  let ts0 := ts in
  (fix mu_ {n : nat} (ts : telescope n) :
     (((ts *-> Type) -> Type) -> (ts0 *-> Type) -> Type) -> (ts *-> Type) :=
     match ts with
     | Tip => fun ap =>
       forall g, algebra ts0 f g -> ap (fun x => x) g
     | Arr t ts => fun ap =>
       fun x : t => mu_ (ts x) (fun k => ap (fun g' => k (g' x)))
     end) _ ts0 (fun k g => k g).

(*
(* Shorter definition, but runs into universe inconsistency. *)
Polymorphic Definition mu (ts : list Type)
           (f : (ts *-> Type) -> (ts *-> Type)) :
  ts *-> Type :=
  funs xs : ts => forall g, algebra ts f g -> uncurry g xs.
*)
