Require Import Coq.Lists.List.
Import ListNotations.

Require Import RecursionSchemes.Indexed.

Definition algebra (ts : list Type)
           (f : (ts *-> Type) -> (ts *-> Type))
           (g :  ts *-> Type ) : Type :=
  quantify ts (lift_curried ts (fun fga ga => fga -> ga) (f g) g).

(* Least fixed-point of a functor [f] in the category of
   [ts0 *-> Type]. *)
Definition Mu (ts0 : list Type)
           (f : (ts0 *-> Type) -> (ts0 *-> Type)) :
  ts0 *-> Type :=
  (fix Mu_ ts :
     (((ts *-> Type) -> Type) -> (ts0 *-> Type) -> Type) -> (ts *-> Type) :=
     match ts with
     | [] => fun ap =>
       forall g, algebra ts0 f g -> ap (fun x => x) g
     | t :: ts => fun ap =>
       fun x : t => Mu_ ts (fun k => ap (fun g' => k (g' x)))
     end) ts0 (fun k g => k g).
