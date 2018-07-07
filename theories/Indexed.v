(* Uniform representation of indexed types. *)

Require Import Coq.Lists.List.
Import ListNotations.

(* Monomorphism breaks [Mu] for some reason. *)
(* Keep polymorphism minimal for now in case I want to
   understand what's going on. *)
Polymorphic Definition curried (ts : list Type) (type : Type) : Type :=
  (fix curried_ (ts : list Type) :=
     match ts with
     | [] => type
     | t :: ts => t -> curried_ ts
     end) ts.

Infix "*->" := curried (at level 100).

Fixpoint lift_curried (ts : list Type) {A B C : Type}
         (f : A -> B -> C) :
  (ts *-> A) -> (ts *-> B) -> (ts *-> C) :=
  match ts with
  | [] => fun a b => f a b
  | t :: ts => fun a b x => lift_curried ts f (a x) (b x)
  end.

Fixpoint quantify (ts : list Type) :
  (ts *-> Type) -> Type :=
  match ts with
  | [] => fun f => f
  | t :: ts => fun f => forall x : t, quantify ts (f x)
  end.
