(* Uniform representation of indexed types. *)

Require Import Coq.Lists.List.
Import ListNotations.

Polymorphic Fixpoint product (ts : list Type) : Type :=
  match ts with
  | [] => unit
  | t :: ts => t * product ts
  end.

(* Monomorphism breaks [Mu] for some reason. *)
(* Keep polymorphism minimal for now in case I want to
   understand what's going on. *)
Polymorphic Fixpoint foralls_ (ts : list Type) :
  (product ts -> Type) -> Type :=
  match ts with
  | [] => fun res => res tt
  | t :: ts => fun res =>
    forall x : t, foralls_ ts (fun xs => res (x, xs))
  end.

Notation "ts *-> r" := (foralls_ ts (fun _ => r))
(at level 100).

Notation "'foralls' xs : ts , t" := (foralls_ ts (fun xs => t))
(at level 100, xs, ts at level 10).

Polymorphic Fixpoint repeat (A : Type) (n : nat) : list Type :=
  match n with
  | O => []
  | S n => A :: repeat A n
  end.

Notation "'foralls' xs : n * A , t" :=
  (foralls_ (repeat A n) (fun xs => t))
(at level 100, xs, n at level 10).

Polymorphic Fixpoint uncurry (ts : list Type) :
  forall (res : product ts -> Type),
    foralls_ ts res -> forall xs, res xs :=
  match ts with
  | [] => fun _ f 'tt => f
  | t :: ts => fun _ f '(x, xs) => uncurry ts _ (f x) xs
  end.

Arguments uncurry {ts res} f xs.

(* naive version *)
Polymorphic Fixpoint curry (ts : list Type) :
  forall (res : product ts -> Type),
    (forall xs, res xs) -> foralls_ ts res :=
  match ts with
  | [] => fun _ f => f tt
  | t :: ts => fun _ f x => curry ts _ (fun xs => f (x, xs))
  end.

Arguments curry {ts res} f.

Notation "'funs' xs : ts => r" := (@curry ts _ (fun xs => r))
(at level 100, xs, ts at level 10).

Notation "'funs' xs : n * A => r" :=
  (@curry (repeat A n) _ (fun xs => r))
(at level 100, xs, n at level 10).

Polymorphic Definition consts (ts : list Type) {A : Type} (a : A) :
  ts *-> A :=
  (fix pure ts : ts *-> A :=
     match ts with
     | [] => a
     | t :: ts => fun _ => pure ts
     end) ts.

Polymorphic Fixpoint lift_curried (ts : list Type) {A B C : Type}
         (f : A -> B -> C) :
  (ts *-> A) -> (ts *-> B) -> (ts *-> C) :=
  match ts with
  | [] => fun a b => f a b
  | t :: ts => fun a b x => lift_curried ts f (a x) (b x)
  end.
