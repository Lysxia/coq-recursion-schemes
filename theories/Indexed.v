(* Uniform representation of indexed types. *)

Require Import Coq.Lists.List.
Import ListNotations.

(* Not sure if that's what this is called
   In Richard Eisenberg's thesis, a telescope is a list of
   bindings where each binding can depend on the previous ones. *)
Polymorphic Inductive telescope : Type :=
| Tip : telescope
| Arr : forall t : Type, (t -> telescope) -> telescope.

(* A non-dependent list of types is a special kind of telescope. *)
Fixpoint list_to_telescope (ts : list Type) : telescope :=
  match ts with
  | [] => Tip
  | t :: ts => Arr t (fun _ => list_to_telescope ts)
  end.

Polymorphic Fixpoint product (ts : telescope) : Type :=
  match ts with
  | Tip => unit
  | Arr t ts => sigT (fun x : t => product (ts x))
  end.

Polymorphic Fixpoint foralls_ (ts : telescope) :
  (product ts -> Type) -> Type :=
  match ts with
  | Tip => fun res => res tt
  | Arr t ts => fun res =>
    forall x : t, foralls_ (ts x) (fun xs => res (existT _ x xs))
  end.

Notation "ts *-> r" := (foralls_ ts (fun _ => r))
(at level 100).

Notation "'foralls' xs : ts , t" := (foralls_ ts (fun xs => t))
(at level 100, xs, ts at level 10).

Polymorphic Fixpoint repeat (A : Type) (n : nat) : telescope :=
  match n with
  | O => Tip
  | S n => Arr A (fun _ => repeat A n)
  end.

Polymorphic Fixpoint forget {A : Type} {n : nat}
            (xs : product (repeat A n)) : list A :=
  match n, xs with
  | O, _ => []
  | S n, existT _ x xs => x :: forget xs
  end.

Notation "'foralls' xs : n * A , t" :=
  (foralls_ (repeat A n) (fun xs => t))
(at level 100, xs, n at level 10).

Polymorphic Fixpoint uncurry (ts : telescope) :
  forall (res : product ts -> Type),
    foralls_ ts res -> forall xs, res xs :=
  match ts with
  | Tip => fun _ f 'tt => f
  | Arr t ts => fun _ f '(existT _ x xs) =>
    uncurry (ts x) _ (f x) xs
  end.

Arguments uncurry {ts res} f xs.

(* naive version *)
Polymorphic Fixpoint curry (ts : telescope) :
  forall (res : product ts -> Type),
    (forall xs, res xs) -> foralls_ ts res :=
  match ts with
  | Tip => fun _ f => f tt
  | Arr t ts => fun _ f x =>
    curry (ts x) _ (fun xs => f (existT _ x xs))
  end.

Arguments curry {ts res} f.

Notation "'funs' xs : ts => r" := (@curry ts _ (fun xs => r))
(at level 100, xs, ts at level 10).

Notation "'funs' xs : n * A => r" :=
  (@curry (repeat A n) _ (fun xs => r))
(at level 100, xs, n at level 10).

Polymorphic Definition consts (ts : telescope) {A : Type} (a : A) :
  ts *-> A :=
  (fix pure ts : ts *-> A :=
     match ts with
     | Tip => a
     | Arr t ts => fun x => pure (ts x)
     end) ts.

Polymorphic Fixpoint lift_curried (ts : telescope) {A B C : Type}
         (f : A -> B -> C) :
  (ts *-> A) -> (ts *-> B) -> (ts *-> C) :=
  match ts with
  | Tip => fun a b => f a b
  | Arr t ts => fun a b x => lift_curried (ts x) f (a x) (b x)
  end.

Fixpoint extend (ts : telescope) : (ts *-> Type) -> telescope :=
  match ts with
  | Tip => fun f => Arr f (fun _ => Tip)
  | Arr t ts => fun f => Arr t (fun x => extend (ts x) (f x))
  end.

Infix ">-" := extend (at level 40, left associativity).

Module TelescopeNotations.

Notation "[[ ]]" := Tip : tele_scope.
Notation "[[ a1 .. an ]]" :=
  (Arr _ (fun a1 => .. (Arr _ (fun an => Tip)) .. ))
(a1 binder, an binder) : tele_scope.

End TelescopeNotations.
