(* Uniform representation of indexed types. *)

Require Import Coq.Lists.List.
Import ListNotations.

(* Not sure if that's what this is called. A telescope is a list of
   bindings where each binding can depend on the previous ones. *)
Fixpoint telescope (n : nat) : Type :=
  match n with
  | O => True
  | S n => sigT (fun t : Type => t -> telescope n)
  end.

(* A non-dependent list of types is a special kind of telescope. *)
Fixpoint list_to_telescope (ts : list Type) : telescope (length ts) :=
  match ts with
  | [] => I
  | t :: ts => existT _ t (fun _ => list_to_telescope ts)
  end.

Polymorphic Fixpoint product {n : nat} : telescope n -> Type :=
  match n with
  | O => fun _ => True
  | S n => fun ts => sigT (fun x : projT1 ts => product (projT2 ts x))
  end.

Polymorphic Fixpoint foralls_ {n : nat} :
  forall ts : telescope n, (product ts -> Type) -> Type :=
  match n with
  | O => fun _ res => res I
  | S n => fun ts res =>
    forall x : projT1 ts,
      foralls_ (projT2 ts x) (fun xs => res (existT _ x xs))
  end.

Notation "ts *-> r" := (foralls_ ts (fun _ => r))
(at level 100).

Notation "'foralls' xs : ts , t" := (foralls_ ts (fun xs => t))
(at level 100, xs, ts at level 10).

Polymorphic Fixpoint repeat (A : Type) (n : nat) : telescope n :=
  match n with
  | O => I
  | S n => existT _ A (fun _ => repeat A n)
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

Polymorphic Fixpoint uncurry {n : nat} :
  forall (ts : telescope n) (res : product ts -> Type),
    foralls_ ts res -> forall xs, res xs :=
  match n with
  | O => fun _ _ f 'I => f
  | S n => fun '(existT _ t ts) _ f '(existT _ x xs) =>
    uncurry (ts x) _ (f x) xs
  end.

Arguments uncurry {n ts res} f xs.

(* naive version *)
Polymorphic Fixpoint curry {n : nat} :
  forall (ts : telescope n) (res : product ts -> Type),
    (forall xs, res xs) -> foralls_ ts res :=
  match n with
  | O => fun _ _ f => f I
  | S n => fun '(existT _ t ts) _ f x =>
    curry (ts x) _ (fun xs => f (existT _ x xs))
  end.

Arguments curry {n ts res} f.

Notation "'funs' xs : ts => r" := (@curry _ ts _ (fun xs => r))
(at level 100, xs, ts at level 10).

Notation "'funs' xs : n * A => r" :=
  (@curry n (repeat A n) _ (fun xs => r))
(at level 100, xs, n at level 10).

Polymorphic Definition consts {n : nat} :
  forall (ts : telescope n) {A : Type} (a : A),
  ts *-> A :=
  fun ts _ a => funs xs : ts => a.

Polymorphic Fixpoint lift_curried {n : nat} :
  forall (ts : telescope n) {A B C : Type} (f : A -> B -> C),
    (ts *-> A) -> (ts *-> B) -> (ts *-> C) :=
  match n with
  | O => fun _ _ _ _ f a b => f a b
  | S n => fun ts _ _ _ f a b x =>
             lift_curried (projT2 ts x) f (a x) (b x)
  end.
