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

Module Examples.

Example example_curried_0 : forall t, ([] *-> t) = t.
Proof. reflexivity. Qed.

Example example_curried_1 : forall t1 t, ([t1] *-> t) = (t1 -> t).
Proof. reflexivity. Qed.

Example example_curried_2 : forall t1 t2 t,
    ([t1; t2] *-> t) = (t1 -> t2 -> t).
Proof. reflexivity. Qed.

Example example_lift_curried :
  forall t1 t2 s t u
         (f : s -> t -> u) (a : [t1; t2] *-> s) (b : [t1; t2] *-> t)
         (x1 : t1) (x2 : t2),
    lift_curried [t1; t2] f a b x1 x2 = f (a x1 x2) (b x1 x2).
Proof. reflexivity. Qed.

Example example_algebra : forall t1 t2 f g,
    algebra [t1; t2] f g =
    (forall x1 x2, f g x1 x2 -> g x1 x2).
Proof. reflexivity. Qed.

Example example_Mu : forall t1 t2 f x1 x2,
    Mu [t1; t2] f x1 x2 =
    forall g, algebra [t1; t2] f g -> g x1 x2.
Proof. reflexivity. Qed.

Inductive listF (A : Type) (list_A : Type) :=
| nilF : listF A list_A
| consF : A -> list_A -> listF A list_A.

Arguments nilF {A list_A}.
Arguments consF {A list_A}.

Definition list' (A : Type) := Mu [] (listF A).

Definition from_list_ {A : Type} (xs : list A) : listF A (list A) :=
  match xs with
  | [] => nilF
  | x :: xs => consF x xs
  end.

Definition from_list {A : Type} (xs : list A) : list' A :=
  fun _ alg =>
    (fix fold xs :=
       match xs with
       | [] => alg nilF
       | x :: xs => alg (consF x (fold xs))
       end) xs.

Definition to_list {A : Type} (xs : list' A) : list A :=
  xs _ (fun xs =>
          match xs with
          | nilF => []
          | consF x xs => x :: xs
          end).

End Examples.
