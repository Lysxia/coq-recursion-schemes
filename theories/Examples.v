Require Coq.Lists.List.
Import List.ListNotations.

Require Import RecursionSchemes.Indexed.
Require Import RecursionSchemes.Fix.
Require Import RecursionSchemes.PCofix.

Example example_curried_0 : forall t, (Tip *-> t) = t.
Proof. reflexivity. Qed.

Example example_curried_1 :
  forall t1 t, (list_to_telescope [t1] *-> t) = (t1 -> t).
Proof. reflexivity. Qed.

Example example_curried_2 : forall t1 t2 t,
    (list_to_telescope [t1; t2] *-> t) = (t1 -> t2 -> t).
Proof. reflexivity. Qed.

Example example_lift_curried :
  forall t1 t2 s t u
         (f : s -> t -> u)
         (a : list_to_telescope [t1; t2] *-> s)
         (b : list_to_telescope [t1; t2] *-> t)
         (x1 : t1) (x2 : t2),
    lift_curried (list_to_telescope [t1; t2]) f a b x1 x2
    = f (a x1 x2) (b x1 x2).
Proof. reflexivity. Qed.

Example example_algebra : forall t1 t2 f g,
    algebra (list_to_telescope [t1; t2]) f g =
    (forall x1 x2, f g x1 x2 -> g x1 x2).
Proof. reflexivity. Qed.

Example example_mu : forall t1 t2 f x1 x2,
    mu (list_to_telescope [t1; t2]) f x1 x2 =
    forall g, algebra (list_to_telescope [t1; t2]) f g -> g x1 x2.
Proof. reflexivity. Qed.

Inductive listF (A : Type) (list_A : Type) :=
| nilF : listF A list_A
| consF : A -> list_A -> listF A list_A.

Arguments nilF {A list_A}.
Arguments consF {A list_A}.

Definition list' (A : Type) := mu Tip (listF A).

Definition from_list_ {A : Type} (xs : list A) : listF A (list A) :=
  match xs with
  | [] => nilF
  | x :: xs => consF x xs
  end%list.

Definition from_list {A : Type} (xs : list A) : list' A :=
  fun _ alg =>
    (fix fold xs :=
       match xs with
       | [] => alg nilF
       | x :: xs => alg (consF x (fold xs))
       end%list) xs.

Definition to_list {A : Type} (xs : list' A) : list A :=
  xs _ (fun xs =>
          match xs with
          | nilF => []
          | consF x xs => x :: xs
          end%list).

CoInductive stream :=
| Yield : nat -> stream.

Inductive zz_ (zz : list nat -> Prop) : list nat -> Prop :=
| ZZ : forall t, zz t -> zz_ zz (0 :: t).

Definition zz := paco 1 zz_ (bot 1).
