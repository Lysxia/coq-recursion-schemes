Require Import Coq.Lists.List.
Import ListNotations.

Require Import RecursionSchemes.Indexed.

CoInductive
  paco_ (T : Type)
  (gf : (T -> Prop) -> (T -> Prop))
  (r : T -> Prop)
  (x : T) : Prop :=
| paco_pfold (pco : T -> Prop) :
    (forall y, pco y -> paco_ T gf r y \/ r y) ->
    gf pco x ->
    paco_ T gf r x.

(* Trick to help type inference. *)
Class Destruct {T : Type} (t : T).
Instance Destruct_Pair (A B : Type) (a : A) (b : B) `{Destruct _ b} :
  Destruct (a, b).
Instance Destruct_Unit : Destruct tt.

Definition paco
    (n : nat)
    (ts : product (repeat Type n)) `{Destruct _ ts} :
  let ts := forget ts in
  ((ts *-> Prop) -> (ts *-> Prop)) ->
  ((ts *-> Prop) -> (ts *-> Prop)) :=
  fun gf r => 
    curry
      (paco_ _
             (fun pco => uncurry (gf (curry pco)))
             (uncurry r)).

Arguments paco n {ts _} gf r.

Definition
  bot (n : nat) :
    forall (ts : product (repeat Type n)) `{Destruct _ ts},
      forget ts *-> Prop :=
  fun ts _ => funs xs : forget ts => False.

Arguments bot n {ts _}.

Definition upaco
    (n : nat)
    (ts : product (repeat Type n)) `{Destruct _ ts} :
  let ts := forget ts in
  ((ts *-> Prop) -> (ts *-> Prop)) ->
  ((ts *-> Prop) -> (ts *-> Prop)) :=
  fun gf r =>
    curry (fun xs =>
             uncurry (paco n gf r) xs \/ uncurry r xs).
