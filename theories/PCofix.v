Require Import Coq.Lists.List.
Import ListNotations.

Require Import RecursionSchemes.Indexed.

CoInductive
  paco_ (T : Type)
  (gf : (T -> Prop) -> (T -> Prop))
  (r : T -> Prop)
  (x : T) : Prop :=
| paco_pfold_ (pco : T -> Prop) :
    (forall y, pco y -> paco_ T gf r y \/ r y) ->
    gf pco x ->
    paco_ T gf r x.

Arguments paco_ {T}.
Arguments paco_pfold_ {T gf r x} pco.

Notation "r --> r'" := (forall y, (r y : Prop) -> (r' y : Prop))
(at level 100).

Notation "r \_/ r'" := (fun y => r y \/ r' y)
(at level 50).

Definition monotone_ {T : Type} (gf : (T -> Prop) -> (T -> Prop)) :=
  forall (r r' : T -> Prop),
    (r --> r') ->
    forall x, gf r x -> gf r' x.

Require Import Paco.paco.

Theorem paco_acc_ {T : Type} (gf : (T -> Prop) -> (T -> Prop)) :
  forall l r,
    (forall rr, (r --> rr) -> (l --> rr) -> l --> paco_ gf rr) ->
    l --> paco_ gf r.
Proof.
  intros l r OBG x Plx.
  assert (SIM : paco_ gf (r \_/ l) x).
  { apply OBG; auto. }
  clear Plx.
  generalize dependent x.
  cofix paco_acc_.
  intros x SIM.
  destruct SIM as [pco LE SIM'].
  apply paco_pfold_ with (pco0 := pco).
  { intros y PRy. destruct (LE y) as [ | [ | ]]; auto. }
  auto.
Qed.

Theorem paco_mon_ (T : Type) (gf : (T -> Prop) -> (T -> Prop)) :
  monotone_ (paco_ gf).
Proof.
  intros r r' Hrr'.
  cofix paco_mon_.
  intros x [pco LE SIM].
  apply paco_pfold_ with (pco0 := pco).
  { intros y PRy; destruct (LE y); auto. }
  auto.
Qed.

(* Trick to help type inference. *)
Class Destruct {T : Type} (t : T).
Instance Destruct_Tip : Destruct I.
Instance Destruct_Arr {T : Type} (t : Type) (ts : t -> T)
         `(forall x : t, Destruct (ts x)) :
  Destruct (existT (fun t => t -> T) t (fun x => ts x)).

Definition paco
    (n : nat)
    (ts : telescope n) `{Destruct _ ts} :
  ((ts *-> Prop) -> (ts *-> Prop)) ->
  ((ts *-> Prop) -> (ts *-> Prop)) :=
  fun gf r => 
    curry
      (paco_ (fun pco => uncurry (gf (curry pco)))
             (uncurry r)).

Arguments paco n {ts _} gf r.

Definition
  bot (n : nat) :
    forall (ts : telescope n) `{Destruct _ ts},
      ts *-> Prop :=
  fun ts _ => funs xs : ts => False.

Arguments bot n {ts _}.

Definition upaco
    (n : nat)
    (ts : telescope n) `{Destruct _ ts} :
  ((ts *-> Prop) -> (ts *-> Prop)) ->
  ((ts *-> Prop) -> (ts *-> Prop)) :=
  fun gf r =>
    curry (fun xs =>
             uncurry (paco n gf r) xs \/ uncurry r xs).
