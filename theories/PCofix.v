Require Import Coq.Lists.List.
Import ListNotations.

Require Import RecursionSchemes.Indexed.

Notation ENDO T := (T -> T) (only parsing).
Notation FIX T := ((T -> T) -> (T -> T)).

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

Definition paco (ts : telescope) : FIX (ts *-> Prop) :=
  fun gf r => 
    curry
      (paco_ (fun pco => uncurry (gf (curry pco)))
             (uncurry r)).

Arguments paco {ts}.

Definition bot : forall (ts : telescope), ts *-> Prop :=
  fun ts => funs xs : ts => False.

Arguments bot {ts}.

Definition upaco (ts : telescope) : FIX (ts *-> Prop) :=
  fun gf r =>
    curry (fun xs =>
             uncurry (paco gf r) xs \/ uncurry r xs).

Arguments upaco {ts}.

Section PacoN.

Import TelescopeNotations.
Open Scope tele_scope.

Variable T0 : Type.
Variable T1 : forall (x0 : T0), Type.
Variable T2 : forall (x0 : T0) (x1 : T1 x0), Type.
Variable T3 : forall (x0 : T0) (x1 : T1 x0) (x2 : T2 x0 x1), Type.
Variable T4 : forall (x0 : T0) (x1 : T1 x0) (x2 : T2 x0 x1) (x3 : T3 x0 x1 x2), Type.

Definition paco0 : FIX Prop :=
  @paco [[ ]].
Definition paco1 : FIX (Tip >- T0 *-> Prop) :=
  @paco [[ (_ : T0) ]].
Definition paco2 : FIX (Tip >- T0 >- T1 *-> Prop) :=
  @paco [[ (x0 : T0) (x1 : T1 x0) ]].
Definition paco3 : FIX (Tip >- T0 >- T1 >- T2 *-> Prop) :=
  @paco [[ (x0 : T0) (x1 : T1 x0) (x2 : T2 x0 x1) ]].
Definition paco4 : FIX (Tip >- T0 >- T1 >- T2 >- T3 *-> Prop) :=
  @paco [[ (x0 : T0) (x1 : T1 x0) (x2 : T2 x0 x1)
           (x3 : T3 x0 x1 x2) ]].
Definition paco5 : FIX (Tip >- T0 >- T1 >- T2 >- T3 >- T4 *-> Prop) :=
  @paco [[ (x0 : T0) (x1 : T1 x0) (x2 : T2 x0 x1)
           (x3 : T3 x0 x1 x2) (x4 : T4 x0 x1 x2 x3) ]].

End PacoN.
