Require Import Coq.Lists.List.
Import ListNotations.

Require Import RecursionSchemes.Indexed.

Require Import Paco.paconotation.

Local Notation ENDO T := (T -> T) (only parsing).
Local Notation FIX T := ((T -> T) -> (T -> T)).

CoInductive
  paco1 (T : Type)
  (gf : (T -> Prop) -> (T -> Prop))
  (r : T -> Prop)
  (x : T) : Prop :=
| paco_pfold1 (pco : T -> Prop) :
    (forall y, pco y -> paco1 T gf r y \/ r y) ->
    gf pco x ->
    paco1 T gf r x.

Arguments paco1 {T}.
Arguments paco_pfold1 {T gf r x} pco.

Definition monotone1 {T : Type} (gf : (T -> Prop) -> (T -> Prop)) :=
  forall (r r' : T -> Prop),
    (r <1= r') ->
    (gf r <1= gf r').

Require Paco.paco.
About paco2.monotone2.

Definition rel_ (n : nat) : FORALLS_ n (fun _ => Type) :=
  FUNS_ n _ (fun ts => ts *-> Prop).

Definition monotone_ (n : nat) : FORALLS_ n (fun ts =>
                                            )

Theorem paco_acc1 {T : Type} (gf : (T -> Prop) -> (T -> Prop)) :
  forall l r,
    (forall rr, (r <1= rr) -> (l <1= rr) -> l <1= paco1 gf rr) ->
    l <1= paco1 gf r.
Proof.
  intros l r OBG x Plx.
  assert (SIM : paco1 gf (r \1/ l) x).
  { apply OBG; auto. }
  clear Plx.
  generalize dependent x.
  cofix paco_acc_.
  intros x SIM.
  destruct SIM as [pco LE SIM'].
  apply paco_pfold1 with (pco0 := pco).
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

Definition paco (n : nat) (ts : telescope n) : FIX (ts *-> Prop) :=
  fun gf r => 
    curry
      (paco_ (fun pco => uncurry (gf (curry pco)))
             (uncurry r)).

Arguments paco n {ts}.

Definition bot (n : nat) (ts : telescope n) : ts *-> Prop :=
  funs xs : ts => False.

Arguments bot n {ts}.

Definition upaco (n : nat) (ts : telescope n) : FIX (ts *-> Prop) :=
  fun gf r =>
    curry (fun xs =>
             uncurry (paco n gf r) xs \/ uncurry r xs).

Arguments upaco n {ts}.

Section PacoN.

Import TelescopeNotations.
Open Scope tele_scope.

Variable T0 : Type.
Variable T1 : forall (x0 : T0), Type.
Variable T2 : forall (x0 : T0) (x1 : T1 x0), Type.
Variable T3 : forall (x0 : T0) (x1 : T1 x0) (x2 : T2 x0 x1), Type.
Variable T4 : forall (x0 : T0) (x1 : T1 x0) (x2 : T2 x0 x1) (x3 : T3 x0 x1 x2), Type.

Definition paco0 : FIX Prop :=
  @paco 0 [[ ]].
Definition paco1 : FIX (Tip >- T0 *-> Prop) :=
  @paco 1 [[ (_ : T0) ]].
Definition paco2 : FIX (Tip >- T0 >- T1 *-> Prop) :=
  @paco 2 [[ (x0 : T0) (x1 : T1 x0) ]].
Definition paco3 : FIX (Tip >- T0 >- T1 >- T2 *-> Prop) :=
  @paco 3 [[ (x0 : T0) (x1 : T1 x0) (x2 : T2 x0 x1) ]].
Definition paco4 : FIX (Tip >- T0 >- T1 >- T2 >- T3 *-> Prop) :=
  @paco 4 [[ (x0 : T0) (x1 : T1 x0) (x2 : T2 x0 x1)
           (x3 : T3 x0 x1 x2) ]].
Definition paco5 : FIX (Tip >- T0 >- T1 >- T2 >- T3 >- T4 *-> Prop) :=
  @paco 5 [[ (x0 : T0) (x1 : T1 x0) (x2 : T2 x0 x1)
           (x3 : T3 x0 x1 x2) (x4 : T4 x0 x1 x2 x3) ]].

End PacoN.
