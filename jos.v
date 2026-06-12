Set Implicit Arguments.

Record ADT (E : Type) (S : Type) := {
  etats : Type ;
  transition : etats -> E -> etats * S ;
  initial : etats
}.

Record Histoire (A : Type) := {
  events : Type ;
  label : events -> A ;
  ord : events -> events -> Type ;
  refl : forall a, ord a a ;
  trans : forall a b c, ord a b -> ord b c -> ord a c
}.

Record Seq (A : Type) := {
  seq :> nat -> option A ;
  does_not_restart : forall n, seq n = None -> seq (S n) = None
}.

Fixpoint eval {E Sor} (A : ADT E Sor) (aseq : Seq E) (n : nat) : A.(etats) :=
  match n with
  | 0 => A.(initial)
  | S n => match aseq n with
    | None => eval A aseq n
    | Some a => fst (A.(transition) (eval A aseq n) a)
    end
  end.

#[refine]
Definition ADTSeq {E S} (A : ADT E S) (aseq : Seq E) : Seq (E * S) := {|
  seq := fun n => option_map (fun e => (e , snd (A.(transition) (eval A aseq n) e))) (aseq n) ;
  does_not_restart := _
|}.
Proof.
  intros n H.
  pose proof (DNR := does_not_restart aseq n).
  destruct (aseq n).
  - discriminate H.
  - rewrite (DNR eq_refl).
    reflexivity.
Defined.

Record EventSeq {A} (H : Histoire A) (eseq : Seq (H.(events))) := {
  monotone : forall n a b, eseq n = Some a -> eseq (S n) = Some b -> H.(ord) a b ;
  exhausts : forall e, { n : nat & eseq n = Some e }
}.

#[refine]
Definition Ba {A} {H : Histoire A} (eseq : Seq H.(events)) : Seq A := {|
  seq := fun n => (option_map (fun ev => H.(label) ev) (eseq n))
|}.
Proof.
  intros n H1.
  pose proof (DNR := does_not_restart eseq n).
  destruct (eseq n).
  - discriminate H1.
  - rewrite (DNR eq_refl).
    reflexivity.
Defined.

Definition crit_seq {E S} (A : ADT E S) (H : Histoire (E * S)) : Type :=
  { aseq : Seq E &
    {eseq : Seq (H.(events)) & EventSeq H eseq * forall n, ADTSeq A aseq n = Ba eseq n} }.


Definition crit_entoehunteh : ADT E S -> Histoire (E * (option S)) -> Type.
