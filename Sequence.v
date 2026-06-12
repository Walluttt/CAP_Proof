Require Import List Arith PeanoNat Bool Lia.
Import ListNotations.


Section FOIF_Sequence.
  Variable A : Type.
  Variable skip_elem : A.

  (* 1. DÉFINITION DE LA SÉQUENCE *)
  Definition Sequence := nat -> A.

  (* 2. DÉFINITION FINIE *)
  (* Il existe un N à partir duquel on ne fait plus que des "skip" *)
  Definition is_finite (seq : Sequence) : Prop :=
    exists N, forall n, n >= N -> seq n = skip_elem.

  (* 3. DÉFINITION INFINIE (Version Constructive Positive) *)
  (* "Pour n'importe quel instant N, je peux toujours trouver un instant m plus tard 
     où il se passe quelque chose de concret (pas un skip)." *)
  Definition is_infinite (seq : Sequence) : Prop :=
    forall N, exists m, m >= N /\ seq m <> skip_elem.

  (* 4. LE LEMME DEVIENT TRIVIAL *)
  Lemma infinite_implies_always_next : forall (seq : Sequence) (N : nat),
    is_infinite seq -> exists m, m >= N /\ seq m <> skip_elem.
  Proof.
    intros seq N Hinf. (* L'ordre est le bon cette fois *)
    (* Comme notre définition de is_infinite correspond exactement au but, 
       on a juste à appliquer l'hypothèse. *)
    apply Hinf.
  Qed.

End FOIF_Sequence.