(* ================================================================== *)
(*  PREUVE CONSTRUCTIVE DU THÉORÈME CAP                                *)
(* ================================================================== *)

Require Import List Arith PeanoNat Bool.
Import ListNotations.

(* ================================================================== *)
(*  SECTION 1 : TOPOLOGIE DU RÉSEAU                                   *)
(* ================================================================== *)

Definition Proc := bool.
Definition Var  := bool.
Definition Value := nat.

Record Link := mkLink {
  src : Proc;
  dst : Proc;
  src_neq_dst : src <> dst
}.

Definition link_p_to_p' : Link := mkLink true false diff_true_false.
Definition link_p'_to_p : Link := mkLink false true diff_false_true.
Definition all_links : list Link := [link_p_to_p'; link_p'_to_p].

(* ================================================================== *)
(*  SECTION 2 : PARTITION                                              *)
(* ================================================================== *)

Definition FaultConfig := Link -> bool.

Definition is_partitioned (f : FaultConfig) : Prop :=
  forall l, f l = false.

(* ================================================================== *)
(*  SECTION 3 : OPÉRATIONS                                            *)
(* ================================================================== *)

Inductive Operation :=
  | Write : Proc -> Var -> Value -> Operation
  | Read  : Proc -> Var -> Value -> Operation.

(* ================================================================== *)
(*  SECTION 4 : ÉTAT                                                   *)
(* ================================================================== *)

Record State := mkState {
  mem     : Proc -> Var -> Value;
  history : list Operation
}.

Definition update_mem (m : Proc -> Var -> Value)
                      (i : Proc) (v : Var) (val : Value)
                      : Proc -> Var -> Value :=
  fun proc var =>
    if (Bool.eqb proc i) && (Bool.eqb var v) then val
    else m proc var.

Definition init_mem : Proc -> Var -> Value := fun _ _ => 0.
Definition init_state : State := mkState init_mem [].

(* ================================================================== *)
(*  SECTION 5 : TRANSITIONS                                           *)
(* ================================================================== *)

Inductive Step (f : FaultConfig) : State -> State -> Prop :=
  | step_write : forall s (i : Proc) (val : Value),
      Step f s (mkState
        (update_mem (mem s) i i val)
        (Write i i val :: history s))
  | step_read : forall s (i : Proc) (v : Var),
      Step f s (mkState
        (mem s)
        (Read i v (mem s i v) :: history s))
  | step_propagate : forall s (l : Link) (val : Value),
      f l = true ->
      mem s (src l) (src l) = val ->
      Step f s (mkState
        (update_mem (mem s) (dst l) (src l) val)
        (history s)).

(* ================================================================== *)
(*  SECTION 6 : ACCESSIBILITÉ                                         *)
(* ================================================================== *)

Inductive Reachable (f : FaultConfig) : State -> Prop :=
  | reach_init : Reachable f init_state
  | reach_step : forall s1 s2,
      Reachable f s1 -> Step f s1 s2 -> Reachable f s2.

(* ================================================================== *)
(*  SECTION 7 : AVAILABILITY — WAIT-FREE                              *)
(* ================================================================== *)

Inductive WriteStep (f : FaultConfig) (i : Proc) (val : Value)
  : State -> State -> Prop :=
  | do_write : forall s,
      WriteStep f i val s (mkState
        (update_mem (mem s) i i val)
        (Write i i val :: history s)).

Inductive ReadStep (f : FaultConfig) (i : Proc) (v : Var)
  : State -> State -> Prop :=
  | do_read : forall s,
      ReadStep f i v s (mkState
        (mem s)
        (Read i v (mem s i v) :: history s)).

Lemma write_is_step : forall f i val s s',
  WriteStep f i val s s' -> Step f s s'.
Proof. intros. destruct H. apply (step_write f s i val). Qed.

Lemma read_is_step : forall f i v s s',
  ReadStep f i v s s' -> Step f s s'.
Proof. intros. destruct H. apply (step_read f s i v). Qed.

Definition wait_free_write (f : FaultConfig) : Prop :=
  forall s, Reachable f s ->
    forall i val, exists s', WriteStep f i val s s'.

Definition wait_free_read (f : FaultConfig) : Prop :=
  forall s, Reachable f s ->
    forall i v, exists s', ReadStep f i v s s'.

Definition wait_free_available (f : FaultConfig) : Prop :=
  wait_free_write f /\ wait_free_read f.

Theorem system_is_wait_free : forall f, wait_free_available f.
Proof.
  intro f. split.
  - intros s _ i val. eexists. apply do_write.
  - intros s _ i v. eexists. apply do_read.
Qed.

(* ================================================================== *)
(*  SECTION 8 : CONSISTENCY — RW1 (décidable)                         *)
(* ================================================================== *)

Definition op_eqb (o1 o2 : Operation) : bool :=
  match o1, o2 with
  | Write i1 v1 n1, Write i2 v2 n2 =>
      Bool.eqb i1 i2 && Bool.eqb v1 v2 && Nat.eqb n1 n2
  | Read i1 v1 n1, Read i2 v2 n2 =>
      Bool.eqb i1 i2 && Bool.eqb v1 v2 && Nat.eqb n1 n2
  | _, _ => false
  end.

Definition in_list (o : Operation) (h : list Operation) : bool :=
  existsb (op_eqb o) h.

Definition has_RW1_pattern_b (h : list Operation) : bool :=
  in_list (Write true  true  1) h &&
  in_list (Read  true  false 0) h &&
  in_list (Write false false 1) h &&
  in_list (Read  false true  0) h.

Definition consistent (f : FaultConfig) : Prop :=
  forall s, Reachable f s -> has_RW1_pattern_b (history s) = false.

(* ================================================================== *)
(*  SECTION 9 : LEMMES MÉMOIRE                                        *)
(* ================================================================== *)

Lemma update_mem_same : forall m i val,
  update_mem m i i val i i = val.
Proof.
  intros. unfold update_mem.
  rewrite Bool.eqb_reflx. simpl. reflexivity.
Qed.

Lemma update_mem_other : forall m i val j v,
  (j <> i \/ v <> i) ->
  update_mem m i i val j v = m j v.
Proof.
  intros m i val j v Hdiff.
  unfold update_mem.
  destruct (Bool.eqb j i) eqn:Hj;
  destruct (Bool.eqb v i) eqn:Hv;
  simpl; try reflexivity.
  apply Bool.eqb_prop in Hj.
  apply Bool.eqb_prop in Hv.
  subst. destruct Hdiff; contradiction.
Qed.

(* ================================================================== *)
(*  SECTION 10 : INVARIANT DE PARTITION                                *)
(* ================================================================== *)

Lemma no_propagation_under_partition :
  forall f, is_partitioned f ->
    forall s s', Step f s s' ->
      (exists i val, s' = mkState
        (update_mem (mem s) i i val)
        (Write i i val :: history s))
      \/
      (exists i v, s' = mkState
        (mem s)
        (Read i v (mem s i v) :: history s)).
Proof.
  intros f Hpart s s' Hstep.
  inversion Hstep; subst.
  - left. exists i, val. reflexivity.
  - right. exists i, v. reflexivity.
  - exfalso. specialize (Hpart l). rewrite Hpart in H. discriminate.
Qed.

Lemma cross_memory_invariant :
  forall f, is_partitioned f ->
    forall s, Reachable f s ->
      forall i, mem s (negb i) i = 0.
Proof.
  intros f Hpart s Hreach.
  induction Hreach as [| s1 s2 Hreach1 IH Hstep].
  - intro i. reflexivity.
  - intro i.
    destruct (no_propagation_under_partition f Hpart s1 s2 Hstep)
      as [[j [val Heq]] | [j [v Heq]]]; subst; simpl.
    + unfold update_mem.
      destruct (Bool.eqb (negb i) j) eqn:E1;
      destruct (Bool.eqb i j) eqn:E2;
      simpl; try apply IH.
      apply Bool.eqb_prop in E1.
      apply Bool.eqb_prop in E2.
      subst. destruct i; discriminate.
    + apply IH.
Qed.

(* ================================================================== *)
(*  SECTION 11 : LEMME in_list                                        *)
(* ================================================================== *)

Lemma op_eqb_refl : forall o, op_eqb o o = true.
Proof.
  destruct o; simpl;
  repeat rewrite Bool.eqb_reflx;
  rewrite Nat.eqb_refl; reflexivity.
Qed.

Lemma in_list_head : forall o h,
  in_list o (o :: h) = true.
Proof.
  intros. unfold in_list. simpl.
  rewrite op_eqb_refl. reflexivity.
Qed.

Lemma in_list_tail : forall o a h,
  in_list o h = true -> in_list o (a :: h) = true.
Proof.
  intros. unfold in_list in *. simpl.
  rewrite H. apply Bool.orb_true_r.
Qed.

(* ================================================================== *)
(*  SECTION 12 : THÉORÈME CAP                                         *)
(* ================================================================== *)

Theorem CAP_impossibility :
  forall f : FaultConfig,
    is_partitioned f ->
    wait_free_available f ->
    ~ consistent f.
Proof.
  intros f Hpart [Hwf_w Hwf_r] Hcons.

  (* === Étape 1 : p écrit x = 1 === *)
  (* Par Hwf_w, p peut écrire depuis init_state *)
  destruct (Hwf_w init_state (reach_init f) true 1) as [sa Hsa].
  inversion Hsa; subst. clear Hsa.
  (* sa = mkState (update_mem init_mem true true 1)
                   [Write true true 1] *)
  remember (mkState (update_mem init_mem true true 1)
                    [Write true true 1]) as state_a eqn:Hdef_a.
  assert (Ra : Reachable f state_a).
  { subst. apply reach_step with init_state.
    - apply reach_init.
    - apply (step_write f init_state true 1). }

  (* === Étape 2 : p' écrit x' = 1 === *)
  destruct (Hwf_w state_a Ra false 1) as [sb Hsb].
  inversion Hsb; subst. clear Hsb.
  remember (mkState (update_mem (mem state_a) false false 1)
                    (Write false false 1 :: history state_a)) as state_b eqn:Hdef_b.
  assert (Rb : Reachable f state_b).
  { subst. apply reach_step with state_a.
    - exact Ra.
    - apply (step_write f state_a false 1). }

  (* === Étape 3 : p lit x' === *)
  destruct (Hwf_r state_b Rb true false) as [sc Hsc].
  inversion Hsc; subst. clear Hsc.
  remember (mkState (mem state_b)
                    (Read true false (mem state_b true false) :: history state_b))
    as state_c eqn:Hdef_c.
  assert (Rc : Reachable f state_c).
  { subst. apply reach_step with state_b.
    - exact Rb.
    - apply (step_read f state_b true false). }
  (* L'invariant : mem state_b true false = 0 *)
  assert (Hcross1 : mem state_b true false = 0).
  { exact (cross_memory_invariant f Hpart state_b Rb true). }

  (* === Étape 4 : p' lit x === *)
  destruct (Hwf_r state_c Rc false true) as [sd Hsd].
  inversion Hsd; subst. clear Hsd.
  remember (mkState (mem state_c)
                    (Read false true (mem state_c false true) :: history state_c))
    as state_d eqn:Hdef_d.
  assert (Rd : Reachable f state_d).
  { subst. apply reach_step with state_c.
    - exact Rc.
    - apply (step_read f state_c false true). }
  (* L'invariant : mem state_c false true = 0 *)
  assert (Hcross2 : mem state_c false true = 0).
  { exact (cross_memory_invariant f Hpart state_c Rc false). }

  (* === Vérification RW1 === *)
  (* L'historique de state_d contient les 4 opérations du pattern RW1 *)
  assert (HRWI : has_RW1_pattern_b (history state_d) = true).
  {
    subst state_d state_c state_b state_a.
    simpl.
    rewrite Hcross1. rewrite Hcross2.
    reflexivity.
  }

  specialize (Hcons state_d Rd).
  rewrite HRWI in Hcons.
  discriminate.
Qed.