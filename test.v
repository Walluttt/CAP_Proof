Set Implicit Arguments.
Require Import List.
Require Import Bool.
Require Import Arith.
Import ListNotations.
Require Import Wellfounded.
Require Import Coq.Vectors.Fin.
Require Import Lia.
Require Import Coq.Logic.ProofIrrelevance.
(* ================================================================= *)
(* 1. FONDATIONS : ADT ET MÉMOIRE                                    *)
(* ================================================================= *)

Record ADT (E : Type) (S : Type) := {
  etats : Type ;
  transition : etats -> E -> etats * S ;
  initial : etats
}.

Section Mem_Section.
  Variable X : Type.
  Variable eq_dec_X : forall (x y : X), {x = y} + {x <> y}.
  Variable to_nat : X -> nat.
  Variable to_nat_injective : forall x y : X, to_nat x = to_nat y -> x = y.

  Inductive Command_mem :=
  | write : X -> nat -> Command_mem
  | read : X -> Command_mem.

  Inductive Response_type_mem :=
  | out_mem : X -> nat -> Response_type_mem
  | bottom_mem : Response_type_mem.

  Definition State_mem := X -> nat.
  Definition Init_mem : State_mem := fun _ => 0.

  Definition Transition_mem (state : State_mem) (c : Command_mem) : (State_mem * Response_type_mem) :=
    match c with
    | write x n => (fun y => if eq_dec_X y x then n else state y, bottom_mem)
    | read x   => (state, out_mem x (state x))
    end.

  Definition MX : ADT Command_mem Response_type_mem := {|
    etats := State_mem;
    transition := Transition_mem;
    initial := Init_mem
  |}.
End Mem_Section.

(* ================================================================= *)
(* 2. HISTOIRE ET SÉQUENCES                                          *)
(* ================================================================= *)

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

Definition seq_is_infinite {A : Type} (s : Seq A) : Type :=
    forall n : nat, { a : A & s n = Some a }.

Definition seq_is_finite {A : Type} (s : Seq A) : Type :=
    { n : nat & s n = None }.

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
  destruct (aseq n); [discriminate H | rewrite (DNR eq_refl); reflexivity].
Defined.

Record EventSeq {A} (H : Histoire A) (eseq : Seq (H.(events))) := {
  monotone : forall i j a b, 
    eseq i = Some a -> 
    eseq j = Some b -> 
    H.(ord) a b -> 
    i <= j ;
  exhausts : forall e, { n : nat & eseq n = Some e }
}.

#[refine]
Definition Ba {A} {H : Histoire A} (eseq : Seq H.(events)) : Seq A := {|
  seq := fun n => (option_map (fun ev => H.(label) ev) (eseq n)) ;
  does_not_restart := _
|}.
Proof.
  intros n H1.
  pose proof (DNR := does_not_restart eseq n).
  destruct (eseq n); [discriminate H1 | rewrite (DNR eq_refl); reflexivity].
Defined.

Definition crit_seq {E S} (A : ADT E S) (H : Histoire (E * S)) : Type :=
  { aseq : Seq E &
    {eseq : Seq (H.(events)) & (EventSeq H eseq * (forall n, ADTSeq A aseq n = Ba eseq n))%type} }.

(* ================================================================= *)
(* 3. ALGORITHME DISTRIBUÉ ET EXÉCUTIONS                             *)
(* ================================================================= *)

Section Algorithme_Distribue.
  Variable Node : Type.
  Variable eq_node_dec : forall x y : Node, {x = y} + {x <> y}.
  Variable Message : Type.
  Variable eq_msg_dec : forall x y : Message, {x = y} + {x <> y}.
  Variable C R : Type. 
  Variable Q : Type.

  Inductive Transition :=
  | call     : C -> Transition
  | ret      : R -> Transition
  | send     : Message -> Node -> Transition
  | receive  : Message -> Node -> Transition
  | internal : Transition.

  Record Algorithme := {
    init_state : Q ;
    step : Q -> Transition -> Q -> Type
  }.

  Record Config := {
    states : Node -> Q ;
    network : Message -> Node -> Node -> nat ;
    pending_call : Node -> bool
  }.

  Definition config_initiale (A : Algorithme) : Config := {|
    states := fun _ => A.(init_state) ;
    network := fun _ _ _ => 0 ;
    pending_call := fun _ => false
  |}.

  Definition update_state (st : Node -> Q) (n : Node) (new_q : Q) : Node -> Q :=
    fun x => if eq_node_dec x n then new_q else st x.

  Definition update_pending (pc : Node -> bool) (n : Node) (b : bool) : Node -> bool :=
    fun x => if eq_node_dec x n then b else pc x.

  Definition add_msg (net : Message -> Node -> Node -> nat) (m : Message) (src dst : Node) :=
    fun msg s d => 
      if eq_msg_dec msg m then
        if eq_node_dec s src then
          if eq_node_dec d dst then net msg s d + 1
          else net msg s d
        else net msg s d
      else net msg s d.

  Definition remove_msg (net : Message -> Node -> Node -> nat) (m : Message) (src dst : Node) :=
    fun msg s d => 
      if eq_msg_dec msg m then
        if eq_node_dec s src then
          if eq_node_dec d dst then net msg s d - 1
          else net msg s d
        else net msg s d
      else net msg s d. 

  Inductive Valid_Step (A : Algorithme) (cfg : Config) (n : Node) (t : Transition) (next_cfg : Config) : Type :=
    | step_intro : 
        A.(step) (cfg.(states) n) t (next_cfg.(states) n) ->
        (next_cfg.(states) = update_state cfg.(states) n (next_cfg.(states) n)) ->
        match t return Type with 
        | call c => 
            ( (cfg.(pending_call) n = false) * (next_cfg.(pending_call) = update_pending cfg.(pending_call) n true) * (next_cfg.(network) = cfg.(network)) )%type
        | ret r => 
            ( (cfg.(pending_call) n = true) * (next_cfg.(pending_call) = update_pending cfg.(pending_call) n false) * (next_cfg.(network) = cfg.(network)) )%type
        | send m dest => 
            ( (next_cfg.(pending_call) = cfg.(pending_call)) * (next_cfg.(network) = add_msg cfg.(network) m n dest) )%type
        | receive m src => 
            ( (next_cfg.(pending_call) = cfg.(pending_call)) * { k : nat & cfg.(network) m src n = S k } * (next_cfg.(network) = remove_msg cfg.(network) m src n) )%type
        | internal => 
            ( (next_cfg.(pending_call) = cfg.(pending_call)) * (next_cfg.(network) = cfg.(network)) )%type
        end ->
        Valid_Step A cfg n t next_cfg.

  Record Execution (A : Algorithme) : Type := {
    configs : nat -> Config ;
    trace : nat -> option (Transition * Node) ;
    init_exec : configs 0 = config_initiale A ;
    valid_exec : forall n : nat, 
      match trace n with
      | Some (t, current_node) => Valid_Step A (configs n) current_node t (configs (S n))
      | None => configs (S n) = configs n
      end ;
    halting : forall n : nat, trace n = None -> trace (S n) = None
  }.

  Definition is_call {A : Algorithme} (E : Execution A) (i : nat) (nd : Node) : Type :=
    { c : C & E.(trace) i = Some (call c, nd) }.

  Definition is_ret {A : Algorithme} (E : Execution A) (i : nat) (nd : Node) : Type :=
    { r : R & E.(trace) i = Some (ret r, nd) }.

  Inductive is_halted {A : Algorithme} (E : Execution A) (j : nat) : Type :=
    | halted_proof : E.(trace) j = None -> is_halted E j.

  Definition wait_free {A : Algorithme} (E : Execution A) : Type :=
    forall (i : nat) (nd : Node),
      is_call E i nd -> 
      { j : nat & ({ k : nat & j = S (i + k) } * (is_ret E j nd + is_halted E j))%type }.
  
  Definition active_at {A : Algorithme} (E : Execution A) (j : nat) (nd : Node) : Type :=
    { trans : Transition & E.(trace) j = Some (trans, nd) }.

  Definition is_crashed {A : Algorithme} (E : Execution A) (nd : Node) : Type :=
    { k : nat & forall (j : nat), ({ dt : nat & j = S (k + dt) } * active_at E j nd)%type -> False }.

  Definition is_correct {A : Algorithme} (E : Execution A) (nd : Node) : Type :=
    forall (k : nat), { j : nat & ({ dt : nat & j = S (k + dt) } * active_at E j nd)%type }.

  Fixpoint In_T (nd : Node) (l : list Node) : Type :=
    match l with
    | nil => False
    | h :: tail => (nd = h) + (In_T nd tail)
    end.

  Definition at_most_t_crashes {A : Algorithme} (E : Execution A) (t : nat) : Type :=
    { crashed_list : list Node & ((length crashed_list <= t) * (forall nd, is_crashed E nd -> In_T nd crashed_list))%type }.

  Definition t_resilient {A : Algorithme} (E : Execution A) (t : nat) : Type :=
    at_most_t_crashes E t ->
    forall (i : nat) (nd : Node),
      is_correct E nd -> 
      is_call E i nd -> 
      { j : nat & ({ dt : nat & j = S (i + dt) } * is_ret E j nd)%type }.
    
  Variable N_total : nat.

  Definition wait_free_gen {A : Algorithme} (E : Execution A) : Type :=
    t_resilient E (N_total - 1).

  Record Completed_Op {A : Algorithme} (E : Execution A) : Type := {
    op_node : Node ;
    op_call : C ;
    op_ret  : R ;
    t_call  : nat ;
    t_ret   : nat ;
    proof_c : E.(trace) t_call = Some (call op_call, op_node) ;
    proof_r : E.(trace) t_ret = Some (ret op_ret, op_node) ;
    proof_time : t_call < t_ret
  }.

  (* L'ordre de programme corrigé (Inductif) *)
  Inductive prog_order {A : Algorithme} {E : Execution A} (op1 op2 : Completed_Op E) : Type :=
  | PO_refl : op1 = op2 -> prog_order op1 op2
  | PO_step : op_node op1 = op_node op2 -> t_call op1 < t_call op2 -> prog_order op1 op2.

  #[refine]
  Definition extract_history {A : Algorithme} (E : Execution A) : Histoire (C * R) := {|
    events := Completed_Op E ;
    label  := fun op => (op_call op, op_ret op) ;
    ord    := prog_order ;
    refl   := fun a => PO_refl eq_refl ;
    trans  := _
  |}.
  Proof.
    intros a b c Hab Hbc.
    inversion Hab as [Hab_eq| Hnode_ab Htime_ab];
    inversion Hbc as [Hbc_eq| Hnode_bc Htime_bc].
    - subst; apply PO_refl; reflexivity.
    - subst; apply PO_step; assumption.
    - subst; apply PO_step; assumption.
    - apply PO_step; [ rewrite Hnode_ab; assumption | lia ].  
  Defined.
  
End Algorithme_Distribue.

(* ================================================================= *)
(* 4. THÉORÈME DE CAP (LA PREUVE)                                    *)
(* ================================================================= *)

Section Preuve_CAP.

  Variable Node : Type.
  Variable eq_node_dec : forall x y : Node, {x = y} + {x <> y}.
  Variable Message : Type.
  Variable eq_msg_dec : forall x y : Message, {x = y} + {x <> y}.

  Definition Addr := nat.
  Variable x y : Addr.
  Hypothesis x_neq_y : x <> y.

  Definition C := Command_mem Addr.
  Definition R := Response_type_mem Addr.
  Variable Q : Type.

  Variable Algo : Algorithme Node Message C R Q.

  Variable v_init v_write : nat.
  Hypothesis v_diff : v_init <> v_write.
  Hypothesis mx_init_is_v_init : v_init = 0. 

  Definition w_x : C := write x v_write.
  Definition r_y : C := read y.
  Definition w_y : C := write y v_write.
  Definition r_x : C := read x.

  Definition ConcreteMX := MX Nat.eq_dec.
  Variable n1 n2 : Node.
  Hypothesis n1_neq_n2 : n1 <> n2.
  Definition Maintains_Seq_Consistency (A : Algorithme Node Message C R Q) : Type :=
    forall (Ex : Execution eq_node_dec eq_msg_dec A), crit_seq ConcreteMX (extract_history Ex).

  Definition Is_T_Resilient (A : Algorithme Node Message C R Q) (t : nat) : Type :=
    forall (Ex : Execution eq_node_dec eq_msg_dec A), t_resilient Ex t.

  Lemma transition_preserves_addr :
    forall (addr : Addr) (st : State_mem Addr) (cmd : C),
      (forall v', cmd <> write addr v') ->
      fst (Transition_mem Nat.eq_dec st cmd) addr = st addr.
  Proof.
    intros addr st cmd Hnotwrite.
    destruct cmd as [addr' n | addr'].
    - simpl.
      destruct (Nat.eq_dec addr addr') as [Heq | Hne].
      + subst addr'. exfalso. apply (Hnotwrite n). reflexivity.
      + reflexivity.
    - simpl.
      reflexivity.
  Qed.
  
Lemma eval_stable_after_write :
    forall (aseq : Seq C) (addr : Addr) (v : nat) (i j : nat),
      i < j -> 
      aseq i = Some (write addr v) ->
      (forall k, i < k < j -> forall cmd, aseq k = Some cmd -> forall v', cmd <> write addr v') ->
      eval ConcreteMX aseq j addr = v.
  Proof.
    intros aseq addr v i j Hlt Hw Hno_w.
    unfold C in *.
    (* f_seq devient la vraie trace, f_dnr est la preuve qu'elle ne redémarre pas *)
    destruct aseq as [f_seq f_dnr].
    simpl in *.
    
    induction j as [|j' IHj].
    - lia.
    - destruct (Nat.eq_dec i j') as [Heq | Hneq].
      + (* Instant juste après l'écriture *)
        subst j'.
        simpl.
        (* Maintenant f_seq i correspond EXACTEMENT au but, 100% garanti *)
        rewrite Hw. 
        simpl. destruct (Nat.eq_dec addr addr); [reflexivity | congruence].
        
      + (* Instant ultérieur *)
        assert (Hlt' : i < j') by lia.
        assert (Hno_w' : forall k, i < k < j' -> forall cmd, f_seq k = Some cmd -> forall v', cmd <> write addr v').
        { intros k Hk cmd Hcmd v' Heq. eapply (Hno_w k); eauto. lia. }
        specialize (IHj Hlt' Hno_w').
        
        simpl.
        (* Le destruct se fait sur la fonction pure, pas de bug de type *)
        destruct (f_seq j') as [cmd|] eqn:Hcmd.
        * rewrite transition_preserves_addr.
          -- exact IHj.
          -- intros v' H_is_write. eapply (Hno_w j'); eauto.
        * exact IHj.
  Qed.

  Lemma read_returns_init_implies_no_write_gen :
    forall (aseq : Seq C) (addr : Addr) (idx_write idx_read : nat),
      aseq idx_write = Some (write addr v_write) ->
      aseq idx_read = Some (read addr) ->
      (forall k, idx_write < k < idx_read ->
        forall cmd, aseq k = Some cmd -> forall v', cmd <> write addr v') ->
      snd (ConcreteMX.(transition) (eval ConcreteMX aseq idx_read) (read addr)) = out_mem addr v_init ->
      idx_read < idx_write.
  Proof.
    intros aseq addr idx_w idx_r Hw Hr Hno_w Hresp.
    destruct (Nat.lt_trichotomy idx_r idx_w) as [Hlt | [Heq | Hgt]].
    - exact Hlt.
    - subst. rewrite Hw in Hr. discriminate.
    - exfalso.
      assert (Hstable : eval ConcreteMX aseq idx_r addr = v_write).
      { eapply eval_stable_after_write; eauto. }
      simpl in Hresp. injection Hresp. intros Heq_v.
      rewrite Hstable in Heq_v.
      apply v_diff. symmetry. exact Heq_v.
  Qed.

  Lemma read_returns_init_implies_no_write_y :
    forall (aseq : Seq C) (idx_write idx_read : nat),
      aseq idx_write = Some w_y -> 
      aseq idx_read = Some r_y ->
      (forall k, idx_write < k < idx_read -> forall cmd, aseq k = Some cmd -> forall v', cmd <> write y v') ->
      snd (ConcreteMX.(transition) (eval ConcreteMX aseq idx_read) r_y) = out_mem y v_init ->
      idx_read < idx_write.
  Proof.
    intros. eapply read_returns_init_implies_no_write_gen; eauto.
  Qed.

  Lemma read_returns_init_implies_no_write_x :
    forall (aseq : Seq C) (idx_write idx_read : nat),
      aseq idx_write = Some w_x -> 
      aseq idx_read = Some r_x ->
      (forall k, idx_write < k < idx_read -> forall cmd, aseq k = Some cmd -> forall v', cmd <> write x v') ->
      snd (ConcreteMX.(transition) (eval ConcreteMX aseq idx_read) r_x) = out_mem x v_init ->
      idx_read < idx_write.
  Proof.
    intros. eapply read_returns_init_implies_no_write_gen; eauto.
  Qed.

  Notation Exec := (Execution eq_node_dec eq_msg_dec Algo).
  Definition Trans := Transition Node Message C R.
  Definition Cfg  := Config Node Message Q.
  Notation Init_Cfg := (config_initiale Algo).
  Hypothesis step_fun : forall (q : Q) (t : Trans), { q' : Q & Algo.(step) q t q' }.
  

  Definition cfg_indist (c1 c2 : Cfg) (n : Node) : Prop :=
    c1.(states) n = c2.(states) n /\
    c1.(pending_call) n = c2.(pending_call) n.

  Definition apply_step (cfg : Cfg) (nd : Node) (t : Trans) : Cfg :=
    let q_old := cfg.(states) nd in
    let q_new := projT1 (step_fun q_old t) in 
    {| 
       (* Mise à jour de la mémoire locale du nœud nd uniquement *)
       states := fun x => if eq_node_dec x nd then q_new else cfg.(states) x;
       
       (* Dans le cadre d'une partition réseau, on n'altère pas l'état des messages en vol pour l'instant *)
       network := cfg.(network);
       
       (* Mise à jour du drapeau d'appel en cours (bloquant) *)
       pending_call := fun x => 
         if eq_node_dec x nd then
           match t with
           | @call _ _ _ _ _ => true
           | @ret _ _ _ _ _  => false
           | _               => cfg.(pending_call) x
           end
         else cfg.(pending_call) x
    |}.

 

  Lemma partition_isolation_N1 : forall cfg t2, 
    cfg_indist cfg (apply_step cfg n2 t2) n1.
  Proof.
    intros cfg t2. unfold cfg_indist, apply_step; simpl.
    split.
    - (* Preuve pour states *)
      destruct (eq_node_dec n1 n2) as [Heq | Hneq].
      + exfalso; apply n1_neq_n2; exact Heq.
      + reflexivity.
    - (* Preuve pour pending_call *)
      destruct (eq_node_dec n1 n2) as [Heq | Hneq].
      + exfalso; apply n1_neq_n2; exact Heq.
      + reflexivity.
  Qed.


  Lemma partition_isolation_N2 : forall cfg t1, 
    cfg_indist cfg (apply_step cfg n1 t1) n2.
  Proof.
    intros cfg t1. unfold cfg_indist, apply_step; simpl.
    split.
    - destruct (eq_node_dec n2 n1) as [Heq | Hneq].
      + exfalso; apply n1_neq_n2; auto.
      + reflexivity.
    - destruct (eq_node_dec n2 n1) as [Heq | Hneq].
      + exfalso; apply n1_neq_n2; auto.
      + reflexivity.
  Qed.

  Lemma cfg_indist_refl : forall cfg n, cfg_indist cfg cfg n.
  Proof.
    intros cfg n. unfold cfg_indist. 
    split; reflexivity.
  Qed.

  Lemma cfg_indist_trans : forall c1 c2 c3 n, 
    cfg_indist c1 c2 n -> cfg_indist c2 c3 n -> cfg_indist c1 c3 n.
  Proof.
    intros c1 c2 c3 n [H1s H1p] [H2s H2p].
    unfold cfg_indist. split.
    - rewrite H1s. exact H2s.
    - rewrite H1p. exact H2p.
  Qed.

  Lemma step_preservation : forall c1 c2 nd t,
    cfg_indist c1 c2 nd -> 
    cfg_indist (apply_step c1 nd t) (apply_step c2 nd t) nd.
  Proof.
    intros c1 c2 nd t [Hs Hp].
    unfold cfg_indist, apply_step; simpl.
    split.
    - (* La nouvelle mémoire dépend uniquement de l'ancienne (Hs) via step_fun *)
      destruct (eq_node_dec nd nd) as [_ | Hneq]; [|congruence].
      rewrite Hs. reflexivity.
    - (* L'état du pending_call se met à jour de la même manière *)
      destruct (eq_node_dec nd nd) as [_ | Hneq]; [|congruence].
      destruct t; try reflexivity; exact Hp.
  Qed.

  Variable local_scheduler : Cfg -> Node -> option Trans.

  Hypothesis scheduler_is_valid : 
    forall cfg n t, local_scheduler cfg n = Some t -> 
    Valid_Step eq_node_dec eq_msg_dec Algo cfg n t (apply_step cfg n t).

  Hypothesis Local_Determinism :
    forall cfg1 cfg2 n, 
    cfg_indist cfg1 cfg2 n -> 
    local_scheduler cfg1 n = local_scheduler cfg2 n.
  
  
    Inductive eventually_ret : Q -> Type :=
  | ret_now : forall (q : Q) (r : R) (q' : Q),
      Algo.(step) q (@ret Node Message C R r) q' -> eventually_ret q
  | ret_later : forall (q : Q) (q' : Q),
      Algo.(step) q (@internal Node Message C R) q' ->
      eventually_ret q' ->
      eventually_ret q.

  Lemma progress : forall (q : Q), eventually_ret q.
  Proof. (* découle de Is_T_Resilient 1 *) Admitted.

    Fixpoint build_trace (nd : Node) (q : Q) (H : eventually_ret q) : list (Trans * Node) * Q * R :=
    match H with
    | ret_now q r q' Hret => ([(@ret Node Message C R r, nd)], q', r)
    | ret_later q q' Hint Hrest =>
        let '(trace_rest, q'', r) := build_trace nd q' Hrest in
        ((@internal Node Message C R, nd) :: trace_rest, q'', r)
    end.
  (* Lemmes d'existence avec retours inconnus *)
  Lemma E1_exists :
    { E1 : Exec &
      { tcall_wx : nat & { tret_wx : nat &
      { tcall_ry : nat & { tret_ry : nat &
        { r_wx : R & { r_ry : R |
          (trace E1 tcall_wx = Some (@call Node Message C R w_x, n1)) *
          (trace E1 tret_wx  = Some (@ret Node Message C R r_wx, n1)) *
          (trace E1 tcall_ry = Some (@call Node Message C R r_y, n1)) *
          (trace E1 tret_ry  = Some (@ret Node Message C R r_ry, n1)) *
          (tcall_wx < tret_wx) * (tret_wx < tcall_ry) * (tcall_ry < tret_ry) *
          (forall i tnd, trace E1 i = Some tnd ->
            (i = tcall_wx /\ tnd = (@call Node Message C R w_x, n1)) \/
            (i = tret_wx  /\ tnd = (@ret Node Message C R r_wx, n1)) \/
            (i = tcall_ry /\ tnd = (@call Node Message C R r_y, n1)) \/
            (i = tret_ry  /\ tnd = (@ret Node Message C R r_ry, n1)))
        } } } } } } }.
  Proof.
    destruct (two_calls_execution n1 w_x r_y) as [E [tc1 [tr1 [tc2 [tr2 [r1 [r2 H]]]]]]].
    exists E, tc1, tr1, tc2, tr2, r1, r2. exact H.
  Qed.

  Lemma E2_exists :
    { E2 : Exec &
      { tcall_wy : nat & { tret_wy : nat &
      { tcall_rx : nat & { tret_rx : nat &
        { r_wy : R & { r_rx : R |
          (trace E2 tcall_wy = Some (@call Node Message C R w_y, n2)) *
          (trace E2 tret_wy  = Some (@ret Node Message C R r_wy, n2)) *
          (trace E2 tcall_rx = Some (@call Node Message C R r_x, n2)) *
          (trace E2 tret_rx  = Some (@ret Node Message C R r_rx, n2)) *
          (tcall_wy < tret_wy) * (tret_wy < tcall_rx) * (tcall_rx < tret_rx) *
          (forall i tnd, trace E2 i = Some tnd ->
            (i = tcall_wy /\ tnd = (@call Node Message C R w_y, n2)) \/
            (i = tret_wy  /\ tnd = (@ret Node Message C R r_wy, n2)) \/
            (i = tcall_rx /\ tnd = (@call Node Message C R r_x, n2)) \/
            (i = tret_rx  /\ tnd = (@ret Node Message C R r_rx, n2)))
        } } } } } } }.
  Proof.
    destruct (two_calls_execution n2 w_y r_x) as [E [tc1 [tr1 [tc2 [tr2 [r1 [r2 H]]]]]]].
    exists E, tc1, tr1, tc2, tr2, r1, r2. exact H.
  Qed.

  (* Identification des retours par cohérence (sera utilisé plus tard) *)
  Lemma E1_returns :
    forall (H_Cons : Maintains_Seq_Consistency Algo)
           (E1 : Exec) (tcall_wx tret_wx tcall_ry tret_ry : nat) (r_wx r_ry : R),
      trace E1 tcall_wx = Some (@call Node Message C R w_x, n1) ->
      trace E1 tret_wx  = Some (@ret Node Message C R r_wx, n1) ->
      trace E1 tcall_ry = Some (@call Node Message C R r_y, n1) ->
      trace E1 tret_ry  = Some (@ret Node Message C R r_ry, n1) ->
      tcall_wx < tret_wx < tcall_ry < tret_ry ->
      r_wx = bottom_mem Addr /\ r_ry = out_mem y v_init.
  Proof.
    (* Preuve utilisant H_Cons et les lemmes mémoire *) Admitted.

  Lemma E2_returns :
    forall (H_Cons : Maintains_Seq_Consistency Algo)
           (E2 : Exec) (tcall_wy tret_wy tcall_rx tret_rx : nat) (r_wy r_rx : R),
      trace E2 tcall_wy = Some (@call Node Message C R w_y, n2) ->
      trace E2 tret_wy  = Some (@ret Node Message C R r_wy, n2) ->
      trace E2 tcall_rx = Some (@call Node Message C R r_x, n2) ->
      trace E2 tret_rx  = Some (@ret Node Message C R r_rx, n2) ->
      tcall_wy < tret_wy < tcall_rx < tret_rx ->
      r_wy = bottom_mem Addr /\ r_rx = out_mem x v_init.
  Proof. Admitted.

  (* Extraction des indices avec les retours déjà identifiés (comme avant) *)
  Lemma E1_indices :
    forall (H_Cons : Maintains_Seq_Consistency Algo),
    exists (E1 : Exec) (tcall_wx tret_wx tcall_ry tret_ry : nat),
      trace E1 tcall_wx = Some (@call Node Message C R w_x, n1) /\
      trace E1 tret_wx  = Some (@ret Node Message C R (bottom_mem Addr), n1) /\
      trace E1 tcall_ry = Some (@call Node Message C R r_y, n1) /\
      trace E1 tret_ry  = Some (@ret Node Message C R (out_mem y v_init), n1) /\
      tcall_wx < tret_wx /\ tret_wx < tcall_ry /\ tcall_ry < tret_ry /\
      (forall i tnd, trace E1 i = Some tnd ->
         i = tcall_wx \/ i = tret_wx \/ i = tcall_ry \/ i = tret_ry) /\
      (forall n, n > tret_ry -> trace E1 n = None).
  Proof.
    intro H_Cons.
    destruct E1_exists as [E1 [twx [trx [try_ [trr [r_wx [r_ry H]]]]]]].
    destruct H as [[[[[[Hcall Hret] Hcall'] Hret'] Hord] Hclos].
    pose proof (E1_returns H_Cons E1 twx trx try_ trr r_wx r_ry Hcall Hret Hcall' Hret' Hord) as [Hrwx Hrry].
    subst r_wx. subst r_ry.
    exists E1, twx, trx, try_, trr.
    repeat split; auto.
    - intros i tnd Hi. apply Hclos in Hi.
      destruct Hi as [[-> _]|[[-> _]|[[-> _]|[-> _]]]]; auto.
    - intros n Hn. destruct (trace E1 n) as [tnd|] eqn:Heq; [|reflexivity].
      apply Hclos in Heq. destruct Heq as [[-> _]|[[-> _]|[[-> _]|[-> _]]]]; lia.
  Qed.

  Lemma E2_indices :
    forall (H_Cons : Maintains_Seq_Consistency Algo),
    exists (E2 : Exec) (tcall_wy tret_wy tcall_rx tret_rx : nat),
      trace E2 tcall_wy = Some (@call Node Message C R w_y, n2) /\
      trace E2 tret_wy  = Some (@ret Node Message C R (bottom_mem Addr), n2) /\
      trace E2 tcall_rx = Some (@call Node Message C R r_x, n2) /\
      trace E2 tret_rx  = Some (@ret Node Message C R (out_mem x v_init), n2) /\
      tcall_wy < tret_wy /\ tret_wy < tcall_rx /\ tcall_rx < tret_rx /\
      (forall i tnd, trace E2 i = Some tnd ->
         i = tcall_wy \/ i = tret_wy \/ i = tcall_rx \/ i = tret_rx) /\
      (forall n, n > tret_rx -> trace E2 n = None).
  Proof.
    intro H_Cons.
    destruct E2_exists as [E2 [twy [try_ [trx [trr [r_wy [r_rx H]]]]]]].
    destruct H as [[[[[[Hcall Hret] Hcall'] Hret'] Hord] Hclos].
    pose proof (E2_returns H_Cons E2 twy try_ trx trr r_wy r_rx Hcall Hret Hcall' Hret' Hord) as [Hrwy Hrrx].
    subst r_wy. subst r_rx.
    exists E2, twy, try_, trx, trr.
    repeat split; auto.
    - intros i tnd Hi. apply Hclos in Hi.
      destruct Hi as [[-> _]|[[-> _]|[[-> _]|[-> _]]]]; auto.
    - intros n Hn. destruct (trace E2 n) as [tnd|] eqn:Heq; [|reflexivity].
      apply Hclos in Heq. destruct Heq as [[-> _]|[[-> _]|[[-> _]|[-> _]]]]; lia.
  Qed.
  

  Theorem exists_partitioned_execution :
    exists (E : Execution eq_node_dec eq_msg_dec Algo)
          (tcall_wx tret_wx tcall_ry tret_ry : nat)
          (tcall_wy tret_wy tcall_rx tret_rx : nat),
      (* Traces du nœud isolé N1 *)
      trace E tcall_wx = Some (@call Node Message C R w_x, n1) /\
      trace E tret_wx  = Some (@ret Node Message C R (bottom_mem Addr), n1) /\
      trace E tcall_ry = Some (@call Node Message C R r_y, n1) /\
      trace E tret_ry  = Some (@ret Node Message C R (out_mem y v_init), n1) /\
      tcall_wx < tret_wx /\ tret_wx < tcall_ry /\ tcall_ry < tret_ry /\
      
      (* Traces du nœud isolé N2 *)
      trace E tcall_wy = Some (@call Node Message C R w_y, n2) /\
      trace E tret_wy  = Some (@ret Node Message C R (bottom_mem Addr), n2) /\
      trace E tcall_rx = Some (@call Node Message C R r_x, n2) /\
      trace E tret_rx  = Some (@ret Node Message C R (out_mem x v_init), n2) /\
      tcall_wy < tret_wy /\ tret_wy < tcall_rx /\ tcall_rx < tret_rx /\
      
      (* Fermeture de la trace *)
      (forall i tnd, trace E i = Some tnd ->
        (i = tcall_wx /\ tnd = (@call Node Message C R w_x, n1)) \/
        (i = tret_wx  /\ tnd = (@ret Node Message C R (bottom_mem Addr), n1)) \/
        (i = tcall_ry /\ tnd = (@call Node Message C R r_y, n1)) \/
        (i = tret_ry  /\ tnd = (@ret Node Message C R (out_mem y v_init), n1)) \/
        (i = tcall_wy /\ tnd = (@call Node Message C R w_y, n2)) \/
        (i = tret_wy  /\ tnd = (@ret Node Message C R (bottom_mem Addr), n2)) \/
        (i = tcall_rx /\ tnd = (@call Node Message C R r_x, n2)) \/
        (i = tret_rx  /\ tnd = (@ret Node Message C R (out_mem x v_init), n2))).
  Proof.
  Admitted.

  (*
  créer les 3 execs en meme temps plutot que faire la conjonction
  l'ordonnance va construire les 3 en memme temps
  on peut supposer que l'algo est déterministe (ou alors plutot si 2 cfg indistingables pour un proc alors les valid steps sont les memes)
  ordonnanceur: en entrée un algo+cgf et retourne un valid_step
  avec mes 3 execs, je fais un pas dans E1, E2 et un pas dans les 2 branches de E3
  à la fin x et y doivent terminer (parce que E1 et E2 et la prop t>=n/2 et donc [n1 n'a pas crash])
  définir inductivement sur n le nieme pas en fct des pas précédents ?
  *)
  
    (* --- 4.3 AXIOMES PHYSIQUES DE LA PARTITION --- *)

  (* --- 4.4 LE THÉORÈME FINAL --- *)
  Theorem CAP_Impossible :
    forall (N_total t : nat),
    t >= N_total / 2 ->
    Maintains_Seq_Consistency Algo ->
    Is_T_Resilient Algo t ->
    False.
  Proof.
    intros N_total t H_t_majority H_Cons H_Avail.

    (* 1. Extraction de l'exécution et des temps *)
    destruct exists_partitioned_execution as [E H_props].
    simpl in H_props.
    destruct H_props as [tcall_wx [tret_wx [tcall_ry [tret_ry [tcall_wy [tret_wy [tcall_rx [tret_rx H_rest]]]]]]]].
    
    (* 2. Destruction exacte de l'arbre logique de l'axiome *)
    destruct H_rest as [Hwx_call [Hwx_ret [Hry_call [Hry_ret [Hwx_ord1 [Hwx_ord2 [Hwx_ord3 
                      [Hwy_call [Hwy_ret [Hrx_call [Hrx_ret [Hwy_ord1 [Hwy_ord2 [Hwy_ord3 Honly]]]]]]]]]]]]]].

    (* Projection sur la Cohérence Séquentielle *)
    pose proof (H_Cons E) as H_crit.
    unfold crit_seq in H_crit.
    destruct H_crit as [aseq [eseq [H_EvSeq H_ADTSeq]]].
    destruct H_EvSeq as [mono exhausts].

    (* Création des 4 opérations locales avec les variables extraites *)
    pose (op_Wx := {| op_node := n1; op_call := w_x; op_ret := bottom_mem Addr;
                      t_call := tcall_wx; t_ret := tret_wx;
                      proof_c := Hwx_call; proof_r := Hwx_ret; proof_time := Hwx_ord1 |}).
    pose (op_Ry := {| op_node := n1; op_call := r_y; op_ret := out_mem y v_init;
                      t_call := tcall_ry; t_ret := tret_ry;
                      proof_c := Hry_call; proof_r := Hry_ret; proof_time := Hwx_ord3 |}).
    pose (op_Wy := {| op_node := n2; op_call := w_y; op_ret := bottom_mem Addr;
                      t_call := tcall_wy; t_ret := tret_wy;
                      proof_c := Hwy_call; proof_r := Hwy_ret; proof_time := Hwy_ord1 |}).
    pose (op_Rx := {| op_node := n2; op_call := r_x; op_ret := out_mem x v_init;
                      t_call := tcall_rx; t_ret := tret_rx;
                      proof_c := Hrx_call; proof_r := Hrx_ret; proof_time := Hwy_ord3 |}).

    (* Extraction de leurs indices dans l'histoire globale (aseq) *)
    destruct (exhausts op_Wx) as [iwx Hiwx].
    destruct (exhausts op_Ry) as [iry Hiry].
    destruct (exhausts op_Wy) as [iwy Hiwy].
    destruct (exhausts op_Rx) as [irx Hirx].

    (* Ordre de Programme (Temps local intra-noeud) *)
    (* On utilise 'simpl; lia' car tcall_wx < tret_wx < tcall_ry *)
    assert (H_ord_n1 : prog_order op_Wx op_Ry) by (apply PO_step; [reflexivity| simpl; lia]).
    assert (H_ord_n2 : prog_order op_Wy op_Rx) by (apply PO_step; [reflexivity| simpl; lia]).

    pose proof (mono _ _ _ _ Hiwx Hiry H_ord_n1) as H_n1_idx.
    pose proof (mono _ _ _ _ Hiwy Hirx H_ord_n2) as H_n2_idx.

    (* Alignement des types de séquences *)
    assert (Heq_wx : ADTSeq ConcreteMX aseq iwx = Ba eseq iwx) by apply H_ADTSeq.
    assert (Heq_ry : ADTSeq ConcreteMX aseq iry = Ba eseq iry) by apply H_ADTSeq.
    assert (Heq_wy : ADTSeq ConcreteMX aseq iwy = Ba eseq iwy) by apply H_ADTSeq.
    assert (Heq_rx : ADTSeq ConcreteMX aseq irx = Ba eseq irx) by apply H_ADTSeq.

    unfold Ba, seq, ADTSeq in *; simpl in *.
    rewrite Hiwx, Hiry, Hiwy, Hirx in *; simpl in *.

    destruct (aseq iwx) as [cmd_wx|] eqn:Haseq_wx; [|discriminate Heq_wx].
    destruct (aseq iry) as [cmd_ry|] eqn:Haseq_ry; [|discriminate Heq_ry].
    destruct (aseq iwy) as [cmd_wy|] eqn:Haseq_wy; [|discriminate Heq_wy].
    destruct (aseq irx) as [cmd_rx|] eqn:Haseq_rx; [|discriminate Heq_rx].

    injection Heq_wx; intros; subst cmd_wx.
    injection Heq_ry; intros; subst cmd_ry.
    injection Heq_wy; intros; subst cmd_wy.
    injection Heq_rx; intros; subst cmd_rx.

   (* Assertions de pureté topologique : Démonstration d'isolation *)
    assert (no_wy_init : forall k, iwy < k < iry -> forall cmd, aseq k = Some cmd -> forall v', cmd <> write y v').
    {
      intros k Hk cmd Hcmd v' Hneq. subst cmd.
      pose proof (H_ADTSeq k) as H_k_adt.
      unfold ADTSeq, Ba in H_k_adt; simpl in H_k_adt.
      rewrite Hcmd in H_k_adt; simpl in H_k_adt.
      
      destruct ((let (seq, _) := eseq in seq) k) as [ev|] eqn:Hev.
      - (* Cas 1 : La séquence contient un événement (Some ev) *)
        (* H_k_adt est automatiquement mis à jour. Simpl l'évalue : *)
        simpl in H_k_adt.
        inversion H_k_adt; clear H_k_adt.
        
        assert (Hc : op_call ev = write y v') by congruence.
        pose proof (proof_c ev) as H_tr_c. rewrite Hc in H_tr_c.
        pose proof (Honly _ _ H_tr_c) as Hcases_c.
        destruct Hcases_c as [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [Ht_c Hnd_c]]]]]]]];
        unfold w_x, r_y, w_y, r_x in Hnd_c; try congruence.
        assert (ev = op_Wy).
        {
          destruct ev as [n' c' r' tc' tr' pc' pr' pt'].
          simpl in *. subst tc'.
          injection Hnd_c; intros H_n_eq H_c_eq. subst n' c'.
          assert (Hr : r' = bottom_mem Addr) by congruence.
          subst r'.
          
          pose proof (Honly _ _ pr') as Hcases_r.
          destruct Hcases_r as [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [Ht_r Hnd_r]]]]]]]];
          unfold w_x, r_y, w_y, r_x in Hnd_r; try congruence.
          
          subst tr'. subst v'.
          
          (* On déplie op_Wy pour que f_equal voie les vraies valeurs *)
          unfold op_Wy.
          
          (* La combinaison magique : on égalise, on résout les évidences, on nettoie les preuves *)
          f_equal; try reflexivity; try apply proof_irrelevance.
        }
        subst ev.
        assert (H_ord : prog_order op_Wy op_Wy) by (apply PO_refl; reflexivity).
        
        (* Hev correspond maintenant exactement à ce que `mono` attend *)
        pose proof (mono _ _ _ _ Hev Hiwy H_ord) as H_le.
        lia.
      - (* Cas 2 : La séquence est vide (None) *)
        simpl in H_k_adt.
        discriminate H_k_adt.
    }

    assert (no_wx_init : forall k, iwx < k < irx -> forall cmd, aseq k = Some cmd -> forall v', cmd <> write x v').
    {
      intros k Hk cmd Hcmd v' Hneq. subst cmd.
      pose proof (H_ADTSeq k) as H_k_adt.
      unfold ADTSeq, Ba in H_k_adt; simpl in H_k_adt.
      rewrite Hcmd in H_k_adt; simpl in H_k_adt.
      
      destruct ((let (seq, _) := eseq in seq) k) as [ev|] eqn:Hev.
      - (* Cas 1 : La séquence contient un événement (Some ev) *)
        simpl in H_k_adt.
        inversion H_k_adt; clear H_k_adt.
        
        assert (Hc : op_call ev = write x v') by congruence.
        pose proof (proof_c ev) as H_tr_c. rewrite Hc in H_tr_c.
        pose proof (Honly _ _ H_tr_c) as Hcases_c.
        destruct Hcases_c as [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [Ht_c Hnd_c]]]]]]]];
        unfold w_x, r_y, w_y, r_x in Hnd_c; try congruence.
        
        (* Pour op_Wx : Démonstration de l'identité de l'événement *)
        assert (ev = op_Wx).
        {
          destruct ev as [n' c' r' tc' tr' pc' pr' pt'].
          simpl in *. subst tc'.
          injection Hnd_c; intros H_n_eq H_c_eq. subst n' c'.
          assert (Hr : r' = bottom_mem Addr) by congruence.
          subst r'.
          
          pose proof (Honly _ _ pr') as Hcases_r.
          destruct Hcases_r as [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [[Ht_r Hnd_r] | [Ht_r Hnd_r]]]]]]]];
          unfold w_x, r_y, w_y, r_x in Hnd_r; try congruence.
          
          subst tr'. subst v'.
          
          unfold op_Wx.
          f_equal; try reflexivity; try apply proof_irrelevance.
        }
        subst ev.
        assert (H_ord : prog_order op_Wx op_Wx) by (apply PO_refl; reflexivity).
        
        pose proof (mono _ _ _ _ Hev Hiwx H_ord) as H_le.
        lia.
      - (* Cas 2 : La séquence est vide (None) *)
        simpl in H_k_adt.
        discriminate H_k_adt.
    }

    (* Appel direct des hypothèses extraites plus tôt (H0 et H2) *)
    assert (Hresp_ry : snd (ConcreteMX.(transition) (eval ConcreteMX aseq iry) r_y) = out_mem y v_init).
    { exact H0. }
    assert (Hresp_rx : snd (ConcreteMX.(transition) (eval ConcreteMX aseq irx) r_x) = out_mem x v_init).
    { exact H2. }
    (* Le Paradoxe d'Ordre Global (Appel des lemmes d'anomalie causale) *)
    assert (H_ry_before_wy : iry < iwy) by (eapply read_returns_init_implies_no_write_y; eauto).
    assert (H_rx_before_wx : irx < iwx) by (eapply read_returns_init_implies_no_write_x; eauto).

    lia.
    
  Qed.

End Preuve_CAP.