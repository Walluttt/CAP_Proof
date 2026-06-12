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

  Inductive LocalTransition :=
| LS_Internal
| LS_Send (m : Message)
| LS_Return (r : R).

  Record Algorithme := {
    init_state : Q ;
    step : Q -> Transition -> Q -> Type
  local_step : Q -> { lt : LocalTransition & Q }
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
  (*
  changer la definition d'algo pour :
  Dans tout état il existe un unique pas local (send/internal/return) (pas sans hypothese dans la validité, rec a une hypothese que le message ait été envoyé) => montrer que le scheduler peut avancer (preuve = scheduler)
  (une exécuton est une suite de valid_step)

  supprimer l'hypothese step_fun ou prouver 
  dans les execs, les messages envoyés finissent par etre reçus, démontrer T1/T3 execs (photo)
  *)
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
      (*tout message envoyé à un correct doit etre reçu*)
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
  (*construire un exec avec moins de t crash, dans une exec finie tout le monde crash, 
  construire exec infinie (faire des internals en boucle si aucune action, 
  dans tout état il doit y avoir un pas possible, soit internal, soit send, soit return)*)
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
  Lemma cfg_indist_sym : forall c1 c2 n, cfg_indist c1 c2 n -> cfg_indist c2 c1 n.
  Proof.
    intros c1 c2 n H. unfold cfg_indist in *. destruct H; split; auto.
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
  (*
  remplacer (dans ma def de n1, traces fausses) par induction qui dit que je fais mes pas
  je fais mes call_writes, je laisse l'algo s'exécuter jusqu'à return_wrte, 
  une fois return je fais call_read etc jusqu'au return_read
  pas trivial: liveness, seule supposition t-resilience
  montrer que y a moins de t faults alors termine
  t>=n/2, n-t proc qui font des pas, le scheduleur doit laisser les n-t s'exécuter
  Mon sys peut etre séparé entre Q et T où T = n - t et Q  = n - t, T u Q  = |n|, T n Q = vide,
  dans mes 3 traces, il faut n - t proc qui fassent des pas de calculs en permanence  
  *)
  Hypothesis scheduler_is_valid : 
    forall cfg n t, local_scheduler cfg n = Some t -> 
    Valid_Step eq_node_dec eq_msg_dec Algo cfg n t (apply_step cfg n t).

  Definition step_E1 (cfg : Cfg) : option (Trans * Node) :=
    match local_scheduler cfg n1 with 
    | Some t => Some (t, n1) 
    | None => None 
    end.

  Fixpoint config_E1 (n : nat) : Cfg :=
    match n with
    | 0 => Init_Cfg
    | S p => match step_E1 (config_E1 p) with 
             | Some (t, nd) => apply_step (config_E1 p) nd t 
             | None => config_E1 p 
             end
    end.

  Definition trace_E1 (n : nat) : option (Trans * Node) := step_E1 (config_E1 n).

  Definition Exec_E1 : Exec.
  Proof.
    refine {| configs := config_E1; trace := trace_E1 |}.
    - reflexivity.
    - intros n. unfold trace_E1, config_E1. fold config_E1.
      destruct (step_E1 (config_E1 n)) as [[t nd]|] eqn:Hstep.
      + unfold step_E1 in Hstep. destruct (local_scheduler (config_E1 n) n1) eqn:Hsched; inversion Hstep; subst.
        apply scheduler_is_valid. exact Hsched.
      + reflexivity.
    - intros n H_halt. 
      assert (H_cfg : config_E1 (S n) = config_E1 n).
      { simpl. unfold trace_E1 in H_halt. rewrite H_halt. reflexivity. }
      unfold trace_E1. rewrite H_cfg. exact H_halt.
  Defined.


  Definition step_E2 (cfg : Cfg) : option (Trans * Node) :=
    match local_scheduler cfg n2 with 
    | Some t => Some (t, n2) 
    | None => None 
    end.

  Fixpoint config_E2 (n : nat) : Cfg :=
    match n with
    | 0 => Init_Cfg
    | S p => match step_E2 (config_E2 p) with 
             | Some (t, nd) => apply_step (config_E2 p) nd t 
             | None => config_E2 p 
             end
    end.

  Definition trace_E2 (n : nat) : option (Trans * Node) := step_E2 (config_E2 n).

  Definition Exec_E2 : Exec.
  Proof.
    refine {| configs := config_E2; trace := trace_E2 |}.
    - reflexivity.
    - intros n. unfold trace_E2, config_E2. fold config_E2.
      destruct (step_E2 (config_E2 n)) as [[t nd]|] eqn:Hstep.
      + unfold step_E2 in Hstep. destruct (local_scheduler (config_E2 n) n2) eqn:Hsched; inversion Hstep; subst.
        apply scheduler_is_valid. exact Hsched.
      + reflexivity.
    - intros n H_halt. 
      assert (H_cfg : config_E2 (S n) = config_E2 n).
      { simpl. unfold trace_E2 in H_halt. rewrite H_halt. reflexivity. }
      unfold trace_E2. rewrite H_cfg. exact H_halt.
  Defined.

  Variable r_wx r_ry r_wy r_rx : R.

  Definition trace_N1 (i : nat) : option (Trans * Node) :=
    match i with
    | 0 => Some (@call Node Message C R w_x, n1)
    | 1 => Some (@ret Node Message C R r_wx, n1)
    | 2 => Some (@call Node Message C R r_y, n1)
    | 3 => Some (@ret Node Message C R r_ry, n1)
    | _ => None
    end.

  (* 2. Le moteur qui calcule les états successifs en suivant la trace *)
  Fixpoint config_N1 (n : nat) : Cfg :=
    match n with
    | 0 => Init_Cfg
    | S p => 
        match trace_N1 p with
        | Some (t, nd) => apply_step (config_N1 p) nd t
        | None => config_N1 p
        end
    end.
  
  Definition E1 : Exec.
  Proof.
    refine {| configs := config_N1; trace := trace_N1 |}.
    - reflexivity.
    - intros n. unfold trace_N1, config_N1. fold config_N1.
      destruct n as [|[|[|[|n]]]]; simpl.
      + apply step_intro; [ unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [exact (projT2 (step_fun _ _)) | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [reflexivity | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [repeat split; reflexivity | congruence] ].
      + apply step_intro; [ unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [exact (projT2 (step_fun _ _)) | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [reflexivity | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [repeat split; reflexivity | congruence] ].
      + apply step_intro; [ unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [exact (projT2 (step_fun _ _)) | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [reflexivity | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [repeat split; reflexivity | congruence] ].
      + apply step_intro; [ unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [exact (projT2 (step_fun _ _)) | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [reflexivity | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n1 n1) as [_|Hneq]; [repeat split; reflexivity | congruence] ].
      + reflexivity.
    - intros n Hhalt. destruct n as [|[|[|[|n]]]]; simpl in *; try discriminate Hhalt; reflexivity.
  Defined.


  Definition trace_N2 (i : nat) : option (Trans * Node) :=
    match i with
    | 0 => Some (@call Node Message C R w_y, n2)
    | 1 => Some (@ret Node Message C R r_wy, n2)
    | 2 => Some (@call Node Message C R r_x, n2)
    | 3 => Some (@ret Node Message C R r_rx, n2)
    | _ => None
    end.

  Fixpoint config_N2 (n : nat) : Cfg :=
    match n with
    | 0 => Init_Cfg
    | S p => 
        match trace_N2 p with
        | Some (t, nd) => apply_step (config_N2 p) nd t
        | None => config_N2 p
        end
    end.

  Definition E2 : Exec.
  Proof.
    refine {| configs := config_N2; trace := trace_N2 |}.
    - reflexivity.
    - intros n. unfold trace_N2, config_N2. fold config_N2.
      destruct n as [|[|[|[|n]]]]; simpl.
      + apply step_intro; [ unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [exact (projT2 (step_fun _ _)) | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [reflexivity | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [repeat split; reflexivity | congruence] ].
      + apply step_intro; [ unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [exact (projT2 (step_fun _ _)) | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [reflexivity | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [repeat split; reflexivity | congruence] ].
      + apply step_intro; [ unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [exact (projT2 (step_fun _ _)) | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [reflexivity | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [repeat split; reflexivity | congruence] ].
      + apply step_intro; [ unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [exact (projT2 (step_fun _ _)) | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [reflexivity | congruence]
                          | unfold apply_step; simpl; destruct (eq_node_dec n2 n2) as [_|Hneq]; [repeat split; reflexivity | congruence] ].
      + reflexivity.
    - intros n Hhalt. destruct n as [|[|[|[|n]]]]; simpl in *; try discriminate Hhalt; reflexivity.
  Defined.

  Lemma eval_zero_if_no_write : forall (aseq : Seq C) (addr : Addr) (k : nat),
    (forall j, j < k -> forall v, aseq j <> Some (write addr v)) ->
    eval ConcreteMX aseq k addr = 0.
  Proof.
    intros aseq addr k. 
    (* TA TECHNIQUE : On casse le record Seq pour enlever la coercition cachée ! *)
    destruct aseq as [f_seq f_dnr].
    simpl in *.
    
    induction k as [|k' IH]; intros Hno.
    - reflexivity.
    - simpl. 
      (* Maintenant f_seq k' est pur, le destruct va remplacer parfaitement *)
      destruct (f_seq k') as [cmd|] eqn:Hcmd.
      + destruct cmd as [a v' | a].
        * (* Cas d'une écriture *)
          destruct (Nat.eq_dec addr a) as [Heq|Hneq].
          -- (* L'adresse écrite est notre adresse : Contradiction *)
             subst a.
             assert (H_lt : k' < S k') by lia.
             specialize (Hno k' H_lt v').
             exfalso. apply Hno. exact Hcmd.
          -- (* L'adresse écrite est différente : On applique IH *)
             unfold ConcreteMX, Transition_mem; simpl.
             destruct (Nat.eq_dec addr a) as [Heq2|Hneq2].
             ++ (* Si addr = a, c'est absurde d'après Hneq *)
                exfalso. apply Hneq. exact Heq2.
             ++ (* Si addr <> a, la mémoire ne change pas, on applique IH *)
                apply IH.
                intros j Hj v'' Hcontra.
                assert (H_lt : j < S k') by lia.
                specialize (Hno j H_lt v'').
                apply Hno. exact Hcontra.
        * (* Cas d'une lecture : la mémoire ne change pas *)
          apply IH.
          intros j Hj v'' Hcontra.
          assert (H_lt : j < S k') by lia.
          specialize (Hno j H_lt v'').
          apply Hno. exact Hcontra.
      + (* Cas d'un événement vide (None) *)
        apply IH.
        intros j Hj v'' Hcontra.
        assert (H_lt : j < S k') by lia.
        specialize (Hno j H_lt v'').
        apply Hno. exact Hcontra.
  Qed.

  Lemma E1_only_wx_ry : forall (op : Completed_Op E1), 
    op_call op = w_x \/ op_call op = r_y.
  Proof.
    intros op.
    destruct op as [nd c r tc tr pc pr pt]. simpl in *.
    (* On explore les temps de call possibles dans trace_N1 *)
    destruct tc as [|[|[|[|tc]]]]; simpl in pc; inversion pc.
    - left. reflexivity.  (* tc = 0 : c'est w_x *)
    - right. reflexivity. (* tc = 2 : c'est r_y *)
  Qed.

  Lemma E1_forces_v_init :
    Maintains_Seq_Consistency Algo ->
    r_ry = out_mem y v_init /\ r_wx = bottom_mem Addr.
  Proof.
    intros H_cons.
    pose proof (H_cons E1) as H_crit.
    unfold crit_seq in H_crit.
    
    (* On casse les records Seq pour éviter les problèmes de coercition *)
    destruct H_crit as [[f_seq f_dnr] [[e_seq e_dnr] [H_EvSeq H_ADTSeq]]].
    destruct H_EvSeq as [mono exhausts].
    
   (* Instanciation manuelle de l'opération r_y dans E1 *)
    assert (H_call_ry : trace E1 2 = Some (@call Node Message C R r_y, n1)) by reflexivity.
    assert (H_ret_ry  : trace E1 3 = Some (@ret Node Message C R r_ry, n1)) by reflexivity.
    assert (H_time_ry : 2 < 3) by lia.
    pose (op_Ry := {| op_node := n1; op_call := r_y; op_ret := r_ry; 
                      t_call := 2; t_ret := 3; 
                      proof_c := H_call_ry; proof_r := H_ret_ry; proof_time := H_time_ry |}).
                      
    (* Instanciation manuelle de l'opération w_x dans E1 *)
    assert (H_call_wx : trace E1 0 = Some (@call Node Message C R w_x, n1)) by reflexivity.
    assert (H_ret_wx  : trace E1 1 = Some (@ret Node Message C R r_wx, n1)) by reflexivity.
    assert (H_time_wx : 0 < 1) by lia.
    pose (op_Wx := {| op_node := n1; op_call := w_x; op_ret := r_wx; 
                      t_call := 0; t_ret := 1; 
                      proof_c := H_call_wx; proof_r := H_ret_wx; proof_time := H_time_wx |}).
    destruct (exhausts op_Ry) as [iry Hiry].
    destruct (exhausts op_Wx) as [iwx Hiwx].
    
    split.
    - (* BUT 1 : r_ry = out_mem y v_init *)
      pose proof (H_ADTSeq iry) as H_adt_ry.
      unfold ADTSeq, Ba in H_adt_ry. simpl in H_adt_ry.
      
      (* LA CORRECTION EST ICI : On simplifie Hiry d'abord *)
      simpl in Hiry.
      rewrite Hiry in H_adt_ry. simpl in H_adt_ry.
      
      destruct (f_seq iry) as [cmd_ry|] eqn:Hcmd_ry; [|discriminate].
      injection H_adt_ry. intros H_snd H_fst.
      subst cmd_ry.
      
      assert (H_eval_y : eval ConcreteMX {| seq := f_seq; does_not_restart := f_dnr |} iry y = 0).
      {
        apply eval_zero_if_no_write.
        intros j Hj v' Hcontra.
        pose proof (H_ADTSeq j) as H_adt_j.
        unfold ADTSeq, Ba in H_adt_j. simpl in H_adt_j.
        
        (* LA CORRECTION EST ICI : On simplifie Hcontra pour enlever le record *)
        simpl in Hcontra.
        rewrite Hcontra in H_adt_j. simpl in H_adt_j.
        
        destruct (e_seq j) as [op_j|] eqn:Heseq_j; [|discriminate].
        simpl in H_adt_j. injection H_adt_j. intros _ H_op_call.
        
        pose proof (E1_only_wx_ry op_j) as [Hwx | Hry].
        - unfold w_x in Hwx. rewrite <- H_op_call in Hwx. 
          inversion Hwx. exfalso. apply x_neq_y. symmetry. assumption.
        - unfold r_y in Hry. rewrite <- H_op_call in Hry. 
          discriminate Hry.
      }
      
      unfold Transition_mem in H_snd. 
      simpl in H_snd.
      
      (* Maintenant H_snd affiche clairement (eval ... y), le rewrite va marcher ! *)
      rewrite H_eval_y in H_snd.
      
      (* Ton but est r_ry = out_mem y v_init. On remplace v_init par 0 dans le but *)
      rewrite mx_init_is_v_init.
      
      (* Il ne reste plus qu'à conclure *)
      symmetry. exact H_snd.
      
    - (* BUT 2 : r_wx = bottom_mem Addr *)
      pose proof (H_ADTSeq iwx) as H_adt_wx.
      unfold ADTSeq, Ba in H_adt_wx. simpl in H_adt_wx.
      
      (* ANTICIPATION : On simplifie Hiwx pour éviter la même erreur *)
      simpl in Hiwx.
      rewrite Hiwx in H_adt_wx. simpl in H_adt_wx.
      
      destruct (f_seq iwx) as [cmd_wx|] eqn:Hcmd_wx; [|discriminate].
      injection H_adt_wx. intros H_snd H_fst.
      subst cmd_wx.
      
      simpl in H_snd. symmetry. exact H_snd.
  Qed.


  Lemma E2_only_wy_rx : forall (op : Completed_Op E2), 
    op_call op = w_y \/ op_call op = r_x.
  Proof.
    intros op.
    destruct op as [nd c r tc tr pc pr pt].
    simpl in pc.
    destruct tc as [|[|[|[|tc]]]]; simpl in pc; inversion pc; subst.
    - left. reflexivity.
    - right. reflexivity.
  Qed.

  Lemma E2_forces_v_init :
    Maintains_Seq_Consistency Algo ->
    r_rx = out_mem x v_init /\ r_wy = bottom_mem Addr.
  Proof.
    intros H_cons.
    pose proof (H_cons E2) as H_crit.
    unfold crit_seq in H_crit.
    
    (* 1. On casse les records Seq d'emblée *)
    destruct H_crit as [[f_seq f_dnr] [[e_seq e_dnr] [H_EvSeq H_ADTSeq]]].
    destruct H_EvSeq as [mono exhausts].
    
    (* 2. Instanciation manuelle de l'opération r_x dans E2 (avec typage explicite) *)
    assert (H_call_rx : trace E2 2 = Some (@call Node Message C R r_x, n2)) by reflexivity.
    assert (H_ret_rx  : trace E2 3 = Some (@ret Node Message C R r_rx, n2)) by reflexivity.
    assert (H_time_rx : 2 < 3) by lia.
    pose (op_Rx := {| op_node := n2; op_call := r_x; op_ret := r_rx; 
                      t_call := 2; t_ret := 3; 
                      proof_c := H_call_rx; proof_r := H_ret_rx; proof_time := H_time_rx |}).
                      
    (* 3. Instanciation manuelle de l'opération w_y dans E2 (avec typage explicite) *)
    assert (H_call_wy : trace E2 0 = Some (@call Node Message C R w_y, n2)) by reflexivity.
    assert (H_ret_wy  : trace E2 1 = Some (@ret Node Message C R r_wy, n2)) by reflexivity.
    assert (H_time_wy : 0 < 1) by lia.
    pose (op_Wy := {| op_node := n2; op_call := w_y; op_ret := r_wy; 
                      t_call := 0; t_ret := 1; 
                      proof_c := H_call_wy; proof_r := H_ret_wy; proof_time := H_time_wy |}).

    destruct (exhausts op_Rx) as [irx Hirx].
    destruct (exhausts op_Wy) as [iwy Hiwy].
    
    split.
    - (* BUT 1 : r_rx = out_mem x v_init *)
      pose proof (H_ADTSeq irx) as H_adt_rx.
      unfold ADTSeq, Ba in H_adt_rx. simpl in H_adt_rx.
      
      simpl in Hirx.
      rewrite Hirx in H_adt_rx. simpl in H_adt_rx.
      
      destruct (f_seq irx) as [cmd_rx|] eqn:Hcmd_rx; [|discriminate].
      injection H_adt_rx. intros H_snd H_fst.
      subst cmd_rx.
      
      assert (H_eval_x : eval ConcreteMX {| seq := f_seq; does_not_restart := f_dnr |} irx x = 0).
      {
        apply eval_zero_if_no_write.
        intros j Hj v' Hcontra.
        pose proof (H_ADTSeq j) as H_adt_j.
        unfold ADTSeq, Ba in H_adt_j. simpl in H_adt_j.
        
        simpl in Hcontra.
        rewrite Hcontra in H_adt_j. simpl in H_adt_j.
        
        destruct (e_seq j) as [op_j|] eqn:Heseq_j; [|discriminate].
        simpl in H_adt_j. injection H_adt_j. intros _ H_op_call.
        
        pose proof (E2_only_wy_rx op_j) as [Hwy | Hrx].
        - unfold w_y in Hwy. rewrite <- H_op_call in Hwy. 
          (* Ici, Hwy génère x = y. C'est exactement l'inverse de E1, 
             donc plus besoin de 'symmetry', x_neq_y s'applique directement ! *)
          inversion Hwy. exfalso. apply x_neq_y. assumption.
        - unfold r_x in Hrx. rewrite <- H_op_call in Hrx. 
          discriminate Hrx.
      }
      
      unfold Transition_mem in H_snd. 
      simpl in H_snd.
      rewrite H_eval_x in H_snd.
      rewrite mx_init_is_v_init.
      symmetry. exact H_snd.
      
    - (* BUT 2 : r_wy = bottom_mem Addr *)
      pose proof (H_ADTSeq iwy) as H_adt_wy.
      unfold ADTSeq, Ba in H_adt_wy. simpl in H_adt_wy.
      
      simpl in Hiwy.
      rewrite Hiwy in H_adt_wy. simpl in H_adt_wy.
      
      destruct (f_seq iwy) as [cmd_wy|] eqn:Hcmd_wy; [|discriminate].
      injection H_adt_wy. intros H_snd H_fst.
      subst cmd_wy.
      
      simpl in H_snd. symmetry. exact H_snd.
  Qed.
  

  Definition trace_N3 (i : nat) : option (Trans * Node) :=
    match i with
    | 0 => Some (@call Node Message C R w_x, n1)
    | 1 => Some (@ret Node Message C R r_wx, n1)
    | 2 => Some (@call Node Message C R r_y, n1)
    | 3 => Some (@ret Node Message C R r_ry, n1)
    | 4 => Some (@call Node Message C R w_y, n2)
    | 5 => Some (@ret Node Message C R r_wy, n2)
    | 6 => Some (@call Node Message C R r_x, n2)
    | 7 => Some (@ret Node Message C R r_rx, n2)
    | _ => None
    end.


  (* Le moteur d'état global *)
  Fixpoint config_N3 (n : nat) : Cfg :=
    match n with
    | 0 => Init_Cfg
    | S p => 
        match trace_N3 p with
        | Some (t, nd) => apply_step (config_N3 p) nd t
        | None => config_N3 p
        end
    end.

  Lemma config_N3_stable : forall t, t >= 9 -> config_N3 (S t) = config_N3 t.
  Proof.
    intros t Ht. destruct t as [|[|[|[|[|[|[|[|[|t]]]]]]]]]; try lia; reflexivity.
  Qed.

  Ltac solve_E3_step n_eq :=
    apply step_intro;
    [ unfold apply_step; simpl; destruct n_eq as [_|Hneq]; [exact (projT2 (step_fun _ _)) | congruence]
    | unfold apply_step; simpl; destruct n_eq as [_|Hneq]; [reflexivity | congruence]
    | unfold apply_step; simpl; destruct n_eq as [_|Hneq]; [ | congruence ];
      repeat split; 
      (* On repère tous les tests d'égalité entre nœuds restants et on les résout *)
      repeat match goal with
      | |- context[eq_node_dec ?x ?y] => destruct (eq_node_dec x y); try congruence
      end;
      auto ].
  Definition E3 : Exec.
  Proof.
    refine {| configs := config_N3; trace := trace_N3 |}.
    - reflexivity.
    - intros n. unfold trace_N3, config_N3. fold config_N3.
      destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; simpl.
      + solve_E3_step (eq_node_dec n1 n1).
      + solve_E3_step (eq_node_dec n1 n1).
      + solve_E3_step (eq_node_dec n1 n1).
      + solve_E3_step (eq_node_dec n1 n1).
      + solve_E3_step (eq_node_dec n2 n2).
      + solve_E3_step (eq_node_dec n2 n2).
      + solve_E3_step (eq_node_dec n2 n2).
      + solve_E3_step (eq_node_dec n2 n2).
      + reflexivity.
    - intros n Hhalt. destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; simpl in *; try discriminate Hhalt; reflexivity.
  Defined.

  Lemma E3_indist_E1_for_n1 : forall k, cfg_indist (config_N3 k) (config_N1 k) n1.
  Proof.
    intros k. induction k as [|k IH].
    - (* Cas k = 0 : État initial (Init_Cfg) pour les deux *)
      simpl. apply cfg_indist_refl.
      
    - (* Cas k = S k : On regarde le temps exact avec destruct *)
      destruct k as [|[|[|[|k']]]].
      + (* k=0 (Temps 1) *)
        simpl. apply cfg_indist_refl.
      + (* k=1 (Temps 2) *)
        simpl. apply cfg_indist_refl.
      + (* k=2 (Temps 3) *)
        simpl. apply cfg_indist_refl.
      + (* k=3 (Temps 4) *)
        simpl. apply cfg_indist_refl.
        
      + (* Temps >= 5 : C'est N2 qui joue dans E3. N1 est figé. *)
        assert (H_N1_frozen : config_N1 (S (S (S (S (S k'))))) = config_N1 (S (S (S (S k'))))) by reflexivity.
        rewrite H_N1_frozen.
        
        destruct k' as [|[|[|[|k'']]]].
        * (* Temps 5 : N2 appelle w_y dans E3 *)
          assert (H_N3_5 : config_N3 5 = apply_step (config_N3 4) n2 (@call Node Message C R w_y)) by reflexivity.
          rewrite H_N3_5.
          apply cfg_indist_trans with (c2 := config_N3 4).
          -- apply cfg_indist_sym. apply partition_isolation_N1.
          -- exact IH.
          
        * (* Temps 6 : N2 reçoit r_wy dans E3 *)
          assert (H_N3_6 : config_N3 6 = apply_step (config_N3 5) n2 (@ret Node Message C R r_wy)) by reflexivity.
          rewrite H_N3_6.
          apply cfg_indist_trans with (c2 := config_N3 5).
          -- apply cfg_indist_sym. apply partition_isolation_N1.
          -- exact IH.
          
        * (* Temps 7 : N2 appelle r_x dans E3 *)
          assert (H_N3_7 : config_N3 7 = apply_step (config_N3 6) n2 (@call Node Message C R r_x)) by reflexivity.
          rewrite H_N3_7.
          apply cfg_indist_trans with (c2 := config_N3 6).
          -- apply cfg_indist_sym. apply partition_isolation_N1.
          -- exact IH.
          
        * (* Temps 8 : N2 reçoit r_rx dans E3 *)
          assert (H_N3_8 : config_N3 8 = apply_step (config_N3 7) n2 (@ret Node Message C R r_rx)) by reflexivity.
          rewrite H_N3_8.
          apply cfg_indist_trans with (c2 := config_N3 7).
          -- apply cfg_indist_sym. apply partition_isolation_N1.
          -- exact IH.
          
        * (* Temps >= 9 : N2 a aussi terminé, E3 est figée *)
          assert (H_N3_frozen : config_N3 (S (S (S (S (S (S (S (S (S k''))))))))) = 
                                config_N3 (S (S (S (S (S (S (S (S k''))))))))) by reflexivity.
          rewrite H_N3_frozen.
          exact IH.
  Qed.

  (* Lemme utilitaire : Une même action sur des états identiques donne des états identiques *)
  Lemma apply_step_indist : forall c1 c2 n t,
    cfg_indist c1 c2 n ->
    cfg_indist (apply_step c1 n t) (apply_step c2 n t) n.
  Proof.
    intros c1 c2 n t [Hst Hpc].
    unfold cfg_indist, apply_step; simpl.
    destruct (eq_node_dec n n) as [_|Hneq].
    - (* On utilise explicitement nos égalités pour remplacer c1 par c2 *)
      rewrite Hst. rewrite Hpc. 
      split; reflexivity.
    - exfalso; apply Hneq; reflexivity.
  Qed.

  (* Théorème : N2 dans E3 a le même comportement que dans E2, décalé de 4 unités de temps *)
  Lemma E3_indist_E2_for_n2 : forall k, cfg_indist (config_N3 (k + 4)) (config_N2 k) n2.
  Proof.
    intros k. induction k as [|k IH].
    - (* Cas de base : k = 0 (t=4 pour E3 vs t=0 pour E2) *)
      (* Pendant que N1 joue ses 4 actions, N2 est totalement isolé *)
      assert (H1: cfg_indist (config_N3 1) (config_N3 0) n2) by (apply cfg_indist_sym; apply partition_isolation_N2).
      assert (H2: cfg_indist (config_N3 2) (config_N3 1) n2) by (apply cfg_indist_sym; apply partition_isolation_N2).
      assert (H3: cfg_indist (config_N3 3) (config_N3 2) n2) by (apply cfg_indist_sym; apply partition_isolation_N2).
      assert (H4: cfg_indist (config_N3 4) (config_N3 3) n2) by (apply cfg_indist_sym; apply partition_isolation_N2).
      
      assert (H0: config_N3 0 = config_N2 0) by reflexivity.
      rewrite <- H0.
      
      apply cfg_indist_trans with (config_N3 3); [exact H4 |].
      apply cfg_indist_trans with (config_N3 2); [exact H3 |].
      apply cfg_indist_trans with (config_N3 1); [exact H2 |].
      exact H1.
      
    - (* Hérédité : k = S k (Déroulement des actions de N2) *)
      (* On analyse exactement à quelle étape de sa trace N2 se trouve *)
      destruct k as [|[|[|[|k']]]].
      
      + (* k=0 => on passe à k=1 : N2 appelle w_y *)
        change (1 + 4) with 5.
        change (0 + 4) with 4 in IH.
        assert (H_N3: config_N3 5 = apply_step (config_N3 4) n2 (@call Node Message C R w_y)) by reflexivity.
        assert (H_N2: config_N2 1 = apply_step (config_N2 0) n2 (@call Node Message C R w_y)) by reflexivity.
        rewrite H_N3, H_N2.
        apply apply_step_indist. exact IH.
        
      + (* k=1 => on passe à k=2 : N2 reçoit r_wy *)
        change (2 + 4) with 6.
        change (1 + 4) with 5 in IH.
        assert (H_N3: config_N3 6 = apply_step (config_N3 5) n2 (@ret Node Message C R r_wy)) by reflexivity.
        assert (H_N2: config_N2 2 = apply_step (config_N2 1) n2 (@ret Node Message C R r_wy)) by reflexivity.
        rewrite H_N3, H_N2.
        apply apply_step_indist. exact IH.
        
      + (* k=2 => on passe à k=3 : N2 appelle r_x *)
        change (3 + 4) with 7.
        change (2 + 4) with 6 in IH.
        assert (H_N3: config_N3 7 = apply_step (config_N3 6) n2 (@call Node Message C R r_x)) by reflexivity.
        assert (H_N2: config_N2 3 = apply_step (config_N2 2) n2 (@call Node Message C R r_x)) by reflexivity.
        rewrite H_N3, H_N2.
        apply apply_step_indist. exact IH.
        
      + (* k=3 => on passe à k=4 : N2 reçoit r_rx *)
        change (4 + 4) with 8.
        change (3 + 4) with 7 in IH.
        assert (H_N3: config_N3 8 = apply_step (config_N3 7) n2 (@ret Node Message C R r_rx)) by reflexivity.
        assert (H_N2: config_N2 4 = apply_step (config_N2 3) n2 (@ret Node Message C R r_rx)) by reflexivity.
        rewrite H_N3, H_N2.
        apply apply_step_indist. exact IH.
        
      + (* k >= 4 => Les traces sont terminées ! *)
        (* LA MAGIE EST ICI : On interdit à Coq de déplier quoi que ce soit. *)
        (* On affirme juste que l'état au temps S t est le même qu'au temps t *)
        assert (H_N3_frozen : config_N3 (S (S (S (S (S k')))) + 4) = config_N3 (S (S (S (S k'))) + 4)).
        { 
          (* MAGIE : On détruit k' 4 fois pour révéler les 4 "S" manquants (4+4=8). 
             Ainsi, Coq voit t>=8 et évalue trace_N3 à None ! *)
          destruct k' as [|[|[|[|k'']]]]; reflexivity. 
        }
        
        (* On affirme que l'état de N2 est figé. *)
        assert (H_N2_frozen : config_N2 (S (S (S (S (S k'))))) = config_N2 (S (S (S (S k'))))).
        { 
          (* Ici, on a déjà 4 "S" explicites, et la trace E2 finit à t=4.
             Coq a donc déjà tout ce qu'il lui faut. *)
          reflexivity. 
        }
        
        (* Maintenant on a nos égalités, on recule d'un pas de temps dans le but *)
        rewrite H_N3_frozen, H_N2_frozen.
        
        (* Le but redevient exactement l'hypothèse de récurrence *)
        exact IH.
  Qed.



  Theorem exists_partitioned_execution :
  Maintains_Seq_Consistency Algo ->
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
    intros H_Cons.

    (* SC force les variables génériques à prendre les bonnes valeurs *)
    pose proof (E1_forces_v_init H_Cons) as [H_ry H_wx].
    pose proof (E2_forces_v_init H_Cons) as [H_rx H_wy].

    (* L'exécution cherchée est tout simplement E3 ! *)
    exists E3, 0, 1, 2, 3, 4, 5, 6, 7.
    
    (* 1. On évalue (trace E3 x) pour faire apparaître r_wx, r_ry, etc. *)
    simpl.
    
    (* 2. On remplace ces variables par les valeurs prouvées par SC *)
    rewrite H_wx, H_ry, H_wy, H_rx.
    
    (* 3. Les égalités sont maintenant parfaites *)
    repeat split; try lia; try reflexivity.
    
    (* Résolution de la clôture de la trace *)
    intros i tnd H.
    
    (* 1. On détruit 'i' pour forcer l'évaluation de la trace *)
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; inversion H; subst;
    
    (* 2. On réécrit les variables. Le '?' permet de ne pas planter si la variable n'est pas dans la ligne actuelle *)
    rewrite ?H_wx, ?H_ry, ?H_wy, ?H_rx;
    
    (* 3. La tactique magique corrigée avec "||" *)
    (* On teste "gauche", si c'est la bonne on valide avec split+reflexivity, sinon on va à "droite" *)
    repeat (solve [left; split; reflexivity] || right);
    
    (* 4. Pour le tout dernier cas de la liste (qui n'a plus de "droite" possible) *)
    try (split; reflexivity).
  Qed.

  (*
  créer les 3 execs en meme temps plutot que faire la conjonction
  l'ordonnance va construire les 3 en memme temps
  on peut supposer que l'algo est déterministe (ou alors plutot si 2 cfg indistingables pour un proc alors les valid steps sont les memes)
  ordonnanceur: en entrée un algo+cgf et retourne un valid_step
  avec mes 3 execs, je fais un pas dans E1, E2 et un pas dans les 2 branches de E3
  à la fin x et y doivent terminer (parce que E1 et E2 et la prop t>=n/2 et donc [n1 n'a pas crash])
  définir inductivement sur n le nieme pas en fct des pas précédents ?
  *)
  

  Theorem CAP_Impossible :
    forall (N_total t : nat),
    t >= N_total / 2 ->
    Maintains_Seq_Consistency Algo ->
    Is_T_Resilient Algo t ->
    False.
  Proof.
    intros N_total t H_t_majority H_Cons H_Avail.

    (* 1. Extraction de l'exécution et des temps (en utilisant H_Cons) *)
    destruct (exists_partitioned_execution H_Cons) as [E [tcall_wx [tret_wx [tcall_ry [tret_ry [tcall_wy [tret_wy [tcall_rx [tret_rx H_rest]]]]]]]]].
    
    (* 2. Destruction de l'arbre logique des propriétés de l'exécution en cascade pour éviter les bugs de parenthésage *)
    destruct H_rest as [Hwx_call H_rest].
    destruct H_rest as [Hwx_ret H_rest].
    destruct H_rest as [Hry_call H_rest].
    destruct H_rest as [Hry_ret H_rest].
    destruct H_rest as [Hwx_ord1 H_rest].
    destruct H_rest as [Hwx_ord2 H_rest].
    destruct H_rest as [Hwx_ord3 H_rest].
    destruct H_rest as [Hwy_call H_rest].
    destruct H_rest as [Hwy_ret H_rest].
    destruct H_rest as [Hrx_call H_rest].
    destruct H_rest as [Hrx_ret H_rest].
    destruct H_rest as [Hwy_ord1 H_rest].
    destruct H_rest as [Hwy_ord2 H_rest].
    destruct H_rest as [Hwy_ord3 Honly].

    (* 3. Projection sur la Cohérence Séquentielle *)
    pose proof (H_Cons E) as H_crit.
    unfold crit_seq in H_crit.
    destruct H_crit as [aseq [eseq [H_EvSeq H_ADTSeq]]].
    destruct H_EvSeq as [mono exhausts].

    (* 4. Création des 4 opérations locales *)
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

    (* 5. Extraction de leurs indices dans l'histoire globale *)
    destruct (exhausts op_Wx) as [iwx Hiwx].
    destruct (exhausts op_Ry) as [iry Hiry].
    destruct (exhausts op_Wy) as [iwy Hiwy].
    destruct (exhausts op_Rx) as [irx Hirx].

    (* 6. Ordre de Programme (Temps local intra-noeud) *)
    assert (H_ord_n1 : prog_order op_Wx op_Ry) by (apply PO_step; [reflexivity| simpl; lia]).
    assert (H_ord_n2 : prog_order op_Wy op_Rx) by (apply PO_step; [reflexivity| simpl; lia]).

    pose proof (mono _ _ _ _ Hiwx Hiry H_ord_n1) as H_n1_idx.
    pose proof (mono _ _ _ _ Hiwy Hirx H_ord_n2) as H_n2_idx.

    (* 7. Alignement des types de séquences *)
    assert (Heq_wx : ADTSeq ConcreteMX aseq iwx = Ba eseq iwx) by apply H_ADTSeq.
    assert (Heq_ry : ADTSeq ConcreteMX aseq iry = Ba eseq iry) by apply H_ADTSeq.
    assert (Heq_wy : ADTSeq ConcreteMX aseq iwy = Ba eseq iwy) by apply H_ADTSeq.
    assert (Heq_rx : ADTSeq ConcreteMX aseq irx = Ba eseq irx) by apply H_ADTSeq.

    unfold Ba, seq, ADTSeq in *. simpl in *.
    rewrite Hiwx, Hiry, Hiwy, Hirx in *. simpl in *.

    destruct (aseq iwx) as [cmd_wx|] eqn:Haseq_wx; [|discriminate Heq_wx].
    destruct (aseq iry) as [cmd_ry|] eqn:Haseq_ry; [|discriminate Heq_ry].
    destruct (aseq iwy) as [cmd_wy|] eqn:Haseq_wy; [|discriminate Heq_wy].
    destruct (aseq irx) as [cmd_rx|] eqn:Haseq_rx; [|discriminate Heq_rx].

    simpl in Heq_wx, Heq_ry, Heq_wy, Heq_rx.
    injection Heq_wx; intros Hresp_wx Hcmd_wx; subst cmd_wx.
    injection Heq_ry; intros Hresp_ry Hcmd_ry; subst cmd_ry.
    injection Heq_wy; intros Hresp_wy Hcmd_wy; subst cmd_wy.
    injection Heq_rx; intros Hresp_rx Hcmd_rx; subst cmd_rx.


    
    (* 8. Démonstration d'isolation (Pureté topologique) *)
    assert (no_wy_init : forall k, iwy < k < iry -> forall cmd, aseq k = Some cmd -> forall v', cmd <> write y v').
    {
      intros k Hk cmd Hcmd v' Hneq. subst cmd.
      pose proof (H_ADTSeq k) as H_k_adt.
      unfold ADTSeq, Ba in H_k_adt; simpl in H_k_adt.
      rewrite Hcmd in H_k_adt; simpl in H_k_adt.
      
      (* Fix : On utilise "change" pour forcer la coercition et on évite List.seq *)
      change ((let (seq, _) := eseq in seq) k) with (eseq k) in H_k_adt.
      destruct (eseq k) as [ev|] eqn:Hev.
      - inversion H_k_adt; clear H_k_adt.
        
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
          unfold op_Wy.
          f_equal; try reflexivity; try apply proof_irrelevance.
        }
        subst ev.
        assert (H_ord : prog_order op_Wy op_Wy) by (apply PO_refl; reflexivity).
        
        pose proof (mono _ _ _ _ Hev Hiwy H_ord) as H_le.
        lia.
      - discriminate H_k_adt.
    }

    assert (no_wx_init : forall k, iwx < k < irx -> forall cmd, aseq k = Some cmd -> forall v', cmd <> write x v').
    {
      intros k Hk cmd Hcmd v' Hneq. subst cmd.
      pose proof (H_ADTSeq k) as H_k_adt.
      unfold ADTSeq, Ba in H_k_adt; simpl in H_k_adt.
      rewrite Hcmd in H_k_adt; simpl in H_k_adt.
      
      (* Fix : Même chose pour la deuxième assertion *)
      change ((let (seq, _) := eseq in seq) k) with (eseq k) in H_k_adt.
      destruct (eseq k) as [ev|] eqn:Hev.
      - inversion H_k_adt; clear H_k_adt.
        
        assert (Hc : op_call ev = write x v') by congruence.
        pose proof (proof_c ev) as H_tr_c. rewrite Hc in H_tr_c.
        pose proof (Honly _ _ H_tr_c) as Hcases_c.
        destruct Hcases_c as [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [[Ht_c Hnd_c] | [Ht_c Hnd_c]]]]]]]];
        unfold w_x, r_y, w_y, r_x in Hnd_c; try congruence.
        
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
      - discriminate H_k_adt.
    }

    (* 9. Le Paradoxe d'Ordre Global (Anomalie causale) *)
    assert (H_ry_before_wy : iry < iwy).
    { apply read_returns_init_implies_no_write_y with (aseq := aseq); auto. }
    
    assert (H_rx_before_wx : irx < iwx).
    { apply read_returns_init_implies_no_write_x with (aseq := aseq); auto. }

    (* 10. CHUTE : Le cycle temporel fatal est bouclé ! *)
    (* W(x) <= R(y) < W(y) <= R(x) < W(x) *)
    lia.
  Qed.