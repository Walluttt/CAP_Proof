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
  Variable G1 G2 : list Node.
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
  | LS_Send (m : Message) (dest : Node)
  | LS_Return (r : R).

  Definition to_Trans (lt : LocalTransition) : Transition :=
    match lt with
    | LS_Internal => internal
    | LS_Send m dest => send m dest
    | LS_Return r => ret r
    end.

  Definition is_local_action (t : Transition) : bool :=
    match t with
    | internal    => true
    | send _ _    => true
    | ret _       => true
    | call _      => false
    | receive _ _ => false
    end.

  Record Algorithme := {
    init_state : Q ;
    step : Q -> Transition -> Q -> Type ;
    local_step : Q -> { lt : LocalTransition & Q } ;
    local_step_is_valid : forall q, 
      let '(existT _ lt q') := local_step q in 
      step q (to_Trans lt) q' ;
    input_step : forall (q : Q) (t : Transition), 
      is_local_action t = false -> { q' : Q & step q t q' }
  }.

  Record Config := {
    states : Node -> Q ;
    network : list (Message * Node * Node) ;
    pending_call : Node -> bool
  }.

  Definition config_initiale (A : Algorithme) : Config := {|
    states := fun _ => A.(init_state) ;
    network := nil;
    pending_call := fun _ => false
  |}.

  Definition update_state (st : Node -> Q) (n : Node) (new_q : Q) : Node -> Q :=
    fun x => if eq_node_dec x n then new_q else st x.

  Definition update_pending (pc : Node -> bool) (n : Node) (b : bool) : Node -> bool :=
    fun x => if eq_node_dec x n then b else pc x.

  Definition add_msg (net : list (Message * Node * Node)) (m : Message) (src dst : Node) :=
    (m, src, dst) :: net.

  (* Retirer = enlever la première occurrence exacte *)
  Fixpoint remove_msg (net : list (Message * Node * Node)) (m : Message) (src dst : Node) : list (Message * Node * Node) :=
    match net with
    | nil => nil
    | (m', s', d') :: tail =>
        if eq_msg_dec m' m then
          if eq_node_dec s' src then
            if eq_node_dec d' dst then tail (* On a trouvé, on l'enlève et on s'arrête *)
            else (m', s', d') :: remove_msg tail m src dst
          else (m', s', d') :: remove_msg tail m src dst
        else (m', s', d') :: remove_msg tail m src dst
    end.

  Fixpoint contains_msg (net : list (Message * Node * Node)) (m : Message) (src dst : Node) : bool :=
    match net with
    | nil => false
    | (m', s', d') :: tail =>
        if eq_msg_dec m' m then
          if eq_node_dec s' src then
            if eq_node_dec d' dst then true
            else contains_msg tail m src dst
          else contains_msg tail m src dst
        else contains_msg tail m src dst
    end.
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
            ( (next_cfg.(pending_call) = cfg.(pending_call)) * (contains_msg cfg.(network) m src n = true) * (* <-- On vérifie qu'il est dans la liste *)
              (next_cfg.(network) = remove_msg cfg.(network) m src n) )%type
        | internal => 
            ( (next_cfg.(pending_call) = cfg.(pending_call)) * (next_cfg.(network) = cfg.(network)) )%type
        end ->
        Valid_Step A cfg n t next_cfg.

  Definition active_at (tr : nat -> option (Transition * Node)) (j : nat) (nd : Node) : Type :=
  { trans : Transition & tr j = Some (trans, nd) }.

  Definition is_correct (tr : nat -> option (Transition * Node)) (nd : Node) : Type :=
  forall (k : nat), { j : nat & ({ dt : nat & j = S (k + dt) } * active_at tr j nd)%type }.

  Definition is_crashed (tr : nat -> option (Transition * Node)) (nd : Node) : Type :=
  { k : nat & forall (j : nat), ({ dt : nat & j = S (k + dt) } * active_at tr j nd)%type -> False }.

  (*Definition active_at {A : Algorithme} (E : Execution A) (j : nat) (nd : Node) : Type :=
    { trans : Transition & E.(trace) j = Some (trans, nd) }.
  
  Definition is_correct {A : Algorithme} (E : Execution A) (nd : Node) : Type :=
    forall (k : nat), { j : nat & ({ dt : nat & j = S (k + dt) } * active_at E j nd)%type }.*)
  (* Exemple basique si tout le monde est connecté *)


  Record Execution (A : Algorithme) : Type := {
    configs : nat -> Config ;
    trace : nat -> option (Transition * Node) ;
    partitioned : Node -> Node -> nat -> bool ;
    init_exec : configs 0 = config_initiale A ;
    valid_exec : forall n : nat, 
      match trace n with
      | Some (t, current_node) => Valid_Step A (configs n) current_node t (configs (S n))
      | None => configs (S n) = configs n
      end ;
    reliable_channel : forall (i : nat) (m : Message) (src dst : Node),
      trace i = Some (send m dst, src) ->
      partitioned src dst i = true ->
      is_correct trace dst ->
      exists j, j > i /\ trace j = Some (receive m src, dst) ;
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
  
  (*construire un exec avec moins de t crash, dans une exec finie tout le monde crash, 
  construire exec infinie (faire des internals en boucle si aucune action, 
  dans tout état il doit y avoir un pas possible, soit internal, soit send, soit return)*)
  
  
  (*Definition is_crashed {A : Algorithme} (E : Execution A) (nd : Node) : Type :=
    { k : nat & forall (j : nat), ({ dt : nat & j = S (k + dt) } * active_at E j nd)%type -> False }.*)


  Fixpoint In_T (nd : Node) (l : list Node) : Type :=
    match l with
    | nil => False
    | h :: tail => (nd = h) + (In_T nd tail)
    end.

  (*Definition at_most_t_crashes {A : Algorithme} (E : Execution A) (t : nat) : Type :=
    { crashed_list : list Node & ((length crashed_list <= t) * (forall nd, is_crashed E nd -> In_T nd crashed_list))%type }.

  Definition t_resilient {A : Algorithme} (E : Execution A) (t : nat) : Type :=
    at_most_t_crashes E t ->
    forall (i : nat) (nd : Node),
      is_correct E nd -> 
      is_call E i nd -> 
      { j : nat & ({ dt : nat & j = S (i + dt) } * is_ret E j nd)%type }.
    
  Variable N_total : nat.

  Definition wait_free_gen {A : Algorithme} (E : Execution A) : Type :=
    t_resilient E (N_total - 1).*)

  Definition at_most_t_crashes {A : Algorithme} (E : Execution A) (t : nat) : Type :=
    { crashed_list : list Node & ((length crashed_list <= t) * (forall nd, is_crashed E.(trace) nd -> In_T nd crashed_list))%type }.

  Definition t_resilient {A : Algorithme} (E : Execution A) (t : nat) : Type :=
    at_most_t_crashes E t ->
    forall (i : nat) (nd : Node),
      is_correct E.(trace) nd -> 
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


Section Definitions_Globales.
  Variable Node : Type.
  Variable eq_node_dec : forall x y : Node, {x = y} + {x <> y}.
  Variable Message : Type.
  Variable eq_msg_dec : forall x y : Message, {x = y} + {x <> y}.
  Variable C R Q : Type.

  Definition Is_T_Resilient (A : Algorithme Node Message C R Q) (t : nat) : Type :=
    forall (Ex : Execution eq_node_dec eq_msg_dec A), t_resilient Ex t.

  Lemma t_resilient_mono : forall (A : Algorithme Node Message C R Q) (t1 t2 : nat),
    t1 <= t2 -> Is_T_Resilient A t2 -> Is_T_Resilient A t1.
  Proof.
    intros A t1 t2 Hle Hres E Hcrashes.
    apply Hres.
    destruct Hcrashes as [l [Hlen Hforall]].
    exists l; split; [lia|exact Hforall].
  Qed.
End Definitions_Globales.


Section Construction_Execution_Partitionnee.

  (* ----------------------------------------------------------------- *)
  (* 0. Les Fondations (Types de base)                                 *)
  (* ----------------------------------------------------------------- *)
  Variable Node : Type.
  Variable eq_node_dec : forall x y : Node, {x = y} + {x <> y}.
  Variable Message : Type.
  Variable eq_msg_dec : forall x y : Message, {x = y} + {x <> y}.
  Variable C R Q : Type.

  (* ----------------------------------------------------------------- *)
  (* 1. Le Contexte Local de l'Ordonnanceur                            *)
  (* ----------------------------------------------------------------- *)
  Variable A : Algorithme Node Message C R Q.
  Variable G1 G2 : list Node.

  (* Les hypothèses de notre Lemme 5.2 qu'on garde sous la main *)
  Hypothesis H_cover : forall n, In n G1 \/ In n G2.
  Hypothesis H_nodup : NoDup (G1 ++ G2).
  (* On passe explicitement eq_node_dec et eq_msg_dec avant A *)
  Hypothesis H_res_G2 : Is_T_Resilient eq_node_dec eq_msg_dec A (length G2).
  Hypothesis H_res_G1 : Is_T_Resilient eq_node_dec eq_msg_dec A (length G1).
 
  (* Cette fonction regarde l'état d'un nœud dans la configuration, 
     invoque l'algorithme, et renvoie l'action qu'il veut faire 
     et son nouvel état. *)
  Definition in_G1_bool (n : Node) : bool :=
    if in_dec eq_node_dec n G1 then true else false.

  Definition my_partitioned (src dst : Node) (_ : nat) : bool :=
    Bool.eqb (in_G1_bool src) (in_G1_bool dst).


  Definition can_communicate (src dest : Node) : bool :=
    match in_G1_bool src, in_G1_bool dest with
    | true, true => true   
    | false, false => true 
    | _, _ => false        
    end.

  Definition extract_local_step (cfg : Config Node Message Q) (n : Node) : (Transition Node Message C R * Q) :=
    let current_q := states cfg n in
    let '(existT _ lt next_q) := local_step A current_q in
    (to_Trans C lt, next_q).

  Definition apply_local_step (cfg : Config Node Message Q) (n : Node) : Config Node Message Q :=
    let '(trans, next_q) := extract_local_step cfg n in
    match trans with
    | internal _ _ _ _ => 
        {| states := update_state eq_node_dec (states cfg) n next_q;
           network := network cfg;
           pending_call := pending_call cfg |}
    | send _ _ m dest => 
        {| states := update_state eq_node_dec (states cfg) n next_q;
           network := add_msg (network cfg) m n dest;
           pending_call := pending_call cfg |}
    | ret _ _ _ r => 
        {| states := update_state eq_node_dec (states cfg) n next_q;
           network := network cfg;
           pending_call := update_pending eq_node_dec (pending_call cfg) n false |}
    | _ => cfg 
    end.


  (* On s'assure d'utiliser uniquement (Message * Node * Node) partout *)
  Fixpoint extract_valid_message_from_list (net : list (Message * Node * Node)) (n : Node) 
    : option (Message * Node * list (Message * Node * Node)) :=
    match net with
    | nil => None
    | (m, src, dest) :: tail =>
        if eq_node_dec dest n then
          if can_communicate src dest then
            Some (m, src, tail)
          else
            match extract_valid_message_from_list tail n with
            | Some (found_m, found_src, new_tail) => 
                Some (found_m, found_src, (m, src, dest) :: new_tail)
            | None => None
            end
        else
          match extract_valid_message_from_list tail n with
          | Some (found_m, found_src, new_tail) => 
              Some (found_m, found_src, (m, src, dest) :: new_tail)
          | None => None
          end
    end.

  (* 3.4. Application directe sur la Configuration *)
  Definition apply_receive_step (cfg : Config Node Message Q) (n : Node) : option (Config Node Message Q * Transition Node Message C R) :=
    match extract_valid_message_from_list (network cfg) n with
    | Some (m, src, new_net) =>
        let trans := receive C R m src in
        let '(existT _ next_q _) := input_step A (states cfg n) trans eq_refl in
        let new_cfg := {| 
           states := update_state eq_node_dec (states cfg) n next_q;
           network := new_net;
           pending_call := pending_call cfg 
        |} in
        Some (new_cfg, trans)
    | None => None
    end.

    Definition node_step (cfg : Config Node Message Q) (n : Node) 
    : (Config Node Message Q * Transition Node Message C R) :=
    match apply_receive_step cfg n with
    | Some res => 
        
        res 
    | None => 
        let '(trans, _) := extract_local_step cfg n in
        let new_cfg := apply_local_step cfg n in
        (new_cfg, trans)
    end.

  Definition all_nodes : list Node := G1 ++ G2.

  (* Fonction temporelle : désigne le nœud actif au temps t *)
  Definition schedule_node (t : nat) : option Node :=
    nth_error all_nodes (t mod (length all_nodes)).

  (* Fait avancer le système entier d'un "tic" d'horloge t *)
  Definition system_step (cfg : Config Node Message Q) (t : nat) 
    : (Config Node Message Q * option (Transition Node Message C R * Node)) :=
    match schedule_node t with
    | Some n => 
        let '(new_cfg, trans) := node_step cfg n in
        (new_cfg, Some (trans, n))
    | None => (cfg, None)
    end.

  Definition apply_call_step (cfg : Config Node Message Q) (n : Node) (c : C) 
    : (Config Node Message Q * Transition Node Message C R) :=
    
    (* 1. L'arobase @ force Coq à prendre les 4 types d'abord, puis la valeur c *)
    let trans := @call Node Message C R c in
    
    (* 2. On force l'algorithme à traiter cet appel (eq_refl prouve que ce n'est pas local) *)
    let '(existT _ next_q _) := input_step A (states cfg n) trans eq_refl in
    
    (* 3. On met à jour la configuration en marquant que ce nœud est occupé *)
    let new_cfg := {| 
       states := update_state eq_node_dec (states cfg) n next_q;
       network := network cfg;
       pending_call := update_pending eq_node_dec (pending_call cfg) n true
    |} in
    
    (new_cfg, trans).

    Variable n1 n2 : Node.
    Variable c_write1 c_read1 c_write2 c_read2 : C.
    Variable T1 T2 T3 T4 : nat.

    Definition director_step (t : nat) (cfg : Config Node Message Q) 
    : (Config Node Message Q * option (Transition Node Message C R * Node)) :=
    if t =? T1 then
      let '(new_cfg, trans) := apply_call_step cfg n1 c_write1 in
      (new_cfg, Some (trans, n1))
    else if t =? T2 then
      let '(new_cfg, trans) := apply_call_step cfg n1 c_read1 in
      (new_cfg, Some (trans, n1))
    else if t =? T3 then
      let '(new_cfg, trans) := apply_call_step cfg n2 c_write2 in
      (new_cfg, Some (trans, n2))
    else if t =? T4 then
      let '(new_cfg, trans) := apply_call_step cfg n2 c_read2 in
      (new_cfg, Some (trans, n2))
    else
      (* La majorité du temps, le réseau tourne normalement *)
      system_step cfg t.

  (* Le Cœur du Réacteur : On calcule l'état du monde au temps t par induction pure ! *)
  Fixpoint build_config (t : nat) : Config Node Message Q :=
    match t with
    | 0 => config_initiale A
    | S t' => fst (director_step t' (build_config t'))
    end.

  (* On extrait l'action qui a eu lieu au temps t *)
  Definition build_trace (t : nat) : option (Transition Node Message C R * Node) :=
    snd (director_step t (build_config t)).


  Lemma pending_call_false_before_T1 : 
  forall t, t <= T1 -> (pending_call (build_config t)) n1 = false.
  Proof.
    intros t Ht.
    induction t as [| t' IH].
    { 
      (* Cas t = 0 : état initial *)
      simpl.
      reflexivity. 
    }
  Admitted.

  Lemma pending_call_false_before_T2 : pending_call (build_config T2) n1 = false.
Proof.
  (* La preuve exacte ici nécessitera de faire un 'unfold build_config' 
     et de montrer qu'entre T1 (où l'appel a été fait) et T2, 
     le noeud n1 a bien reçu un événement 'ret' qui a remis 
     son pending_call à false.
  *)
  Admitted.

  Lemma pending_call_false_before_T3 : pending_call (build_config T3) n2 = false.
Proof. Admitted.

Lemma pending_call_false_before_T4 : pending_call (build_config T4) n2 = false.
  Proof. Admitted.

  Lemma my_exec_init : build_config 0 = config_initiale A.
  Proof.
    simpl. 
    reflexivity. 
  Qed.

  Lemma my_exec_valid_lemma : forall n : nat, 
  match build_trace n with
  | Some (t, current_node) => 
      Valid_Step eq_node_dec eq_msg_dec A (build_config n) current_node t (build_config (S n))
  | None => 
      build_config (S n) = build_config n
  end.
Proof.
  Admitted.


  Lemma my_exec_reliable_lemma : forall i m src dst,
  build_trace i = Some (send _ _ m dst, src) ->
  can_communicate src dst = true -> 
  is_correct build_trace dst ->
  exists j, j > i /\ build_trace j = Some (receive _ _ m src, dst).
Proof.
  Admitted.

Lemma my_exec_halting_lemma : forall n : nat, 
  build_trace n = None -> build_trace (S n) = None.
Proof.
  Admitted.



  Definition my_partitioned_execution : Execution eq_node_dec eq_msg_dec A.
  Proof.
    refine {|
      partitioned := my_partitioned ;
      configs := build_config ;
      trace := build_trace ;
      init_exec := _ ;
      valid_exec := _ ;
      reliable_channel := _ ;
      halting := _
    |}.
    
    - (* BUT 1 : init_exec (configs 0 = config_initiale) *)
      reflexivity.
      
    - (* BUT 2 : valid_exec (chaque pas respecte l'algorithme) *)
      intro n.
      (* 1. On déplie la définition de build_trace pour voir ce qu'il y a dedans *)
      unfold build_trace.
      
      (* 2. director_step renvoie une paire (nouvelle_config, option_trace). 
            On demande à Coq de nommer cette paire 'step_result' et d'analyser son contenu. *)
      remember (director_step n (build_config n)) as step_result.
      destruct step_result as [new_cfg opt_trace].
      
      (* 3. On simplifie le 'snd' qui extrait l'action de la paire *)
      simpl.
      
      (* 4. Maintenant, on analyse la nature de la trace (Some ou None) *)
      destruct opt_trace as [[trans current_node] | ].

      + (* Sous-cas 1 : Une transition a eu lieu (Some) *)
          
          (* 1. On remplace l'appel à director_step par son résultat connu (new_cfg, ...) *)
          rewrite <- Heqstep_result.
          
          (* 2. On simplifie le 'fst (new_cfg, ...)' qui devient simplement 'new_cfg' *)
          simpl.
          
          (* 3. On déplie le metteur en scène dans l'hypothèse pour préparer l'analyse *)
          unfold director_step in Heqstep_result.
          destruct (n =? T1) eqn:HeqT1.
          { 
            (* === CAS T1 : Injection du premier Call === *)
            unfold apply_call_step in Heqstep_result.
            
            (* On libère le paquet de l'algorithme (next_q et sa preuve Hstep) *)
            destruct (input_step A (states (build_config n) n1) (@call Node Message C R c_write1) eq_refl) as [next_q Hstep] eqn:Halgo.
            
            (* On unifie toutes nos variables (new_cfg, trans, current_node) avec celles du paquet *)
            inversion Heqstep_result; subst; clear Heqstep_result.
            
            (* C'est l'instant magique : on invoque ton constructeur ! *)
            apply step_intro.
            

            { (* Preuve 1 : mise à jour état *)
              assert (H_eq : update_state eq_node_dec (states (build_config n)) n1 next_q n1 = next_q). 
              { unfold update_state; destruct (eq_node_dec n1 n1); congruence. }
              simpl. rewrite H_eq. exact Hstep.
            }
            
            { (* Preuve 2 : mise à jour pending_call *)
              unfold apply_call_step. simpl.
              f_equal.
              unfold update_state.
              destruct (eq_node_dec n1 n1) as [eq | neq]; [reflexivity | congruence].
            }
            
            { (* Preuve 3 : vérification du Goal 1 (pending + network) *)
              apply Nat.eqb_eq in HeqT1.
              
              (* 2. Maintenant HeqT1 est devenu : n = T1. Utilise 'subst' *)
              subst n.
              
              (* 3. Ton but devient : pending_call (build_config T1) n1 = false. 
                Cependant, si le lemme attend (n <= T1), on peut le prouver facilement *)
              repeat split.

              { (* 1. Preuve du pending_call n1 = false *)
                apply pending_call_false_before_T1.
                apply Nat.le_refl.
              }
            }
          }
          destruct (n =? T2) eqn:HeqT2.
          { 
            (* Déballage global avant d'ouvrir les sous-buts *)
            inversion Heqstep_result; subst; clear Heqstep_result.
            unfold apply_call_step in H0.
            
            (* CORRECTION ICI : on ajoute @ et les types *)
            destruct (input_step A (states (build_config n) n1) (@call Node Message C R c_read1) eq_refl) as [next_q Hstep].
            
            inversion H0; subst; clear H0.
            
            econstructor.
            { (* Goal 1 : Preuve de l'étape de l'algorithme *)
              simpl. 
              destruct (eq_node_dec n1 n1); 
              simpl. 
              destruct (eq_node_dec n1 n1) as [eq | neq].
              unfold update_state. 
              destruct (eq_node_dec n1 n1).
              { exact Hstep. }
              { congruence. }
              exfalso. 
              apply neq. 
              reflexivity.
              unfold update_state.
              destruct (eq_node_dec n1 n1).
              { 
                (* Ici l'état est correctement mis à jour, on applique la preuve *)
                exact Hstep. 
              }
              { 
                (* Coq génère à nouveau le cas impossible, on le tue de la même façon *)
                exfalso. 
                apply n0. 
                reflexivity. 
              }
            }
            { (* Goal 2 : Égalité des états *)
              (* 1. On nettoie les records {||} qui polluent la vue *)
              simpl. 
              
              (* 2. On prouve que lire l'état mis à jour de n1 donne bien next_q *)
              assert (H_val : update_state eq_node_dec (states (build_config n)) n1 next_q n1 = next_q).
              { 
                unfold update_state. 
                destruct (eq_node_dec n1 n1) as [ | neq].
                - reflexivity.
                - exfalso. apply neq. reflexivity.
              }
              
              (* 3. On remplace ce gros bloc par next_q dans le Goal principal *)
              rewrite H_val.
              
              (* 4. Maintenant les deux côtés sont rigoureusement identiques *)
              reflexivity. 
            }
            { (* Goal 3 : Gestion du réseau et du call *)
              (* On nettoie les cas évidents (le réseau qui ne change pas, etc.) *)
              repeat split; try reflexivity. 
              
              (* 1. On dit à Coq qu'on est exactement au temps T2 *)
              apply Nat.eqb_eq in HeqT2.
              subst n.
              apply pending_call_false_before_T2.
              
            }
          }
          destruct (n =? T3) eqn:HeqT3.
          { 
            (* --- CAS T3 --- *)
            inversion Heqstep_result; subst; clear Heqstep_result.
            
            (* On déplie sur H0 *)
            unfold apply_call_step in H0.
            
            (* On destruct sur n2 *)
            destruct (input_step A (states (build_config n) n2) (@call Node Message C R c_write2) eq_refl) as [next_q Hstep].
            
            (* On inverse H0 et on le nettoie *)
            inversion H0; subst; clear H0.
            
            econstructor.
            { (* Goal 1 : Preuve algorithme *)
              simpl. 
              unfold update_state.
              destruct (eq_node_dec n2 n2) as [ | neq].
              - exact Hstep.
              - exfalso; apply neq; reflexivity.
            }
            { (* Goal 2 : Égalité des états *)
              simpl.
              assert (H_val : update_state eq_node_dec (states (build_config n)) n2 next_q n2 = next_q).
              { 
                unfold update_state. destruct (eq_node_dec n2 n2) as [ | neq].
                - reflexivity.
                - exfalso. apply neq. reflexivity.
              }
              rewrite H_val. reflexivity.
            }
            { (* Goal 3 : Call dispo *)
              repeat split; try reflexivity. 
              apply Nat.eqb_eq in HeqT3; subst.
              apply pending_call_false_before_T3.
            }
          }


          destruct (n =? T4) eqn:HeqT4.
          { 
            (* --- CAS T4 --- *)
            inversion Heqstep_result; subst; clear Heqstep_result.
            
            (* L'hypothèse s'appelle bien H0 ici ! *)
            unfold apply_call_step in H0.
            
            destruct (input_step A (states (build_config n) n2) (@call Node Message C R c_read2) eq_refl) as [next_q Hstep].
            
            inversion H0; subst; clear H0.
            
            econstructor.
            { (* Goal 1 : Preuve algorithme *)
              simpl. 
              unfold update_state.
              destruct (eq_node_dec n2 n2) as [ | neq].
              - exact Hstep.
              - exfalso; apply neq; reflexivity.
            }
            { (* Goal 2 : Égalité des états *)
              simpl.
              assert (H_val : update_state eq_node_dec (states (build_config n)) n2 next_q n2 = next_q).
              { 
                unfold update_state. destruct (eq_node_dec n2 n2) as [ | neq].
                - reflexivity.
                - exfalso. apply neq. reflexivity.
              }
              rewrite H_val. reflexivity.
            }
            { (* Goal 3 : Call dispo *)
              repeat split; try reflexivity. 
              apply Nat.eqb_eq in HeqT4; subst.
              apply pending_call_false_before_T4.
            }
          }
          
          (* --- CAS PAR DÉFAUT (system_step en tâche de fond) --- *)
          { 
            (* On nettoie les variables si nécessaire *)
            inversion Heqstep_result; subst; clear Heqstep_result.
            
            (* 1. On ouvre le moteur du réseau dans l'hypothèse H0 *)
            unfold system_step in H0.
            
            (* 2. On regarde qui l'ordonnanceur a décidé de réveiller *)
            destruct (schedule_node n) as [n_sched | ].
            {
              (* Cas Normal : Le noeud n_sched s'est réveillé *)
              (* On extrait le résultat de son exécution (la fonction node_step) *)
              destruct (node_step (build_config n) n_sched) as [cfg_next trans_next] eqn:Hnode.
              
              (* On aligne nos variables (new_cfg devient cfg_next, etc.) *)
              inversion H0; subst; clear H0.
              
              (* 3. L'INSTANT DE VÉRITÉ *)
              (* Le but est maintenant de prouver que ce node_step est un Valid_Step. *)
              (* Cherche le lemme de ton fichier qui fait ce pont ! *)
              
              (* Exemple : *)
              (* apply valid_node_step. *)
              (* exact Hnode. *)
              
              unfold node_step in Hnode.
              
              (* Ici, on va devoir destructurer l'action interne (le existT / input_step) *)
              (* destruct (input_step A ...) as [next_q Hstep]. *)
              
              unfold node_step in Hnode.
              
              (* On analyse le comportement du noeud : Réception de message ou Action locale *)
              destruct (apply_receive_step (build_config n) n_sched) as [[cfg_rec trans_rec] | ] eqn:Hrecv.
              {
                (* Sous-cas A : Un message a été reçu (apply_receive_step) *)
                inversion Hnode; subst; clear Hnode.
                
                (* La preuve nécessite d'ouvrir apply_receive_step pour exposer le existT *)
                admit. 
              }
              {
                (* Sous-cas B : Aucune réception, c'est une action interne (apply_local_step) *)
                destruct (extract_local_step (build_config n) n_sched) as [trans_loc dummy] eqn:Hext.
                inversion Hnode; subst; clear Hnode.
                
                (* La preuve nécessite d'ouvrir apply_local_step pour exposer le existT *)
                admit.
              }
            }
            {
              (* Cas Absurde : L'ordonnanceur dort (None), mais on a une trace (Some) *)
              inversion H0.
            }
          }

      + (* Sous-cas 2 : Aucune transition n'a eu lieu (opt_trace = None) *)
        
        (* 1. LA LIGNE MAGIQUE : On remplace la fonction par new_cfg dans le but AVANT de la détruire *)
        rewrite <- Heqstep_result.
        
        (* Le but devient proprement 'new_cfg = build_config n' *)
        simpl.

        (* 2. Maintenant on déroule notre rouleau compresseur sur l'hypothèse *)
        unfold director_step in Heqstep_result.
        
        destruct (n =? T1).
        { destruct (apply_call_step (build_config n) n1 c_write1) as [cfg_t trans_t]. inversion Heqstep_result. }
        
        destruct (n =? T2).
        { destruct (apply_call_step (build_config n) n1 c_read1) as [cfg_t trans_t]. inversion Heqstep_result. }
        
        destruct (n =? T3).
        { destruct (apply_call_step (build_config n) n2 c_write2) as [cfg_t trans_t]. inversion Heqstep_result. }
        
        destruct (n =? T4).
        { destruct (apply_call_step (build_config n) n2 c_read2) as [cfg_t trans_t]. inversion Heqstep_result. }
        
        (* 3. Le repos *)
        unfold system_step in Heqstep_result.
        destruct (schedule_node n) as [n_sched | ].
        { 
          destruct (node_step (build_config n) n_sched) as [cfg_next trans_next]. 
          inversion Heqstep_result. 
        }
        { 
          (* Fin du jeu. *)
          inversion Heqstep_result; subst. 
          reflexivity. 
        }

Admitted.

End Construction_Execution_Partitionnee.



Section Preuve_CAP.
  Variable Node : Type.
  Variable all_nodes : list Node.
  Hypothesis all_nodes_nodup    : NoDup all_nodes.
  Hypothesis all_nodes_complete : forall n : Node, In n all_nodes.
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

  Definition Maintains_Seq_Consistency (A : Algorithme Node Message C R Q) : Type :=
    forall (Ex : Execution eq_node_dec eq_msg_dec A), crit_seq ConcreteMX (extract_history Ex).

  Definition Is_T_Resilient (A : Algorithme Node Message C R Q) (t : nat) : Type :=
    forall (Ex : Execution eq_node_dec eq_msg_dec A), t_resilient Ex t.

  (* ----------------------------------------------------------------- *)
  (* Définitions pour la partition et l’indistinguabilité              *)
  (* ----------------------------------------------------------------- *)

  Definition Partition_UpTo {A : Algorithme Node Message C R Q}
                            (Ex : Execution eq_node_dec eq_msg_dec A)
                            (G1 G2 : list Node) (T : nat) : Type :=
    forall (i j : nat) (m : Message) (src dst : Node),
      j <= T ->
      Ex.(trace) i = Some (@send Node Message C R m dst, src) ->
      Ex.(trace) j = Some (@receive Node Message C R m src, dst) ->
      ((In_T src G1 * In_T dst G2) + (In_T src G2 * In_T dst G1))%type -> False.

  Definition Indistinguishable_UpTo {A : Algorithme Node Message C R Q}
                                    (Ex1 Ex2 : Execution eq_node_dec eq_msg_dec A)
                                    (G : list Node) (T : nat) : Type :=
    forall (t : nat) (nd : Node),
      t <= T -> In_T nd G -> Ex1.(trace) t = Ex2.(trace) t.

  Record CAP_Scenario {A : Algorithme Node Message C R Q}
                    (Ex : Execution eq_node_dec eq_msg_dec A)
                    (G1 G2 : list Node) (T_max : nat) : Type := {
  (* Opérations dans G1 *)
  op_w1 : Completed_Op Ex ;
  op_r1 : Completed_Op Ex ;
  w1_in_G1 : In_T (op_node op_w1) G1 ;
  same_node1 : op_node op_w1 = op_node op_r1 ;
  r1_in_G1 : In_T (op_node op_r1) G1 ;
  is_write1 : op_call op_w1 = w_x ;
  is_read1  : op_call op_r1 = r_y ;
  prog_order1 : t_ret op_w1 < t_call op_r1 ;

  (* Opérations dans G2 *)
  op_w2 : Completed_Op Ex ;
  op_r2 : Completed_Op Ex ;
  w2_in_G2 : In_T (op_node op_w2) G2 ;
  same_node2 : op_node op_w2 = op_node op_r2 ;
  r2_in_G2 : In_T (op_node op_r2) G2 ;
  is_write2 : op_call op_w2 = w_y ;
  is_read2  : op_call op_r2 = r_x ;
  prog_order2 : t_ret op_w2 < t_call op_r2 ;

  (* La partition est active jusqu'à la fin de toutes les opérations *)
  partition_active : t_ret op_r1 <= T_max /\ t_ret op_r2 <= T_max
}.
  Lemma t_resilient_mono : forall (A : Algorithme Node Message C R Q) (t1 t2 : nat),
    t1 <= t2 -> Is_T_Resilient A t2 -> Is_T_Resilient A t1.
  Proof.
    intros A t1 t2 Hle Hres E Hcrashes.
    apply Hres.
    destruct Hcrashes as [l [Hlen Hforall]].
    exists l; split; [lia|exact Hforall].
  Qed.

  (* ----------------------------------------------------------------- *)
  (* 5.1 Partitionnement des nœuds (combinatoire)                     *)
  (* ----------------------------------------------------------------- *)

   Lemma exists_partition :
    forall (t : nat),
      2 * t >= length all_nodes ->
      exists (G1 G2 : list Node),
        (forall n, In n all_nodes -> In n G1 \/ In n G2) /\
        NoDup (G1 ++ G2) /\
        length G1 <= t /\
        length G2 <= t.
  Proof.
    intros t Ht.
    exists (firstn t all_nodes), (skipn t all_nodes).
    split; [ | split; [ | split ] ].
    - intros n Hin.
      pose proof (firstn_skipn t all_nodes) as Hsplit.
      rewrite <- Hsplit in Hin.
      apply in_app_iff in Hin; exact Hin.
    - rewrite firstn_skipn; exact all_nodes_nodup.
    - rewrite firstn_length; apply Nat.le_min_l.
    - rewrite skipn_length; lia.
  Qed.
  (* ----------------------------------------------------------------- *)
  (* 5.2 Existence d’une exécution partitionnée (admis)               *)
  (* ----------------------------------------------------------------- *)

    Lemma exists_partitioned_execution :
    forall (A : Algorithme Node Message C R Q) (G1 G2 : list Node),
      (forall n, In n G1 \/ In n G2) ->
      NoDup (G1 ++ G2) ->
      Is_T_Resilient A (length G2) ->
      Is_T_Resilient A (length G1) ->
      { Ex : Execution eq_node_dec eq_msg_dec A & { T : nat & (Partition_UpTo Ex G1 G2 T * CAP_Scenario Ex G1 G2 T) %type } }.
  Proof.
  Admitted.

  (* ----------------------------------------------------------------- *)
  (* 5.3 Aucune écriture parasite entre l’écriture et la lecture      *)
  (* ----------------------------------------------------------------- *)
  Lemma no_write_between :
    forall (A : Algorithme Node Message C R Q) (Ex : Execution eq_node_dec eq_msg_dec A)
           (G1 G2 : list Node) (T : nat) (op_w op_r : Completed_Op Ex),
      Partition_UpTo Ex G1 G2 T ->
      CAP_Scenario Ex G1 G2 T ->
      forall (aseq : Seq C) (eseq : Seq (Completed_Op Ex))
             (H_EvSeq : EventSeq (extract_history Ex) eseq)
             (H_ADTSeq : forall n, ADTSeq ConcreteMX aseq n = Ba (H := extract_history Ex) eseq n)
             (iw ir : nat),
        iw = projT1 (exhausts H_EvSeq op_w) ->
        ir = projT1 (exhausts H_EvSeq op_r) ->
        forall (k : nat) (cmd : C),
          iw < k < ir ->
          aseq k = Some cmd ->
          forall v', cmd <> write x v'.
  Proof.
  Admitted.
  (* ----------------------------------------------------------------- *)
  (* 5.4 La lecture retourne la valeur initiale                        *)
  (* ----------------------------------------------------------------- *)

  Lemma read_returns_v_init :
    forall (A : Algorithme Node Message C R Q) (Ex : Execution eq_node_dec eq_msg_dec A)
           (G1 G2 : list Node) (T : nat) (op_r : Completed_Op Ex),
      Partition_UpTo Ex G1 G2 T ->
      CAP_Scenario Ex G1 G2 T ->
      Maintains_Seq_Consistency A ->
      op_ret op_r = out_mem x v_init.
  Proof.
  Admitted.

    Lemma eval_stable_after_write :
    forall (aseq : Seq C) (addr : Addr) (v : nat) (i j : nat),
      i < j -> 
      aseq i = Some (write addr v) ->
      (forall k, i < k < j -> forall cmd, aseq k = Some cmd -> forall v', cmd <> write addr v') ->
      eval ConcreteMX aseq j addr = v.
  Proof.
    intros aseq addr v i j Hlt Hw Hno_w.
    unfold C in *.
    destruct aseq as [f_seq f_dnr].
    simpl in *.
    induction j as [|j' IHj].
    - lia.
    - destruct (Nat.eq_dec i j') as [Heq | Hneq].
      + subst j'. simpl. rewrite Hw. simpl.
        destruct (Nat.eq_dec addr addr); [reflexivity | congruence].
      + assert (Hlt' : i < j') by lia.
        assert (Hno_w' : forall k, i < k < j' -> forall cmd, f_seq k = Some cmd -> forall v', cmd <> write addr v').
        { intros k Hk cmd Hcmd v' Heq. eapply (Hno_w k); eauto. lia. }
        specialize (IHj Hlt' Hno_w').
        simpl.
        destruct (f_seq j') as [cmd|] eqn:Hcmd.
        * assert (Hpreserve : fst (Transition_mem Nat.eq_dec (eval ConcreteMX {| seq := f_seq; does_not_restart := f_dnr |} j') cmd) addr = eval ConcreteMX {| seq := f_seq; does_not_restart := f_dnr |} j' addr).
          { destruct cmd as [addr' n | addr']; simpl.
            - destruct (Nat.eq_dec addr addr') as [Heq_addr | Hne_addr].
              + exfalso. eapply (Hno_w j'); eauto. 
              + reflexivity.
            - reflexivity. }
          rewrite Hpreserve. exact IHj.
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

  (* ----------------------------------------------------------------- *)
  (* 5.5 Preuve principale du théorème CAP                             *)
  (* ----------------------------------------------------------------- *)

  Theorem CAP_Impossibility :
    forall (A : Algorithme Node Message C R Q) (t : nat),
      2 * t >= length all_nodes ->
      Is_T_Resilient A t ->
      Maintains_Seq_Consistency A ->
    False.
  Proof.
    Proof.
    intros A t Ht Hresilient Hcons.
    (* 1. Obtenir une partition G1, G2 à partir de la liste des noeuds *)
    destruct (exists_partition t Ht) as [G1 [G2 [Hcover [Hnodup [Hlen1 Hlen2]]]]].
    (* Hcover : forall n, In n all_nodes -> In n G1 \/ In n G2 *)
    
    assert (Hcover_all : forall n, In n G1 \/ In n G2). {
      intro n; apply Hcover, all_nodes_complete.
    }
    (* 2. Construire l’exécution partitionnée Ex *)
    pose proof (@t_resilient_mono A (length G1) t Hlen1 Hresilient) as Hres1.
    pose proof (@t_resilient_mono A (length G2) t Hlen2 Hresilient) as Hres2.
    destruct (@exists_partitioned_execution A G1 G2 Hcover_all Hnodup Hres2 Hres1)
      as [Ex [T [Hpart Hscen]]].
   
    (* 3. Appliquer la cohérence séquentielle à Ex *)
    pose proof (Hcons Ex) as Hcrit.
    destruct Hcrit as [aseq [eseq [HevSeq Heq]]].
    destruct HevSeq as [mono exhausts].
    
    (* 4. Extraire les opérations du scénario (l'ordre doit correspondre au Record) *)
    destruct Hscen as [op_w1 op_r1 Hw1_in_G1 same_node1 Hr1_in_G1 is_write1 is_read1 prog_order1
                       op_w2 op_r2 Hw2_in_G2 same_node2 Hr2_in_G2 is_write2 is_read2 prog_order2
                       Hpart_active].
    destruct Hpart_active as [Hactive1 Hactive2].

    (* 5. Obtenir leurs indices dans la séquence linéarisée *)
    destruct (exhausts op_w1) as [iw1 Hiw1].
    destruct (exhausts op_r1) as [ir1 Hir1].
    destruct (exhausts op_w2) as [iw2 Hiw2].
    destruct (exhausts op_r2) as [ir2 Hir2].

    (* 6. Prouver les relations d'ordre programme intra-groupe *)
    assert (Hord1 : prog_order op_w1 op_r1). {
      apply PO_step.
      - exact same_node1. (* On utilise l'égalité stricte des noeuds, pas l'appartenance In_T *)
      - pose proof (proof_time op_w1). lia. (* proof_time garantit t_call < t_ret, complétant prog_order1 *)
    }
    assert (Hord2 : prog_order op_w2 op_r2). {
      apply PO_step.
      - exact same_node2.
      - pose proof (proof_time op_w2). lia.
    }

    (* 7. L'ordre dans la séquence linéarisée *)
    pose proof (mono _ _ _ _ Hiw1 Hir1 Hord1) as Hle1.   (* iw1 <= ir1 *)
    pose proof (mono _ _ _ _ Hiw2 Hir2 Hord2) as Hle2.   (* iw2 <= ir2 *)

    (* 8. Les lectures retournent la valeur initiale (admis pour l'instant) *)
    assert (Hresp1 : op_ret op_r1 = out_mem y v_init). { admit. }
    assert (Hresp2 : op_ret op_r2 = out_mem x v_init). { admit. }

    (* 9. Aucune écriture parasite n'intervient (admis pour l'instant) *)
    assert (Hno_write_y : forall (k : nat) (cmd : C),
              iw2 < k < ir1 -> aseq k = Some cmd -> forall v', cmd <> write y v'). { admit. }
    assert (Hno_write_x : forall (k : nat) (cmd : C),
              iw1 < k < ir2 -> aseq k = Some cmd -> forall v', cmd <> write x v'). { admit. }

    (* 10. Extraire les égalités ADT pour chaque indice *)
    assert (Heq_ir1 : ADTSeq ConcreteMX aseq ir1 = Ba eseq ir1) by apply Heq.
    assert (Heq_ir2 : ADTSeq ConcreteMX aseq ir2 = Ba eseq ir2) by apply Heq.
    assert (Heq_iw2 : ADTSeq ConcreteMX aseq iw2 = Ba eseq iw2) by apply Heq.
    assert (Heq_iw1 : ADTSeq ConcreteMX aseq iw1 = Ba eseq iw1) by apply Heq.

    unfold Ba, seq, ADTSeq in *; simpl in *.
    rewrite Hir1, Hir2, Hiw2, Hiw1 in *; simpl in *.

    (* Récupération des commandes lues *)
    destruct (aseq ir1) as [cmd_r1|] eqn:Haseq_ir1; [|discriminate Heq_ir1].
    destruct (aseq ir2) as [cmd_r2|] eqn:Haseq_ir2; [|discriminate Heq_ir2].
    destruct (aseq iw2) as [cmd_w2|] eqn:Haseq_iw2; [|discriminate Heq_iw2].
    destruct (aseq iw1) as [cmd_w1|] eqn:Haseq_iw1; [|discriminate Heq_iw1].

    injection Heq_ir1; intros H_snd1 H_fst1; subst cmd_r1.
    injection Heq_ir2; intros H_snd2 H_fst2; subst cmd_r2.
    injection Heq_iw2; intros _ H_fst2'; subst cmd_w2.
    injection Heq_iw1; intros _ H_fst1'; subst cmd_w1.

    (* 11. Application des lemmes mémoire *)
    assert (Hno_write_y'' : forall k, iw2 < k < ir1 -> forall cmd, aseq k = Some cmd -> forall v', cmd <> write y v'). {
      intros k Hk cmd Hcmd v'. apply (Hno_write_y k cmd Hk). simpl in Hcmd; exact Hcmd.
    }
    assert (Hno_write_x'' : forall k, iw1 < k < ir2 -> forall cmd, aseq k = Some cmd -> forall v', cmd <> write x v'). {
      intros k Hk cmd Hcmd v'. apply (Hno_write_x k cmd Hk). simpl in Hcmd; exact Hcmd.
    }

    (* Pour y *)
    assert (Haseq_iw2' : aseq iw2 = Some w_y). { rewrite is_write2 in Haseq_iw2; exact Haseq_iw2. }
    assert (Haseq_ir1' : aseq ir1 = Some r_y). { rewrite is_read1 in Haseq_ir1; exact Haseq_ir1. }
    assert (Hy : snd (ConcreteMX.(transition) (eval ConcreteMX aseq ir1) r_y) = out_mem y v_init). {
      unfold ConcreteMX; simpl. rewrite is_read1 in H_snd1. rewrite Hresp1 in H_snd1. exact H_snd1.
    }
    assert (Hlt_y : ir1 < iw2). {
      apply (@read_returns_init_implies_no_write_y aseq iw2 ir1 Haseq_iw2' Haseq_ir1' Hno_write_y'' Hy).
    }

    (* Pour x *)
    assert (Haseq_iw1' : aseq iw1 = Some w_x). { rewrite is_write1 in Haseq_iw1; exact Haseq_iw1. }
    assert (Haseq_ir2' : aseq ir2 = Some r_x). { rewrite is_read2 in Haseq_ir2; exact Haseq_ir2. }
    assert (Hx : snd (ConcreteMX.(transition) (eval ConcreteMX aseq ir2) r_x) = out_mem x v_init). {
      unfold ConcreteMX; simpl. rewrite is_read2 in H_snd2. rewrite Hresp2 in H_snd2. exact H_snd2.
    }
    assert (Hlt_x : ir2 < iw1). {
      apply (@read_returns_init_implies_no_write_x aseq iw1 ir2 Haseq_iw1' Haseq_ir2' Hno_write_x'' Hx).
    }

    (* 12. Contradiction cyclique *)
    lia.
  Qed.
End Preuve_CAP.