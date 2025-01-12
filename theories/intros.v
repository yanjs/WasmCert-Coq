From Wasm Require Export datatypes_properties operations typing opsem common properties subtyping_properties typing_inversion instantiation_func.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Bool Program NArith ZArith Wf_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section intro_opsem.
  
Context `{ho: host}.

(* Reduction of an instruction sequence.
   There's no explicit rule that allows this, yet this is certainly an expected behaviour. Prove the following by finding one/several appropriate reduction rule(s) that allows the reduction:
 *) 
Lemma opsem_reduce_seq1: forall hs1 s1 f1 es1 hs2 s2 f2 es2 es0,
      reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
      reduce hs1 s1 f1 (es1 ++ es0) hs2 s2 f2 (es2 ++ es0).
Proof.
  intros.
  apply r_label with (es := es1) (es' := es2) (k := 0) (lh := LH_base [::] es0).
  - apply H.
  - auto.
  - auto.
Qed.
  
(* The same applies for attaching a list of values on the left. *)
Lemma opsem_reduce_seq2: forall hs1 s1 f1 es1 hs2 s2 f2 es2 vs,
    const_list vs ->
    reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
    reduce hs1 s1 f1 (vs ++ es1) hs2 s2 f2 (vs ++ es2).
Proof.
  intros.
  apply const_es_exists in H.
  destruct H as [vs0 Hvs].
  apply r_label with (es := es1) (es' := es2) (k := 0) (lh := LH_base vs0 [::]).
  - apply H0.
  - simpl.
    rewrite -Hvs catA cats0 //.
  - simpl.
    rewrite -Hvs catA cats0 //.
Qed.

Variable hs: host_state.

(* Is the above true without the const_list assumption?
   Prove or disprove it by establishing a witness to the following: *)
(* [nop] --reduce-> [] *)
(* [trap;trap;nop]  no reduction rule to [trap;trap] *)
Lemma opsem_reduce_seq2':
    {forall s1 f1 es1 s2 f2 es2 es0,
    reduce hs s1 f1 es1 hs s2 f2 es2 ->
    reduce hs s1 f1 (es0 ++ es1) hs s2 f2 (es0 ++ es2)} +
    {exists s1 f1 es1 s2 f2 es2 es0,
    (reduce hs s1 f1 es1 hs s2 f2 es2 ->
     reduce hs s1 f1 (es0 ++ es1) hs s2 f2 (es0 ++ es2)) -> False}.
Proof.
  right.
  exists empty_store_record.
  exists empty_frame.
  exists [::AI_basic BI_nop].
  exists empty_store_record.
  exists empty_frame.
  exists [::].
  exists [:: AI_trap; AI_trap].
  rewrite cats0.
  intros.
  assert (reduce hs empty_store_record empty_frame [:: AI_basic BI_nop]
    hs empty_store_record empty_frame [::]).
  {
    apply r_simple.
    apply rs_nop.
  }
  apply H in H0.
  dependent induction H0.
  - inversion H0; subst.
  - apply extract_list3 in x0 as [H11 H12].
    inversion H12.
  - 
    apply IHreduce; eauto.
    induction lh.
    + unfold lfill in x0.
      unfold lfill in x.
      destruct l.
      simpl in x0.
      * destruct es'. simpl in x.
        rewrite x in x0.
        assert (es ++ [:: AI_trap; AI_trap] = (es ++ [:: AI_trap]) ++ [:: AI_trap]). { rewrite -catA. by []. }
        rewrite H1 in x0.
        apply extract_list3 in x0.
        destruct x0.
        inversion H3.
      * inversion x.
        destruct es'.
        simpl in H3.
        rewrite H3 in x0.
        apply extract_list3 in x0.
        destruct x0. inversion H4.
      * inversion H3.
        apply cat0_inv in H5.
        destruct H5.
        subst.
        rewrite cats0 in x0.
        rewrite x0.
        by [].
      * inversion x0.
        destruct v; unfold v_to_e in H2; inversion H2.
        destruct v; unfold vref_to_e in H2; inversion H2.
    + unfold lfill in x0.
      destruct l.
      * simpl in x0.
        inversion x0.
      * simpl in x0.
        inversion x0.
        destruct v; unfold v_to_e in H2; inversion H2.
        destruct v; unfold vref_to_e in H2; inversion H2.
(* The proof is too verbose. *)
    induction lh.
    + unfold lfill in x0.
      unfold lfill in x.
      destruct l.
      simpl in x0.
      * destruct es'. simpl in x.
        rewrite x in x0.
        assert (es ++ [:: AI_trap; AI_trap] = (es ++ [:: AI_trap]) ++ [:: AI_trap]). { rewrite -catA. by []. }
        rewrite H1 in x0.
        apply extract_list3 in x0.
        destruct x0.
        inversion H3.
      * inversion x.
        destruct es'.
        simpl in H3.
        rewrite H3 in x0.
        apply extract_list3 in x0.
        destruct x0. inversion H4.
      * inversion H3.
        apply cat0_inv in H5.
        destruct H5.
        subst. eauto.
      * inversion x0.
        destruct v; unfold v_to_e in H2; inversion H2.
        destruct v; unfold vref_to_e in H2; inversion H2.
    + unfold lfill in x0.
      destruct l.
      * simpl in x0.
        inversion x0.
      * simpl in x0.
        inversion x0.
        destruct v; unfold v_to_e in H2; inversion H2.
        destruct v; unfold vref_to_e in H2; inversion H2.
Qed.

Inductive test_same : nat -> Prop :=
  | ts_default n: test_same n -> test_same n.

Print test_same_sind.
Print test_same_ind.

End intro_opsem.

Section intro_types.

Context `{ho: host}.

(* The newer proposals of Wasm introduces a notion of a subtyping relation <:,
   which did not exist in Wasm 1.0 (and not even formally in Wasm 2.0).

   This is implemented in the Coq mechanisation, which complicates the type
   system slightly. If a program can be associated with a function type, then
   it can also be associated with any supertype of that function type
   (`bet_subtyping`).

   The following exercise helps to understand how instruction subtyping works.
 *)
Lemma subtypes_1:
  instr_subtyping (Tf nil [::T_num T_i32]) (Tf [::T_num T_i32] [::T_num T_i32; T_num T_i32]).
Proof.
  apply instr_subtyping_weaken with (ts := [::T_num T_i32]).
  apply instr_subtyping_eq.
Qed.

Notation "$N v" := (BI_const_num v) (at level 20).

(* Establish the following typing derivation by applying the composition
   rule `bet_composition`, with appropriate rewrites and other typing rules
   in the `be_typing` inductive definition. *)
Lemma types_composition: forall C c1 c2,
  be_typing C [:: $N (VAL_int32 c1); $N (VAL_int32 c2); BI_binop T_i32 (Binop_i BOI_add)] (Tf nil [::T_num T_i32]).
Proof.
  intros.
  eapply bet_composition with (e := BI_binop T_i32 (Binop_i BOI_add))
    (es := [:: $N (VAL_int32 c1)] ++ [:: $N (VAL_int32 c2)]).
  - eapply bet_composition with (e := $N (VAL_int32 c2)).
    + apply bet_const_num.
    + eapply bet_subtyping.
      * apply bet_const_num.
      * eapply instr_subtyping_weaken with (ts := [:: T_num (typeof_num (VAL_int32 c1))]).
        apply instr_subtyping_eq.
  - apply bet_binop.
    apply Binop_i32_agree.
Qed.

(* The following 2 are slightly more difficult *)
(* It is slightly awkward to apply the `bet_composition` rule, since it only
   allows appending one instruction at a time instead of allowing arbitrary
   concatenation of instruction lists. The following composition typing lemma
   is a more general version. Prove it by an appropriate induction.
*)
Lemma bet_composition2: forall C es1 es2 ts1 ts2 ts3,
    be_typing C es1 (Tf ts1 ts2) ->
    be_typing C es2 (Tf ts2 ts3) ->
    be_typing C (es1 ++ es2) (Tf ts1 ts3).
Proof.
  intros until ts3.
  dependent induction es2 using List.rev_ind.
  - intros H112 H223.
    apply empty_typing in H223.
    rewrite cats0.
    eapply bet_subtyping.
    + apply H112.
    + simpl.
      exists [::], [::], ts1, ts3.
      repeat split; auto.
      apply values_subtyping_eq.
  - intros H112 H223.
    rewrite catA.
    eapply be_composition_typing in H223 as [ts4 [H224 Hx43]].
    eapply bet_composition.
    + eapply IHes2.
      apply H112.
    + apply H224.
    + apply Hx43.
Qed.

(* The following 'typing inversion lemma' is some sort of a converse to the
   one above. Prove it by an appropriate induction.
   These typing inversion lemmas are key to proving the soundness properties,
   as they provide a way to extract information from the typing premises.
 *)
Lemma be_composition_inversion: forall C es1 es2 t1s t2s,
    be_typing C (es1 ++ es2) (Tf t1s t2s) ->
    exists t3s, be_typing C es1 (Tf t1s t3s) /\
           be_typing C es2 (Tf t3s t2s).
Proof.
  intros until t2s.
  intros Hcat.
  dependent induction es2 using List.rev_ind.
  - exists t2s.
    split.
    + rewrite cats0 in Hcat.
      apply Hcat.
    + eapply bet_subtyping.
      * apply bet_empty.
      * simpl.
        exists t2s, t2s, [::], [::].
        repeat (split); try (rewrite cats0; auto).
        apply values_subtyping_eq.
    + (* TODO *)
Admitted.

End intro_types.
