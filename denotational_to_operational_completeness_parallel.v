(**
  @name Formalization of Verilog
  @version 0.1
  @authors Zhao Hongyan
  @date 11/2/2022
  @description From Denotational semantics to Operational Semantics 
 **)
Add LoadPath "/Users/blackcat/formalization_of_MDESL/".

Require Import syntax.
Require Import Logic.ClassicalFacts.
Require Import Logic.Classical_Prop.
Require Import Omega.
Require Import Arith.
Require Import List.
Require Import String.
Import ListNotations.
Require Import denotational_semantics.
Require Import denotational_to_operational_soundness.
Require Import denotational_to_operational_completeness.
Require Import denotational_to_operational_soundness_parallel.
Require Import FunctionalExtensionality.
Require Import CpdtTactics.

(* add helpful lemma 4.8 in denotational_to_operational_soundness *)
Lemma helpfulLemma_4_8 :
  forall (x : id) (v : nat),
  PhaseCond_3_1 x v = bCondTripored C_null (triger_nf x v).
Proof.
  (** TODO: **)
Admitted.

Lemma andt_abso :
  forall P Q, andt P (andt P Q) = andt P Q.
Proof.
  intros. do 2 (apply functional_extensionality;intros).
  unfold andt. apply EquivThenEqual; split; crush.
Qed.

Lemma bCondTripored_abso :
  forall (b : trans) (P : tripored),
  b /H\ (b /H\ P) = b /H\ P.
Proof.
  intros. unfold bCondTripored.
  destruct P as ((q1, w1), t1).
  unfold qt, wt, tt. simpl.
  rewrite <- double_nott. do 3 rewrite andt_abso.
  reflexivity.
Qed.

(* (P \/ Q) \/ R = P \/ (Q \/ R) *)
Lemma uniontr_assoc:
  forall P Q R : tripored,
  uniontr (uniontr P Q) R = uniontr P (uniontr Q R).
Proof.
  intros.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  destruct R as ((q3, w3), t3).
  unfold uniontr. f_equal.
  - f_equal; do 2 (apply functional_extensionality;intros);
    apply EquivThenEqual; split; intros;
    unfold qt, wt, tt, andt, ort in *;simpl in *; crush.
  - do 2 (apply functional_extensionality;intros);
    apply EquivThenEqual; split; intros;
    unfold qt, wt, tt, andt, ort in *;simpl in *; crush.
Qed.

Lemma preparallelLemma_4_5_1_1 :
  forall (c d : guard),
  uniontr
    (uniontr (PhaseCond_4_2 (nand d c) true; par')
             (PhaseCond_4_2 (nand c d) true; par'))
    (PhaseCond_4_2 (and c d) true; par')
  = PhaseCond_4_2 (or c d) true; par'.
Proof.
  intros. do 4 rewrite -> helpfulLemma_4_14.
  do 4 rewrite H_C_null_seq.
  do 2 rewrite <- uniontr_distributive.
  do 2 rewrite uniontr_seqtr_distr.
  assert (H : uniontr
                (uniontr (trig (nand d c)) (trig (nand c d)))
                (trig (and c d)) = trig (or c d)).
  { unfold trig, uniontr, qt, wt, tt. simpl.
    do 2 rewrite andt_ttrue_l. do 2 rewrite ort_tfalse_l.
    f_equal. do 2 rewrite <- trigtrans1_or.
    do 2 (apply functional_extensionality;intros).
    destruct x as (((n1, t1), tr1), f1).
    destruct x0 as (((n2, t2), tr2), f2).
    apply EquivThenEqual. split;intros.
    { unfold trigtrans1 in *.
      unfold trOfEnv, ttrOfEnv, timeOfEnv in *. crush.
      unfold andb, negb, orb in *. 
      remember (dfire c (last t1) (last t2)) as Hq.
      destruct Hq. reflexivity.
      remember (dfire d (last t1) (last t2)) as Hr.
      destruct Hr. reflexivity. discriminate H0. }
    { unfold trigtrans1 in *.
      unfold trOfEnv, ttrOfEnv, timeOfEnv in *. crush.
      unfold andb, negb, orb in *. 
      remember (dfire c (last t1) (last t2)) as Hq.
      destruct Hq.
      { remember (dfire d (last t1) (last t2)) as Hr.
        destruct Hr. reflexivity. reflexivity. }
      { rewrite H0. reflexivity. } } }
  rewrite H. reflexivity.
Qed.
Lemma preparallelLemma_4_5_1_2 :
  forall (c : guard),
  C_null /H\ selftriger c = (ttrue, tfalse, tfalse).
Proof.
  intros. unfold bCondTripored, selftriger.
  unfold selftrigsub, II, flash, andtr, seqtr.
  unfold qt, wt, tt. simpl. f_equal.
  - f_equal; do 2 (apply functional_extensionality;intros);
    destruct x as (((n1, t1), tr1), f1);
    destruct x0 as (((n2, t2), tr2), f2);
    apply EquivThenEqual.
    + split;intros;
      rewrite ort_ttrue_l in *; rewrite nott_ttrue_tfalse in *;
      rewrite dseq_tfalse_r in *; rewrite ort_tfalse_l in *;
      rewrite <- double_nott in *; rewrite andt_tfalse_r in *;
      unfold tfalse, ttrue, nott in *; crush.
    + split;intros.
      { rewrite ort_tfalse_r in H. rewrite nott_ttrue_tfalse in H.
        rewrite andt_tfalse_l in H. rewrite dseq_tfalse_r in H.
        rewrite ort_tfalse_r in H. destruct H as [HA HB].
        unfold C_null, tselftriger in *. crush. }
      { crush. }
  - do 2 (apply functional_extensionality;intros).
    destruct x as (((n1, t1), tr1), f1).
    destruct x0 as (((n2, t2), tr2), f2).
    apply EquivThenEqual. split;intros.
    + rewrite nott_ttrue_tfalse in H. do 2 rewrite ort_tfalse_l in H.
      destruct H as [HA HB]. 
      unfold C_null, tselftriger, dseq in *. crush.
    + crush.
Qed.

Lemma preparallelLemma_4_5_1_3 :
  forall (x : id) (v : nat),
  C_null /H\ bassign true x v = C_null /H\ hold 0; triger_nf x v.
Proof.
  intros. unfold bCondTripored, bassign, hold, triger_nf, seqtr.
  unfold qt, wt, tt. simpl. rewrite nott_ttrue_tfalse.
  rewrite andt_tfalse_r. do 4 rewrite dseq_tfalse_r.
  do 2 rewrite <- double_nott. do 4 rewrite ort_tfalse_l.
  rewrite dseq_tfalse_r. do 2 rewrite ort_tfalse_r. f_equal.
  - f_equal; do 2 (apply functional_extensionality;intros);
    destruct x0 as (((n1, t1), tr1), f1);
    destruct x1 as (((n2, t2), tr2), f2);
    apply EquivThenEqual. 
    + split;intros.
      { unfold tfalse. crush. }
      { unfold tfalse, nott in *. crush. apply H0.
        destruct H0 as [HA HB].
        unfold C_null, ifelse, bassign_cond1, ttrOfEnv, qt in *;simpl in *.
        remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
        { apply H. } { rewrite HA in HeqHq. crush. }  }
    + split;intros.
      { destruct H as [HA HB]. split. apply HA.
        unfold C_null, ifelse, bassign_cond1, ttrOfEnv, wt in *;simpl in *.
        remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
        { rewrite dseq_unit_I in HB. apply HB. }
        { rewrite HA in HeqHq. crush. } }
      { destruct H as [HA HB]. split. apply HA.
        unfold C_null, holdw, Inv in *. crush. }
  - do 2 (apply functional_extensionality;intros).
    destruct x0 as (((n1, t1), tr1), f1).
    destruct x1 as (((n2, t2), tr2), f2).
    apply EquivThenEqual. split;intros.
    + destruct H as [HA HB]. rewrite dseq_unit_I in HB.
      unfold ifelse, bassign_cond1, ttrOfEnv in HB.
      unfold C_null, ttrOfEnv in HA. simpl in *.
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      { destruct HB as [x2 [HBA HBB]]. exists x2.
        split. split. unfold C_null, ttrOfEnv. simpl.
        apply HA. apply HBA. apply HBB. }
      { rewrite HA in HeqHq. crush. }
    + destruct H as [x2 [[HA HB] HC]]. split. apply HA.
      unfold ifelse, bassign_cond1, ttrOfEnv.
      unfold C_null, ttrOfEnv in HA. simpl in *.
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      { rewrite dseq_unit_I. exists x2. split.
        apply HB. apply HC. }
      { rewrite HA in HeqHq. crush. }
Qed.


Lemma preparallelLemma_4_5_1_4 :
  forall (c : guard) (sig : bool) (P : tripored),
  PhaseCond_4_2 c sig; C_null /H\ P
    = C_null /H\ PhaseCond_4_2 c sig; P.
Proof.
  intros. destruct P as ((qq1, ww1), tt1).
  unfold PhaseCond_4_2, bCondTripored, seqtr.
  unfold qt, wt, tt. simpl. rewrite nott_ttrue_tfalse.
  rewrite andt_tfalse_r. do 2 rewrite <- double_nott.
  do 4 rewrite ort_tfalse_l. f_equal.
  - f_equal; do 2 (apply functional_extensionality;intros);
    destruct x as (((n1, t1), tr1), f1);
    destruct x0 as (((n2, t2), tr2), f2);
    apply EquivThenEqual.
    + split;intros.
      { unfold nott at 1 in H. unfold nott at 1. crush.
        apply H. destruct H0 as [x1 [HA HB]]. exists x1.
        split. apply HA. split. 
        { destruct HA as [HAA HAB].
          destruct x1 as (((n3, t3), tr3), f3).
          unfold Cond_4_2, C_null in *.
          unfold Inv, ttrOfEnv in *. crush. }
        { apply HB. } }
      { unfold nott at 1 in H. unfold nott at 1. crush.
        apply H. destruct H0 as [x1 [HA HB]]. exists x1.
        split. split. 
        { destruct HB as [HBA HBB].
          destruct x1 as (((n3, t3), tr3), f3).
          unfold Cond_4_2, C_null in *.
          unfold Inv, ttrOfEnv in *. crush. }
        { apply HA. }
        apply HB. }
    + split;intros.
      { destruct H as [x1 [HA HB]]. exists x1.
        split. split. 
        { destruct HB as [HBA HBB].
          destruct x1 as (((n3, t3), tr3), f3).
          unfold Cond_4_2, C_null in *.
          unfold Inv, ttrOfEnv in *. crush. }
        { apply HA. }
        apply HB. }
      { destruct H as [x1 [HA HB]]. exists x1.
        split. apply HA. split. 
        { destruct HA as [HAA HAB].
          destruct x1 as (((n3, t3), tr3), f3).
          unfold Cond_4_2, C_null in *.
          unfold Inv, ttrOfEnv in *. crush. }
        { apply HB. } }
  - do 2 (apply functional_extensionality;intros).
    destruct x as (((n1, t1), tr1), f1).
    destruct x0 as (((n2, t2), tr2), f2).
    apply EquivThenEqual. split;intros.
    + destruct H as [x1 [HA HB]]. exists x1.
      split. split. 
      { destruct HB as [HBA HBB].
        destruct x1 as (((n3, t3), tr3), f3).
        unfold Cond_4_2, C_null in *.
        unfold Inv, ttrOfEnv in *. crush. }
      { apply HA. }
      apply HB.
    + destruct H as [x1 [HA HB]]. exists x1.
      split. apply HA. split. 
      { destruct HA as [HAA HAB].
        destruct x1 as (((n3, t3), tr3), f3).
        unfold Cond_4_2, C_null in *.
        unfold Inv, ttrOfEnv in *. crush. }
      { apply HB. }
Qed.

Lemma parallelcompleteRule_4_5_1 :
  forall (x : id) (v : nat) (c d : guard),
  uniontr
    (uniontr
      (uniontr (PhaseCond_1_1 x v; par')
               (PhaseCond_3_1 x v; par'))
      (PhaseCond_4_2 (or c d) false;
        hf_assign_trig C_null (or c d) x v))
    (uniontr
      (uniontr (PhaseCond_4_2 (nand d c) true; par')
               (PhaseCond_4_2 (nand c d) true; par'))
      (PhaseCond_4_2 (and c d) true; par'))
  = hf_assign_trig C_null (or c d) x v.
Proof.
  intros. rewrite preparallelLemma_4_5_1_1.
  unfold hf_assign_trig. rewrite <- uniontr_assoc.
  rewrite H_bPQ_distributive. rewrite seqtr_uniontr_distr.
  rewrite <- uniontr_assoc. rewrite uniontr_assoc.
  rewrite helpfulLemma_4_14.
  assert (H1 :
  uniontr
    (uniontr (PhaseCond_1_1 x v; par') (PhaseCond_3_1 x v; par'))
    (PhaseCond_4_2 (or c d) false; C_null /H\
       uniontr (selftriger (or c d); par') (bassign true x v; par'))
  = C_null /H\ uniontr (selftriger (or c d); par') (bassign true x v; par')).
  { rewrite H_bPQ_distributive. rewrite seqtr_uniontr_distr.
    do 2 rewrite <- H_C_null_seq. do 2 rewrite <- seqtr_comm.
    do 4 rewrite uniontr_seqtr_distr. f_equal.
    rewrite helpfulLemma_4_6. rewrite helpfulLemma_4_8.
    rewrite preparallelLemma_4_5_1_2.
    rewrite preparallelLemma_4_5_1_3.
    rewrite <- H_bPQ_distributive.
    unfold PhaseCond_4_2 at 1. unfold seqtr at 2.
    unfold qt, wt, tt. simpl. rewrite nott_ttrue_tfalse.
    rewrite dseq_tfalse_r. rewrite ort_tfalse_l.
    rewrite <- nott_ttrue_tfalse at 1. rewrite <- double_nott.
    rewrite H_C_null_seq. rewrite preparallelLemma_4_5_1_4.
    rewrite H_C_null_seq. rewrite <- seqtr_comm.
    rewrite helpfulLemma_4_12. rewrite H_C_null_seq.
    rewrite bCondTripored_abso. apply equal_and_or_tri.
    unfold init, tassign, triger_nf, hold, seqtr, uniontr, bCondTripored.
    unfold qt, wt, tt. simpl. rewrite nott_ttrue_tfalse.
    do 2 rewrite dseq_tfalse_r. rewrite <- double_nott.
    do 3 rewrite ort_tfalse_r. rewrite andt_tfalse_r.
    do 2 rewrite ort_tfalse_l. unfold implytr. crush.
    - unfold qt in *;simpl in *.
      unfold tfalse, ttrue, andt, nott in *. crush.
    - destruct H as [HA HB]. destruct HB.
      + destruct H as [s0 [HB HC]]. split. apply HA. exists s1.
        destruct s1 as (((n1, t1), tr1), f1).
        destruct s2 as (((n2, t2), tr2), f2).
        destruct s0 as (((n3, t3), tr3), f3).
        unfold C_null, ini, dassign, holdt, trigtrans3, andt in *.
        unfold Inv, trOfEnv, ttrOfEnv, timeOfEnv in *. crush.
        apply idle_self.
      + split. apply HA. exists s1. 
        destruct s1 as (((n1, t1), tr1), f1).
        destruct s2 as (((n2, t2), tr2), f2). split.
        { unfold C_null, holdt, trigtrans3, andt in *.
          unfold Inv, trOfEnv, ttrOfEnv, timeOfEnv in *. crush.
          unfold subseq. exists []. crush. apply idle_self. }
        { apply H. } }
  assert (H2 :
  uniontr
    (PhaseCond_4_2 (or c d) false; C_null /H\
       ((andtr (await (or c d)) (hold 0); trig (or c d)); par'))
    (C_null /H\ trig (or c d); par')
  = C_null /H\ ((andtr (await (or c d)) (hold 0); trig (or c d)); par')).
  { rewrite uniontr_comm. rewrite preparallelLemma_4_5_1_4.
    rewrite <- seqtr_comm. rewrite uniontr_seqtr_distr.
    rewrite <- H_C_null_seq. f_equal.
    rewrite H_C_null_seq. rewrite <- seqtr_comm. 
    rewrite helpfulLemma_4_13_extend. rewrite H_C_null_seq.
    rewrite bCondTripored_abso. apply equal_and_or_tri.
    unfold trig, await, hold, andtr, bCondTripored, implytr.
    unfold awaitsub1, awaitsub2, flash, seqtr.
    intros. unfold qt, wt, tt. simpl.
    rewrite nott_ttrue_tfalse. do 5 rewrite <- double_nott.
    rewrite andt_tfalse_r. crush. split. apply H.
    do 2 rewrite dseq_tfalse_r. do 4 rewrite ort_tfalse_l.
    exists s1. split. 
    { destruct H as [HA HB]. split.
      { unfold C_null, awaitrans1, awaitrans2, tflash, dseq in *.
        crush. exists s1. split.
        { exists s1. crush. apply Inv_self. }
        { split. apply idle_self. split. apply HA. 
          apply stateProp_self. } }
      { unfold C_null, trigtrans1, holdt in *. crush.
        apply Inv_self. apply idle_self. } }
    { apply H. } }
  rewrite H1. rewrite H2. reflexivity.
Qed.

(*
Lemma test1:
  II ==> hold 0.
Proof.
  unfold II, hold, implytr.
  intros. unfold qt, wt, tt. crush.
  unfold I, holdt, Inv in *.
  crush. unfold subseq. exists []. crush.
  apply idle_self.
Qed.

Lemma test2:
forall (c : guard),
  C_null /H\ II ==> C_null /H\ andtr (await c) (hold 0).
Proof.
  intros. unfold bCondTripored, II, andtr, await, hold, implytr.
  intros. unfold qt, wt, tt. crush.
  - rewrite nott_ttrue_tfalse in H. rewrite <- double_nott in H.
    rewrite andt_tfalse_r in H. crush.
  - rewrite andt_tfalse_r in H. crush.
  - split. apply H. split.
    + right. unfold C_null, I, awaitrans1, awaitrans2, tflash, andt, dseq in *.
      crush. exists s2. split.
      { exists s2. crush. apply Inv_self. }
      { split. apply idle_self. split. apply H0. apply stateProp_self. }
    + right. destruct H as [HA HB].
      unfold I, holdt, Inv in *.
      crush. unfold subseq. exists []. crush.
      apply idle_self.
Qed.

Lemma test3:
  forall (x : id) (v : nat),
  init; tassign x v ==> triger_nf x v.
Proof.
  intros. unfold init, tassign, triger_nf, seqtr, implytr.
  unfold qt, wt, tt. crush.
  - rewrite nott_ttrue_tfalse in *. rewrite dseq_tfalse_r in H.
    rewrite ort_tfalse_l in H. rewrite <- double_nott in H.
    apply H.
  - rewrite dseq_tfalse_r in H. rewrite ort_tfalse_l in H.
    apply H.
  - destruct H as [s0 [HA HB]].
    destruct s0 as (((n0, t0), tr0), f0).
    destruct s1 as (((n1, t1), tr1), f1).
    destruct s2 as (((n2, t2), tr2), f2).
    unfold ini, dassign, trigtrans3 in *.
    unfold Inv, trOfEnv, ttrOfEnv, timeOfEnv, flagOfEnv in *.
    crush.
Qed.
*)











