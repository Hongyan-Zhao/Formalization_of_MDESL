(**
  @name Formalization of Verilog
  @version 0.1
  @authors Zhao Hongyan
  @date 15/9/2021
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
Require Import FunctionalExtensionality.
Require Import CpdtTactics.

(* b&(x:=e) *)
Definition bassign_cond1 : env -> env -> bool :=
  fun s1 s2 : env => beq_ttr_dec (ttrOfEnv s1) tnil.
Definition bassign_cond2 : env -> env -> bool :=
  fun s1 s2 : env => flagOfEnv s1.

Definition trigtrans3 (x : id) (v : nat) : trans :=
  fun s1 s2 =>
    timeOfEnv s1 = timeOfEnv s2 /\
    trOfEnv s1 = trOfEnv s2 /\
    ttr1 (ttrOfEnv s2) = (last (trOfEnv s1)) /\
    ttr2 (ttrOfEnv s2) = fvalue_update (last (trOfEnv s1)) x v.

(* triger x e without flag *)
Definition triger_nf (x : id) (e : nat) :=
(ttrue, tfalse, trigtrans3 x e).

(* b will always be true while bassign is needed *)
Definition bassign (b : bool)
                   (x : id) (e : nat) : tripored :=
if b then (ifelsetr bassign_cond1 (II; (hold 0); (triger_nf x e))
            (ifelsetr bassign_cond2 (II; (triger_nf x e))
            (flash; II; (triger_nf x e)))
          )
else II.

(*Due to the uncertainty of the state after execute one step, 
  we need to define an abstract A(P'||Q, C_null/notnull_1/notnull_0) *)
Definition par' (*(P'Q : tripored) (C : trans)*) : tripored.
Admitted.

(*denotational semantics to healthy normal form*)
Definition hf_assign (C : trans) (x : id) (e : nat) : tripored :=
  C /H\ ((bassign true x e); par').

Definition hf_trig (C : trans) (g : guard) : tripored :=
  C /H\ (uniontr ((selftriger g); par') (((await g); (trig g)); par')).

Definition hf_delay (C : trans) : tripored :=
  C /H\ ((mdelay 1); par').

Definition hf_assign_trig (C : trans) (g : guard)
                           (x : id) (e : nat) : tripored :=
  C /H\ (uniontr ((selftriger g); par') 
                 ((uniontr ((bassign true x e); par')
                           ((andtr (await g) (hold 0));
                            (trig g); par')))).

Definition hf_trig_delay (C : trans) (g : guard) : tripored :=
  C /H\ (uniontr ((selftriger g); par')
                 (uniontr ((andtr (await g) (hold 0)); (trig g); par')
                          ((andtr (await g) (hold 0)); phase5; par'))).

(* P; R \/ Q; R = (P \/ Q); R *)
Theorem uniontr_seqtr_distr:
forall (P Q R : tripored),
  uniontr (seqtr P R) (seqtr Q R) = seqtr (uniontr P Q) R.
Proof.
  intros.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  destruct R as ((q3, w3), t3).
  unfold seqtr, uniontr. unfold qt, wt, tt. simpl. f_equal. f_equal.
  - rewrite notort_distributive. rewrite andt_comm.
    do 2 rewrite notort_distributive. rewrite <- double_nott.
    do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split;intros;destruct H as [HA HB].
    + rewrite <- double_nott in *. split.
      { split. apply HB. apply HA. }
      { unfold andt, dseq, ort, nott in *. crush.
        apply H3. exists x1. split. apply H. apply H5.
        apply H1. exists x1. split. apply H. apply H5. }
    + rewrite <- double_nott in *. split.
      { destruct HA as [HAA HAB]. split. apply HAB.
        unfold nott, dseq, ort in *. crush. apply HB.
        exists x1. split. crush. apply H1. }
      { destruct HA as [HAA HAB]. split. apply HAA.
        unfold nott, dseq, ort in *. crush. apply HB.
        exists x1. split. crush. apply H1. }
  - do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split;intros.
    + destruct H; destruct H.
      { left. left. apply H. }
      { right. unfold dseq, ort in *. crush. exists x1. crush. }
      { left. right. apply H. }
      { right. unfold dseq, ort in *. crush. exists x1. crush. }
    + destruct H. destruct H.
      { left. left. apply H. }
      { right. left. apply H. }
      unfold dseq, ort in H. crush.
      { left. right. exists x1. crush. }
      { right. right. exists x1. crush. }
  - do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split;intros.
    + destruct H; unfold dseq, ort in *; crush;
      exists x1; crush.
    + unfold dseq, ort in *. crush.
      { left. exists x1. crush. }
      { right. exists x1. crush. }
Qed. 

(** ----------------------------------------------------------------- **)

Lemma parallelLemma_assign_1_1:
forall (x : id) (v : nat),
  (PhaseCond_1_1 x v); par' ==> hf_assign C_null x v.
Proof.
  intros. unfold hf_assign, bassign. 
  rewrite helpfulLemma_4_6. do 2 rewrite <- H_C_null_seq.
  apply implytr_comp_1. unfold bCondTripored, implytr.
  unfold qt, wt, tt, tassign. simpl. intros.
  unfold qt, wt, tt. simpl.
  rewrite nott_ttrue_tfalse. rewrite andt_tfalse_r.
  rewrite dseq_tfalse_r. do 3 rewrite <- double_nott.
  rewrite ort_tfalse_l. crush.
  unfold dseq, andt in H. crush.
  destruct s1 as (((n1, t1), tr1), f1).
  destruct x0 as (((n2, t2), tr2), f2).
  destruct s2 as (((n3, t3), tr3), f3).
  unfold andt, ifelse, bassign_cond1, bassign_cond2.
  unfold C_null, ttrOfEnv, flagOfEnv in *;simpl in *.
  split.
  - apply H.
  - rewrite H. simpl. rewrite dseq_unit_I. 
    unfold dseq. exists (n1, t1, tr1, f1). split.
    + unfold ini, holdt in *.
      unfold Inv, ttrOfEnv, timeOfEnv in *. crush. apply idle_self.
    + unfold dassign, ini, trigtrans3 in *.
      unfold Inv, timeOfEnv, trOfEnv, ttrOfEnv, flagOfEnv in *. crush.
Qed.

(** ----------------------------------------------------------------- **)

Lemma C_null_bCond_uniontr_l :
forall P Q R,
(C_null /H\ P ==> C_null /H\ Q) -> (C_null /H\ P ==> C_null /H\ uniontr Q R).
Proof.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  destruct R as ((q3, w3), t3).
  unfold uniontr, bCondTripored, implytr, qt, wt, tt. crush.
  - do 2 rewrite <- double_nott in *. apply H in H0.
    unfold nott, andt in *. crush.
  - apply H in H0. split. apply H0. left. apply H0.
  - apply H in H0. split. apply H0. left. apply H0.
Qed.

Lemma C_null_bCond_uniontr_r :
forall P Q R,
(C_null /H\ P ==> C_null /H\ R) -> (C_null /H\ P ==> C_null /H\ uniontr Q R).
Proof.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  destruct R as ((q3, w3), t3).
  unfold uniontr, bCondTripored, implytr, qt, wt, tt. crush.
  - do 2 rewrite <- double_nott in *. apply H in H0.
    unfold nott, andt in *. crush.
  - apply H in H0. split. apply H0. right. apply H0.
  - apply H in H0. split. apply H0. right. apply H0.
Qed.

Lemma parallelLemma_assign_trig_1_1:
forall (c : guard) (x : id) (v : nat),
  (PhaseCond_1_1 x v); par' ==> hf_assign_trig C_null c x v.
Proof.
  intros. unfold hf_assign_trig. rewrite helpfulLemma_4_6.
  do 2 rewrite uniontr_seqtr_distr. do 2 rewrite <- H_C_null_seq.
  apply implytr_comp_1. rewrite H_C_null_seq.
  apply C_null_bCond_uniontr_r. apply C_null_bCond_uniontr_l.
  rewrite <- H_C_null_seq. unfold bassign, bCondTripored, implytr.
  unfold qt, wt, tt, tassign. simpl. intros.
  unfold qt, wt, tt. simpl.
  rewrite nott_ttrue_tfalse. rewrite andt_tfalse_r.
  rewrite dseq_tfalse_r. do 3 rewrite <- double_nott.
  rewrite ort_tfalse_l. crush.
  unfold dseq, andt in H. crush.
  destruct s1 as (((n1, t1), tr1), f1).
  destruct x0 as (((n2, t2), tr2), f2).
  destruct s2 as (((n3, t3), tr3), f3).
  unfold andt, ifelse, bassign_cond1, bassign_cond2.
  unfold C_null, ttrOfEnv, flagOfEnv in *;simpl in *.
  split.
  - apply H.
  - rewrite H. simpl. rewrite dseq_unit_I. 
    unfold dseq. exists (n1, t1, tr1, f1). split.
    + unfold ini, holdt in *.
      unfold Inv, ttrOfEnv, timeOfEnv in *. crush. apply idle_self.
    + unfold dassign, ini, trigtrans3 in *.
      unfold Inv, timeOfEnv, trOfEnv, ttrOfEnv, flagOfEnv in *. crush.
Qed.

(** ----------------------------------------------------------------- **)

Lemma C_notnull_1_addinit:
forall (x : id) (v : nat),
  C_notnull_1 /H\ tassign x v = C_notnull_1 /H\ (init; tassign x v).
Proof.
  intros. unfold bCondTripored. f_equal.
  - f_equal; do 2 (apply functional_extensionality;intros);
    apply EquivThenEqual.
    + split;intros;
      unfold init, tassign, seqtr in *;
      unfold qt, wt, tt in *;simpl in *;
      rewrite nott_ttrue_tfalse in *; rewrite <- double_nott in *;
      rewrite dseq_tfalse_r in *; rewrite ort_tfalse_l in *; apply H.
    + split;intros;
      unfold init, tassign, seqtr in *;
      unfold qt, wt, tt in *;simpl in *;
      rewrite dseq_tfalse_r in *; rewrite ort_tfalse_l in *; apply H.
  - do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split;intros;
    destruct x0 as (((n1, t1), tr1), f1);
    destruct x1 as (((n2, t2), tr2), f2).
    + split. apply H. unfold init, tassign, seqtr in *.
      unfold qt, wt, tt in *;simpl in *.
      destruct H as [HA HB]. exists (n2, t2, tr2, f2).
      unfold C_notnull_1, ini, dassign, dseq in *.
      unfold Inv, trOfEnv, ttrOfEnv, timeOfEnv, flagOfEnv in *. crush.
Admitted.

Lemma parallelLemma_assign_1_2:
forall (x : id) (v : nat),
  (PhaseCond_1_2 x v); par' ==> hf_assign C_notnull_1 x v.
Proof.
  intros. unfold hf_assign, bassign.
  rewrite helpfulLemma_4_7. rewrite C_notnull_1_addinit.
  do 2 rewrite <- H_C_notnull_1_seq.
  apply implytr_comp_1. unfold bCondTripored, implytr.
  unfold qt, wt, tt, tassign. simpl. intros.
  unfold qt, wt, tt. simpl.
  rewrite nott_ttrue_tfalse. rewrite andt_tfalse_r.
  rewrite dseq_tfalse_r. do 3 rewrite <- double_nott.
  rewrite ort_tfalse_l. crush.
  unfold dseq, andt in H. crush.
  destruct s1 as (((n1, t1), tr1), f1).
  destruct x0 as (((n2, t2), tr2), f2).
  destruct s2 as (((n3, t3), tr3), f3).
  unfold andt, ifelse, bassign_cond1, bassign_cond2.
  unfold C_notnull_1, ttrOfEnv, flagOfEnv in *;simpl in *.
  split.
  - apply H.
  - remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq. 
    + apply beq_tnil in HeqHq. crush.
    + crush. rewrite dseq_unit_I. 
      unfold dassign, ini, trigtrans3 in *.
      unfold Inv, timeOfEnv, trOfEnv, ttrOfEnv, flagOfEnv in *. crush.
Qed.

(** ----------------------------------------------------------------- **)

Lemma parallelLemma_trig_4_1:
  forall (c : guard),
  (PhaseCond_4_1 c true); par' ==> hf_trig C_notnull_0 c.
Proof.
  intros. unfold hf_trig. rewrite uniontr_seqtr_distr. 
  rewrite helpfulLemma_4_11. rewrite <- H_C_notnull_0_seq.
  apply implytr_comp_1. unfold bCondTripored, implytr.
  unfold qt, wt, tt, selftriger. simpl. intros.
  unfold qt, wt, tt. simpl.
  rewrite nott_ttrue_tfalse. do 3 rewrite <- double_nott.
  do 3 rewrite ort_tfalse_l. crush.
  - split. apply H. rewrite notandt_distributive.
    rewrite <- double_nott. left. right. apply H.
  - split. apply H. left. left. unfold selftrigsub, wt. simpl. 
    unfold II, flash, andtr, qt, wt, tt in H;simpl in H.
    rewrite nott_ttrue_tfalse in H. rewrite ort_tfalse_l in H.
    rewrite andt_tfalse_l in H. rewrite dseq_tfalse_r in H.
    rewrite ort_tfalse_r in H. apply H.
  - split. apply H. left. apply H.
Qed.

(** ----------------------------------------------------------------- **)

Lemma parallelLemma_trig_4_2:
  forall (c : guard),
  (PhaseCond_4_2 c true); par' ==> hf_trig C_null c.
Proof.
  intros. unfold hf_trig. rewrite uniontr_seqtr_distr.
  rewrite helpfulLemma_4_14. rewrite <- H_C_null_seq.
  apply implytr_comp_1. unfold implytr. intros. split.
  - intros. unfold bCondTripored, qt in *;simpl in *.
    rewrite <- double_nott in *. rewrite nott_ttrue_tfalse in H.
    unfold andt, tfalse in H. crush.
  - split;intros.
    + unfold bCondTripored, wt in *;simpl in *.
      unfold andt, tfalse in H. crush.
    + unfold bCondTripored, tt in *;simpl in *.
      split. apply H. right. destruct H as [HA HB].
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold C_null, ttrOfEnv in HA;simpl in HA.
      unfold dseq. crush. exists (n1, t1, tnil, f1). split.
      { exists (n1, t1, tnil, f1). split.
        { exists (n1, t1, tnil, f1). split.
          { unfold trigtrans1, awaitrans1, ttrOfEnv in *. crush. }
          { unfold trigtrans1, tflash, Inv, ttrOfEnv, trOfEnv in *.
            crush. unfold subseq. exists []. crush. } }
        { unfold awaitrans2, ttrOfEnv in *. crush. 
          apply idle_self. apply stateProp_self. } }
      { apply HB. }
Qed.

(** ----------------------------------------------------------------- **)

Lemma preParLemma_trig_4_3_1:
  forall (c : guard),
  (PhaseCond_4_1 c false); hf_trig C_null c ==> 
        (PhaseCond_4_1 c false); (await c; trig c); par'.
Proof. 
  intros. unfold hf_trig. 
(* Beacuse of PhaseCond_4_1 ttr' = null, selftriger ttr =\= null, easy to proved *)
Admitted.

Lemma preParLemma_trig_4_3_2:
  forall (c : guard),
  (PhaseCond_4_1 c false); (await c; trig c); par' ==>
        hf_trig C_notnull_0 c.
Proof. 
  intros. unfold hf_trig.
(* See derivationLemma_trig_4_3 for details, very similar *)
Admitted.

Lemma parallelLemma_trig_4_3:
  forall (c : guard),
  (PhaseCond_4_1 c false); (hf_trig C_null c) ==> hf_trig C_notnull_0 c.
Proof.
  intros. apply implytr_trans with 
      (Q := (PhaseCond_4_1 c false); (await c; trig c); par').
  apply preParLemma_trig_4_3_1. apply preParLemma_trig_4_3_2.
Qed.

(** ----------------------------------------------------------------- **)

Lemma parallelLemma_delay_5_2:
  phase5; par' ==> hf_delay C_null.
Proof.
  intros. unfold hf_delay. rewrite <- H_C_null_seq.
  apply implytr_comp_1. unfold mdelay, implytr. intros. split.
  - intros. unfold bCondTripored, phase5, qt in *;simpl in *.
    unfold nott, ttrue in H. crush.
  - split;intros.
    + unfold bCondTripored, phase5, wt in *;simpl in *.
      unfold flash, hold, seqtr, wt. simpl. rewrite ort_tfalse_l.
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2). split.
      { unfold delayw, C_null, ttrOfEnv in *. crush. }
      { right. unfold dseq. exists (n1, t1, tr1, f1). split. 
        { exists (n1, t1, tr1, f1). 
          unfold delayw, tflash, holdt in *.
          unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush. 
          apply idle_self. }
        { apply H. } }
    + unfold bCondTripored, phase5, tt in *;simpl in *. 
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2). split.
      { unfold delayt, C_null, ttrOfEnv in *. crush. }
      { unfold dseq. exists (n1, t1, tr1, f1). split.
        { exists (n1, t1, tr1, f1).
          unfold delayt, tflash, holdt in *.
          unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
          apply idle_self. }
        { apply H. } }
Qed.











