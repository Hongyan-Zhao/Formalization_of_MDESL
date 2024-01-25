(**
  @name Formalization of Verilog
  @version 0.1
  @authors Zhao Hongyan
  @date 1/3/2021
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

Lemma uniontr_comm :
  forall (P Q : tripored),
  uniontr P Q = uniontr Q P.
Proof.
  intros. destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  unfold uniontr, qt, wt, tt in *;simpl in *.
  f_equal.
  - f_equal. rewrite andt_comm. reflexivity. 
    rewrite ort_comm. reflexivity.
  - rewrite ort_comm. reflexivity.
Qed.

Lemma equal_and_or_tri : (** the absorption law for tripored **)
  forall (P Q : tripored),
  P ==> Q -> uniontr P Q = Q.
Proof.
  intros. destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  unfold implytr, uniontr, qt, wt, tt in *;simpl in *.
  f_equal.
  - f_equal;do 2 (apply functional_extensionality;intros);
    apply EquivThenEqual.
    + split;intros.
      { apply H0. }
      { unfold nott in H. assert (HH : ~ q1 x x0 -> ~q2 x x0).
        { apply H. } apply imply_to_or in HH. destruct HH.
        { apply NNPP in H1. split. apply H1. apply H0. }
        { crush. } }
    + split;intros.
      { destruct H0. apply H in H0. apply H0. apply H0. }
      { right. apply H0. }
  - do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split;intros.
    + destruct H0. apply H in H0. apply H0. apply H0.
    + right. apply H0.
Qed.

Lemma uniontr_distributive :
  forall (a : trans) (P Q : tripored),
  a /H\ (uniontr P Q) = uniontr (a /H\ P) (a /H\ Q).
Proof.
  intros. destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  unfold bCondTripored, uniontr, qt, wt, tt;simpl.
  f_equal.
  - f_equal.
    + rewrite notandt_distributive. rewrite <- double_nott.
      do 2 rewrite notandt_distributive. do 2 rewrite <- double_nott.
      rewrite <- oat_distributive_r. crush.
    + rewrite <- aot_distributive_r. crush.
  - rewrite <- aot_distributive_r. crush.
Qed.

(** the completeness of transition rules **)
(** ----------------------------------------------------------------- **)

Lemma completeRule_Skip_1_1_4_2 :
  forall (x : id) (v : nat) (c : guard),
  uniontr ((PhaseCond_1_1 x v); II) 
          ((PhaseCond_4_2 c true); Skip) = C_null /H\ Skip.
Proof.
  intros. rewrite derivationLemma_Skip_4_2.
  apply equal_and_or_tri. apply derivationLemma_Skip_1_1.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_Skip_1_2 :
  forall (x : id) (v : nat),
  (PhaseCond_1_2 x v); II = C_notnull_1 /H\ Skip.
Proof.
  apply derivationLemma_Skip_1_2.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_Skip_4_1 :
  forall (c : guard),
  (PhaseCond_4_1 c true); Skip = C_notnull_0 /H\ Skip.
Proof.
  apply derivationLemma_Skip_4_1.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_assign_1_1_4_2 :
  forall (c : guard) (x : id) (v : nat),
  uniontr ((PhaseCond_1_1 x v); II) ((PhaseCond_4_2 c true); (sassign x v))
                                         = C_null /H\ (Skip; (tassign x v)).
Proof.
  intros. unfold sassign. rewrite <- seqtr_comm. 
  rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq.
  apply equal_and_or_tri. apply derivationLemma_assign_1_1.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_assign_1_2 :
  forall (x : id) (v : nat),
  (PhaseCond_1_2 x v); II = C_notnull_1 /H\ (sassign x v).
Proof.
  apply derivationLemma_assign_1_2.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_assign_4_1 :
  forall (c : guard) (x : id) (v : nat),
  (PhaseCond_4_1 c true); (sassign x v) = C_notnull_0 /H\ (sassign x v).
Proof.
  intros. unfold sassign. rewrite <- seqtr_comm.
  rewrite derivationLemma_Skip_4_1. rewrite H_C_notnull_0_seq. crush.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_trig_2_1 :
  forall (c : guard),
  (PhaseCond_2_1); (guardawake c) = C_notnull_1 /H\ (guardawake c).
Proof.
  apply derivationLemma_trig_2_1.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_trig_4_1_4_3 :
  forall (c : guard),
  uniontr ((PhaseCond_4_1 c true); II) ((PhaseCond_4_1 c false); (guardawake c))
                                                = C_notnull_0 /H\ (guardawake c).
Proof.
  intros. rewrite seqtr_ii. rewrite helpfulLemma_4_11.
  rewrite preDeriLemma_trig_4_3. rewrite <- seqtr_comm.
  rewrite helpfulLemma_4_10. rewrite H_C_notnull_0_seq.
  unfold guardawake. rewrite <- uniontr_distributive. crush.
Qed.

(** ----------------------------------------------------------------- **)

Lemma preCompLemma_trig_4_2_4_4_5_1 :
  forall (c : guard),
  C_null /H\ (guardawake c) = C_null /H\ (await c; trig c).
Proof.
  intros. unfold bCondTripored. f_equal.
  - f_equal;do 2 (apply functional_extensionality;intros);
    apply EquivThenEqual.
    + unfold nott at 3. unfold nott at 1. crush.
      { apply H. split. apply H0. destruct H0 as [HA HB].
        unfold nott in *. crush. apply HB.
        unfold guardawake in H0.
        unfold seqtr, uniontr, selftriger, await, trig in *.
        unfold qt, wt, tt in *;simpl in *. apply H0. }
      { apply H. split. apply H0. destruct H0 as [HA HB].
        unfold nott in *. crush. apply HB.
        unfold guardawake.
        unfold seqtr, uniontr, selftriger, await, trig in *.
        unfold qt, wt, tt in *;simpl in *. split.
        { rewrite nott_ttrue_tfalse in H0. 
          rewrite dseq_tfalse_r in H0.
          do 2 rewrite notort_distributive in H0.
          do 2 rewrite <- double_nott in H0.
          rewrite notort_distributive. rewrite <- double_nott.
          unfold II, flash, andtr, qt, wt, tt;simpl.
          rewrite ort_ttrue_l. rewrite nott_ttrue_tfalse.
          rewrite dseq_tfalse_r. destruct H0 as [HAA HBB].
          unfold tfalse, ttrue, andt, nott in *. crush. }
        { apply H0. } }
    + split;intros.
      { split. apply H. destruct H as [HA HB]. 
        unfold guardawake, seqtr, uniontr, selftriger, await, trig in *.
        unfold qt, wt, tt in *;simpl in *.
        unfold flash at 1 in HB. unfold II, andtr in HB.
        unfold wt at 2, qt, wt at 3, wt at 2 in HB;simpl in HB.
        rewrite nott_ttrue_tfalse in HB. rewrite ort_tfalse_l in HB.
        rewrite andt_tfalse_l in HB. rewrite dseq_tfalse_r in HB.
        rewrite ort_tfalse_r in HB. rewrite dseq_tfalse_r in *.
        rewrite ort_tfalse_r in *. destruct HB.
        { right. unfold selftrigsub, wt in H;simpl in H. 
          unfold C_null, tselftriger in *. crush. }
        { apply H. } }
      { split. apply H. destruct H as [HA HB].
        unfold guardawake, seqtr, uniontr, selftriger, await, trig in *.
        unfold qt, wt, tt in *;simpl in *.
        rewrite dseq_tfalse_r in HB. rewrite ort_tfalse_r in HB.
        destruct HB.
        { right. left. left. apply H. }
        { right. left. right. apply H. } }
  - do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split;intros.
    + split. apply H. destruct H as [HA HB].
      unfold seqtr, guardawake, await, trig, uniontr in *;simpl in *.
      unfold II, flash, qt in HB;simpl in HB. 
      rewrite nott_ttrue_tfalse in HB. do 2 rewrite ort_tfalse_l in HB.
      destruct HB.
      { unfold dseq in H. crush. unfold C_null, tselftriger in *. crush. }
      { apply H. }
    + split. apply H. destruct H as [HA HB].
      unfold guardawake, seqtr, await, trig, uniontr in *;simpl in *.
      right. apply HB.
Qed.

Lemma completeRule_trig_4_2_4_4_5_1 :
  forall (c : guard),
  uniontr (uniontr ((PhaseCond_4_2 c true); II) 
                   ((PhaseCond_4_2 c false); (guardawake c)))
          (phase5; (guardawake c))
                                  = C_null /H\ (guardawake c).
Proof.
  intros. rewrite seqtr_ii. rewrite helpfulLemma_4_14.
  rewrite preDeriLemma_trig_4_4. rewrite <- seqtr_comm.
  rewrite helpfulLemma_4_13. rewrite H_C_null_seq.
  rewrite preCompLemma_trig_4_2_4_4_5_1.
  unfold seqtr, bCondTripored, uniontr.
  unfold qt, wt, tt;simpl. f_equal.
  - f_equal;do 2 (apply functional_extensionality;intros);
    apply EquivThenEqual.
    + rewrite nott_ttrue_tfalse. do 2 rewrite <- double_nott.
      rewrite dseq_tfalse_r. rewrite andt_tfalse_r.
      rewrite ort_tfalse_l. rewrite ort_tfalse_r.
      do 2 rewrite <- notort_distributive. rewrite ort_tfalse_l.
      unfold nott at 5. unfold nott at 1. crush.
      { apply H. left. apply H0. }
      { apply H. destruct H0. apply H0. unfold dseq in H0. crush.
        split. unfold delayt, C_null in *. crush. right.
        unfold awaitsub2, qt;simpl. rewrite nott_ttrue_tfalse.
        rewrite dseq_tfalse_r. 
        unfold selftriger, selftrigsub, seqtr, await, trig in H2.
        unfold qt, wt, tt in H2;simpl in H2.
        unfold seqtr, II, flash, awaitsub1, awaitsub2 in H2.
        unfold qt, wt, tt in H2;simpl in H2. 
        rewrite ort_ttrue_l in H2. rewrite nott_ttrue_tfalse in H2.
        do 4 rewrite dseq_tfalse_r in H2. 
        unfold tfalse, ort, andt, nott in H2. crush. }
    + unfold selftriger, seqtr, await, trig, awaitsub1, awaitsub2, flash.
      unfold qt, wt, tt;simpl. unfold seqtr, II. unfold qt, wt, tt;simpl.
      rewrite nott_ttrue_tfalse. do 2 rewrite dseq_tfalse_r.
      rewrite andt_tfalse_r. do 3 rewrite ort_tfalse_r.
      rewrite andt_tfalse_r. rewrite dseq_tfalse_r.
      rewrite ort_tfalse_r. rewrite ort_tfalse_l. split;intros.
      { destruct H. apply H. destruct H. split. 
        unfold delayw, C_null in *. crush.
        left. unfold delayw, awaitrans1 in *. crush.
        unfold dseq at 1 in H. crush. split.
        unfold delayt, C_null in *. crush.
        destruct H1. unfold delayt, tselftriger in *. crush.
        destruct H.
        { left. unfold delayt, awaitrans1 in *.
          unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush. }
        { right. unfold dseq in *. crush. exists x2. split. exists x3.
          split. unfold delayt, awaitrans1 in *. crush. apply H3.
          apply H2. } }
      { left. apply H. }
  - do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. unfold II, flash, qt;simpl.
    rewrite nott_ttrue_tfalse. do 2 rewrite ort_tfalse_l.
    split;intros.
    + destruct H. destruct H.
      { split. apply H. destruct H as [HA HB].
        unfold dseq. exists x. split. exists x. split. exists x.
        split. unfold C_null, trigtrans1, awaitrans1 in *. crush.
        destruct x as (((t1, r1), tr1), f1).
        destruct x0 as (((t2, r2), tr2), f2).
        unfold C_null, trigtrans1, tflash, Inv, trOfEnv, ttrOfEnv in *.
        crush. unfold subseq. exists []. crush.
        unfold C_null, trigtrans1, awaitrans2 in *. crush.
        apply idle_self. apply stateProp_self. apply HB. }
      { apply H. }
      { unfold dseq at 1 in H. crush. split.
        unfold delayt, C_null in *. crush. destruct H1.
        { unfold dseq in H. crush. unfold delayt, tselftriger in *. crush. }
        { unfold dseq in *. crush. exists x2. split. exists x3.
          split. exists x4. split.
          unfold delayt, awaitrans1 in *. crush. 
          apply H4. apply H3. apply H2. } }
    + left. right. apply H.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_delay_2_1 :
  forall (n : nat),
  PhaseCond_2_1; (mdelay n) = C_notnull_1 /H\ (mdelay n).
Proof.
  apply derivationLemma_delay_2_1.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_delay_4_1 :
  forall (c : guard) (n : nat),
  (PhaseCond_4_1 c true); (mdelay n) = C_notnull_0 /H\ (mdelay n).
Proof.
  apply derivationLemma_delay_4_1.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_delayn_4_2_5_1 :
  forall (c : guard) (n : nat),
  n >= 2 -> 
  uniontr (PhaseCond_4_2 c true; (mdelay n)) 
          (phase5; flash; (hold (n - 2)); phase5)
                          = C_null /H\ (mdelay n).
Proof.
  intros. rewrite derivationLemma_delay_4_2.
  rewrite uniontr_comm. apply equal_and_or_tri.
  apply derivationLemma_delay_5_1. crush. crush.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_delay1_4_2_5_2 :
  forall (c : guard) (n : nat),
  n = 1 -> 
  uniontr (PhaseCond_4_2 c true; (mdelay n))
          (phase5;II)
                     = C_null /H\ (mdelay n).
Proof.
  intros. rewrite derivationLemma_delay_4_2.
  rewrite uniontr_comm. apply equal_and_or_tri.
  rewrite H. apply derivationLemma_delay_5_2. crush.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_sequential :
(** TODO : simple**) 
  forall (n : nat), n = 1 -> n = 1.
Proof.
Admitted.

(** ----------------------------------------------------------------- **)

Lemma completeRule_conditional_1_1_1_2_4_2 :
  forall (b : env -> env -> bool) (P Q : tripored)
         (x : id) (v : nat) (s1 s2 : env) (c : guard),
  (((if b s1 s2 then nott (qt ((PhaseCond_1_1 x v); P)) s1 s2
               else nott (qt ((PhaseCond_1_1 x v); Q)) s1 s2)
     \/ nott (qt ((PhaseCond_4_2 c true); (condition b P Q))) s1 s2)
                    = nott (qt (C_null /H\ condition b P Q)) s1 s2) /\
  (((if b s1 s2 then wt ((PhaseCond_1_1 x v); P) s1 s2
               else wt ((PhaseCond_1_1 x v); Q) s1 s2)
     \/ wt ((PhaseCond_4_2 c true); (condition b P Q)) s1 s2)
                    = wt (C_null /H\ condition b P Q) s1 s2) /\
  (((if b s1 s2 then tt ((PhaseCond_1_1 x v); P) s1 s2
               else tt ((PhaseCond_1_1 x v); Q) s1 s2)
     \/ tt ((PhaseCond_4_2 c true); (condition b P Q)) s1 s2)
                    = tt (C_null /H\ condition b P Q) s1 s2).
Proof.
  intros. 
  assert (HHq : nott (qt ((PhaseCond_4_2 c true); (condition b P Q))) s1 s2
                = nott (qt (C_null /H\ condition b P Q)) s1 s2).
  { unfold condition. rewrite <- seqtr_comm. rewrite derivationLemma_Skip_4_2.
    rewrite H_C_null_seq. reflexivity. }
  assert (HHw : wt ((PhaseCond_4_2 c true); (condition b P Q)) s1 s2
                = wt (C_null /H\ condition b P Q) s1 s2).
  { unfold condition. rewrite <- seqtr_comm. rewrite derivationLemma_Skip_4_2. 
    rewrite H_C_null_seq. reflexivity. }
  assert (HHt : tt ((PhaseCond_4_2 c true); (condition b P Q)) s1 s2
                = tt (C_null /H\ condition b P Q) s1 s2).
  { unfold condition. rewrite <- seqtr_comm. rewrite derivationLemma_Skip_4_2. 
    rewrite H_C_null_seq. reflexivity. }
  remember (b s1 s2) as Hq. destruct Hq.
  - assert (H : (nott (qt ((PhaseCond_1_1 x v); P)) s1 s2 ->
                 nott (qt (C_null /H\ condition b P Q)) s1 s2) /\
                (wt ((PhaseCond_1_1 x v); P) s1 s2 ->
                 wt (C_null /H\ condition b P Q) s1 s2) /\
                (tt ((PhaseCond_1_1 x v); P) s1 s2 ->
                 tt (C_null /H\ condition b P Q) s1 s2)).
    { apply derivationLemma_conditional_1_1. rewrite HeqHq. reflexivity. }
    split. 
    + apply EquivThenEqual. split.
      { rewrite HHq. apply imply_and_or. apply H. }
      { unfold condition. rewrite <- seqtr_comm.
        rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. }
    + split.
      { apply EquivThenEqual. split.
        { rewrite HHw. apply imply_and_or. apply H. }
        { unfold condition. rewrite <- seqtr_comm.
          rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. } }
      { apply EquivThenEqual. split.
        { rewrite HHt. apply imply_and_or. apply H. }
        { unfold condition. rewrite <- seqtr_comm.
          rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. } }
  - assert (H : (nott (qt ((PhaseCond_1_1 x v); Q)) s1 s2 ->
                 nott (qt (C_null /H\ condition b P Q)) s1 s2) /\
                (wt ((PhaseCond_1_1 x v); Q) s1 s2 ->
                 wt (C_null /H\ condition b P Q) s1 s2) /\
                (tt ((PhaseCond_1_1 x v); Q) s1 s2 ->
                 tt (C_null /H\ condition b P Q) s1 s2)).
    { apply derivationLemma_conditional_1_2. rewrite HeqHq. reflexivity. }
    split. 
    + apply EquivThenEqual. split.
      { rewrite HHq. apply imply_and_or. apply H. }
      { unfold condition. rewrite <- seqtr_comm.
        rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. }
    + split.
      { apply EquivThenEqual. split.
        { rewrite HHw. apply imply_and_or. apply H. }
        { unfold condition. rewrite <- seqtr_comm.
          rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. } }
      { apply EquivThenEqual. split.
        { rewrite HHt. apply imply_and_or. apply H. }
        { unfold condition. rewrite <- seqtr_comm.
          rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. } }
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_conditional_1_3_1_4 :
  forall (b : env -> env -> bool) (P Q : tripored)
         (x : id) (v : nat) (s1 s2 : env),
  ((if b s1 s2 then nott (qt ((PhaseCond_1_2 x v); P)) s1 s2
              else nott (qt ((PhaseCond_1_2 x v); Q)) s1 s2)
                = nott (qt (C_notnull_1 /H\ condition b P Q)) s1 s2) /\
  ((if b s1 s2 then wt ((PhaseCond_1_2 x v); P) s1 s2
              else wt ((PhaseCond_1_2 x v); Q) s1 s2)
                = wt (C_notnull_1 /H\ condition b P Q) s1 s2) /\
  ((if b s1 s2 then tt ((PhaseCond_1_2 x v); P) s1 s2
              else tt ((PhaseCond_1_2 x v); Q) s1 s2)
                = tt (C_notnull_1 /H\ condition b P Q) s1 s2).
Proof.
  intros. remember (b s1 s2) as Hq. destruct Hq.
  - split.
    + apply EquivThenEqual. split.
      { apply derivationLemma_conditional_1_3. rewrite HeqHq. reflexivity. }
      { destruct P as ((qq, ww), ttt). 
        assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
        { rewrite <- seqtr_ii. reflexivity. }
        rewrite <- HH. rewrite derivationLemma_Skip_1_2.
        unfold condition. rewrite H_C_notnull_1_seq.
        intros. unfold qt at 1 in H. unfold qt at 1. crush.
        rewrite <- double_nott in *. destruct H as [HA HB].
        split. apply HA. unfold nott at 1 in HB. unfold nott at 1. crush. 
        apply HB. unfold seqtr, qt at 1 in H. unfold seqtr, qt at 1.
        crush. rewrite notort_distributive in *. 
        rewrite <- double_nott in *. destruct H as [HAA HBB].
        split. apply HAA. unfold nott at 1 in HBB. unfold nott at 1. crush. 
        apply HBB. unfold dseq at 1 in H. unfold dseq at 1. crush.
        exists x0. destruct s1 as (((n1, t1), tr1), f1).
        destruct s2 as (((n2, t2), tr2), f2).
        destruct x0 as (((n3, t3), tr3), f3). split. crush.
        unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
        do 2 rewrite dseq_unit_I in H0.
        unfold ifelse, skip_cond1, ttrOfEnv in H0;simpl in H0.
        remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
        + apply beq_tnil in HeqHqq. crush.
        + crush. unfold I in H0. 
          assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
          { apply judge_b. assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
            rewrite <- HeqHqq. rewrite beq_ttr2_dec_self. reflexivity. }
          rewrite HHH in HeqHq. unfold nott, qt in *. crush. apply H1.
          unfold ifelse. rewrite <- HeqHq. unfold qt. crush. }
    + split.
      { apply EquivThenEqual. split.
        { apply derivationLemma_conditional_1_3. rewrite HeqHq. reflexivity. }
        { destruct P as ((qq, ww), ttt). 
          assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
          { rewrite <- seqtr_ii. reflexivity. }
          rewrite <- HH. rewrite derivationLemma_Skip_1_2.
          unfold condition. rewrite H_C_notnull_1_seq.
          intros. unfold wt at 1 in H. unfold wt at 1. crush.
          destruct H as [HA HB]. split. apply HA.
          unfold seqtr, wt at 1 in HB. unfold seqtr, wt at 1. crush.
          destruct HB. left. apply H. right.
          unfold dseq at 1 in H. unfold dseq at 1. crush.
          exists x0. destruct s1 as (((n1, t1), tr1), f1).
          destruct s2 as (((n2, t2), tr2), f2).
          destruct x0 as (((n3, t3), tr3), f3). split. crush.
          unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
          do 2 rewrite dseq_unit_I in H0.
          unfold ifelse, skip_cond1, ttrOfEnv in H0;simpl in H0.
          remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
          { apply beq_tnil in HeqHqq. crush. }
          { crush. unfold I in H0.
            assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
            { apply judge_b. 
              assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
              rewrite <- HeqHqq. rewrite beq_ttr2_dec_self. reflexivity. }
            rewrite HHH in HeqHq. unfold wt in *. crush.
            unfold ifelse in H1. rewrite <- HeqHq in H1. 
            unfold wt in H1. crush. } } }
      { apply EquivThenEqual. split.
        { apply derivationLemma_conditional_1_3. rewrite HeqHq. reflexivity. }
        { destruct P as ((qq, ww), ttt). 
          assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
          { rewrite <- seqtr_ii. reflexivity. }
          rewrite <- HH. rewrite derivationLemma_Skip_1_2.
          unfold condition. rewrite H_C_notnull_1_seq.
          intros. unfold tt at 1 in H. unfold tt at 1. crush.
          destruct H as [HA HB]. split. apply HA.
          unfold dseq at 1 in HB. unfold dseq at 1. crush.
          exists x0. destruct s1 as (((n1, t1), tr1), f1).
          destruct s2 as (((n2, t2), tr2), f2).
          destruct x0 as (((n3, t3), tr3), f3). split. crush.
          unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
          do 2 rewrite dseq_unit_I in H0.
          unfold ifelse, skip_cond1, ttrOfEnv in H0;simpl in H0.
          remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
          { apply beq_tnil in HeqHqq. crush. }
          { crush. unfold I in H0.
            assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
            { apply judge_b. 
              assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
              rewrite <- HeqHqq. rewrite beq_ttr2_dec_self. reflexivity. }
            rewrite HHH in HeqHq. unfold ifelse in H1. 
            rewrite <- HeqHq in H1. apply H1. } } }
  - split.
    + apply EquivThenEqual. split.
      { apply derivationLemma_conditional_1_4. rewrite HeqHq. reflexivity. }
      { destruct P as ((qq, ww), ttt). 
        assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
        { rewrite <- seqtr_ii. reflexivity. }
        rewrite <- HH. rewrite derivationLemma_Skip_1_2.
        unfold condition. rewrite H_C_notnull_1_seq.
        intros. unfold qt at 1 in H. unfold qt at 1. crush.
        rewrite <- double_nott in *. destruct H as [HA HB].
        split. apply HA. unfold nott at 1 in HB.
        unfold nott at 1. crush. apply HB.
        unfold seqtr, qt at 1 in H. unfold seqtr, qt at 1.
        crush. rewrite notort_distributive in *. 
        rewrite <- double_nott in *. destruct H as [HAA HBB].
        split. apply HAA. unfold nott at 1 in HBB.
        unfold nott at 1. crush. apply HBB.
        unfold dseq at 1 in H. unfold dseq at 1. crush.
        exists x0. destruct s1 as (((n1, t1), tr1), f1).
        destruct s2 as (((n2, t2), tr2), f2).
        destruct x0 as (((n3, t3), tr3), f3). split. crush.
        unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
        do 2 rewrite dseq_unit_I in H0.
        unfold ifelse, skip_cond1, ttrOfEnv in H0;simpl in H0.
        remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
        + apply beq_tnil in HeqHqq. crush.
        + crush. unfold I in H0. 
          assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
          { apply judge_b. assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
            rewrite <- HeqHqq. rewrite beq_ttr2_dec_self. reflexivity. }
          rewrite HHH in HeqHq. unfold nott, qt in *. crush. apply H1.
          unfold ifelse. rewrite <- HeqHq. unfold qt. crush. }
    + split.
      { apply EquivThenEqual. split.
        { apply derivationLemma_conditional_1_4. rewrite HeqHq. reflexivity. }
        { destruct P as ((qq, ww), ttt). 
          assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
          { rewrite <- seqtr_ii. reflexivity. }
          rewrite <- HH. rewrite derivationLemma_Skip_1_2.
          unfold condition. rewrite H_C_notnull_1_seq.
          intros. unfold wt at 1 in H. unfold wt at 1. crush.
          destruct H as [HA HB]. split. apply HA.
          unfold seqtr, wt at 1 in HB. unfold seqtr, wt at 1. crush.
          destruct HB. left. apply H. right.
          unfold dseq at 1 in H. unfold dseq at 1. crush.
          exists x0. destruct s1 as (((n1, t1), tr1), f1).
          destruct s2 as (((n2, t2), tr2), f2).
          destruct x0 as (((n3, t3), tr3), f3). split. crush.
          unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
          do 2 rewrite dseq_unit_I in H0.
          unfold ifelse, skip_cond1, ttrOfEnv in H0;simpl in H0.
          remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
          { apply beq_tnil in HeqHqq. crush. }
          { crush. unfold I in H0.
            assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
            { apply judge_b. 
              assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
              rewrite <- HeqHqq. rewrite beq_ttr2_dec_self. reflexivity. }
            rewrite HHH in HeqHq. unfold wt in *. crush.
            unfold ifelse in H1. rewrite <- HeqHq in H1. 
            unfold wt in H1. crush. } } }
      { apply EquivThenEqual. split.
        { apply derivationLemma_conditional_1_4. rewrite HeqHq. reflexivity. }
        { destruct P as ((qq, ww), ttt). 
          assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
          { rewrite <- seqtr_ii. reflexivity. }
          rewrite <- HH. rewrite derivationLemma_Skip_1_2.
          unfold condition. rewrite H_C_notnull_1_seq.
          intros. unfold tt at 1 in H. unfold tt at 1. crush.
          destruct H as [HA HB]. split. apply HA.
          unfold dseq at 1 in HB. unfold dseq at 1. crush.
          exists x0. destruct s1 as (((n1, t1), tr1), f1).
          destruct s2 as (((n2, t2), tr2), f2).
          destruct x0 as (((n3, t3), tr3), f3). split. crush.
          unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
          do 2 rewrite dseq_unit_I in H0.
          unfold ifelse, skip_cond1, ttrOfEnv in H0;simpl in H0.
          remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
          { apply beq_tnil in HeqHqq. crush. }
          { crush. unfold I in H0.
            assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
            { apply judge_b. 
              assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
              rewrite <- HeqHqq. rewrite beq_ttr2_dec_self. reflexivity. }
            rewrite HHH in HeqHq. unfold ifelse in H1. 
            rewrite <- HeqHq in H1. apply H1. } } }
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_conditional_4_1 :
  forall (c : guard) (b : env -> env -> bool) (P Q : tripored),
  (PhaseCond_4_1 c true); (condition b P Q) = C_notnull_0 /H\ (condition b P Q).
Proof.
  apply derivationLemma_conditional_4_1.
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_iteration_1_1_1_2_4_2 :
  forall (x : id) (v : nat) (s1 s2 : env) (c : guard)
         (b : env -> env -> bool) (P : tripored),
  (((if b s1 s2 then nott (qt ((PhaseCond_1_1 x v); (P; (while b P)))) s1 s2
                else nott (qt ((PhaseCond_1_1 x v); II)) s1 s2)
    \/ nott (qt ((PhaseCond_4_2 c true); (while b P))) s1 s2)
                    = nott (qt (C_null /H\ (while b P))) s1 s2) /\
  (((if b s1 s2 then wt ((PhaseCond_1_1 x v); (P; (while b P))) s1 s2
                else wt ((PhaseCond_1_1 x v); II) s1 s2)
    \/ wt ((PhaseCond_4_2 c true); (while b P)) s1 s2)
                    = wt (C_null /H\ (while b P)) s1 s2) /\
  (((if b s1 s2 then tt ((PhaseCond_1_1 x v); (P; (while b P))) s1 s2
                else tt ((PhaseCond_1_1 x v); II) s1 s2)
    \/ tt ((PhaseCond_4_2 c true); (while b P)) s1 s2)
                    = tt (C_null /H\ (while b P)) s1 s2).
Proof.
  intros. 
  assert (HHq : nott (qt ((PhaseCond_4_2 c true); (while b P))) s1 s2
                = nott (qt (C_null /H\ (while b P))) s1 s2).
  { rewrite eqb_while_faiwhile. unfold fai. rewrite <- seqtr_comm.
    rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. reflexivity. }
  assert (HHw : wt ((PhaseCond_4_2 c true); (while b P)) s1 s2
                = wt (C_null /H\ (while b P)) s1 s2).
  { rewrite eqb_while_faiwhile. unfold fai. rewrite <- seqtr_comm.
    rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. reflexivity. }
  assert (HHt : tt ((PhaseCond_4_2 c true); (while b P)) s1 s2
                = tt (C_null /H\ (while b P)) s1 s2).
  { rewrite eqb_while_faiwhile. unfold fai. rewrite <- seqtr_comm.
    rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. reflexivity. }
  assert (HHH : PhaseCond_4_2 c true;(Skip; ifelsetr b (P; while b P) II)
                = (PhaseCond_4_2 c true; Skip); ifelsetr b (P; while b P) II).
  { rewrite <- seqtr_comm. reflexivity. } 
  remember (b s1 s2) as Hq. destruct Hq.
  - assert (H : (nott (qt ((PhaseCond_1_1 x v); (P; (while b P)))) s1 s2 ->
                 nott (qt (C_null /H\ (while b P))) s1 s2) /\
                (wt ((PhaseCond_1_1 x v); (P; (while b P))) s1 s2 ->
                 wt (C_null /H\ (while b P)) s1 s2) /\
                (tt ((PhaseCond_1_1 x v); (P; (while b P))) s1 s2 ->
                 tt (C_null /H\ (while b P)) s1 s2)).
    { apply derivationLemma_iteration_1_1. rewrite HeqHq. reflexivity. }
    split. 
    + apply EquivThenEqual. split.
      { rewrite HHq. apply imply_and_or. apply H. }
      { rewrite eqb_while_faiwhile. unfold fai. rewrite HHH.
        rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. }
    + split.
      { apply EquivThenEqual. split.
        { rewrite HHw. apply imply_and_or. apply H. }
        { rewrite eqb_while_faiwhile. unfold fai. rewrite HHH.
          rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. } }
      { apply EquivThenEqual. split.
        { rewrite HHt. apply imply_and_or. apply H. }
        { rewrite eqb_while_faiwhile. unfold fai. rewrite HHH.
          rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. } }
  - assert (H : (nott (qt ((PhaseCond_1_1 x v); II)) s1 s2 ->
                 nott (qt (C_null /H\ (while b P))) s1 s2) /\
                (wt ((PhaseCond_1_1 x v); II) s1 s2 ->
                 wt (C_null /H\ (while b P)) s1 s2) /\
                (tt ((PhaseCond_1_1 x v); II) s1 s2 ->
                 tt (C_null /H\ (while b P)) s1 s2)).
    { apply derivationLemma_iteration_1_2. rewrite HeqHq. reflexivity. }
    split. 
    + apply EquivThenEqual. split.
      { rewrite HHq. apply imply_and_or. apply H. }
      { rewrite eqb_while_faiwhile. unfold fai. rewrite HHH.
        rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. }
    + split.
      { apply EquivThenEqual. split.
        { rewrite HHw. apply imply_and_or. apply H. }
        { rewrite eqb_while_faiwhile. unfold fai. rewrite HHH.
          rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. } }
      { apply EquivThenEqual. split.
        { rewrite HHt. apply imply_and_or. apply H. }
        { rewrite eqb_while_faiwhile. unfold fai. rewrite HHH.
          rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq. crush. } }
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_iteration_1_3_1_4 :
  forall (x : id) (v : nat) (s1 s2 : env)
         (b : env -> env -> bool) (P : tripored),
  ((if b s1 s2 then nott (qt ((PhaseCond_1_2 x v); (P; (while b P)))) s1 s2
               else nott (qt ((PhaseCond_1_2 x v); II)) s1 s2)
    = nott (qt (C_notnull_1 /H\ (while b P))) s1 s2) /\
  ((if b s1 s2 then wt ((PhaseCond_1_2 x v); (P; (while b P))) s1 s2
               else wt ((PhaseCond_1_2 x v); II) s1 s2)
    = wt (C_notnull_1 /H\ (while b P)) s1 s2) /\
  ((if b s1 s2 then tt ((PhaseCond_1_2 x v); (P; (while b P))) s1 s2
               else tt ((PhaseCond_1_2 x v); II) s1 s2)
    = tt (C_notnull_1 /H\ (while b P)) s1 s2).
Proof.
  intros. remember (b s1 s2) as Hq. destruct Hq.
  - assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
    { rewrite <- seqtr_ii. reflexivity. } split.
    + apply EquivThenEqual. split.
      { apply derivationLemma_iteration_1_3. rewrite HeqHq. reflexivity. }
      { rewrite <- HH. intros. rewrite derivationLemma_Skip_1_2.
        rewrite H_C_notnull_1_seq.
        rewrite eqb_while_faiwhile in H. unfold fai in H. unfold bCondTripored in *. 
        unfold qt at 1 in H. unfold qt at 1. crush.
        rewrite <- double_nott in *. destruct H as [HA HB].
        split. apply HA. unfold nott in *. crush. apply HB.
        destruct s1 as (((n1, t1), tr1), f1).
        destruct s2 as (((n2, t2), tr2), f2).
        unfold seqtr at 1, qt in H. unfold seqtr at 1, qt.
        crush. rewrite notort_distributive in *.
        rewrite <- double_nott in *. destruct H as [HAA HBB].
        split. apply HAA. unfold nott at 1 in HBB.
        unfold nott at 1. crush. apply HBB. rewrite <- double_nott.
        unfold dseq at 1 in H. unfold dseq at 1. crush.
        exists x0. split.
        + apply H0.
        + destruct x0 as (((n3, t3), tr3), f3). 
          unfold seqtr, qt at 1 in H1. crush. unfold nott at 1, ifelse in H1.
          assert (HHH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                            b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
          { apply judge_b. unfold C_notnull_1, ttrOfEnv in HA;simpl in HA. 
            remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
            apply beq_tnil in HeqHqq. crush. 
            unfold ifelse, skip_cond1, skip_cond2, ttrOfEnv in H0.
            simpl in H0. rewrite <- HeqHqq in H0. destruct HA as [X Y].
            rewrite Y in H0. apply dseq_unit_l in H0.
            unfold I in H0. assert (HHHH : tr1 = tr3). { crush. }
            rewrite <- HHHH. rewrite <- HeqHqq.
            rewrite beq_ttr2_dec_self. reflexivity. }
          rewrite HHH in HeqHq. rewrite <- HeqHq in H1. unfold nott at 1 in H1.
          apply NNPP in H1. apply H1. }
    + split.
      { apply EquivThenEqual. split.
        { apply derivationLemma_iteration_1_3. rewrite HeqHq. reflexivity. }
        { rewrite <- HH. intros. rewrite derivationLemma_Skip_1_2. 
          rewrite H_C_notnull_1_seq.
          rewrite eqb_while_faiwhile in H. unfold fai in H. unfold bCondTripored in *. 
          unfold wt at 1 in H. unfold wt at 1. crush.
          destruct H as [HA HB]. split. apply HA. 
          destruct s1 as (((n1, t1), tr1), f1).
          destruct s2 as (((n2, t2), tr2), f2).
          unfold seqtr at 1, wt in HB. unfold seqtr at 1, wt. 
          crush. destruct HB. left. apply H. right.
          unfold dseq at 1 in H. unfold dseq at 1. crush.
          exists x0. destruct x0 as (((n3, t3), tr3), f3). split. 
          { apply H0. }
          { unfold wt at 1 in H1. simpl in H1.
            assert (HHH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                      b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
            { apply judge_b. unfold C_notnull_1, ttrOfEnv in HA;simpl in HA. 
              remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
              apply beq_tnil in HeqHqq. crush. 
              unfold ifelse, skip_cond1, skip_cond2, ttrOfEnv in H0.
              simpl in H0. rewrite <- HeqHqq in H0. destruct HA as [X Y].
              rewrite Y in H0. apply dseq_unit_l in H0.
              unfold I in H0. assert (HHHH : tr1 = tr3). { crush. }
              rewrite <- HHHH. rewrite <- HeqHqq.
              rewrite beq_ttr2_dec_self. reflexivity. }
              unfold ifelse in H1. rewrite HHH in HeqHq. 
              rewrite <- HeqHq in H1. apply H1. } } }
      { apply EquivThenEqual. split.
        { apply derivationLemma_iteration_1_3. rewrite HeqHq. reflexivity. }
        { rewrite <- HH. intros. rewrite derivationLemma_Skip_1_2. 
          rewrite H_C_notnull_1_seq.
          rewrite eqb_while_faiwhile in H. unfold fai in H. unfold bCondTripored in *.
          unfold tt at 1 in H. unfold tt at 1. simpl in *.
          destruct H as [HA HB]. split. apply HA. 
          destruct s1 as (((n1, t1), tr1), f1).
          destruct s2 as (((n2, t2), tr2), f2).
          unfold dseq at 1 in HB. unfold dseq at 1. crush. exists x0.
          destruct x0 as (((n3, t3), tr3), f3). split. 
          { apply H0. }
          { assert (HHH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                      b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
            { apply judge_b. unfold C_notnull_1, ttrOfEnv in HA;simpl in HA. 
              remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
              apply beq_tnil in HeqHqq. crush. 
              unfold ifelse, skip_cond1, skip_cond2, ttrOfEnv in H0.
              simpl in H0. rewrite <- HeqHqq in H0. destruct HA as [X Y].
              rewrite Y in H0. apply dseq_unit_l in H0.
              unfold I in H0. assert (HHHH : tr1 = tr3). { crush. }
              rewrite <- HHHH. rewrite <- HeqHqq.
              rewrite beq_ttr2_dec_self. reflexivity. }
            unfold ifelse in H1. rewrite HHH in HeqHq. 
            rewrite <- HeqHq in H1. apply H1. } } }
  - assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
    { rewrite <- seqtr_ii. reflexivity. } split.
    + apply EquivThenEqual. split.
      { apply derivationLemma_iteration_1_4. rewrite HeqHq. reflexivity. }
      { rewrite <- HH. intros. rewrite derivationLemma_Skip_1_2.
        rewrite H_C_notnull_1_seq.
        rewrite eqb_while_faiwhile in H. unfold fai in H. unfold bCondTripored in *. 
        unfold qt at 1 in H. unfold qt at 1. crush.
        rewrite <- double_nott in *. destruct H as [HA HB].
        split. apply HA. unfold nott in *. crush. apply HB.
        destruct s1 as (((n1, t1), tr1), f1).
        destruct s2 as (((n2, t2), tr2), f2).
        unfold seqtr at 1, qt in H. unfold seqtr at 1, qt.
        crush. rewrite notort_distributive in *.
        rewrite <- double_nott in *. destruct H as [HAA HBB].
        split. apply HAA. unfold nott at 1 in HBB.
        unfold nott at 1. crush. apply HBB. rewrite nott_ttrue_tfalse.
        unfold dseq at 1 in H. unfold dseq at 1. crush.
        exists x0. split.
        + apply H0.
        + destruct x0 as (((n3, t3), tr3), f3). 
          unfold seqtr, qt at 1 in H1. crush. unfold nott at 1, ifelse in H1.
          assert (HHH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                            b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
          { apply judge_b. unfold C_notnull_1, ttrOfEnv in HA;simpl in HA. 
            remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
            apply beq_tnil in HeqHqq. crush. 
            unfold ifelse, skip_cond1, skip_cond2, ttrOfEnv in H0.
            simpl in H0. rewrite <- HeqHqq in H0. destruct HA as [X Y].
            rewrite Y in H0. apply dseq_unit_l in H0.
            unfold I in H0. assert (HHHH : tr1 = tr3). { crush. }
            rewrite <- HHHH. rewrite <- HeqHqq.
            rewrite beq_ttr2_dec_self. reflexivity. }
          rewrite HHH in HeqHq. rewrite <- HeqHq in H1. 
          unfold II, qt, tfalse, ttrue in *. crush. }
    + split.
      { apply EquivThenEqual. split.
        { apply derivationLemma_iteration_1_4. rewrite HeqHq. reflexivity. }
        { rewrite <- HH. intros. rewrite derivationLemma_Skip_1_2. 
          rewrite H_C_notnull_1_seq.
          rewrite eqb_while_faiwhile in H. unfold fai in H. unfold bCondTripored in *. 
          unfold wt at 1 in H. unfold wt at 1. crush.
          destruct H as [HA HB]. split. apply HA. 
          destruct s1 as (((n1, t1), tr1), f1).
          destruct s2 as (((n2, t2), tr2), f2).
          unfold seqtr at 1, wt in HB. unfold seqtr at 1, wt. 
          crush. destruct HB. left. apply H. right.
          unfold dseq at 1 in H. unfold dseq at 1. crush.
          exists x0. destruct x0 as (((n3, t3), tr3), f3). split. 
          { apply H0. }
          { unfold wt at 1 in H1. simpl in H1.
            assert (HHH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                      b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
            { apply judge_b. unfold C_notnull_1, ttrOfEnv in HA;simpl in HA. 
              remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
              apply beq_tnil in HeqHqq. crush. 
              unfold ifelse, skip_cond1, skip_cond2, ttrOfEnv in H0.
              simpl in H0. rewrite <- HeqHqq in H0. destruct HA as [X Y].
              rewrite Y in H0. apply dseq_unit_l in H0.
              unfold I in H0. assert (HHHH : tr1 = tr3). { crush. }
              rewrite <- HHHH. rewrite <- HeqHqq.
              rewrite beq_ttr2_dec_self. reflexivity. }
              unfold ifelse in H1. rewrite HHH in HeqHq. 
              rewrite <- HeqHq in H1. apply H1. } } } 
      { apply EquivThenEqual. split.
        { apply derivationLemma_iteration_1_4. rewrite HeqHq. reflexivity. }
        { rewrite <- HH. intros. rewrite derivationLemma_Skip_1_2. 
          rewrite H_C_notnull_1_seq.
          rewrite eqb_while_faiwhile in H. unfold fai in H. unfold bCondTripored in *.
          unfold tt at 1 in H. unfold tt at 1. simpl in *.
          destruct H as [HA HB]. split. apply HA. 
          destruct s1 as (((n1, t1), tr1), f1).
          destruct s2 as (((n2, t2), tr2), f2).
          unfold dseq at 1 in HB. unfold dseq at 1. crush. exists x0.
          destruct x0 as (((n3, t3), tr3), f3). split. 
          { apply H0. }
          { assert (HHH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                      b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
            { apply judge_b. unfold C_notnull_1, ttrOfEnv in HA;simpl in HA. 
              remember (beq_ttr_dec tr1 tnil) as Hqq. destruct Hqq.
              apply beq_tnil in HeqHqq. crush. 
              unfold ifelse, skip_cond1, skip_cond2, ttrOfEnv in H0.
              simpl in H0. rewrite <- HeqHqq in H0. destruct HA as [X Y].
              rewrite Y in H0. apply dseq_unit_l in H0.
              unfold I in H0. assert (HHHH : tr1 = tr3). { crush. }
              rewrite <- HHHH. rewrite <- HeqHqq.
              rewrite beq_ttr2_dec_self. reflexivity. }
            unfold ifelse in H1. rewrite HHH in HeqHq. 
            rewrite <- HeqHq in H1. apply H1. } } }
Qed.

(** ----------------------------------------------------------------- **)

Lemma completeRule_iteration_4_1 :
  forall (c : guard) (b : env -> env -> bool) (P : tripored),
  (PhaseCond_4_1 c true); (while b P) = C_notnull_0 /H\ (while b P).
Proof.
  intros. apply derivationLemma_iteration_4_1.
Qed.

(** ----------------------------------------------------------------- **)
















