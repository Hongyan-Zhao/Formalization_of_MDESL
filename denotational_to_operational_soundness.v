(**
  @name Formalization of Verilog
  @version 0.1
  @authors Zhao Hongyan
  @date 7/9/2020
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
Require Import FunctionalExtensionality.
Require Import CpdtTactics.

(** transitional condition **)
(** four instantaneous transitions **)
Definition Cond_1_1 (x : id) (v : nat) : trans := 
  fun s1 s2 => Inv s1 s2 /\
  (timeOfEnv s1) = (timeOfEnv s2) /\
  (trOfEnv s1) = (trOfEnv s2) /\
  (flagOfEnv s2) = true /\
  (ttrOfEnv s1) = tnil /\
  (ttr1 (ttrOfEnv s2)) = (last (trOfEnv s1)) /\
  (ttr2 (ttrOfEnv s2)) = fvalue_update (last (trOfEnv s1)) x v.

Definition Cond_1_2 (x : id) (v : nat) : trans :=
  fun s1 s2 => Inv s1 s2 /\
  (timeOfEnv s1) = (timeOfEnv s2) /\
  (trOfEnv s1) = (trOfEnv s2) /\
  (flagOfEnv s1) = true /\
  (flagOfEnv s2) = true /\
  (ttrOfEnv s1) <> tnil /\
  (ttr1 (ttrOfEnv s2)) = (ttr1 (ttrOfEnv s1)) /\
  (ttr2 (ttrOfEnv s2)) = fvalue_update (ttr2 (ttrOfEnv s1)) x v.

Definition Cond_2_1 : trans :=
  fun s1 s2 => Inv s1 s2 /\
  (timeOfEnv s1) = (timeOfEnv s2) /\
  (trOfEnv s1) = (trOfEnv s2) /\
  (flagOfEnv s1) = true /\
  (flagOfEnv s2) = false /\
  (ttrOfEnv s1) <> tnil /\
  (ttr1 (ttrOfEnv s2)) = (ttr1 (ttrOfEnv s1)) /\
  (ttr2 (ttrOfEnv s2)) = (ttr2 (ttrOfEnv s1)).

Definition Cond_3_1 (x : id) (v : nat) : trans :=
  fun s1 s2 => Inv s1 s2 /\
  (timeOfEnv s1) = (timeOfEnv s2) /\
  (trOfEnv s1) = (trOfEnv s2) /\
  (ttrOfEnv s1) = tnil /\
  (flagOfEnv s2) = false /\
  (ttr1 (ttrOfEnv s2)) = (last (trOfEnv s1)) /\
  (ttr2 (ttrOfEnv s2)) = fvalue_update (last (trOfEnv s1)) x v.

(** phase semantics about four instantaneous transitions **)
Definition PhaseCond_1_1 (x : id) (v : nat) : tripored :=
  (ttrue, tfalse, Cond_1_1 x v).

Definition PhaseCond_1_2 (x : id) (v : nat) : tripored :=
  (ttrue, tfalse, Cond_1_2 x v).

Definition PhaseCond_2_1 : tripored :=
  (ttrue, tfalse, Cond_2_1).

Definition PhaseCond_3_1 (x : id) (v : nat) : tripored :=
  (ttrue, tfalse, Cond_3_1 x v).

(** two event transitions **)
Definition Cond_4_1 (c : guard) (sig : bool) : trans :=
  fun s1 s2 => Inv s1 s2 /\
  (timeOfEnv s1) = (timeOfEnv s2) /\
  (if sig
    then dfire c (ttr1 (ttrOfEnv s1)) (ttr2 (ttrOfEnv s2)) = true
    else dfire c (ttr1 (ttrOfEnv s1)) (ttr2 (ttrOfEnv s2)) = false) /\
  (flagOfEnv s1) = false /\
  (ttrOfEnv s1) <> tnil /\
  (ttrOfEnv s2) = tnil /\
  (if (eq_lfvalue_dec (last (trOfEnv s1)) (ttr2 (ttrOfEnv s1)))
    then ((trOfEnv s2) = (trOfEnv s1))
    else ((trOfEnv s2) = (trOfEnv s1) ++ [((timeOfEnv s1), (ttr2 (ttrOfEnv s1)), true)])
  ).

Definition Cond_4_2 (c : guard) (sig : bool) : trans :=
  fun s1 s2 => Inv s1 s2 /\
  (timeOfEnv s1) = (timeOfEnv s2) /\
  (ttrOfEnv s1) = tnil /\
  (ttrOfEnv s2) = tnil /\
  (if sig
    then dfire c (last (trOfEnv s1)) (last (trOfEnv s2)) = true
    else dfire c (last (trOfEnv s1)) (last (trOfEnv s2)) = false) /\
  ((trOfEnv s1) = (trOfEnv s2) \/
    ((forall f, In f (getFlag s1 s2) -> f = false) /\
     (forall t, In t (getTime s1 s2) -> t = timeOfEnv s1)
     (** /\ (SortedList (getTime s1 s2)) **))
  ).

(** phase semantics about two event transitions **)
Definition PhaseCond_4_1 (c : guard) (sig : bool) : tripored :=
  (ttrue, tfalse, Cond_4_1 c sig).

Definition PhaseCond_4_2 (c : guard) (sig : bool): tripored :=
  (ttrue, tfalse, Cond_4_2 c sig).

(** one time advancing transition **)(** seems no use?**)
Definition Cond_5_1 : trans :=
  fun s1 s2 => Inv s1 s2 /\
  (trOfEnv s1) = (trOfEnv s2) /\
  (ttrOfEnv s1) = tnil /\
  (ttrOfEnv s2) = tnil.

(** phase semantics about time advancing transition **)
Definition PhaseCond_5_1 : tripored :=
  phase5.

Definition C_null : trans :=
  fun s1 s2 => (ttrOfEnv s1) = tnil.
Definition C_notnull_1 : trans :=
  fun s1 s2 => (ttrOfEnv s1) <> tnil /\ (flagOfEnv s1) = true.
Definition C_notnull_0 : trans :=
  fun s1 s2 => (ttrOfEnv s1) <> tnil /\ (flagOfEnv s1) = false.

(**
Inductive bCond : Type :=
  | C_null : forall s1 s2, Cond_null s1 s2 -> bCond
  | C_notnull_1 : forall s1 s2, Cond_notnull_1 s1 s2 -> bCond
  | C_notnull_0 : forall s1 s2, Cond_notnull_0 s1 s2 -> bCond.
**)

(** healthy formula P with Boolean condition b
    which does not contain ok, ok', wait and wait' 
    b: C_null / C_notnull_1 / C_notnull_0
  **)
Definition bCondTripored (b : trans) (P : tripored) : tripored :=
  ((nott (andt b (nott (qt P)))), (andt b (wt P)), (andt b (tt P))).

Notation "b /H\ P" := (bCondTripored b P)(at level 30). 

(** the equality of two trans **)


(** Lemma: true /H\ P = P **)
Lemma double_nott :
  forall (P : trans), P = nott (nott P).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold nott. apply EquivThenEqual. split.
  - intros H. unfold not. intros G. apply G. apply H.
  - apply NNPP.
Qed.
Lemma H_ttrue :
  forall (P : tripored), bCondTripored ttrue P = P.
Proof.
  unfold bCondTripored. intros.
  destruct P as ((q1, w1), t1).
  do 3 rewrite -> andt_ttrue_l.
  unfold qt, wt. simpl. rewrite <- double_nott. 
  reflexivity.
Qed.

(** Lemma: b /H\ (P \/ Q) = (b /H\ P) \/ (b /H\ Q) **)
Lemma notandt_distributive :
  forall P Q, nott (andt P Q) = ort (nott P) (nott Q).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold nott, andt, ort. apply EquivThenEqual. split.
  - apply not_and_or.
  - apply or_not_and.
Qed.
Lemma notort_distributive :
  forall P Q, nott (ort P Q) = andt (nott P) (nott Q).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold nott, andt, ort. apply EquivThenEqual. split.
  - apply not_or_and.
  - apply and_not_or.
Qed.
Lemma aot_distributive_l :
  forall P Q R, andt (ort P Q) R = ort (andt P R) (andt Q R).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold nott, andt, ort. apply EquivThenEqual. split.
  - intros. destruct H as [HA HB]. destruct HA.
    + left. split. { apply H. } { apply HB. }
    +  right. split. { apply H. } { apply HB. }
  - intros. destruct H.
    + split. { left. apply H. } { apply H. }
    + split. { right. apply H. } { apply H. }
Qed.
Lemma aot_distributive_r :
  forall P Q R, andt P (ort Q R) = ort (andt P Q) (andt P R).
Proof.
  intros. rewrite andt_comm. 
  rewrite -> aot_distributive_l. rewrite -> andt_comm. 
  assert (H : andt R P = andt P R). { rewrite -> andt_comm. reflexivity. } 
  rewrite -> H. reflexivity.
Qed.

Lemma oat_distributive_r :
  forall P Q R, ort P (andt Q R) = andt (ort P Q) (ort P R).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold andt, ort. apply EquivThenEqual. split.
  - intros. split.
    + destruct H. { left. apply H. } { right. apply H. } 
    + destruct H. { left. apply H. } { right. apply H. }
  - intros. destruct H as [HA HB]. destruct HA.
    + left. apply H.
    + destruct HB. { left. apply H0. } { right. split. apply H. apply H0. }
Qed.

Lemma H_bPQ_distributive :
  forall (b : trans) (P Q : tripored),
  bCondTripored b (uniontr P Q) = uniontr (bCondTripored b P) (bCondTripored b Q).
Proof.
  unfold bCondTripored. intros. 
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  unfold uniontr, qt, wt. simpl.
  rewrite <- notort_distributive.
  rewrite <- aot_distributive_r.
  rewrite <- notandt_distributive. 
  do 2 rewrite -> aot_distributive_r.
  reflexivity.
Qed.

(** Lemma: (b \/ c) /H\ P = (b /H\ P) \/ (c /H\ P) **)
Lemma H_bcP_distributive :
  forall (b c : trans) (P : tripored),
  bCondTripored (ort b c) P = uniontr (bCondTripored b P) (bCondTripored c P).
Proof.
  unfold bCondTripored. intros.
  destruct P as ((q1, w1), t1).
  unfold uniontr, qt, wt. simpl.
  rewrite -> aot_distributive_l.
  rewrite -> notort_distributive.
  do 2 rewrite -> aot_distributive_l.
  reflexivity.
Qed.

(** Lemma : a /H\ (b /H\ P) = b /H\ (a /H\ P) **)
Lemma andt_assoc :
  forall P Q R, andt P (andt Q R) = andt Q (andt P R).
Proof.
  intros. do 2 (apply functional_extensionality;intros).
  unfold andt. apply EquivThenEqual; split; crush.
Qed.

Lemma bCondTripored_comm :
  forall (a b : trans) (P : tripored),
  a /H\ (b /H\ P) = b /H\ (a /H\ P).
Proof.
  intros. unfold bCondTripored.
  destruct P as ((q1, w1), t1).
  unfold qt, wt, tt. simpl.
  do 2 rewrite <- double_nott. f_equal.
  - f_equal; rewrite andt_assoc; reflexivity. 
  - rewrite andt_assoc. reflexivity.
Qed.

(** Lemma : a /H\ (a /H\ P) = a /H\ P **)
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

(** Lemma: if P => Q, then b /H\ P => b /H\ Q **)
(** Definition implyt (P Q : trans) : trans :=
  fun s1 s2 => P s1 s2 -> Q s1 s2. **)
Definition implytr (m n : tripored) : Prop :=
  forall (s1 s2 : env),
    ((nott (qt m)) s1 s2 -> (nott (qt n)) s1 s2) /\
    ((wt m) s1 s2 -> (wt n) s1 s2) /\
    ((tt m) s1 s2 -> (tt n) s1 s2).

Notation "m '==>' n" := (implytr m n) 
          (at level 50, no associativity).

Lemma transmit_H :
  forall b P Q, (P ==> Q) -> ((b /H\ P) ==> (b /H\ Q)).
Proof.
  unfold implytr. intros b P Q. intros H s1 s2.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  unfold bCondTripored, qt, wt, tt in *; simpl in *.
  split.
  - intros. unfold nott, andt in *; simpl in *. crush.
    apply NNPP in H0. destruct H0 as [HA HB]. apply H in HB.
    + apply HB.
    + apply NNPP in H2. apply H2. apply HA.
  - split.
    + intros. unfold andt in *; simpl in *. crush. apply H in H2. apply H2.
    + intros. unfold andt in *; simpl in *. crush. apply H in H2. apply H2.
Qed.

(** compositionality of implytr **)
Theorem implytr_comp_1 :
  forall P Q R,
  P ==> Q -> P;R ==> Q;R.
Proof.
  intros.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  destruct R as ((q3, w3), t3).
  unfold implytr in *. intros.
  unfold seqtr, qt, wt, tt in *;simpl in *. split.
  - intros. rewrite <- double_nott in *. destruct H0.
    + left. apply H in H0. apply H0.
    + right. unfold dseq in *. crush. exists x.
      apply H in H1. split;[apply H1 | apply H2].
  - split;intros.
    + destruct H0.
      { left. apply H in H0. apply H0. }
      { right. unfold dseq in *. crush. exists x.
        apply H in H1. split;[apply H1 | apply H2]. }
    + unfold dseq in *. crush. exists x. 
      apply H in H1. split;[apply H1 | apply H2].
Qed.


Theorem implytr_trans :
  forall P Q R,
  P ==> Q -> Q ==> R -> P ==> R.
Proof.
  intros.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  destruct R as ((q3, w3), t3).
  unfold implytr in *. intros.
  unfold seqtr, qt, wt, tt in *;simpl in *. split.
  - intros. apply H0. apply H. apply H1.
  - split;intros;apply H0;apply H;apply H1.
Qed.

(** If b only contain any combination of variables tr, ttr, and flag,
    Lemma: (b /H\ P) ;Q = b /H\ (P ;Q) **)
(** Lemma: (C(null) /H\ P) ;Q = C(null) /H\ (P ;Q) **)
Lemma dseqandt_distr_null :
  forall Q R, dseq (andt C_null Q) R = andt C_null (dseq Q R).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold andt, dseq. apply EquivThenEqual. split;crush.
  - exists x1. split. apply H2. apply H1.
  - exists x1. split. 
    + split. 
      { unfold C_null in *;simpl in *. apply H0. }
      { apply H1. }
    + apply H2.
Qed.
  
Lemma H_C_null_seq :
  forall (P Q : tripored),
  seqtr (bCondTripored C_null P) Q = bCondTripored C_null (seqtr P Q).
Proof.
  intros. unfold seqtr, bCondTripored.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  unfold qt, wt, tt. simpl. 
  rewrite -> notandt_distributive. rewrite <- double_nott. 
  rewrite -> notort_distributive. rewrite <- double_nott.
  rewrite <- double_nott. rewrite -> notandt_distributive.
  rewrite -> notort_distributive. rewrite <- double_nott.
  rewrite -> aot_distributive_r. rewrite -> oat_distributive_r.
  rewrite <- notandt_distributive. f_equal.
  - f_equal;rewrite -> dseqandt_distr_null;reflexivity.
  - rewrite -> dseqandt_distr_null. reflexivity.
Qed.

(** Lemma: (C(notnull_1) /H\ P) ;Q = C(notnull_1) /H\ (P ;Q) **)
Lemma dseqandt_distr_notnull_1 :
  forall Q R, dseq (andt C_notnull_1 Q) R = andt C_notnull_1 (dseq Q R).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold andt, dseq. apply EquivThenEqual. split;crush.
  - exists x1. split. apply H2. apply H1.
  - exists x1. split. 
    + split. 
      { unfold C_notnull_1 in *;simpl in *. apply H0. }
      { apply H1. }
    + apply H2.
Qed.
  
Lemma H_C_notnull_1_seq :
  forall (P Q : tripored),
  seqtr (bCondTripored C_notnull_1 P) Q = bCondTripored C_notnull_1 (seqtr P Q).
Proof.
  intros. unfold seqtr, bCondTripored.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  unfold qt, wt, tt. simpl. 
  rewrite -> notandt_distributive. rewrite <- double_nott. 
  rewrite -> notort_distributive. rewrite <- double_nott.
  rewrite <- double_nott. rewrite -> notandt_distributive.
  rewrite -> notort_distributive. rewrite <- double_nott.
  rewrite -> aot_distributive_r. rewrite -> oat_distributive_r.
  rewrite <- notandt_distributive. f_equal.
  - f_equal;rewrite -> dseqandt_distr_notnull_1;reflexivity.
  - rewrite -> dseqandt_distr_notnull_1. reflexivity.
Qed.

(** Lemma: (C(notnull_0) /H\ P) ;Q = C(notnull_0) /H\ (P ;Q) **)
Lemma dseqandt_distr_notnull_0 :
  forall Q R, dseq (andt C_notnull_0 Q) R = andt C_notnull_0 (dseq Q R).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold andt, dseq. apply EquivThenEqual. split;crush.
  - exists x1. split. apply H2. apply H1.
  - exists x1. split. 
    + split. 
      { unfold C_notnull_0 in *;simpl in *. apply H0. }
      { apply H1. }
    + apply H2.
Qed.
  
Lemma H_C_notnull_0_seq :
  forall (P Q : tripored),
  seqtr (bCondTripored C_notnull_0 P) Q = bCondTripored C_notnull_0 (seqtr P Q).
Proof.
  intros. unfold seqtr, bCondTripored.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  unfold qt, wt, tt. simpl. 
  rewrite -> notandt_distributive. rewrite <- double_nott. 
  rewrite -> notort_distributive. rewrite <- double_nott.
  rewrite <- double_nott. rewrite -> notandt_distributive.
  rewrite -> notort_distributive. rewrite <- double_nott.
  rewrite -> aot_distributive_r. rewrite -> oat_distributive_r.
  rewrite <- notandt_distributive. f_equal.
  - f_equal;rewrite -> dseqandt_distr_notnull_0;reflexivity.
  - rewrite -> dseqandt_distr_notnull_0. reflexivity.
Qed.

(** a set of lemmas about phase semantics, 
    which are helpful in considering the linking of MDESL semantics **)
(** Lemma 4.4 **)
Lemma helpfulLemma_4_4 :
  forall (x : id) (v : nat),
  PhaseCond_1_1 x v = bCondTripored C_null init.
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_5 :
  forall (x : id) (v : nat),
  PhaseCond_1_2 x v = bCondTripored C_notnull_1 II.
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_6 :
  forall (x : id) (v : nat),
  PhaseCond_1_1 x v = bCondTripored C_null (init; (tassign x v)).
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_7 :
  forall (x : id) (v : nat),
  PhaseCond_1_2 x v = bCondTripored C_notnull_1 (tassign x v).
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_9 :
  forall (c : guard),
  PhaseCond_4_1 c true = bCondTripored C_notnull_0 flash.
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_10 : (* self-triggered, @(g) remains untriggered *)
  forall (c :guard),
  (PhaseCond_4_1 c false); (await c) = bCondTripored C_notnull_0 (await c).
Proof.
  (** TODO: **)
Admitted.
 
Lemma helpfulLemma_4_11 : (* self can trigger @(g) *)
  forall (c : guard),
  (PhaseCond_4_1 c true) = bCondTripored C_notnull_0 (selftriger c).
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_12 : (* environment does an atomic action *)
  forall (c : guard) (sig : bool), (* so c and sig have no meaning here *)
  (PhaseCond_4_2 c sig);(hold 0) = bCondTripored C_null (hold 0).
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_13 : (* environment triggered, @(g) remains untriggered *)
  forall (c : guard),
  (PhaseCond_4_2 c false);(await c) = bCondTripored C_null (await c).
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_13_extend :
  forall (c : guard),
  (PhaseCond_4_2 c false);(andtr (await c) (hold 0)) = bCondTripored C_null (andtr (await c) (hold 0)).
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_14 : (* environment can trigger @(g) *)
  forall (c : guard),
  (PhaseCond_4_2 c true) = bCondTripored C_null (trig c).
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_15_1 :
  forall (c : guard),
  (PhaseCond_2_1);(selftriger c) = bCondTripored C_notnull_1 (selftriger c).
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_15_2 :
  forall (c : guard),
  (PhaseCond_2_1);(await c) = bCondTripored C_notnull_1 (await c).
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_15_3 :
  (PhaseCond_2_1);flash = bCondTripored C_notnull_1 flash.
Proof.
  (** TODO: **)
Admitted.

Lemma helpfulLemma_4_16 :
  phase5 ==> C_null /H\ (hold 1).
Proof.
  (** TODO: **)
Admitted.

(** the derivation of operational semantics (soundness) **)
(** ----------------------------------------------------------------- **)

Lemma derivationLemma_Skip_1_1 :
  forall (x : id) (v : nat),
  (PhaseCond_1_1 x v); II ==> C_null /H\ Skip.
Proof.
  intros. rewrite -> seqtr_ii.
  rewrite -> helpfulLemma_4_4.
  unfold implytr. intros. split.
  - intros. unfold init, Skip, bCondTripored in *. 
    unfold qt at 1 in H; simpl in H. apply NNPP in H.
    unfold qt in H; simpl in H. 
    unfold nott, andt, ttrue, C_null, ttrOfEnv in H; simpl in H.
    crush.
  - split.
    + intros. unfold init, Skip, bCondTripored in *.
      unfold wt at 1 in H; simpl in H. unfold wt in H; simpl in H.
      unfold andt, tfalse, C_null, ttrOfEnv in H;simpl in H.
      crush.
    + intros. unfold init, Skip, bCondTripored in *.
      unfold tt at 1 in H;simpl in H.
      rewrite ii_seqtr in *. rewrite seqtr_ii in *.
      unfold tt at 1;simpl.
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold andt, ini, C_null in H. 
      unfold Inv, ttrOfEnv, timeOfEnv, flagOfEnv, trOfEnv in H;simpl in H.
      unfold andt. split.
      { unfold C_null, ttrOfEnv. crush. }
      { unfold ifelse, skip_cond1, ttrOfEnv;simpl.
        remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
        { unfold holdt, ini, dseq, Inv, ttrOfEnv, timeOfEnv, flagOfEnv, trOfEnv. 
          exists (n1, t1, tr1, f1). crush. apply idle_self. }
        { destruct f1. unfold I. crush.
          unfold holdt, ini, dseq, tflash, Inv, ttrOfEnv, timeOfEnv, flagOfEnv, trOfEnv.
          exists (n1, t1, tr1, false). crush. } }
      { rewrite qt_hold_init_ttrue in *. reflexivity. }
Qed.

(** ----------------------------------------------------------------- **)

Lemma notnull_1_Skip_II_qt :
  andt C_notnull_1 (nott (qt II)) = andt C_notnull_1 (nott (qt Skip)).
Proof.
  intros. do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split; intros.
  - unfold II, Skip, qt in *; simpl in *. 
    rewrite ii_seqtr in *. rewrite seqtr_ii in *.
    rewrite qt_hold_init_ttrue in *.
    unfold andt in *; simpl in *.
    destruct x as (((n1, t1), tr1), f1).
    destruct x0 as (((n2, t2), tr2), f2).
    destruct H as [HA HB].
    split.
    + apply HA.
    + unfold ifelse, skip_cond1, nott.
      unfold ttrOfEnv. simpl.
      destruct (beq_ttr_dec tr1 tnil).
      { apply HB. }
      { unfold qt. simpl. unfold ifelse, skip_cond2, flagOfEnv in *; simpl in *.
        unfold C_notnull_1, ttrOfEnv, flagOfEnv in HA. simpl in HA.
        destruct HA as [HAA HAB].
        destruct f1.
        { unfold II, qt. simpl. apply HB. }
        { crush. }
      }
    + rewrite qt_hold_init_ttrue in *. reflexivity.
  - unfold II, qt. simpl.
    unfold andt in *; simpl in *.
    destruct H as [HA HB].
    split.
    + apply HA.
    + destruct x as (((n1, t1), tr1), f1).
      destruct x0 as (((n2, t2), tr2), f2).
      unfold C_notnull_1, ttrOfEnv, flagOfEnv in HA. simpl in HA.
      destruct HA as [HAA HAB].
      unfold qt, Skip in HB. simpl in HB.
      unfold nott in *; simpl in *.
      rewrite ii_seqtr in *. rewrite seqtr_ii in *.
      rewrite qt_hold_init_ttrue in *.
      unfold ifelse, skip_cond1, ttrOfEnv in HB; simpl in HB.
      destruct (beq_ttr_dec tr1 tnil).
      { apply HB. }
      { unfold qt in HB; simpl in HB.
        unfold ifelse, skip_cond2, flagOfEnv in HB; simpl in HB.
        rewrite HAB in HB. unfold qt, II in HB; simpl in HB. apply HB. }
      rewrite qt_hold_init_ttrue in *. reflexivity.
Qed.

Lemma notnull_1_Skip_II_wt :
  andt C_notnull_1 (wt II) = andt C_notnull_1 (wt Skip).
Proof.
  intros. do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split; intros.
  - unfold II, wt in H. simpl in H. rewrite andt_tfalse_r in H.
    unfold andt, C_notnull_1, Skip, wt in *; simpl in *.
    destruct x as (((n1, t1), tr1), f1).
    destruct x0 as (((n2, t2), tr2), f2).
    unfold seqtr, wt. simpl.
    unfold wt. simpl.
    do 2 rewrite dseq_tfalse_r.
    do 2 rewrite ort_tfalse_r.
    do 2 rewrite ort_tfalse_l.
    rewrite dseq_unit_I.
    unfold dseq, ifelse. crush.
  - unfold II, wt. simpl. rewrite andt_tfalse_r. 
    unfold andt, C_notnull_1, Skip, wt in H. simpl in H.
    destruct x as (((n1, t1), tr1), f1).
    destruct x0 as (((n2, t2), tr2), f2).
    unfold seqtr, wt in H. simpl in H.
    unfold wt in H. simpl in H.
    do 2 rewrite dseq_tfalse_r in H.
    do 2 rewrite ort_tfalse_r in H.
    do 2 rewrite ort_tfalse_l in H.
    rewrite dseq_unit_I in H.
    unfold dseq, ifelse in H. crush.
    unfold skip_cond1, ttrOfEnv in *. crush.
    destruct (beq_ttr_dec tr1 tnil).
    + unfold holdw in *. simpl in *.
      unfold trOfEnv, timeOfEnv in *; simpl in *.
      crush. rewrite plus_0_r in *.
      unfold Inv, timeOfEnv, trOfEnv in H0. simpl in H0.
      destruct H0 as [HA HB].
      apply (leb_correct n1 n2) in HB.
      apply (leb_correct_conv n2 n1) in H2. 
      rewrite HB in H2. crush.
    + apply H1.
Qed.

Lemma beq_tnil :
forall (tr1 : ttr),
  true = beq_ttr_dec tr1 tnil -> tr1 = tnil.
Proof.
  intros. destruct tr1.
  - reflexivity.
  - destruct p as (a, b). unfold beq_ttr_dec in H.
    discriminate H.
Qed.

Lemma notnull_1_Skip_II_tt :
  andt C_notnull_1 (tt II) = andt C_notnull_1 (tt Skip).
Proof.
  intros. do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split; intros.
  - unfold andt in *. destruct H as [HA HB]. split.
    + apply HA.
    + destruct x as (((n1, t1), tr1), f1).
      destruct x0 as (((n2, t2), tr2), f2).
      unfold C_notnull_1, ttrOfEnv, flagOfEnv in HA; simpl in HA. 
      destruct HA as [HAA HAB]. 
      unfold II, Skip, tt, I in *; simpl in *. rewrite <- HB.
      do 2 rewrite dseq_unit_I in *. 
      unfold ifelse, skip_cond1, ttrOfEnv; simpl.
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      { apply beq_tnil in HeqHq. rewrite HeqHq in HAA. crush. }
      { rewrite -> HAB. unfold I. reflexivity. }
  - unfold andt in *. destruct H as [HA HB]. split.
    + apply HA.
    + destruct x as (((n1, t1), tr1), f1).
      destruct x0 as (((n2, t2), tr2), f2).
      unfold C_notnull_1, ttrOfEnv, flagOfEnv in HA; simpl in HA. 
      destruct HA as [HAA HAB]. 
      unfold II, Skip, tt, I in *; simpl in *.
      do 2 rewrite dseq_unit_I in *. 
      unfold ifelse, skip_cond1, ttrOfEnv in HB; simpl in HB.
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      { apply beq_tnil in HeqHq. rewrite HeqHq in HAA. crush. }
      { rewrite -> HAB in HB. unfold I in HB. rewrite -> HAB. apply HB. }
Qed.

Lemma derivationLemma_Skip_1_2 :
  forall (x : id) (v : nat),
  (PhaseCond_1_2 x v); II = C_notnull_1 /H\ Skip.
Proof.
  intros. rewrite -> seqtr_ii. rewrite -> helpfulLemma_4_5.
  unfold bCondTripored. f_equal. f_equal.
  - rewrite -> notnull_1_Skip_II_qt. reflexivity.
  - rewrite -> notnull_1_Skip_II_wt. reflexivity.
  - rewrite -> notnull_1_Skip_II_tt. reflexivity.
Qed.

(** ----------------------------------------------------------------- **)

Lemma nott_ttrue_tfalse : 
  nott ttrue = tfalse.
Proof.
  do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split;unfold ttrue, tfalse, nott;crush.
Qed.

Lemma notnull_0_flash_skip_qt :
  dseq (andt C_notnull_0 tflash) (nott (qt Skip)) = andt C_notnull_0 (nott (qt Skip)).
Proof.
  intros. do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split; intros.
  - unfold dseq in H. destruct H as [x1 Hx].
    destruct x as (((n1, t1), tr1), f1).
    destruct x1 as (((n2, t2), tr2), f2).
    destruct x0 as (((n3, t3), tr3), f3).
    unfold C_notnull_0, tflash, Skip, qt, nott, andt, Inv, ttrOfEnv, timeOfEnv, flagOfEnv, trOfEnv in *. crush.
    rewrite ii_seqtr in *.
    + rewrite qt_hold_init_ttrue in *. rewrite seqtr_ii in *.
      unfold skip_cond1, ifelse, ttrOfEnv in H0. crush.
      unfold skip_cond1, ifelse, ttrOfEnv in H6. crush. 
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq. 
      { apply beq_tnil in HeqHq. apply H in HeqHq. apply HeqHq. }
      { unfold ttrue in H0. crush. }
    + rewrite qt_hold_init_ttrue. reflexivity.
    + rewrite qt_hold_init_ttrue. reflexivity.
  - unfold dseq. exists x.
    destruct x as (((n1, t1), tr1), f1).
    destruct x0 as (((n2, t2), tr2), f2).
    unfold C_notnull_0, tflash, Skip, qt, nott, andt, Inv, ttrOfEnv, timeOfEnv, flagOfEnv, trOfEnv in *. crush.
    rewrite ii_seqtr in *. rewrite qt_hold_init_ttrue in *. rewrite seqtr_ii in *.
    + unfold subseq. exists []. crush.
    + rewrite qt_hold_init_ttrue. reflexivity.
    + unfold skip_cond1, ifelse, ttrOfEnv in H1. crush.
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      { apply beq_tnil in HeqHq. apply H in HeqHq. crush. }
      { rewrite seqtr_ii in *. unfold qt, ifelsetr, skip_cond2 in H1. crush. 
        unfold ifelse in H1. crush. 
        unfold flash, hold, init, seqtr, qt, Inv, ttrOfEnv, timeOfEnv, flagOfEnv, trOfEnv in H1. crush.
        rewrite notort_distributive in H1. 
        unfold andt in H1. rewrite <- double_nott in H1. unfold ttrue at 1 in H1.
        rewrite <- double_nott in H1. rewrite -> nott_ttrue_tfalse in H1. rewrite dseq_tfalse_r in H1.
        rewrite ort_tfalse_l in H1. rewrite dseq_tfalse_r in H1. unfold tfalse, nott in H1. crush. }
    + remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      { apply beq_tnil in HeqHq. apply H in HeqHq. crush. }
      { rewrite ii_seqtr in *. rewrite seqtr_ii in *. rewrite qt_hold_init_ttrue in *.
        unfold skip_cond1, ifelse, ttrOfEnv in H1. crush. rewrite <- HeqHq in H1.
        unfold qt, ifelsetr, skip_cond2 in H1. crush. 
        unfold ifelse in H1. crush. 
        unfold flash, hold, init, seqtr, qt, Inv, ttrOfEnv, timeOfEnv, flagOfEnv, trOfEnv in H1. crush.
        rewrite notort_distributive in H1. 
        unfold andt in H1. rewrite <- double_nott in H1. unfold ttrue at 1 in H1.
        rewrite <- double_nott in H1. rewrite -> nott_ttrue_tfalse in H1. rewrite dseq_tfalse_r in H1.
        rewrite ort_tfalse_l in H1. rewrite dseq_tfalse_r in H1. unfold tfalse, nott in H1. crush.
        rewrite qt_hold_init_ttrue in *. reflexivity. }
Qed.

Lemma notnull_0_flash_skip_wt :
  dseq (andt C_notnull_0 tflash) (wt Skip) = andt C_notnull_0 (wt Skip).
Proof.
  intros. do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split; intros.
  - unfold dseq in H. destruct H as [x1 Hx].
    destruct x as (((n1, t1), tr1), f1).
    destruct x1 as (((n2, t2), tr2), f2).
    destruct x0 as (((n3, t3), tr3), f3).
    unfold tflash, C_notnull_0, andt in Hx;simpl in Hx. 
    unfold ttrOfEnv, Inv, timeOfEnv, trOfEnv in Hx. crush.
    unfold Skip, wt, C_notnull_0, andt, ttrOfEnv in *;simpl in *.
    split.
    + crush.
    + unfold skip_cond1, ifelse, ttrOfEnv in *;simpl in *.
      rewrite ii_seqtr in *. rewrite seqtr_ii in *. 
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      { apply beq_tnil in HeqHq. apply H in HeqHq. crush. }
      { unfold hold, init, seqtr, wt in H0;simpl in H0.
        rewrite dseq_tfalse_r in H0. rewrite ort_tfalse_r in H0.
        unfold holdw in H0. unfold Inv, trOfEnv, timeOfEnv in H0. crush. }
      { rewrite qt_hold_init_ttrue in *. reflexivity. }
      { rewrite qt_hold_init_ttrue in *. reflexivity. }
  - destruct x as (((n1, t1), tr1), f1).
    destruct x0 as (((n3, t3), tr3), f3).
    unfold Skip, C_notnull_0, wt, andt, ttrOfEnv, flagOfEnv in H;simpl in H. 
    destruct H as [HA HB].
    rewrite ii_seqtr in HB. rewrite seqtr_ii in HB.
    unfold dseq. exists (n1, t1, tr1, f1). 
    unfold skip_cond1, ifelse, ttrOfEnv in HB;simpl in HB.
    remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
    + apply beq_tnil in HeqHq. crush.
    + unfold skip_cond2, ifelsetr, ifelse, wt in HB;simpl in HB.
      destruct HA as [HAA HAB]. rewrite HAB in HB. 
      unfold flash, wt at 1 in HB;simpl in HB. rewrite ort_tfalse_l in HB.
      unfold hold, init, wt in HB;simpl in HB. unfold wt in HB;simpl in HB.
      rewrite dseq_tfalse_r in HB. rewrite ort_tfalse_r in HB.
      unfold tflash, holdw, dseq in HB;simpl in HB. destruct HB as [x Hx].
      destruct x as (((n2, t2), tr2), f2). 
      unfold Inv, timeOfEnv, ttrOfEnv, trOfEnv, flagOfEnv in Hx. crush.
    + rewrite qt_hold_init_ttrue. reflexivity.
Qed.

Lemma notnull_0_flash_skip_tt :
  dseq (andt C_notnull_0 tflash) (tt Skip) = andt C_notnull_0 (tt Skip).
Proof.
  intros. do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split; intros.
  - unfold dseq in H. destruct H as [x1 Hx].
    destruct x as (((n1, t1), tr1), f1).
    destruct x1 as (((n2, t2), tr2), f2).
    destruct x0 as (((n3, t3), tr3), f3).
    destruct Hx as [HH HC]. unfold andt in HH. destruct HH as [HA HB].
    unfold andt. unfold C_notnull_0, ttrOfEnv in *;simpl in HA. split.
    + simpl. apply HA.
    + unfold Skip in *;simpl in *. rewrite dseq_unit_I in *. rewrite dseq_unit_I in *.
      unfold dseq in *;simpl in *. unfold skip_cond1, ifelse, ttrOfEnv in *; simpl in *.
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq; crush.
      { apply beq_tnil in HeqHq. apply H in HeqHq. crush. }
      { rewrite <- HeqHq. exists (n2, t2, tr2, f2). split.
        { apply HB. }
        { remember (beq_ttr_dec tr2 tnil) as Hp; destruct Hp; crush. destruct f2. 
          { unfold tflash in HB. unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in HB. crush. }
          { destruct HC as [x Hx]. crush.
            destruct x as (((n4, t4), tr4), f4). 
            destruct x0 as (((n5, t5), tr5), f5). 
            exists (n4, t5, tr5, f5). rewrite <- HeqHq.
            crush;unfold tflash, holdt, ini in *;
            unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv, flagOfEnv in *;crush.
          }
        }
      }
  - destruct x as (((n1, t1), tr1), f1).
    destruct x0 as (((n2, t2), tr2), f2).
    unfold dseq, C_notnull_0, Skip, andt, ttrOfEnv in *;simpl in *.
    rewrite dseq_unit_I in *. rewrite dseq_unit_I in *.
    destruct H as [HA HB].
    unfold skip_cond1, ifelse, ttrOfEnv in HB;simpl in HB.
    remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
    + apply beq_tnil in HeqHq. crush.
    + destruct HA as [HAA HAB]. rewrite HAB in HB. 
      unfold dseq in HB. destruct HB as [x Hx].
      exists x. destruct x as (((n3, t3), tr3), f3). split.
      { split;crush. }
      { destruct Hx as [HA HB]. 
        unfold skip_cond1, ifelse, ttrOfEnv. simpl.
        remember (beq_ttr_dec tr3 tnil) as Hp. 
        destruct Hp;unfold tflash, ttrOfEnv in HA;crush. }
Qed.

Lemma derivationLemma_Skip_4_1 :
  forall (c : guard),
  (PhaseCond_4_1 c true); Skip = C_notnull_0 /H\ Skip.
Proof.
  intros. rewrite -> helpfulLemma_4_9. unfold bCondTripored, seqtr.
  unfold qt at 1, wt at 3, tt at 2, tt at 4, tt at 5. unfold fst, snd.
  unfold flash, qt at 1, wt at 1, tt at 3, tt at 2, tt at 1. unfold fst, snd.
  rewrite <- double_nott. rewrite nott_ttrue_tfalse. rewrite andt_tfalse_r.
  do 2 rewrite -> ort_tfalse_l. f_equal. f_equal.
  - rewrite -> notnull_0_flash_skip_qt. reflexivity.
  - rewrite -> notnull_0_flash_skip_wt. reflexivity.
  - rewrite -> notnull_0_flash_skip_tt. reflexivity.
Qed.

(** ----------------------------------------------------------------- **)

Lemma preDeriLemma_Skip_4_2 :
  forall (c : guard),
  (PhaseCond_4_2 c true); Skip = (PhaseCond_4_2 c true); (hold 0); init.
Proof.
  intros. unfold seqtr. unfold qt, wt, tt in *;simpl in *.
  rewrite -> nott_ttrue_tfalse. rewrite -> ort_tfalse_l.
  rewrite -> ort_tfalse_l. rewrite -> ort_tfalse_l.
  rewrite -> dseq_tfalse_r. rewrite -> dseq_tfalse_r.
  rewrite <- double_nott. rewrite -> ort_tfalse_l.
  rewrite -> ort_tfalse_l. rewrite -> ort_tfalse_r.
  rewrite -> seqtr_ii. rewrite dseq_unit_I. rewrite dseq_unit_I.
  f_equal. f_equal. 
  - assert (H : dseq (Cond_4_2 c true) 
                (nott (ifelse skip_cond1 (qt (II; (hold 0; init)))
                        (qt (ifelsetr skip_cond2 II
                          (flash; (hold 0; init)))))) = tfalse).
    { do 2 (apply functional_extensionality;intros). 
      apply EquivThenEqual. split.
      + intros. unfold dseq in H. crush.
        destruct x as (((n1, t1), tr1), f1).
        destruct x1 as (((n2, t2), tr2), f2).
        destruct x0 as (((n3, t3), tr3), f3).
        unfold Cond_4_2 in H0. unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in H0;simpl in H0.
        unfold nott, skip_cond1, ifelse, ttrOfEnv in H1;simpl in H1.
        remember (beq_ttr_dec tr2 tnil) as Hq. destruct Hq.
        { apply beq_tnil in HeqHq.
          unfold seqtr, qt, wt, tt in H1;simpl in H1. rewrite -> nott_ttrue_tfalse in H1.
          rewrite <- double_nott in H1. rewrite -> dseq_tfalse_r in H1.
          rewrite -> ort_tfalse_l in H1. rewrite -> ort_tfalse_l in H1. 
          rewrite -> dseq_tfalse_r in H1. unfold nott in H1. apply NNPP in H1. apply H1. }
        { crush. }
      + intros. crush. }
    rewrite -> H. reflexivity.
  - do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split.
    + intros. unfold dseq in *. destruct H as [x1 Hx]. exists x1.
      split. { apply Hx. }
      { destruct x as (((n1, t1), tr1), f1).
        destruct x1 as (((n2, t2), tr2), f2).
        destruct x0 as (((n3, t3), tr3), f3).
        destruct Hx as [HA HB]. 
        unfold Cond_4_2, Inv, ttrOfEnv, trOfEnv, timeOfEnv in HA;simpl in HA.
        unfold skip_cond1, ifelse, ttrOfEnv in HB;simpl in HB.
        remember (beq_ttr_dec tr2 tnil) as Hq. destruct Hq.
        { apply beq_tnil in HeqHq.
          unfold seqtr, qt, wt, tt in HB;simpl in HB. rewrite -> dseq_tfalse_r in HB.
          rewrite -> ort_tfalse_r in HB. rewrite -> ort_tfalse_l in HB.
          unfold I, holdw, dseq in *. crush. }
        { crush. } }
    + intros. unfold dseq in *. destruct H as [x1 Hx]. exists x1.
      split. { apply Hx. }
      { destruct x as (((n1, t1), tr1), f1).
        destruct x1 as (((n2, t2), tr2), f2).
        destruct x0 as (((n3, t3), tr3), f3).
        destruct Hx as [HA HB]. 
        unfold Cond_4_2, Inv, ttrOfEnv, trOfEnv, timeOfEnv in HA;simpl in HA.
        unfold skip_cond1, ifelse, ttrOfEnv. simpl.
        remember (beq_ttr_dec tr2 tnil) as Hq. destruct Hq.
        { apply beq_tnil in HeqHq. unfold seqtr, qt, wt, tt. simpl.
          rewrite -> dseq_tfalse_r. rewrite -> ort_tfalse_r. rewrite -> ort_tfalse_l.
          rewrite -> dseq_unit_I. apply HB. }
        { crush. } }
  - do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split.
    + intros. unfold dseq in *. crush. 
      destruct x as (((n1, t1), tr1), f1).
      destruct x1 as (((n2, t2), tr2), f2).
      destruct x0 as (((n4, t4), tr4), f4).
      unfold Cond_4_2, Inv, ttrOfEnv, trOfEnv, timeOfEnv in H0;simpl in H0.
      unfold skip_cond1, ifelse, ttrOfEnv in H1;simpl in H1.
      remember (beq_ttr_dec tr2 tnil) as Hq. destruct Hq.
      { apply beq_tnil in HeqHq. destruct H1 as [x Hx].
        destruct x as (((n3, t3), tr3), f3). exists (n3, t3, tr3, f3). split. 
        { exists (n2, t2, tr2, f2). split. 
          { unfold Cond_4_2, Inv, ttrOfEnv, trOfEnv, timeOfEnv. crush. }
          { apply Hx. } }
        { apply Hx. } }
      { crush. }
    + intros. unfold dseq in *. crush. exists x2. split. { apply H0. }
      { destruct x as (((n1, t1), tr1), f1).
        destruct x2 as (((n2, t2), tr2), f2).
        destruct x1 as (((n3, t3), tr3), f3).
        destruct x0 as (((n4, t4), tr4), f4).
        unfold Cond_4_2, Inv, ttrOfEnv, trOfEnv, timeOfEnv in H0;simpl in H0.
        unfold skip_cond1, ifelse, ttrOfEnv. simpl.
        remember (beq_ttr_dec tr2 tnil) as Hq. destruct Hq.
        { apply beq_tnil in HeqHq. exists (n3, t3, tr3, f3). crush. }
        { crush. } }
Qed.

Lemma null_hold_init_Skip_qt :
  andt C_null (nott (qt (hold 0; init))) = andt C_null (nott (qt Skip)).
Proof.
  do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split;intros;destruct x as (((n1, t1), tr1), f1);
  destruct x0 as (((n2, t2), tr2), f2).
  - unfold nott, andt, qt, C_null, Skip, ttrOfEnv;simpl.
    rewrite seqtr_ii. rewrite ii_seqtr. 
    unfold skip_cond1, ifelse, ttrOfEnv;simpl.
    remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
    + apply beq_tnil in HeqHq. unfold nott, andt in H. crush.
    + unfold nott, andt, C_null, ttrOfEnv in H. crush.
    + rewrite qt_hold_init_ttrue. reflexivity.
  - unfold nott, andt, qt, C_null, Skip, ttrOfEnv in H;simpl in H.
    rewrite seqtr_ii in H. rewrite ii_seqtr in H.
    unfold skip_cond1, ifelse, ttrOfEnv in H;simpl in H.
    remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
    + apply beq_tnil in HeqHq. unfold nott, andt. crush.
    + unfold nott, andt, C_null, ttrOfEnv. crush.
    + rewrite qt_hold_init_ttrue. reflexivity.
Qed.

Lemma null_hold_init_Skip_wt :
  andt C_null (wt (hold 0; init)) = andt C_null (wt Skip).
Proof.
  do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split;intros;destruct x as (((n1, t1), tr1), f1);
  destruct x0 as (((n2, t2), tr2), f2).
  { split. { apply H. }
    { destruct H as [HA HB].
      unfold wt, Skip;simpl. rewrite seqtr_ii. rewrite ii_seqtr.
      unfold skip_cond1, ifelse, C_null, ttrOfEnv in *;simpl in *.
      rewrite HA. crush.
      rewrite qt_hold_init_ttrue. reflexivity. } }
  { split. { apply H. }
    { destruct H as [HA HB].
      unfold wt, Skip in HB;simpl in HB.
      rewrite seqtr_ii in HB. rewrite ii_seqtr in HB.
      unfold skip_cond1, ifelse, C_null, ttrOfEnv in *;simpl in *.
      rewrite HA in HB. crush. 
      rewrite qt_hold_init_ttrue. reflexivity. } }
Qed.

Lemma null_hold_init_Skip_tt :
  andt C_null (tt (hold 0; init)) = andt C_null (tt Skip).
Proof.
  do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split;intros;
  destruct x as (((n1, t1), tr1), f1);
  destruct x0 as (((n2, t2), tr2), f2).
  - split. { apply H. }
    { destruct H as [HA HB].
      unfold tt, Skip. simpl. do 2 rewrite dseq_unit_I.
      unfold skip_cond1, ifelse, C_null, ttrOfEnv in *;simpl in *.
      rewrite HA. crush. }
  - split. { apply H. }
    { destruct H as [HA HB].
      unfold tt, Skip in HB;simpl in HB. do 2 rewrite dseq_unit_I in HB.
      unfold skip_cond1, ifelse, C_null, ttrOfEnv in *;simpl in *.
      rewrite HA in HB. crush. }
Qed.

Lemma derivationLemma_Skip_4_2 :
  forall (c : guard),
  (PhaseCond_4_2 c true); Skip = C_null /H\ Skip.
Proof.
  intros. rewrite -> preDeriLemma_Skip_4_2. 
  rewrite -> helpfulLemma_4_12. rewrite -> H_C_null_seq.
  unfold bCondTripored. f_equal. f_equal.
  - rewrite null_hold_init_Skip_qt. reflexivity.
  - rewrite null_hold_init_Skip_wt. reflexivity.
  - rewrite null_hold_init_Skip_tt. reflexivity.
Qed.

(** ----------------------------------------------------------------- **)

Lemma preDeriLemma_assign_1_1 :
  C_null /H\ init ==> C_null /H\ Skip.
Proof.
  unfold bCondTripored, implytr. unfold qt, wt, tt. simpl.
  intros. rewrite nott_ttrue_tfalse. rewrite andt_tfalse_r.
  rewrite <- double_nott. crush. split. apply H.
  do 2 rewrite dseq_unit_I. destruct H as [HA HB].
  destruct s1 as (((n1, t1), tr1), f1).
  destruct s2 as (((n2, t2), tr2), f2).
  unfold skip_cond1, ifelse, ttrOfEnv;simpl.
  unfold C_null, ttrOfEnv in HA;simpl in HA.
  rewrite HA. crush. unfold dseq. exists (n1, t1, tnil, f1).
  split. unfold holdt, ini in *.
  unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
  apply idle_self. apply HB.
Qed.

Lemma derivationLemma_assign_1_1 :
  forall (x : id) (v : nat),
  (PhaseCond_1_1 x v); II ==> C_null /H\ (Skip; (tassign x v)).
Proof.
  intros. rewrite seqtr_ii. rewrite -> helpfulLemma_4_6.
  rewrite <- H_C_null_seq. rewrite <- H_C_null_seq. 
  apply implytr_comp_1. apply preDeriLemma_assign_1_1.
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_assign_1_2 :
  forall (x : id) (v : nat),
  (PhaseCond_1_2 x v); II = C_notnull_1 /H\ (sassign x v).
Proof.
  intros. rewrite seqtr_ii. rewrite -> helpfulLemma_4_7.
  unfold sassign. unfold bCondTripored. f_equal.
  - f_equal; do 2 (apply functional_extensionality;intros);
    apply EquivThenEqual.
    + split;intros.
      { unfold qt, tassign in H;simpl in H.
        rewrite nott_ttrue_tfalse in H. rewrite andt_tfalse_r in H. 
        destruct x0 as (((n1, t1), tr1), f1).
        destruct x1 as (((n2, t2), tr2), f2).
        unfold andt, nott, C_notnull_1, ttrOfEnv, flagOfEnv in *. crush.
        unfold seqtr, Skip, tassign, qt in H2;simpl in H2.
        rewrite nott_ttrue_tfalse in H2. rewrite dseq_tfalse_r in H2.
        rewrite ort_tfalse_r in H2. rewrite <- double_nott in H2.
        rewrite seqtr_ii in H2. rewrite ii_seqtr in H2.
        unfold skip_cond1, ifelse, ttrOfEnv in H2;simpl in H2.
        remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq. 
        { apply beq_tnil in HeqHq. apply H0 in HeqHq. crush. }
        { unfold qt, skip_cond2, ifelsetr, flagOfEnv, ifelse in H2;simpl in H2.
          unfold II, qt in H2;simpl in H2. unfold ttrue, tfalse in *. crush. }
        rewrite qt_hold_init_ttrue. reflexivity. }
      { unfold qt, tassign. simpl. rewrite nott_ttrue_tfalse. 
        rewrite andt_tfalse_r. unfold nott in *. crush. }
    + split;intros.
      { unfold wt, tassign in H;simpl in H. rewrite andt_tfalse_r in H. crush. }
      { destruct x0 as (((n1, t1), tr1), f1).
        destruct x1 as (((n2, t2), tr2), f2).
        destruct H as [HA HB]. split. { apply HA. }
        { unfold seqtr, Skip, tassign, wt in *;simpl in *.
          rewrite dseq_tfalse_r in HB. rewrite ort_tfalse_r in HB.
          rewrite seqtr_ii in HB. rewrite ii_seqtr in HB.
          unfold C_notnull_1, skip_cond1, ifelse, ttrOfEnv, flagOfEnv in *. crush.
          remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
          { apply beq_tnil in HeqHq. apply H in HeqHq. crush. }
          { unfold wt, skip_cond2, ifelsetr, flagOfEnv, ifelse in HB;simpl in HB.
            unfold II, wt in HB;simpl in HB. apply HB. }
          rewrite qt_hold_init_ttrue. reflexivity. } }
  - do 2 (apply functional_extensionality;intros). 
    apply EquivThenEqual. split;intros;
    destruct x0 as (((n1, t1), tr1), f1);
    destruct x1 as (((n2, t2), tr2), f2);
    destruct H as [HA HB]. 
    + split. { apply HA. }
      { unfold seqtr, Skip, tassign, tt in *;simpl in *.
        do 2 rewrite dseq_unit_I. unfold dseq. exists (n1, t1, tr1, f1).
        unfold skip_cond1, ifelse, C_notnull_1, ttrOfEnv, flagOfEnv in *;simpl in *.
        remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
        { apply beq_tnil in HeqHq. crush. }
        { destruct HA as [HC HD]. rewrite HD. 
          split. { unfold I. crush. } { apply HB. } } }
    + split. { apply HA. }
      { unfold seqtr, Skip, tassign, tt in *;simpl in *.
        do 2 rewrite dseq_unit_I in HB. unfold dseq in HB. crush.
        destruct x0 as (((n3, t3), tr3), f3).
        unfold skip_cond1, ifelse, C_notnull_1, ttrOfEnv, flagOfEnv in *;simpl in *.
        remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
        { apply beq_tnil in HeqHq. crush. }
        { destruct HA as [HC HD]. rewrite HD in H0.
          unfold I, dassign in *. crush. } }
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_assign_4_1 :
  forall (c : guard) (x : id) (v : nat),
  (PhaseCond_4_1 c true); (sassign x v) ==> C_notnull_0 /H\ (sassign x v).
Proof.
  intros. unfold sassign. rewrite <- seqtr_comm. 
  rewrite derivationLemma_Skip_4_1. rewrite H_C_notnull_0_seq.
  unfold implytr. intros. split. crush. split. crush. crush.
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_assign_4_2 :
  forall (c : guard) (x : id) (v : nat),
  (PhaseCond_4_2 c true); (sassign x v) ==> C_null /H\ (sassign x v).
Proof.
  intros. unfold sassign. rewrite <- seqtr_comm.
  rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq.
  unfold implytr. intros. split. crush. split. crush. crush.
Qed.

(** ----------------------------------------------------------------- **)

Theorem seqtr_uniontr_distr :
  forall P Q R, seqtr P (uniontr Q R) = uniontr (seqtr P Q) (seqtr P R).
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
    + split; unfold andt; crush; 
      unfold nott, andt, dseq in *; crush;
      apply HA; exists x1; crush.
    + split. destruct HA as [HAA HAB]. destruct HB as [HBA HBB].
      unfold nott, andt, dseq in *. crush. apply HAB. exists x1. 
      crush. apply HBB. exists x1. crush. apply HA.
  - rewrite <- ort_distributive.
    do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split;intros.
    + destruct H. left. apply H. right. 
      unfold dseq, ort in *. crush.
      left. exists x1. crush. right. exists x1. crush.
    + destruct H. left. apply H. right.
      unfold dseq, ort in *. crush.
      exists x1. crush. exists x1. crush.
  - do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split;intros.
    + unfold dseq, ort in *. crush.
      left. exists x1. crush. right. exists x1. crush.
    + unfold dseq, ort in *. crush.
      exists x1. crush. exists x1. crush.
Qed.
(**
Theorem bCond_uniontr_distr :
  forall C P Q, 
  C /H\ (uniontr P Q) = uniontr (C /H\ P) (C /H\ Q).
Proof.
  intros.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  unfold bCondTripored, uniontr. unfold qt, wt, tt. simpl.
  rewrite <- notort_distributive. do 3 rewrite <- aot_distributive_r.
  rewrite <- notandt_distributive. reflexivity.
Qed. **)

Lemma derivationLemma_trig_2_1 :
  forall (c : guard),
  (PhaseCond_2_1); (guardawake c) = C_notnull_1 /H\ (guardawake c).
Proof.
  intros. unfold guardawake. rewrite seqtr_uniontr_distr.
  rewrite helpfulLemma_4_15_1. rewrite <- seqtr_comm.
  rewrite helpfulLemma_4_15_2. rewrite H_C_notnull_1_seq.
  rewrite <- H_bPQ_distributive. reflexivity.
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_trig_4_1 :
  forall (c : guard),
  (PhaseCond_4_1 c true); II ==> C_notnull_0 /H\ (guardawake c).
Proof.
  intros. rewrite seqtr_ii. rewrite helpfulLemma_4_11. 
  unfold implytr. intros. split. 
  - intros. unfold bCondTripored, qt in *. crush.
    do 2 rewrite <- double_nott in *. unfold selftrigsub, andtr, qt in H; simpl in H.
    rewrite ort_ttrue_l in H. rewrite nott_ttrue_tfalse in H. 
    rewrite ort_tfalse_l in H. rewrite dseq_tfalse_r in H.
    unfold andt in H. crush.
  - split; intros.
    + unfold bCondTripored, wt in *. crush.
       unfold selftriger, wt at 1. crush. split. 
      { apply H. }
      { left. apply H. }
    + unfold bCondTripored, tt in *. crush. split. 
      { apply H. } 
      { left. apply H. }
Qed.

(** ----------------------------------------------------------------- **)

Theorem lststate_self :
  forall s, lststate s s = [].
Proof.
  intros. destruct s as (((n1, t1), tr1), f1).
  unfold lststate. unfold subtr, trOfEnv. simpl.
  induction t1. crush. apply IHt1.
Qed.

Theorem stateProp_self :
  forall s c, stateProp s s c.
Proof.
  intros. unfold stateProp. intros.
  rewrite lststate_self in *. crush.
Qed. 

Lemma derivationLemma_trig_4_2 :
  forall (c : guard),
  (PhaseCond_4_2 c true); II ==> C_null /H\ (guardawake c).
Proof.
  intros. rewrite seqtr_ii. rewrite helpfulLemma_4_14. 
  unfold implytr. intros. split.
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

Lemma preDeriLemma_trig_4_3 :
  forall (c : guard),
  (PhaseCond_4_1 c false); (guardawake c) = (PhaseCond_4_1 c false); ((await c); (trig c)).
Proof.
  intros. unfold seqtr. unfold PhaseCond_4_1, qt, wt, tt. simpl.
  rewrite nott_ttrue_tfalse. do 4 rewrite ort_tfalse_l.
  do 2 rewrite <- double_nott. rewrite dseq_tfalse_r.
  do 2 rewrite ort_tfalse_r. f_equal.
  - f_equal.
    + unfold selftriger, qt at 1. simpl. 
      unfold qt at 2, andtr, II, flash at 1. simpl.
      unfold qt at 3, qt at 2. simpl. rewrite ort_ttrue_l. 
      rewrite nott_ttrue_tfalse. rewrite dseq_tfalse_r.
      rewrite ort_tfalse_r. rewrite <- double_nott.
      unfold selftrigsub, qt at 1. simpl.
      rewrite andt_ttrue_l. unfold qt at 1, seqtr at 1. simpl.
      rewrite <- double_nott. unfold qt at 2, qt at 1, await, trig. simpl.
      rewrite <- double_nott. rewrite nott_ttrue_tfalse. 
      rewrite dseq_tfalse_r. rewrite ort_tfalse_r. reflexivity.
    + unfold seqtr, selftriger, await, trig, awaitsub1, flash, awaitsub2, wt.
      simpl. do 2 rewrite dseq_tfalse_r. 
      unfold selftrigsub, seqtr, andtr, II, wt, qt. simpl.
      rewrite nott_ttrue_tfalse. do 3 rewrite ort_tfalse_r. 
      rewrite andt_tfalse_l. do 2 rewrite dseq_tfalse_r. 
      do 2 rewrite ort_tfalse_r.
      do 2 (apply functional_extensionality;intros).
      apply EquivThenEqual. split;intros;
      unfold dseq at 1 in H;unfold dseq at 1;crush.
      { exists x1. split. apply H0. destruct H1. 
        { destruct x as (((n1, t1), tr1), f1).
          destruct x1 as (((n2, t2), tr2), f2).
          destruct x0 as (((n3, t3), tr3), f3).
          unfold Cond_4_1, tselftriger in *. crush. }
        { apply H. } }
      { exists x1. split. apply H0. right. apply H1. }
  - unfold qt, II, flash. simpl. 
    rewrite nott_ttrue_tfalse. do 2 rewrite ort_tfalse_l.
    do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split;intros;
    unfold dseq at 1 in H;unfold dseq at 1;crush.
    { exists x1. split. apply H0. destruct H1. 
      { destruct x as (((n1, t1), tr1), f1).
        destruct x1 as (((n2, t2), tr2), f2).
        destruct x0 as (((n3, t3), tr3), f3).
        unfold Cond_4_1, tselftriger, I, tflash, andt, dseq in H.
        crush. }
      { apply H. } }
    { exists x1. split. apply H0. right. apply H1. }
Qed.

Lemma derivationLemma_trig_4_3 :
  forall (c : guard),
  (PhaseCond_4_1 c false); (guardawake c) ==> C_notnull_0 /H\ (guardawake c).
Proof.
  intros. rewrite preDeriLemma_trig_4_3.
  rewrite <- seqtr_comm. rewrite helpfulLemma_4_10.
  rewrite H_C_notnull_0_seq. unfold implytr. intros. split.
  - intros. unfold qt, bCondTripored in *;simpl in *.
    rewrite <- double_nott in *. split. apply H.
    unfold guardawake. unfold selftriger, andtr, II, flash.
    unfold qt, wt, tt. simpl. 
    rewrite nott_ttrue_tfalse. do 3 rewrite ort_tfalse_l. 
    rewrite ort_ttrue_l. rewrite andt_tfalse_l. 
    unfold seqtr at 1, selftrigsub, qt at 1. simpl.
    unfold qt at 2, qt at 1. simpl. 
    rewrite nott_ttrue_tfalse. rewrite dseq_tfalse_r.
    rewrite ort_tfalse_l. unfold nott, andt, tfalse in *. crush.
  - split;intros.
    + unfold wt, bCondTripored in *;simpl in *. split. apply H. 
      unfold guardawake, wt, uniontr. simpl. right. apply H.
    + unfold tt, bCondTripored in *;simpl in *. split. apply H.
      right. apply H.
Qed.

(** ----------------------------------------------------------------- **)

Lemma preDeriLemma_trig_4_4 :
  forall (c : guard),
  (PhaseCond_4_2 c false); (guardawake c) = (PhaseCond_4_2 c false); ((await c); (trig c)).
Proof.
  intros. unfold seqtr. unfold PhaseCond_4_2, qt, wt, tt. simpl.
  rewrite nott_ttrue_tfalse. do 4 rewrite ort_tfalse_l.
  do 2 rewrite <- double_nott. rewrite dseq_tfalse_r.
  do 2 rewrite ort_tfalse_r. f_equal.
  - f_equal. 
    + unfold selftriger, qt at 1. simpl. 
      unfold qt at 2, andtr, II, flash at 1. simpl.
      unfold qt at 3, qt at 2. simpl. rewrite ort_ttrue_l. 
      rewrite nott_ttrue_tfalse. rewrite dseq_tfalse_r.
      rewrite ort_tfalse_r. rewrite <- double_nott.
      unfold selftrigsub, qt at 1. simpl.
      rewrite andt_ttrue_l. unfold qt at 1, seqtr at 1. simpl.
      rewrite <- double_nott. unfold qt at 2, qt at 1, await, trig. simpl.
      rewrite <- double_nott. rewrite nott_ttrue_tfalse. 
      rewrite dseq_tfalse_r. rewrite ort_tfalse_r. reflexivity.
    + unfold seqtr, selftriger, await, trig, awaitsub1, flash, awaitsub2, wt.
      simpl. do 2 rewrite dseq_tfalse_r. 
      unfold selftrigsub, seqtr, andtr, II, wt, qt. simpl.
      rewrite nott_ttrue_tfalse. do 3 rewrite ort_tfalse_r. 
      rewrite andt_tfalse_l. do 2 rewrite dseq_tfalse_r. 
      do 2 rewrite ort_tfalse_r.
      do 2 (apply functional_extensionality;intros).
      apply EquivThenEqual. split;intros;
      unfold dseq at 1 in H;unfold dseq at 1;crush.
      { exists x1. split. apply H0. destruct H1. 
        { destruct x as (((n1, t1), tr1), f1).
          destruct x1 as (((n2, t2), tr2), f2).
          destruct x0 as (((n3, t3), tr3), f3).
          unfold Cond_4_2, tselftriger in *. crush. }
        { apply H. } }
      { exists x1. split. apply H0. right. apply H1. }
  - unfold qt, II, flash. simpl. 
    rewrite nott_ttrue_tfalse. do 2 rewrite ort_tfalse_l.
    do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split;intros;
    unfold dseq at 1 in H;unfold dseq at 1;crush.
    { exists x1. split. apply H0. destruct H1. 
      { destruct x as (((n1, t1), tr1), f1).
        destruct x1 as (((n2, t2), tr2), f2).
        destruct x0 as (((n3, t3), tr3), f3).
        unfold Cond_4_2, tselftriger, I, tflash, andt, dseq in H.
        crush. }
      { apply H. } }
    { exists x1. split. apply H0. right. apply H1. }
Qed.

Lemma derivationLemma_trig_4_4 :
  forall (c : guard),
  (PhaseCond_4_2 c false); (guardawake c) ==> C_null /H\ (guardawake c).
Proof.
  intros. rewrite preDeriLemma_trig_4_4.
  rewrite <- seqtr_comm. rewrite helpfulLemma_4_13.
  rewrite H_C_null_seq. unfold implytr. intros. split.
  - intros. unfold qt, bCondTripored in *;simpl in *.
    rewrite <- double_nott in *. split. apply H.
    unfold guardawake. unfold selftriger, andtr, II, flash.
    unfold qt, wt, tt. simpl. 
    rewrite nott_ttrue_tfalse. do 3 rewrite ort_tfalse_l. 
    rewrite ort_ttrue_l. rewrite andt_tfalse_l. 
    unfold seqtr at 1, selftrigsub, qt at 1. simpl.
    unfold qt at 2, qt at 1. simpl. 
    rewrite nott_ttrue_tfalse. rewrite dseq_tfalse_r.
    rewrite ort_tfalse_l. unfold nott, andt, tfalse in *. crush.
  - split;intros.
    + unfold wt, bCondTripored in *;simpl in *. split. 
       { apply H. }
       { unfold guardawake, wt, uniontr. simpl. right. apply H. }
    + unfold tt, bCondTripored in *;simpl in *. split. 
       { apply H. }
       { right. apply H. }
Qed.

(** ----------------------------------------------------------------- **)

Lemma preDeriLemma_trig_5_1_qt :
  forall (c : guard) (s1 s2 : env),
  dseq delayt (nott (qt (guardawake c))) s1 s2 -> andt C_null (nott (qt (guardawake c))) s1 s2.
Proof.
    intros. unfold dseq in H. crush. split.
    - unfold delayt, C_null in *. apply H0.
    - unfold guardawake, qt, nott in *. 
      unfold uniontr in *. simpl in *. 
      apply not_and_or in H1. destruct H1.
      { unfold andt. crush. apply H. 
        unfold selftriger, qt in *;simpl in *. 
        rewrite notort_distributive in *. 
        rewrite <- double_nott in *. destruct H2 as [HA HB].
        split. apply HA. unfold dseq, nott at 1 in HB.
        unfold dseq, nott at 1. crush. apply HB. exists x0. split. 
        { unfold tselftriger in H2. unfold delayt in H0. 
          unfold Inv, ttrOfEnv in *. crush. }
        { apply H4. } }
      { unfold andt. crush. apply H.
        unfold await, trig, seqtr, qt in *;simpl in *.
        rewrite nott_ttrue_tfalse in *. do 3 rewrite dseq_tfalse_r in *.
        do 2 rewrite <- double_nott in *. do 3 rewrite ort_tfalse_r in *. 
        unfold nott, tfalse in *. crush. }
Qed.

Lemma preDeriLemma_trig_5_1_wt :
  forall (c : guard) (s1 s2 : env),
  ort (wt phase5) (dseq delayt (wt (guardawake c))) s1 s2 ->
  andt C_null (wt (guardawake c)) s1 s2.
Proof.
  intros. unfold wt in *; simpl in *. destruct H.
  - split. unfold delayw, C_null in *. crush.
    right. unfold await, trig, seqtr, wt. simpl.
    do 2 rewrite dseq_tfalse_r. do 2 rewrite ort_tfalse_r.
    left. unfold delayw, awaitrans1 in *. crush.
  - unfold dseq in H. crush. split. 
    unfold delayt, C_null in *. crush. destruct H1.
    { left. unfold selftriger, wt in *;simpl in *.
      unfold andtr, II, flash, wt, qt in *;simpl in *.
      rewrite nott_ttrue_tfalse in *. rewrite ort_tfalse_r in *.
      rewrite andt_tfalse_l in *. rewrite dseq_tfalse_r in *.
      rewrite ort_tfalse_r in *.
      unfold tselftriger, delayt in *. crush. }
    { right. unfold await, trig, seqtr, wt in *;simpl in *.
      do 2 rewrite dseq_tfalse_r in *. do 2 rewrite ort_tfalse_r in *.
      left. unfold awaitrans1, delayt in *. crush. }
Qed.

Lemma preDeriLemma_trig_5_1_tt :
  forall (c : guard) (s1 s2 : env),
  dseq (tt phase5) (tt (guardawake c)) s1 s2 -> andt C_null (tt (guardawake c)) s1 s2.
Proof.
  intros. simpl in *. unfold flash, II, qt in *;simpl in *.
  rewrite nott_ttrue_tfalse in *. do 2 rewrite ort_tfalse_l in *.
  unfold dseq at 1 in H. crush. rewrite aot_distributive_r. destruct H1.
  - left. unfold dseq in H. crush. split.
    unfold delayt, C_null, I, tflash, andt in *. crush.
    unfold dseq. exists x0. split. 
    unfold tselftriger, delayt in *. crush. apply H2. 
  - right. unfold dseq in H. crush. split.
    unfold delayt, C_null, trigtrans1 in *. crush.
    unfold dseq. exists x0. split. exists x1. split. exists x2. split.
    unfold awaitrans1, delayt in *. crush.
    apply H4. apply H3. apply H2.
Qed.

Lemma derivationLemma_trig_5_1 :
  forall (c : guard),
  phase5; (guardawake c) ==> C_null /H\ (guardawake c).
Proof.
  intros. unfold seqtr, bCondTripored. 
  unfold implytr. intros. split.
  - unfold qt at 4, qt at 2, qt at 1; simpl. do 2 rewrite <- double_nott.
    rewrite nott_ttrue_tfalse. rewrite ort_tfalse_l.
    apply preDeriLemma_trig_5_1_qt.
  - split.
    + unfold wt at 4, wt at 1; simpl. apply preDeriLemma_trig_5_1_wt.
    + unfold tt at 6, tt at 1. unfold snd. apply preDeriLemma_trig_5_1_tt.
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_delay_2_1 :
  forall (n : nat),
  PhaseCond_2_1; (mdelay n) = C_notnull_1 /H\ (mdelay n).
Proof.
  intros. unfold mdelay. do 2 rewrite <- seqtr_comm.
  rewrite helpfulLemma_4_15_3. 
  do 2 rewrite H_C_notnull_1_seq. reflexivity.
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_delay_4_1 :
  forall (c : guard) (n : nat),
  (PhaseCond_4_1 c true); (mdelay n) = C_notnull_0 /H\ (mdelay n).
Proof.
  intros. rewrite helpfulLemma_4_9. unfold mdelay.
  do 2 rewrite <- seqtr_comm. rewrite H_C_notnull_0_seq.
  rewrite flash_equlity. do 2 rewrite <- H_C_notnull_0_seq.
  reflexivity.
Qed.

(** ----------------------------------------------------------------- **)

Lemma PhaseCond_4_2_flash_holdn :
  forall (c : guard) (n : nat),
  (PhaseCond_4_2 c true); (hold n) = (PhaseCond_4_2 c true); flash; (hold n).
Proof.
  intros. f_equal. unfold seqtr, PhaseCond_4_2, flash.
  unfold qt, wt, tt. simpl. rewrite nott_ttrue_tfalse.
  rewrite dseq_tfalse_r. rewrite ort_tfalse_l. do 2 f_equal;
  do 2 (apply functional_extensionality;intros);
  apply EquivThenEqual; split.
  - unfold nott, tfalse, ttrue. crush.
  - unfold nott, tfalse, ttrue. crush.
  - intros. unfold dseq. exists x0. split. apply H.
    unfold Cond_4_2, tflash in *.
    unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
    unfold subseq. exists []. crush.
  - intros. unfold dseq in H. crush.
    destruct x as (((n1, t1), tr1), f1).
    destruct x1 as (((n2, t2), tr2), f2).
    destruct x0 as (((n3, t3), tr3), f3).
    unfold Cond_4_2, tflash in *.
    unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
Qed.

Lemma C_null_flash_holdn :
  forall (n : nat),
  C_null /H\ (flash; (hold n)) = C_null /H\ (hold n).
Proof.
  intros. unfold bCondTripored, seqtr, flash, hold.
  unfold qt, wt, tt. simpl. rewrite nott_ttrue_tfalse.
  rewrite dseq_tfalse_r. rewrite <- double_nott.
  do 2 rewrite ort_tfalse_l. rewrite andt_tfalse_r. f_equal.
  - f_equal;do 2 (apply functional_extensionality;intros);
    apply EquivThenEqual; split.
    + intros. split. apply H. destruct H as [HA HB].
      unfold dseq in HB. crush.
      destruct x as (((n1, t1), tr1), f1).
      destruct x1 as (((n2, t2), tr2), f2).
      destruct x0 as (((n3, t3), tr3), f3).
      unfold C_null, tflash, holdw in *.
      unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
    + intros. split. apply H. destruct H as [HA HB].
      unfold dseq. exists x. split.
      { destruct x as (((n1, t1), tr1), f1).
        destruct x0 as (((n2, t2), tr2), f2).
        unfold C_null, holdw, tflash in *.
        unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
        unfold subseq. exists []. crush. }
      { apply HB. }
  - do 2 (apply functional_extensionality;intros).
    apply EquivThenEqual. split.
    + intros. split. apply H. destruct H as [HA HB].
      unfold dseq in HB. crush.
      destruct x as (((n1, t1), tr1), f1).
      destruct x1 as (((n2, t2), tr2), f2).
      destruct x0 as (((n3, t3), tr3), f3).
      unfold C_null, tflash, holdt in *.
      unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
    + intros. split. apply H. destruct H as [HA HB].
      unfold dseq. exists x. split.
      { destruct x as (((n1, t1), tr1), f1).
        destruct x0 as (((n2, t2), tr2), f2).
        unfold C_null, holdw, tflash in *.
        unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
        unfold subseq. exists []. crush. }
      { apply HB. }
Qed.

Lemma derivationLemma_delay_4_2 :
  forall (c : guard) (n : nat),
  n >= 1 -> PhaseCond_4_2 c true; (mdelay n) = C_null /H\ (mdelay n).
Proof.
  intros. unfold mdelay. do 2 rewrite <- seqtr_comm.
  rewrite <- PhaseCond_4_2_flash_holdn. rewrite <- H_C_null_seq.
  rewrite C_null_flash_holdn.
  assert (HH : hold (n - 1) = hold (0 + (n - 1))).
  { unfold hold. crush. }
  rewrite HH. rewrite <- hold_equality.
  rewrite <- seqtr_comm. rewrite <- H_C_null_seq.
  rewrite helpfulLemma_4_12. reflexivity.
Qed.

(** ----------------------------------------------------------------- **)

Lemma phase5_flash :
  phase5; flash = phase5.
Proof.
  unfold phase5, flash, seqtr. unfold qt, wt, tt. simpl.
  rewrite nott_ttrue_tfalse. rewrite dseq_tfalse_r.
  do 2 rewrite ort_tfalse_r. do 2 f_equal;
  do 2 (apply functional_extensionality;intros);
  apply EquivThenEqual.
  - split;intros;unfold nott, tfalse, ttrue in *;crush.
  - split;intros;unfold dseq in *;crush.
    + destruct x as (((n1, t1), tr1), f1).
      destruct x1 as (((n2, t2), tr2), f2).
      destruct x0 as (((n3, t3), tr3), f3).
      unfold delayt, tflash in *.
      unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
    + exists x0. split. apply H.
      destruct x as (((n1, t1), tr1), f1).
      destruct x0 as (((n2, t2), tr2), f2).
      unfold delayt, tflash in *.
      unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
Qed.

Lemma preDeriLemma_delay_5_1_qt :
  forall (n : nat),
  n >=2 -> nott (andt C_null (nott (qt (hold (n - 1))))) = nott (andt C_null (nott (qt (flash; hold (n - 1))))).
Proof.
  intros. do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split;intros.
  { unfold nott, andt in *. crush. apply H0. intros. apply H3.
     unfold flash, hold, seqtr, qt in *;simpl in *.
     rewrite nott_ttrue_tfalse in *. rewrite dseq_tfalse_r in *.
     rewrite ort_tfalse_r in *. unfold nott, tfalse in *. crush. }
  { unfold nott, andt in *. crush. unfold hold, qt, ttrue in *. crush. }
Qed.

Lemma preDeriLemma_delay_5_1_wt :
  forall (n : nat),
  n >=2 -> andt C_null (wt (hold (n - 1))) = andt C_null (wt (flash; hold (n - 1))).
Proof.
  intros. do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split;intros.
  { split. apply H0. unfold flash, hold, seqtr, wt in *. crush.
    rewrite ort_tfalse_l. unfold dseq. exists x. split.
    destruct x as (((n1, t1), tr1), f1).
    destruct x0 as (((n2, t2), tr2), f2).
    destruct H0 as [HA HB].
    unfold C_null, tflash, Inv, ttrOfEnv, trOfEnv in *. crush.
    unfold subseq. exists []. crush. apply H0. }
    { split. apply H0. destruct H0 as [HA HB].
       unfold flash, hold, seqtr, wt in *;simpl in *. 
       rewrite ort_tfalse_l in HB. unfold dseq in HB. crush.
       destruct x as (((n1, t1), tr1), f1).
       destruct x1 as (((n2, t2), tr2), f2).
       destruct x0 as (((n3, t3), tr3), f3).
       unfold C_null, tflash, holdw in *.
       unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush. }
Qed.

Lemma preDeriLemma_delay_5_1_tt :
  forall (n : nat),
  n >=2 -> andt C_null (tt (hold (n - 1))) = andt C_null (tt (flash; hold (n - 1))).
Proof.
  intros. do 2 (apply functional_extensionality;intros).
  apply EquivThenEqual. split;intros.
  - split. apply H0. unfold flash, hold, seqtr, tt in *.
    unfold qt, wt, tt in *;simpl in *. 
    unfold dseq. exists x. split. 
    { destruct H0 as [HA HB]. 
      unfold C_null, tflash, Inv in *. crush.
      unfold subseq. exists []. crush. }
    { apply H0. }
  - split. apply H0. unfold flash, hold, seqtr, tt in *.
    unfold qt, wt, tt in *;simpl in *.
    destruct H0 as [HA HB]. unfold dseq in HB. crush.
    destruct x as (((n1, t1), tr1), f1).
    destruct x1 as (((n2, t2), tr2), f2).
    destruct x0 as (((n3, t3), tr3), f3).
    unfold C_null, tflash, holdt in *.
    unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
Qed.

Check implytr_comp_1.
Lemma derivationLemma_delay_5_1 :
  forall (n : nat),
  n >=2 -> phase5; flash; (hold (n - 2)); phase5 ==> C_null /H\ (mdelay n).
Proof.
  intros. rewrite phase5_flash. 
  assert (HH : phase5; (hold (n - 2)) ==> (C_null /H\ (hold 1)); (hold (n - 2))).
  { apply implytr_comp_1. apply helpfulLemma_4_16. }
  unfold mdelay. rewrite <- H_C_null_seq. apply implytr_comp_1.
  rewrite H_C_null_seq in HH. 
  assert (HHH : (hold 1); (hold (n - 2)) = (hold (n - 1))).
  { rewrite hold_equality. crush. }
  rewrite HHH in HH.
  assert (HHHH : C_null /H\ hold (n - 1) = C_null /H\ (flash; hold (n - 1))).
  { unfold bCondTripored. f_equal. f_equal.
    - apply preDeriLemma_delay_5_1_qt. apply H.
    - apply preDeriLemma_delay_5_1_wt. apply H.
    - apply preDeriLemma_delay_5_1_tt. apply H. }
  rewrite <- HHHH. apply HH.
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_delay_5_2 :
  phase5;II ==> C_null /H\ (mdelay 1).
Proof.
  rewrite seqtr_ii. unfold mdelay, implytr. intros. split.
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

(** ----------------------------------------------------------------- **)

(**a part of proof of helpful_4_12, but need to add (SortedList (getTime s1 s2)) in Cond_4_2.
Theorem getFlag_trans :
  forall (s1 x s2 : env) (f : bool),
  subseq (trOfEnv s1) (trOfEnv s2) ->
  subseq (trOfEnv s1) (trOfEnv x) ->
  subseq (trOfEnv x) (trOfEnv s2) ->
  In f (getFlag s1 s2) -> In f ((getFlag s1 x) ++ (getFlag x s2)).
Proof.
  intros.
  destruct s1 as (((n1, t1), tr1), f1).
  destruct x as (((n2, t2), tr2), f2).
  destruct s2 as (((n3, t3), tr3), f3).
  unfold getFlag, trOfEnv in *. crush.
  assert (HH : (sublist t2 (Datatypes.length t1)) ++ 
          (sublist t3 (Datatypes.length t2)) =
    (sublist t3 (Datatypes.length t1))).
  { apply subseq_sublist_trans. apply H1. apply H0. apply H. }
  rewrite <- map_app. rewrite HH. apply H2.
Qed.

Theorem In_f_trans :
  forall (f : bool) (A B : list bool),
  (In f A -> f = false) ->
  (In f B -> f = false) ->
  (In f (A ++ B) -> f = false).
Proof.
  intros. apply in_app_or in H1. destruct H1.
  - apply H. apply H1.
  - apply H0. apply H1.
Qed.

Theorem getTime_trans :
  forall (s1 x s2 : env) (t : nat),
  subseq (trOfEnv s1) (trOfEnv s2) ->
  subseq (trOfEnv s1) (trOfEnv x) ->
  subseq (trOfEnv x) (trOfEnv s2) ->
  In t (getTime s1 s2) -> In t ((getTime s1 x) ++ (getTime x s2)).
Proof.
  intros.
  destruct s1 as (((n1, t1), tr1), f1).
  destruct x as (((n2, t2), tr2), f2).
  destruct s2 as (((n3, t3), tr3), f3).
  unfold getTime, trOfEnv in *. crush.
  assert (HH : (sublist t2 (Datatypes.length t1)) ++ 
          (sublist t3 (Datatypes.length t2)) =
    (sublist t3 (Datatypes.length t1))).
  { apply subseq_sublist_trans. apply H1. apply H0. apply H. }
  rewrite <- map_app. rewrite HH. apply H2.
Qed.

Lemma helpful_4_12 :
  forall (c : guard),
  PhaseCond_4_2 c true; hold 0 ==> C_null /H\ hold 0.
Proof.
  intros. unfold seqtr, bCondTripored, implytr.
  intros. unfold qt, wt, tt. simpl. rewrite nott_ttrue_tfalse.
  rewrite dseq_tfalse_r. rewrite andt_tfalse_r.
  do 2 rewrite ort_tfalse_l. crush.
  - unfold dseq in H. crush.
    destruct s1 as (((n1, t1), tr1), f1).
    destruct x as (((n2, t2), tr2), f2).
    destruct s2 as (((n3, t3), tr3), f3).
    split.
    { unfold Cond_4_2, C_null in *.
      unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush. }
    { unfold Cond_4_2, holdw in *.
      unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush. }
  - unfold dseq in H. crush.
    destruct s1 as (((n1, t1), tr1), f1).
    destruct x as (((n2, t2), tr2), f2).
    destruct s2 as (((n3, t3), tr3), f3).
    split.
    { unfold Cond_4_2, C_null in *.
      unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush. }
    { unfold Cond_4_2, holdt in *.
      unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
      { unfold subseq in *. destruct H1 as [l1 H1].
        destruct H2 as [l2 H2]. exists (l1 ++ l2). crush. }
      { unfold idle in *. 
        unfold Inv, ttrOfEnv, trOfEnv, timeOfEnv in *. crush.
        { unfold subseq in *. destruct H1 as [l1 H1].
          destruct H2 as [l2 H2]. exists (l1 ++ l2). crush. }
        { assert (HH : In f (getFlag (n2, t1, tnil, f1) ((n2 + 0)%nat, t3, tnil, f3)) ->
                  In f (getFlag (n2, t1, tnil, f1) (n2, t2, tnil, f2) ++
                        getFlag (n2, t2, tnil, f2) ((n2 + 0)%nat, t3, tnil, f3))).
          { apply getFlag_trans. unfold trOfEnv. crush. 
            unfold subseq in *. destruct H1 as [l1 H1].
            destruct H2 as [l2 H2]. exists (l1 ++ l2). crush.
            unfold trOfEnv. apply H1. unfold trOfEnv. apply H2. }
          apply HH in H9. generalize dependent H9.
          apply In_f_trans. apply H11. apply H. }
        { unfold subseq in *. destruct H1 as [l1 H1].
          destruct H2 as [l2 H2]. exists (l1 ++ l2). crush. }
        { assert (HH : In t (getTime (n2, t1, tnil, f1) ((n2 + 0)%nat, t3, tnil, f3)) ->
                  In t (getTime (n2, t1, tnil, f1) (n2, t2, tnil, f2) ++
                        getTime (n2, t2, tnil, f2) ((n2 + 0)%nat, t3, tnil, f3))).
          { apply getTime_trans. unfold trOfEnv. crush. 
            unfold subseq in *. destruct H1 as [l1 H1].
            destruct H2 as [l2 H2]. exists (l1 ++ l2). crush.
            unfold trOfEnv. apply H1. unfold trOfEnv. apply H2. }
          apply HH in H9. apply in_app_or in H9. destruct H9.
          { apply H10 in H9. crush. }
          { apply H7 in H9. crush. } }
        { assert (HH : In t (getTime (n2, t1, tnil, f1) ((n2 + 0)%nat, t3, tnil, f3)) ->
                  In t (getTime (n2, t1, tnil, f1) (n2, t2, tnil, f2) ++
                        getTime (n2, t2, tnil, f2) ((n2 + 0)%nat, t3, tnil, f3))).
          { apply getTime_trans. unfold trOfEnv. crush. 
            unfold subseq in *. destruct H1 as [l1 H1].
            destruct H2 as [l2 H2]. exists (l1 ++ l2). crush.
            unfold trOfEnv. apply H1. unfold trOfEnv. apply H2. }
          apply HH in H9. apply in_app_or in H9. destruct H9.
          { apply H10 in H9. crush. }
          { apply H7 in H9. crush. } }
        { } } }
**)

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_sequential_1_C_null :
  forall sem P P' Q : tripored,
  sem; P' ==> C_null /H\ P -> sem; (P'; Q) ==> C_null /H\ (P; Q).
Proof.
  intros. rewrite <- seqtr_comm. rewrite <- H_C_null_seq.
  apply implytr_comp_1. apply H.
Qed.

Lemma derivationLemma_sequential_1_C_notnull_0 :
  forall sem P P' Q : tripored,
  sem; P' ==> C_notnull_0 /H\ P -> sem; (P'; Q) ==> C_notnull_0 /H\ (P; Q).
Proof.
  intros. rewrite <- seqtr_comm. rewrite <- H_C_notnull_0_seq.
  apply implytr_comp_1. apply H.
Qed.

Lemma derivationLemma_sequential_1_C_notnull_1 :
  forall sem P P' Q : tripored,
  sem; P' ==> C_notnull_1 /H\ P -> sem; (P'; Q) ==> C_notnull_1 /H\ (P; Q).
Proof.
  intros. rewrite <- seqtr_comm. rewrite <- H_C_notnull_1_seq.
  apply implytr_comp_1. apply H.
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_sequential_2_C_null :
  forall sem P Q : tripored,
  sem; II ==> C_null /H\ P -> sem; Q ==> C_null /H\ (P; Q).
Proof.
  intros. assert (HH : sem = sem; II). 
  { rewrite seqtr_ii. reflexivity. }
  rewrite HH. rewrite <- H_C_null_seq.
  apply implytr_comp_1. apply H.
Qed.

Lemma derivationLemma_sequential_2_C_notnull_0 :
  forall sem P Q : tripored,
  sem; II ==> C_notnull_0 /H\ P -> sem; Q ==> C_notnull_0 /H\ (P; Q).
Proof.
  intros. assert (HH : sem = sem; II). 
  { rewrite seqtr_ii. reflexivity. }
  rewrite HH. rewrite <- H_C_notnull_0_seq.
  apply implytr_comp_1. apply H.
Qed.

Lemma derivationLemma_sequential_2_C_notnull_1 :
  forall sem P Q : tripored,
  sem; II ==> C_notnull_1 /H\ P -> sem; Q ==> C_notnull_1 /H\ (P; Q).
Proof.
  intros. assert (HH : sem = sem; II). 
  { rewrite seqtr_ii. reflexivity. }
  rewrite HH. rewrite <- H_C_notnull_1_seq.
  apply implytr_comp_1. apply H.
Qed.

(** ----------------------------------------------------------------- **)

Definition if_bCond (b : env -> env -> bool) : trans :=
  fun s1 s2 : env => if b s1 s2 then ttrue s1 s2 else tfalse s1 s2.

(** judge the ttr2s are equal **)
Definition beq_ttr2_dec (c c' : list fvalue) :=
match c, c' with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | _, _ => (eq_lfvalue_dec c c')
end.

Lemma beq_ttr2_dec_self :
  forall (c : list fvalue),
  beq_ttr2_dec c c = true.
Proof. (* Obviously *) Admitted.

Axiom judge_b :
  forall (b: env -> env -> bool) (n1 n2 n3 : nat)
  (t1 t2 t3 : trace) (tr1 tr2 tr3 : ttr) (f1 f2 f3 : bool),
  (if beq_ttr_dec tr1 tnil then beq_ttr2_dec (last t1) (ttr2 tr3) = true
   else if beq_ttr_dec tr3 tnil then beq_ttr2_dec (ttr2 tr1) (last t3) = true
   else beq_ttr2_dec (ttr2 tr1) (ttr2 tr3) = true) -> 
    b (((n1, t1), tr1), f1) (((n2, t2), tr2), f2) = b (((n3, t3), tr3), f3) (((n2, t2), tr2), f2).

Lemma C_null_init_ifelsetr_qt :
  forall (b : env -> env -> bool) (P Q : tripored) (s1 s2 : env),
  b s1 s2 = true ->
    nott (nott (andt C_null (nott (qt (init; P))))) s1 s2 ->
    nott (nott (andt C_null (nott (qt (Skip; ifelsetr b P Q))))) s1 s2.
Proof.
  intros. destruct P as ((qq, ww), ttt).
  rewrite <- double_nott in *. destruct H0 as [HA HB].
  split. apply HA. unfold nott in *. crush. apply HB.
  destruct s1 as (((n1, t1), tr1), f1).
  destruct s2 as (((n2, t2), tr2), f2).
  unfold seqtr, qt in *. crush. rewrite nott_ttrue_tfalse.
  rewrite ort_tfalse_l. rewrite notort_distributive in H0.
  rewrite <- double_nott in H0. destruct H0 as [HAA HBB].
  unfold nott at 1 in HBB. unfold nott at 1. crush.
  apply HBB. unfold dseq in H0. unfold dseq at 1. crush.
  exists x. split.
  + do 2 rewrite dseq_unit_I. 
    unfold ifelse, skip_cond1, C_null, ttrOfEnv in *. crush.
    unfold dseq. exists (n1, t1, tnil, f1). crush.
    unfold holdt, Inv, ttrOfEnv, trOfEnv. crush.
    unfold subseq. exists []. crush. apply idle_self.
  + destruct x as (((n3, t3), tr3), f3). 
    unfold nott in H2. unfold nott. crush. apply H2.
    unfold ifelse in H0.
    unfold qt at 1 in H0;simpl in H0.
    assert (HH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                    b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
    { apply judge_b. unfold C_null, ttrOfEnv in HA;simpl in HA. 
      rewrite HA. crush. unfold ini, trOfEnv, ttrOfEnv in H1;
      simpl in H1. crush. rewrite beq_ttr2_dec_self. reflexivity. }
    rewrite <- HH in H0. rewrite H in H0. apply H0.
Qed.

Lemma C_null_init_ifelsetr_wt :
  forall (b : env -> env -> bool) (P Q : tripored) (s1 s2 : env),
  b s1 s2 = true ->
    andt C_null (wt (init; P)) s1 s2 ->
    andt C_null (wt (Skip; ifelsetr b P Q)) s1 s2.
Proof.
  intros. destruct P as ((qq, ww), ttt).
  destruct H0 as [HA HB]. split. apply HA. 
  destruct s1 as (((n1, t1), tr1), f1).
  destruct s2 as (((n2, t2), tr2), f2).
  unfold seqtr, wt in *. crush. rewrite ort_tfalse_l in HB.
  right. unfold dseq in HB. unfold dseq at 1. crush.
  exists x. destruct x as (((n3, t3), tr3), f3). split. 
  { do 2 rewrite dseq_unit_I.
    unfold ifelse, skip_cond1, C_null, ttrOfEnv in *. crush.
    unfold dseq. exists (n1, t1, tnil, f1). split.
    { unfold ini, holdt, Inv, ttrOfEnv, trOfEnv in *. crush.
      apply idle_self. } { apply H1. } }
  { unfold wt at 1. simpl.
    assert (HH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                    b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
    { apply judge_b. unfold C_null, ttrOfEnv in HA;simpl in HA. 
      rewrite HA. crush. unfold ini, trOfEnv, ttrOfEnv in H1;
      simpl in H1. crush. rewrite beq_ttr2_dec_self. reflexivity. }
    rewrite HH in H. unfold ifelse. crush. }
Qed.

Lemma C_null_init_ifelsetr_tt :
  forall (b : env -> env -> bool) (P Q : tripored) (s1 s2 : env),
  b s1 s2 = true ->
    andt C_null (tt (init; P)) s1 s2 ->
    andt C_null (tt (Skip; ifelsetr b P Q)) s1 s2.
Proof.
  intros. destruct P as ((qq, ww), ttt). crush.
  destruct H0 as [HA HB]. split. apply HA. 
  destruct s1 as (((n1, t1), tr1), f1).
  destruct s2 as (((n2, t2), tr2), f2).
  unfold dseq in HB. unfold dseq at 1. crush. exists x.
  destruct x as (((n3, t3), tr3), f3). split. 
  { do 2 rewrite dseq_unit_I.
    unfold ifelse, skip_cond1, C_null, ttrOfEnv in *. crush.
    unfold dseq. exists (n1, t1, tnil, f1). split.
    { unfold ini, holdt, Inv, ttrOfEnv, trOfEnv in *. crush.
      apply idle_self. } { apply H1. } }
  { assert (HH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                    b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
    { apply judge_b. unfold C_null, ttrOfEnv in HA;simpl in HA. 
      rewrite HA. crush. unfold ini, trOfEnv, ttrOfEnv in H1;
      simpl in H1. crush. rewrite beq_ttr2_dec_self. reflexivity. }
    rewrite HH in H. unfold ifelse. crush. }
Qed.

Lemma derivationLemma_conditional_1_1 :
  forall (b : env -> env -> bool) (P Q : tripored)
         (x : id) (v : nat) (s1 s2 : env),
  b s1 s2 = true ->
  ((nott (qt ((PhaseCond_1_1 x v); P)) s1 s2 -> 
  nott (qt (C_null /H\ condition b P Q)) s1 s2) /\
  (wt ((PhaseCond_1_1 x v); P) s1 s2 -> 
  wt (C_null /H\ condition b P Q) s1 s2) /\
  (tt ((PhaseCond_1_1 x v); P) s1 s2 -> 
  tt (C_null /H\ condition b P Q) s1 s2)).  
Proof.
  intros. rewrite helpfulLemma_4_4. rewrite H_C_null_seq.
  unfold condition. unfold bCondTripored.
  unfold qt at 1, qt at 2, wt at 3, wt at 4, tt at 5, tt at 6. unfold fst, snd. split.
  - apply C_null_init_ifelsetr_qt. apply H.
  - split.
    + apply C_null_init_ifelsetr_wt. apply H.
    + apply C_null_init_ifelsetr_tt. apply H.
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_conditional_1_2 :
  forall (b : env -> env -> bool) (P Q : tripored)
         (x : id) (v : nat) (s1 s2 : env),
  b s1 s2 = false ->
  ((nott (qt ((PhaseCond_1_1 x v); Q)) s1 s2 -> 
  nott (qt (C_null /H\ condition b P Q)) s1 s2) /\
  (wt ((PhaseCond_1_1 x v); Q) s1 s2 -> 
  wt (C_null /H\ condition b P Q) s1 s2) /\
  (tt ((PhaseCond_1_1 x v); Q) s1 s2 -> 
  tt (C_null /H\ condition b P Q) s1 s2)).  
Proof.
  intros. destruct Q as ((qq, ww), ttt). split. 
  - intros. rewrite helpfulLemma_4_4 in H0.
    rewrite H_C_null_seq in H0.
    unfold condition. unfold bCondTripored in *. 
    unfold qt at 1 in H0. unfold qt at 1. crush.
    rewrite <- double_nott in *. destruct H0 as [HA HB].
    split. apply HA. unfold nott in *. crush. apply HB.
    destruct s1 as (((n1, t1), tr1), f1).
    destruct s2 as (((n2, t2), tr2), f2).
    unfold seqtr, qt in *. crush. rewrite nott_ttrue_tfalse.
    rewrite ort_tfalse_l. rewrite notort_distributive in H0.
    rewrite <- double_nott in H0. destruct H0 as [HAA HBB].
    unfold nott at 1 in HBB. unfold nott at 1. crush.
    apply HBB. unfold dseq in H0. unfold dseq at 1. crush.
    exists x0. split.
    + do 2 rewrite dseq_unit_I. 
      unfold ifelse, skip_cond1, C_null, ttrOfEnv in *. crush.
      unfold dseq. exists (n1, t1, tnil, f1). crush.
      unfold holdt, Inv, ttrOfEnv, trOfEnv. crush.
      unfold subseq. exists []. crush. apply idle_self.
    + destruct x0 as (((n3, t3), tr3), f3). 
      unfold nott in H2. unfold nott. crush. apply H2.
      unfold ifelse in H0.
      unfold qt at 1 in H0;simpl in H0.
      assert (HH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                    b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
      { apply judge_b. unfold C_null, ttrOfEnv in HA;simpl in HA. 
        rewrite HA. crush. unfold ini, trOfEnv, ttrOfEnv in H1;
        simpl in H1. crush. rewrite beq_ttr2_dec_self. reflexivity. }
      rewrite <- HH in H0. rewrite H in H0. apply H0.
  - split;intros.
    { rewrite helpfulLemma_4_4 in H0.
      rewrite H_C_null_seq in H0.
      unfold condition. unfold bCondTripored in *. 
      unfold wt at 1 in H0. unfold wt at 1. crush.
      destruct H0 as [HA HB]. split. apply HA. 
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold seqtr, wt in *. crush. rewrite ort_tfalse_l in HB.
      right. unfold dseq in HB. unfold dseq at 1. crush.
      exists x0. destruct x0 as (((n3, t3), tr3), f3). split. 
      { do 2 rewrite dseq_unit_I.
        unfold ifelse, skip_cond1, C_null, ttrOfEnv in *. crush.
        unfold dseq. exists (n1, t1, tnil, f1). split.
        { unfold ini, holdt, Inv, ttrOfEnv, trOfEnv in *. crush.
          apply idle_self. } { apply H1. } }
      { unfold wt at 1. simpl.
        assert (HH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                    b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. unfold C_null, ttrOfEnv in HA;simpl in HA. 
          rewrite HA. crush. unfold ini, trOfEnv, ttrOfEnv in H1;
          simpl in H1. crush. rewrite beq_ttr2_dec_self. reflexivity. }
        rewrite HH in H. unfold ifelse. crush. } }
    { rewrite helpfulLemma_4_4 in H0.
      rewrite H_C_null_seq in H0.
      unfold condition. unfold bCondTripored in *.
      unfold tt at 1 in H0. unfold tt at 1. simpl in *.
      destruct H0 as [HA HB]. split. apply HA. 
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold dseq in HB. unfold dseq at 1. crush. exists x0.
      destruct x0 as (((n3, t3), tr3), f3). split. 
      { do 2 rewrite dseq_unit_I.
        unfold ifelse, skip_cond1, C_null, ttrOfEnv in *. crush.
        unfold dseq. exists (n1, t1, tnil, f1). split.
        { unfold ini, holdt, Inv, ttrOfEnv, trOfEnv in *. crush.
          apply idle_self. } { apply H1. } }
      { assert (HH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                    b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. unfold C_null, ttrOfEnv in HA;simpl in HA. 
          rewrite HA. crush. unfold ini, trOfEnv, ttrOfEnv in H1;
          simpl in H1. crush. rewrite beq_ttr2_dec_self. reflexivity. }
        rewrite HH in H. unfold ifelse. crush. } }
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_conditional_1_3 :
  forall (b : env -> env -> bool) (P Q : tripored)
         (x : id) (v : nat) (s1 s2 : env),
  b s1 s2 = true ->
  ((nott (qt ((PhaseCond_1_2 x v); P)) s1 s2 -> 
  nott (qt (C_notnull_1 /H\ condition b P Q)) s1 s2) /\
  (wt ((PhaseCond_1_2 x v); P) s1 s2 -> 
  wt (C_notnull_1 /H\ condition b P Q) s1 s2) /\
  (tt ((PhaseCond_1_2 x v); P) s1 s2 -> 
  tt (C_notnull_1 /H\ condition b P Q) s1 s2)).  
Proof.
  intros. destruct P as ((qq, ww), ttt). 
  assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
  { rewrite <- seqtr_ii. reflexivity. }
  rewrite <- HH. rewrite derivationLemma_Skip_1_2.
  unfold condition. rewrite H_C_notnull_1_seq. split.
  - intros. unfold qt at 1 in H0. unfold qt at 1. crush.
    rewrite <- double_nott in *. destruct H0 as [HA HB].
    split. apply HA. unfold nott at 1 in HB.
    unfold nott at 1. crush. apply HB.
    unfold seqtr, qt at 1 in H0. unfold seqtr, qt at 1.
    crush. rewrite notort_distributive in *. 
    rewrite <- double_nott in *. destruct H0 as [HAA HBB].
    split. apply HAA. unfold nott at 1 in HBB.
    unfold nott at 1. crush. apply HBB.
    unfold dseq at 1 in H0. unfold dseq at 1. crush.
    exists x0. destruct s1 as (((n1, t1), tr1), f1).
    destruct s2 as (((n2, t2), tr2), f2).
    destruct x0 as (((n3, t3), tr3), f3). split. crush.
    unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
    do 2 rewrite dseq_unit_I in H1.
    unfold ifelse, skip_cond1, ttrOfEnv in H1;simpl in H1.
    remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
    + apply beq_tnil in HeqHq. crush.
    + crush. unfold I in H1. 
      assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
      { apply judge_b. 
        assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
        rewrite <- HeqHq. rewrite beq_ttr2_dec_self. reflexivity. }
      rewrite HHH in H. unfold nott, qt in *. crush. apply H2.
      unfold ifelse in H3. rewrite H in H3. unfold qt in H3. crush. 
  - split;intros.
    + unfold wt at 1 in H0. unfold wt at 1. crush.
      destruct H0 as [HA HB]. split. apply HA.
      unfold seqtr, wt at 1 in HB. unfold seqtr, wt at 1. crush.
      destruct HB. left. apply H0. right.
      unfold dseq at 1 in H0. unfold dseq at 1. crush.
      exists x0. destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      destruct x0 as (((n3, t3), tr3), f3). split. crush.
      unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
      do 2 rewrite dseq_unit_I in H1.
      unfold ifelse, skip_cond1, ttrOfEnv in H1;simpl in H1.
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      { apply beq_tnil in HeqHq. crush. }
      { crush. unfold I in H1.
        assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. 
          assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
          rewrite <- HeqHq. rewrite beq_ttr2_dec_self. reflexivity. }
        rewrite HHH in H. unfold wt in *. crush.
        unfold ifelse. rewrite H. unfold wt. crush. }
    + unfold tt at 1 in H0. unfold tt at 1. crush.
      destruct H0 as [HA HB]. split. apply HA.
      unfold dseq at 1 in HB. unfold dseq at 1. crush.
      exists x0. destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      destruct x0 as (((n3, t3), tr3), f3). split. crush.
      unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
      do 2 rewrite dseq_unit_I in H1.
      unfold ifelse, skip_cond1, ttrOfEnv in H1;simpl in H1.
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      { apply beq_tnil in HeqHq. crush. }
      { crush. unfold I in H1.
        assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. 
          assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
          rewrite <- HeqHq. rewrite beq_ttr2_dec_self. reflexivity. }
        rewrite HHH in H. unfold ifelse. rewrite H. apply H2. }
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_conditional_1_4 :
  forall (b : env -> env -> bool) (P Q : tripored)
         (x : id) (v : nat) (s1 s2 : env),
  b s1 s2 = false ->
  ((nott (qt ((PhaseCond_1_2 x v); Q)) s1 s2 -> 
  nott (qt (C_notnull_1 /H\ condition b P Q)) s1 s2) /\
  (wt ((PhaseCond_1_2 x v); Q) s1 s2 -> 
  wt (C_notnull_1 /H\ condition b P Q) s1 s2) /\
  (tt ((PhaseCond_1_2 x v); Q) s1 s2 -> 
  tt (C_notnull_1 /H\ condition b P Q) s1 s2)).  
Proof.
  intros. destruct Q as ((qq, ww), ttt). 
  assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
  { rewrite <- seqtr_ii. reflexivity. }
  rewrite <- HH. rewrite derivationLemma_Skip_1_2.
  unfold condition. rewrite H_C_notnull_1_seq. split.
  - intros. unfold qt at 1 in H0. unfold qt at 1. crush.
    rewrite <- double_nott in *. destruct H0 as [HA HB].
    split. apply HA. unfold nott at 1 in HB.
    unfold nott at 1. crush. apply HB.
    unfold seqtr, qt at 1 in H0. unfold seqtr, qt at 1.
    crush. rewrite notort_distributive in *. 
    rewrite <- double_nott in *. destruct H0 as [HAA HBB].
    split. apply HAA. unfold nott at 1 in HBB.
    unfold nott at 1. crush. apply HBB.
    unfold dseq at 1 in H0. unfold dseq at 1. crush.
    exists x0. destruct s1 as (((n1, t1), tr1), f1).
    destruct s2 as (((n2, t2), tr2), f2).
    destruct x0 as (((n3, t3), tr3), f3). split. crush.
    unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
    do 2 rewrite dseq_unit_I in H1.
    unfold ifelse, skip_cond1, ttrOfEnv in H1;simpl in H1.
    remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
    + apply beq_tnil in HeqHq. crush.
    + crush. unfold I in H1. 
      assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
      { apply judge_b. 
        assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
        rewrite <- HeqHq. rewrite beq_ttr2_dec_self. reflexivity. }
      rewrite HHH in H. unfold nott, qt in *. crush. apply H2.
      unfold ifelse in H3. rewrite H in H3. unfold qt in H3. crush. 
  - split;intros.
    + unfold wt at 1 in H0. unfold wt at 1. crush.
      destruct H0 as [HA HB]. split. apply HA.
      unfold seqtr, wt at 1 in HB. unfold seqtr, wt at 1. crush.
      destruct HB. left. apply H0. right.
      unfold dseq at 1 in H0. unfold dseq at 1. crush.
      exists x0. destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      destruct x0 as (((n3, t3), tr3), f3). split. crush.
      unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
      do 2 rewrite dseq_unit_I in H1.
      unfold ifelse, skip_cond1, ttrOfEnv in H1;simpl in H1.
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      { apply beq_tnil in HeqHq. crush. }
      { crush. unfold I in H1.
        assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. 
          assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
          rewrite <- HeqHq. rewrite beq_ttr2_dec_self. reflexivity. }
        rewrite HHH in H. unfold wt in *. crush.
        unfold ifelse. rewrite H. unfold wt. crush. }
    + unfold tt at 1 in H0. unfold tt at 1. crush.
      destruct H0 as [HA HB]. split. apply HA.
      unfold dseq at 1 in HB. unfold dseq at 1. crush.
      exists x0. destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      destruct x0 as (((n3, t3), tr3), f3). split. crush.
      unfold C_notnull_1, ttrOfEnv in HA;simpl in HA.
      do 2 rewrite dseq_unit_I in H1.
      unfold ifelse, skip_cond1, ttrOfEnv in H1;simpl in H1.
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      { apply beq_tnil in HeqHq. crush. }
      { crush. unfold I in H1.
        assert (HHH : b (n1, t1, tr1, true) (n2, t2, tr2, f2) =
                  b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. 
          assert (HHHH : tr1 = tr3). { crush. } rewrite <- HHHH.
          rewrite <- HeqHq. rewrite beq_ttr2_dec_self. reflexivity. }
        rewrite HHH in H. unfold ifelse. rewrite H. apply H2. }
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_conditional_4_1 :
  forall (c : guard) (b : env -> env -> bool) (P Q : tripored),
  (PhaseCond_4_1 c true); (condition b P Q) = C_notnull_0 /H\ (condition b P Q).
Proof.
  intros. unfold condition. rewrite <- seqtr_comm. 
  rewrite derivationLemma_Skip_4_1. rewrite H_C_notnull_0_seq.
  reflexivity.
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_conditional_4_2 :
  forall (c : guard) (b : env -> env -> bool) (P Q : tripored),
  (PhaseCond_4_2 c true); (condition b P Q) = C_null /H\ (condition b P Q).
Proof.
  intros. unfold condition. rewrite <- seqtr_comm.
  rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq.
  reflexivity.
Qed.

Check Skip.

(** ----------------------------------------------------------------- **)
Definition while (b : env -> env -> bool) (P : tripored) : tripored. (** :=
  match b with
  | (_, _, false) => Skip
  | (_, _, true) => P; (while b P)
  end. **)
Admitted.

Definition fai (**(while : (env -> env -> bool) -> tripored -> tripored)**)
               (b : env -> env -> bool) (P : tripored) : tripored :=
  Skip; (ifelsetr b (P; (while b P)) II).

Axiom eqb_while_faiwhile :
  forall (b : env -> env -> bool) (P : tripored),
while b P = fai b P.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_iteration_1_1 :
  forall (x : id) (v : nat) (s1 s2 : env)
         (b : env -> env -> bool) (P : tripored),
  b s1 s2 = true ->
  (nott (qt ((PhaseCond_1_1 x v); (P; (while b P)))) s1 s2 ->
   nott (qt (C_null /H\ (while b P))) s1 s2) /\
  (wt ((PhaseCond_1_1 x v); (P; (while b P))) s1 s2 ->
   wt (C_null /H\ (while b P)) s1 s2) /\
  (tt ((PhaseCond_1_1 x v); (P; (while b P))) s1 s2 ->
   tt (C_null /H\ (while b P)) s1 s2).
Proof.
  intros. split.
  - intros. rewrite helpfulLemma_4_4 in H0. rewrite H_C_null_seq in H0.
    rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *. 
    unfold qt at 1 in H0. unfold qt at 1. crush.
    rewrite <- double_nott in *. destruct H0 as [HA HB].
    split. apply HA. unfold nott in *. crush. apply HB.
    destruct s1 as (((n1, t1), tr1), f1).
    destruct s2 as (((n2, t2), tr2), f2).
    unfold seqtr at 1, qt in H0. unfold seqtr at 1, qt.
    crush. rewrite nott_ttrue_tfalse.
    rewrite ort_tfalse_l. rewrite notort_distributive in H0.
    rewrite <- double_nott in *. destruct H0 as [HAA HBB].
    unfold nott at 1 in HBB. unfold nott at 1. crush.
    apply HBB. unfold dseq at 1 in H0. unfold dseq at 1. crush.
    exists x0. split.
    + do 2 rewrite dseq_unit_I. 
      unfold ifelse, skip_cond1, C_null, ttrOfEnv in *. crush.
      unfold dseq. exists (n1, t1, tnil, f1). crush.
      unfold holdt, Inv, ttrOfEnv, trOfEnv. crush.
      unfold subseq. exists []. crush. apply idle_self.
    + destruct x0 as (((n3, t3), tr3), f3). 
      unfold seqtr, qt at 1. crush. unfold nott at 1, ifelse.
      assert (HH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                    b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
      { apply judge_b. unfold C_null, ttrOfEnv in HA;simpl in HA. 
        rewrite HA. crush. unfold ini, trOfEnv, ttrOfEnv in H1;
        simpl in H1. crush. rewrite beq_ttr2_dec_self. reflexivity. }
      rewrite <- HH. rewrite H. unfold nott at 1. crush.
  - split;intros.
    { rewrite helpfulLemma_4_4 in H0. rewrite H_C_null_seq in H0.
      rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *. 
      unfold wt at 1 in H0. unfold wt at 1. crush.
      destruct H0 as [HA HB]. split. apply HA. 
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold seqtr at 1, wt in HB. unfold seqtr at 1, wt. 
      crush. rewrite ort_tfalse_l in HB.
      right. unfold dseq in HB. unfold dseq at 1. crush.
      exists x0. destruct x0 as (((n3, t3), tr3), f3). split. 
      { do 2 rewrite dseq_unit_I.
        unfold ifelse, skip_cond1, C_null, ttrOfEnv in *. crush.
        unfold dseq. exists (n1, t1, tnil, f1). split.
        { unfold ini, holdt, Inv, ttrOfEnv, trOfEnv in *. crush.
          apply idle_self. } { apply H1. } }
      { unfold wt at 1. simpl.
        assert (HH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                    b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. unfold C_null, ttrOfEnv in HA;simpl in HA. 
          rewrite HA. crush. unfold ini, trOfEnv, ttrOfEnv in H1;
          simpl in H1. crush. rewrite beq_ttr2_dec_self. reflexivity. }
        rewrite HH in H. unfold ifelse. crush. } }
    { rewrite helpfulLemma_4_4 in H0. rewrite H_C_null_seq in H0.
      rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *.
      unfold tt at 1 in H0. unfold tt at 1. simpl in *.
      destruct H0 as [HA HB]. split. apply HA. 
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold dseq in HB. unfold dseq at 1. crush. exists x0.
      destruct x0 as (((n3, t3), tr3), f3). split. 
      { do 2 rewrite dseq_unit_I.
        unfold ifelse, skip_cond1, C_null, ttrOfEnv in *. crush.
        unfold dseq. exists (n1, t1, tnil, f1). split.
        { unfold ini, holdt, Inv, ttrOfEnv, trOfEnv in *. crush.
          apply idle_self. } { apply H1. } }
      { assert (HH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                    b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. unfold C_null, ttrOfEnv in HA;simpl in HA. 
          rewrite HA. crush. unfold ini, trOfEnv, ttrOfEnv in H1;
          simpl in H1. crush. rewrite beq_ttr2_dec_self. reflexivity. }
        rewrite HH in H. unfold ifelse. crush. 
        unfold dseq. exists x1. crush. } }
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_iteration_1_2 :
  forall (x : id) (v : nat) (s1 s2 : env)
         (b : env -> env -> bool) (P : tripored),
  b s1 s2 = false ->
  (nott (qt ((PhaseCond_1_1 x v); II)) s1 s2 ->
   nott (qt (C_null /H\ (while b P))) s1 s2) /\
  (wt ((PhaseCond_1_1 x v); II) s1 s2 ->
   wt (C_null /H\ (while b P)) s1 s2) /\
  (tt ((PhaseCond_1_1 x v); II) s1 s2 ->
   tt (C_null /H\ (while b P)) s1 s2).
Proof.
  intros. split.
  - intros. rewrite helpfulLemma_4_4 in H0. rewrite H_C_null_seq in H0.
    rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *. 
    unfold qt at 1 in H0. unfold qt at 1. crush.
    rewrite <- double_nott in *. destruct H0 as [HA HB].
    split. apply HA. unfold nott in *. crush. apply HB.
    destruct s1 as (((n1, t1), tr1), f1).
    destruct s2 as (((n2, t2), tr2), f2).
    unfold seqtr at 1, qt in H0. unfold seqtr at 1, qt.
    crush. rewrite nott_ttrue_tfalse.
    rewrite ort_tfalse_l. rewrite notort_distributive in H0.
    rewrite <- double_nott in *. destruct H0 as [HAA HBB].
    unfold nott at 1 in HBB. unfold nott at 1. crush.
    apply HBB. unfold dseq at 1 in H0. unfold dseq at 1. crush.
  - split;intros.
    { rewrite helpfulLemma_4_4 in H0. rewrite H_C_null_seq in H0.
      rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *. 
      unfold wt at 1 in H0. unfold wt at 1. crush.
      destruct H0 as [HA HB]. split. apply HA. 
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold seqtr at 1, wt in HB. unfold seqtr at 1, wt. 
      crush. rewrite ort_tfalse_l in HB.
      right. unfold dseq in HB. unfold dseq at 1. crush. }
    { rewrite helpfulLemma_4_4 in H0. rewrite H_C_null_seq in H0.
      rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *.
      unfold tt at 1 in H0. unfold tt at 1. simpl in *.
      destruct H0 as [HA HB]. split. apply HA. 
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold dseq in HB. unfold dseq at 1. crush. exists x0.
      destruct x0 as (((n3, t3), tr3), f3). split. 
      { do 2 rewrite dseq_unit_I.
        unfold ifelse, skip_cond1, C_null, ttrOfEnv in *;simpl in *.
        rewrite HA. simpl. unfold dseq. 
        exists (n1, t1, tnil, f1). split.
        { unfold ini, holdt, Inv, ttrOfEnv, trOfEnv in *. crush.
          apply idle_self. } { apply H1. } }
      { assert (HH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                    b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. unfold C_null, ttrOfEnv in HA;simpl in HA. 
          rewrite HA. crush. unfold ini, trOfEnv, ttrOfEnv in H1;
          simpl in H1. crush. rewrite beq_ttr2_dec_self. reflexivity. }
        rewrite HH in H. unfold ifelse. rewrite H. apply H2. } }
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_iteration_1_3 :
  forall (x : id) (v : nat) (s1 s2 : env)
         (b : env -> env -> bool) (P : tripored),
  b s1 s2 = true ->
  (nott (qt ((PhaseCond_1_2 x v); (P; (while b P)))) s1 s2 ->
   nott (qt (C_notnull_1 /H\ (while b P))) s1 s2) /\
  (wt ((PhaseCond_1_2 x v); (P; (while b P))) s1 s2 ->
   wt (C_notnull_1 /H\ (while b P)) s1 s2) /\
  (tt ((PhaseCond_1_2 x v); (P; (while b P))) s1 s2 ->
   tt (C_notnull_1 /H\ (while b P)) s1 s2).
Proof.
  intros. assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
  { rewrite <- seqtr_ii. reflexivity. } rewrite <- HH. split.
  - intros. rewrite derivationLemma_Skip_1_2 in H0.
    rewrite H_C_notnull_1_seq in H0.
    rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *. 
    unfold qt at 1 in H0. unfold qt at 1. crush.
    rewrite <- double_nott in *. destruct H0 as [HA HB].
    split. apply HA. unfold nott in *. crush. apply HB.
    destruct s1 as (((n1, t1), tr1), f1).
    destruct s2 as (((n2, t2), tr2), f2).
    unfold seqtr at 1, qt in H0. unfold seqtr at 1, qt.
    crush. rewrite notort_distributive in *.
    rewrite <- double_nott in *. destruct H0 as [HAA HBB].
    split. apply HAA. unfold nott at 1 in HBB.
    unfold nott at 1. crush. apply HBB. rewrite <- double_nott in H0.
    unfold dseq at 1 in H0. unfold dseq at 1. crush.
    exists x0. split.
    + do 2 rewrite dseq_unit_I. 
      unfold ifelse, skip_cond1, C_notnull_1, ttrOfEnv in *. crush.
      remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
      apply beq_tnil in HeqHq. crush. apply dseq_unit_l in H1.
      apply H1.
    + destruct x0 as (((n3, t3), tr3), f3). 
      unfold seqtr, qt at 1. crush. unfold nott at 1, ifelse.
      assert (HHH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                    b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
      { apply judge_b. unfold C_notnull_1, ttrOfEnv in HA;simpl in HA. 
        remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
        apply beq_tnil in HeqHq. crush. 
        unfold ifelse, skip_cond1, skip_cond2, ttrOfEnv in H1.
        crush. rewrite <- HeqHq in H1. apply dseq_unit_l in H1.
        unfold I in H1. assert (HHHH : tr1 = tr3). { crush. }
        rewrite <- HHHH. rewrite <- HeqHq.
        rewrite beq_ttr2_dec_self. reflexivity. }
      rewrite HHH in H. rewrite H. unfold nott at 1. crush.
  - split;intros.
    { rewrite derivationLemma_Skip_1_2 in H0. 
      rewrite H_C_notnull_1_seq in H0.
      rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *. 
      unfold wt at 1 in H0. unfold wt at 1. crush.
      destruct H0 as [HA HB]. split. apply HA. 
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold seqtr at 1, wt in HB. unfold seqtr at 1, wt. 
      crush. destruct HB. left. apply H0. right.
      unfold dseq at 1 in H0. unfold dseq at 1. crush.
      exists x0. destruct x0 as (((n3, t3), tr3), f3). split. 
      { apply H1. }
      { unfold wt at 1. simpl.
        assert (HHH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                      b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. unfold C_notnull_1, ttrOfEnv in HA;simpl in HA. 
          remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
          apply beq_tnil in HeqHq. crush. 
          unfold ifelse, skip_cond1, skip_cond2, ttrOfEnv in H1.
          crush. rewrite <- HeqHq in H1. apply dseq_unit_l in H1.
          unfold I in H1. assert (HHHH : tr1 = tr3). { crush. }
          rewrite <- HHHH. rewrite <- HeqHq.
          rewrite beq_ttr2_dec_self. reflexivity. }
        unfold ifelse. rewrite HHH in H. rewrite H. apply H2. } }
    { rewrite derivationLemma_Skip_1_2 in H0. 
      rewrite H_C_notnull_1_seq in H0.
      rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *.
      unfold tt at 1 in H0. unfold tt at 1. simpl in *.
      destruct H0 as [HA HB]. split. apply HA. 
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold dseq at 1 in HB. unfold dseq at 1. crush. exists x0.
      destruct x0 as (((n3, t3), tr3), f3). split. 
      { apply H1. }
      { assert (HHH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                      b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. unfold C_notnull_1, ttrOfEnv in HA;simpl in HA. 
          remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
          apply beq_tnil in HeqHq. crush. 
          unfold ifelse, skip_cond1, skip_cond2, ttrOfEnv in H1.
          crush. rewrite <- HeqHq in H1. apply dseq_unit_l in H1.
          unfold I in H1. assert (HHHH : tr1 = tr3). { crush. }
          rewrite <- HHHH. rewrite <- HeqHq.
          rewrite beq_ttr2_dec_self. reflexivity. }
        unfold ifelse. rewrite HHH in H. rewrite H. apply H2. } }
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_iteration_1_4 :
  forall (x : id) (v : nat) (s1 s2 : env)
         (b : env -> env -> bool) (P : tripored),
  b s1 s2 = false ->
  (nott (qt ((PhaseCond_1_2 x v); II)) s1 s2 ->
   nott (qt (C_notnull_1 /H\ (while b P))) s1 s2) /\
  (wt ((PhaseCond_1_2 x v); II) s1 s2 ->
   wt (C_notnull_1 /H\ (while b P)) s1 s2) /\
  (tt ((PhaseCond_1_2 x v); II) s1 s2 ->
   tt (C_notnull_1 /H\ (while b P)) s1 s2).
Proof.
  intros. assert (HH : PhaseCond_1_2 x v; II = PhaseCond_1_2 x v).
  { rewrite <- seqtr_ii. reflexivity. } rewrite <- HH. split.
  - intros. rewrite derivationLemma_Skip_1_2 in H0.
    rewrite H_C_notnull_1_seq in H0.
    rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *. 
    unfold qt at 1 in H0. unfold qt at 1. crush.
    rewrite <- double_nott in *. destruct H0 as [HA HB].
    split. apply HA. unfold nott in *. crush. apply HB.
    destruct s1 as (((n1, t1), tr1), f1).
    destruct s2 as (((n2, t2), tr2), f2).
    unfold seqtr at 1, qt in H0. unfold seqtr at 1, qt.
    crush. rewrite notort_distributive in *.
    rewrite <- double_nott in *. destruct H0 as [HAA HBB].
    split. apply HAA. unfold nott at 1 in HBB.
    unfold nott at 1. crush. apply HBB.
    rewrite nott_ttrue_tfalse in H0. rewrite dseq_tfalse_r in H0.
    unfold dseq at 1. exists (n1, t1, tr1, f1). crush.
  - split;intros.
    { rewrite derivationLemma_Skip_1_2 in H0. 
      rewrite H_C_notnull_1_seq in H0.
      rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *. 
      unfold wt at 1 in H0. unfold wt at 1. crush.
      destruct H0 as [HA HB]. split. apply HA. 
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold seqtr at 1, wt in HB. unfold seqtr at 1, wt. 
      crush. destruct HB. left. apply H0. right.
      unfold dseq at 1 in H0. unfold dseq at 1. crush. }
    { rewrite derivationLemma_Skip_1_2 in H0. 
      rewrite H_C_notnull_1_seq in H0.
      rewrite eqb_while_faiwhile. unfold fai. unfold bCondTripored in *.
      unfold tt at 1 in H0. unfold tt at 1. simpl in *.
      destruct H0 as [HA HB]. split. apply HA. 
      destruct s1 as (((n1, t1), tr1), f1).
      destruct s2 as (((n2, t2), tr2), f2).
      unfold dseq at 1 in HB. unfold dseq at 1. crush. exists x0.
      destruct x0 as (((n3, t3), tr3), f3). split. 
      { apply H1. }
      { assert (HHH : b (n1, t1, tr1, f1) (n2, t2, tr2, f2) =
                      b (n3, t3, tr3, f3) (n2, t2, tr2, f2)).
        { apply judge_b. unfold C_notnull_1, ttrOfEnv in HA;simpl in HA. 
          remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
          apply beq_tnil in HeqHq. crush. 
          unfold ifelse, skip_cond1, skip_cond2, ttrOfEnv in H1.
          crush. rewrite <- HeqHq in H1. apply dseq_unit_l in H1.
          unfold I in H1. assert (HHHH : tr1 = tr3). { crush. }
          rewrite <- HHHH. rewrite <- HeqHq.
          rewrite beq_ttr2_dec_self. reflexivity. }
        unfold ifelse. rewrite HHH in H. rewrite H. apply H2. } }
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_iteration_4_1 :
  forall (c : guard) (b : env -> env -> bool) (P : tripored),
  (PhaseCond_4_1 c true); (while b P) = C_notnull_0 /H\ (while b P).
Proof.
  intros. rewrite eqb_while_faiwhile. unfold fai. rewrite <- seqtr_comm.
  rewrite derivationLemma_Skip_4_1. rewrite H_C_notnull_0_seq.
  reflexivity.
Qed.

(** ----------------------------------------------------------------- **)

Lemma derivationLemma_iteration_4_2 :
  forall (c : guard) (b : env -> env -> bool) (P : tripored),
  (PhaseCond_4_2 c true); (while b P) = C_null /H\ (while b P).
Proof.
  intros. rewrite eqb_while_faiwhile. unfold fai. rewrite <- seqtr_comm.
  rewrite derivationLemma_Skip_4_2. rewrite H_C_null_seq.
  reflexivity.
Qed.

(** ----------------------------------------------------------------- **)








