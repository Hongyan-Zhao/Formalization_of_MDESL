(**
  @name Formalization of Verilog
  @version 0.1
  @authors Feng Sheng
  @date 27/12/2017
  @description Denotational semantics of MDESL 
  @version 1.0
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
Require Import FunctionalExtensionality.
Require Import CpdtTactics.

Axiom EquivThenEqual: prop_extensionality.

(** use the fvalue to denote the value of states **)

(** every id reprensents the name of variables **)
Definition fvalue := id * nat.


(** equality of the fvalue **)
Notation "x /b\ y" := (andb x y) (at level 40).


Definition eq_fvalue_dec :
  forall f1 f2 : fvalue, {f1 = f2} + {f1 <> f2}.
  repeat decide equality.
Qed.


(** judge whether two fvalues  are equal **)
Definition beq_fvalue_dec (f1 f2 : fvalue) : bool :=
  (beq_id (fst f1) (fst f2)) /b\ (beq_nat (snd f1) (snd f2)).


(** the set of ids **)
Definition subset := list id.


(** snapshots (time, state, flag)  **)
Definition snapshot :=
  nat * list fvalue * bool.


(** projection of the snapshot **)
Definition timeOfSnap (s : snapshot) :=
  fst (fst s).

Definition stateOfSnap (s : snapshot) :=
  snd (fst s).

Definition flagOfSnap (s : snapshot) :=
  snd s.


(** judge whether a value f is in the state **)
Fixpoint in_list_fvalue (lf : list fvalue) (f : fvalue) : bool :=
  match lf with
  | [] => false
  | h :: lf' => if beq_fvalue_dec f h then true
               else in_list_fvalue lf' f
  end.


(** judge two lists are equal **)
Definition eq_lfvalue_dec (lf1 lf2 : list fvalue) : bool :=
  (forallb (in_list_fvalue lf2) lf1) /b\
  (forallb (in_list_fvalue lf1) lf2).



(** judge whether two snapshots are equal **)
Definition beq_snap_dec (c1 c2 : snapshot) :=
  match c1, c2 with
  | (n1, s1, b1), (n2, s2, b2) =>
    beq_nat n1 n2 /b\ eq_lfvalue_dec s1 s2 /b\ Bool.eqb b1 b2
  end.


(** trace : a list of snapshots **)
Definition trace := list snapshot.
Definition dstate := list fvalue.


(** ttr = null or ttr = (ttr1, trr2) **)
Inductive ttr :=
| tnil : ttr
| tval : dstate * dstate -> ttr.



(** projection: get the ttr1 **)
Definition ttr1 (t : ttr) :=
  match t with
  | tnil => nil
  | tval (a, b) => a
  end.

(** projection: get the ttr2 **)
Definition ttr2 (t : ttr) :=
  match t with
  | tnil => nil
  | tval (a, b) => b
  end.


(** judge the ttrs are equal **)
Definition beq_ttr_dec (c c' : ttr) :=
  match c, c' with
  | tnil, tnil => true
  | tnil, _ => false
  | _, tnil => false
  | tval (l11, l12), tval (l21, l22) => (eq_lfvalue_dec l11 l21) /b\ (eq_lfvalue_dec l12 l22)
  end.


(** observation **)
(** The observation of a Verilog program can be represented by a tuple
    (time, time', tr, tr', ttr, ttr', flag, flag'). We exact
    env = (time, tr, ttr, flag), and the observation can be reguarded
    as (s1, s2), s1 denotes the init variables while s2 represents 
    the final variables.
 **)

Definition env :=
  nat * trace * ttr * bool.

(** projection of the environment **)
Definition timeOfEnv (o : env) : nat :=
  (fst (fst (fst o))).

Definition trOfEnv (o : env) : trace :=
  snd (fst (fst o)).

Definition ttrOfEnv (o : env) : ttr :=
  snd (fst o).

Definition flagOfEnv (o : env) : bool :=
  snd o.


(** the equality of two environment **)
Definition eq_env_dec :
  forall f1 f2 : env, {f1 = f2} + {f1 <> f2}.
  repeat decide equality.
Qed.


Definition beq_env_dec (e1 e2 : env) : bool :=
  match eq_env_dec e1 e2 with
  | left _ => true
  | right _ => false
  end.


(** the data structure that satisfy the constraints **)

(** define function subseq **)
Definition subseq {A : Type} (l1 l2 : list A) :=
  exists l', l2 = l1 ++ l'.

Set Implicit Arguments.

(** Lemma: subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3 **)
Theorem subseq_trans :
  forall (A: Type) (l1 l2 l3 : list A),
    subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros. unfold subseq in *; crush.
  exists (x0 ++ x); crush.
Qed.


(** we give some constraints on environment **)
Definition Inv := fun s1 s2 =>
  subseq (trOfEnv s1) (trOfEnv s2) /\ 
  timeOfEnv s1 <= timeOfEnv s2.


Theorem Inv_self:
  forall s, Inv s s.
Proof.
  intros. unfold Inv; crush.
  unfold subseq. exists nil.
  rewrite <- app_nil_end. reflexivity.
Qed.


Theorem Inv_trans :
  forall s1 s2 s3 : env,
    Inv s1 s2 -> Inv s2 s3 -> Inv s1 s3.
Proof.
  intros. unfold Inv in *; crush.
  destruct s1 as (((n1, tr1), ttr1), f1).
  destruct s2 as (((n2, tr2), ttr2), f2).
  destruct s3 as (((n3, tr3), ttr3), f3).
  unfold trOfEnv, timeOfEnv in *; crush.
  eapply subseq_trans. apply H1. apply H.
Qed.

(** define the trans to denote the formulae **)
Definition trans := env -> env -> Prop.

(*
Inductive trans' : env -> env -> Prop :=
| e : forall (e1 e2 : env), trans' e1 e2.
*)

Definition andt (P Q : trans) : trans :=
  fun s1 s2 => P s1 s2 /\ Q s1 s2.


Definition nott (P: trans) : trans :=
  fun s1 s2 =>  not (P s1 s2).


Definition ifelse (b : env -> env -> bool) (P Q : trans) : trans :=
  fun s1 s2 => if b s1 s2 then P s1 s2 else Q s1 s2.


Definition ort (P Q : trans) : trans :=
  fun s1 s2 => (P s1 s2 ) \/ (Q s1 s2).


(** sequences or the chop operator **)
Definition dseq (P Q : trans) : trans :=
  fun s1 s2 => exists s', P s1 s' /\ Q s' s2.


(** define the ttrue and tfalse **)
Definition ttrue : trans :=
  fun s1 s2 => True.


Definition tfalse : trans :=
  fun s1 s2 => False.


(** define a unit **)
Definition I : trans :=
  fun s1 s2 => s1 = s2.



(** some auxiliauy lemmas about andt and ort **)


(** andt tfalse P = tfalse **)
Lemma andt_tfalse_l :
  forall (P : trans), andt tfalse P = tfalse.
Proof.
  intros. apply functional_extensionality; intros.
  apply functional_extensionality; intros.
  unfold andt, tfalse. apply EquivThenEqual; split; crush.
Qed.


Lemma andt_tfalse_r :
  forall (P : trans), andt P tfalse = tfalse.
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold andt, tfalse. apply EquivThenEqual; split; crush.
Qed.


(** andt P Q = andt Q P **)
Lemma andt_comm :
  forall (P Q : trans), andt P Q = andt Q P.
Proof.
  intros. apply functional_extensionality; intros.
  apply functional_extensionality; intros.
  unfold andt. apply EquivThenEqual; crush.
Qed.


(** Lemma : andt ttrue P = P **)
Lemma andt_ttrue_l :
  forall (P : trans), andt ttrue P = P.
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold andt, ttrue. apply EquivThenEqual; crush.
Qed.


(** ort P Q = ort Q P **)
Lemma ort_comm :
  forall P Q, ort P Q = ort Q P.
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold ort. apply EquivThenEqual; split; crush.
Qed.


Lemma ort_assoc :
  forall P Q R, ort (ort P Q) R = ort P (ort Q R).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold ort. apply EquivThenEqual; split; crush.
Qed.


Lemma ort_same :
  forall P , ort P P = P.
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold ort. apply EquivThenEqual; split; crush.
Qed.


Lemma ort_distributive :
  forall P Q R, ort P (ort Q R) = ort (ort P Q) (ort P R).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  unfold ort. apply EquivThenEqual; split; crush.
Qed.



(** Lemma : ort tture P = ttrue **)
Lemma ort_ttrue_l :
  forall (P : trans), ort ttrue P = ttrue.
Proof.
  intros. apply functional_extensionality; intros.
  apply functional_extensionality; intros.
  unfold ort, ttrue. apply EquivThenEqual; split; crush.
Qed.


(** Lemma : ort P ttrue = ttrue **)
Lemma ort_ttrue_r :
  forall (P : trans), ort P ttrue = ttrue.
Proof.
  intros. apply functional_extensionality; intros.
  apply functional_extensionality; intros.
  unfold ort, ttrue. apply EquivThenEqual; split; crush.
Qed.


(** Lemma : ort false P = P **)
Lemma ort_tfalse_l :
  forall (P : trans), ort tfalse P = P.
Proof.
  intros. apply functional_extensionality; intros.
  apply functional_extensionality; intros.
  unfold ort, tfalse. apply EquivThenEqual; split; crush.
Qed.


(** Lemma : ort P false = P **)
Lemma ort_tfalse_r :
   forall (P : trans), ort P tfalse = P.
Proof.
  intros. apply functional_extensionality; intros.
  apply functional_extensionality; intros.
  unfold ort, tfalse. apply EquivThenEqual; split; crush.
Qed.


(** Lemma : ifelse true P Q = P **)
Lemma ifelse_true : 
  forall (P Q : trans),
    ifelse (fun s1 s2 => true) P Q = P. 
Proof.
  crush.
Qed.


(** Lemma : ifelse false P Q = Q **)
Lemma ifelse_false :
  forall (P Q : trans),
    ifelse (fun s1 s2 => false) P Q = Q.
Proof.
  crush.
Qed.


(** some lemmas about chop operator **)

(** Lemma: (F ^ H) ^ G = F ^ (G ^ H) **)
Lemma dseq_assoc_l:
  forall (F G H : trans) (s1 s2 : env),
    dseq (dseq F G) H s1 s2 -> dseq F (dseq G H) s1 s2.
Proof.
  intros. unfold dseq in *.
  crush. exists x0. crush.
  exists x; crush.
Qed.

Lemma dseq_assoc_r :
  forall (F G H : trans) (s1 s2 : env),
    dseq F (dseq G H) s1 s2 -> dseq (dseq F G) H s1 s2.
Proof.
  intros. unfold dseq in *.
  crush. exists x0; crush.
  exists x; crush.
Qed.


Theorem dseq_assoc :
  forall (F G H : trans),
    dseq F (dseq G H) = dseq (dseq F G) H.
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  apply EquivThenEqual; split; 
  [apply dseq_assoc_r | apply dseq_assoc_l ]; assumption.
Qed.


(** Lemma: P ^ I = I ^ P = P **)
Lemma dseq_I_l:
  forall (P : trans) (s1 s2 : env),
    dseq P I s1 s2 -> dseq I P s1 s2.
Proof.
  intros. unfold dseq, I in *. crush.
  exists s1. crush. 
Qed.


Lemma dseq_I_r:
  forall (P : trans) (s1 s2 : env),
    dseq I P s1 s2 -> dseq P I s1 s2.
Proof.
  intros. unfold dseq, I in *. crush.
  exists s2; crush. 
Qed.


Theorem dseq_I_assoc :
  forall (P: trans), dseq I P = dseq P I.
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  apply EquivThenEqual; split;
  [ apply dseq_I_r | apply dseq_I_l ]; assumption.
Qed.


Lemma dseq_unit_l :
  forall (P : trans) (s1 s2 : env),
    dseq P I s1 s2 -> P s1 s2.
Proof.
  intros. unfold dseq, I in *. crush.
Qed.


Lemma dseq_unit_r :
  forall (P : trans) (s1 s2 : env),
    P s1 s2 -> dseq P I s1 s2.
Proof.
  intros. unfold dseq, I in *.
  exists s2; crush.
Qed.


Theorem dseq_unit_I:
  forall (P : trans), dseq I P = P.
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  rewrite dseq_I_assoc. apply EquivThenEqual; split.
  + apply dseq_unit_l.
  + apply dseq_unit_r.
Qed.



(** Theorem : False; P = False **)
Theorem dseq_tfalse_l :
  forall (P : trans),
    dseq tfalse P = tfalse.
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  apply EquivThenEqual; split.
  + intros H. unfold dseq in H; crush.
  + intros H. unfold dseq. crush.
Qed.


(** Theorem : P; False = False **)
Theorem dseq_tfalse_r :
  forall (P : trans),
    dseq P tfalse = tfalse.
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  apply EquivThenEqual; split.
  + intros H. unfold dseq in H; crush.
  + intros H. unfold dseq. crush.
Qed.


(** Formula about the UTP **)

(** ------ auxiliary formula flash ------ **)

(** function sublist gets the part of l2 - l1 **)
Definition sublist {A : Type} (l : list A) (n : nat) :=
  skipn n l.


(** Lemma : l - l = [] **)
Lemma sublist_length :
  forall (A : Type) (l : list A),
    sublist l (List.length l) = [].
Proof.
  induction l; crush.
Qed.


(** Lemma : l1 ++ l2 - l1 = l2  **)
Lemma subseq_app :
  forall (A : Type) (l1 l2 : list A),
    sublist (l1 ++ l2) (List.length l1) = l2.
Proof.
  induction l1; intros; crush.
Qed.


(** Lemma : subseq l1 l2 -> l1 ++ (l2 - l1) = l2 **)
Lemma subseq_sublist:
  forall (A : Type) (l1 l2 : list A),
    subseq l1 l2 ->
    l1 ++ sublist l2 (List.length l1) = l2.
Proof.
  induction l1; intros.
  + simpl. crush.
  + simpl. unfold subseq in H; crush.
    rewrite subseq_app. crush.
Qed.


(** Lemma : subseq l1 l2 -> subseq l2 l3 ->
    (l2 - l1) ++ (l3 - l2) = l3 - l1.        **)

Lemma subseq_sublist_trans :
  forall (A : Type) (l1 l2 l3: list A),
    subseq l2 l3 -> 
    subseq l1 l2 -> 
    subseq l1 l3 ->
    sublist l2 (List.length l1) ++
    sublist l3 (List.length l2) = sublist l3 (List.length l1).
Proof.
  intros.
  apply subseq_sublist in H.
  apply subseq_sublist in H0.
  apply subseq_sublist in H1.
  apply app_inv_head with l1.
  rewrite app_assoc. rewrite H0.
  rewrite H. crush.
Qed.


(** function tail gets the last element of state **)
Fixpoint last (l : trace) : list fvalue :=
  match l with
  | [] => nil
  | [a] => stateOfSnap a
  | a :: m => last m 
  end.


(** the predicate flash **)
Definition tflash : trans :=
  fun s1 s2 => Inv s1 s2 /\
    (timeOfEnv s1) = (timeOfEnv s2) /\ (ttrOfEnv s2) = tnil /\
    (if (orb
           (beq_ttr_dec (ttrOfEnv s1) tnil)
           (eq_lfvalue_dec (last (trOfEnv s1)) (ttr2 (ttrOfEnv s1)))
        )
     then (trOfEnv s2 = trOfEnv s1)
     else (trOfEnv s2 = trOfEnv s1 ++ [(timeOfEnv s1, (ttr2 (ttrOfEnv s1)), true)])).


(** Lemma : tflash; tflash = tflash **)
Lemma tflash_dseq_1:
  forall (s1 s2 : env),
    tflash s1 s2 -> dseq tflash tflash s1 s2.
Proof.
  intros. unfold tflash in H. crush.
  unfold dseq, tflash; crush. exists s2. crush.
  rewrite <- H. assumption. apply Inv_self.
Qed.


Lemma tflash_dseq_2:
  forall (s1 s2 : env),
    dseq tflash tflash s1 s2 -> tflash s1 s2.
Proof. 
  intros. unfold dseq, tflash in *. crush.
  apply Inv_trans with x; assumption.
  destruct s1 as (((n1, tr1), ttr1), f1).
  destruct s2 as (((n2, tr2), ttr2), f2).
  destruct x as (((n3, tr3), ttr3), f3).
  unfold timeOfEnv, ttrOfEnv, trOfEnv in *; simpl in *; crush.
Qed.


Theorem tflash_dseq:
  dseq tflash tflash = tflash.
Proof. 
  intros. do 2 (apply functional_extensionality; intros).
  apply EquivThenEqual; split; [apply tflash_dseq_2 | apply tflash_dseq_1].
Qed.


(** Lemma: tflash s1 s2 -> tflash s2 s3 -> tflash s1 s3 **)
Lemma tflash_trans :
  forall (s1 s2 s3 : env),
    tflash s1 s2 -> tflash s2 s3 -> tflash s1 s3.
Proof.
  intros. unfold tflash in *; crush.
  apply Inv_trans with s2; assumption.
  destruct s1 as (((n1, tr1), ttr1), f1).
  destruct s2 as (((n2, tr2), ttr2), f2).
  destruct s3 as (((n3, tr3), ttr3), f3).
  unfold timeOfEnv, ttrOfEnv in *; simpl in *; crush.
Qed.


(** Lemma : ttrOfEnv s = tnil -> tflash s s **)
Lemma tflash_self:
  forall s : env, ttrOfEnv s = tnil -> tflash s s.
Proof.
  intros. unfold tflash in *; crush. apply Inv_self.
Qed.


(** Lemma : tflash s1 s2 -> ttrOfEnv s2 = tnil **)
Lemma tflash_tnil:
  forall s1 s2 : env, tflash s1 s2 -> ttrOfEnv s2 = tnil.
Proof.
  intros; unfold tflash in H; crush.
Qed.


(** ----- auxiliary formula idle ------ **)

(** function lstand returns the union of a list of bool **)
Fixpoint lstand (l : list bool) : bool :=
  match l with
  | nil => true
  | h :: l' => andb h (lstand l')
  end.


(** define a sorted list **)
Inductive SortedList : list nat -> Prop :=
| sort0 : SortedList []
| sort1 : forall a, SortedList [a]
| sort2 : forall z1 z2, forall l, z1 <= z2 -> 
          SortedList (z2 :: l) -> SortedList (z1 :: z2 :: l).


(** Lemma : SortedList (a :: l) -> SortedList l **)
Lemma SortedList_one :
  forall l a,
    SortedList (a :: l) -> SortedList l.
Proof.
  induction l; intros.
  + constructor.
  + inversion H; subst. crush.
Qed.


(** Lemma : SortedList (l1 ++ l2) -> SortedList l1 /\ SortedList l2 **)
Lemma SortedList_sep1:
  forall l1 l2,
    SortedList (l1 ++ l2) -> SortedList l1.
Proof.
  induction l1; firstorder.
  - now constructor.
  - destruct l1.
    now constructor.
    rewrite <- ?app_comm_cons in *.
    inversion H.
    constructor.
    + now trivial.
    + apply IHl1 with l2.
      rewrite <- ?app_comm_cons in *.
      now trivial.
Qed.



Lemma SortedList_sep2:
  forall l1 l2, SortedList (l1 ++ l2) -> SortedList l2.
Proof.
  induction l1; firstorder.
  rewrite <- app_comm_cons in *.
  inversion H.
  - apply IHl1.
    rewrite <- H2.
    now constructor.
  - apply IHl1.
    rewrite H1 in H3.
    now apply H3.
Qed.


Theorem SortedList_sep:
  forall l1 l2,
    SortedList (l1 ++ l2) -> SortedList l1 /\ SortedList l2.
Proof.
  firstorder.
  now apply SortedList_sep1 with l2.
  now apply SortedList_sep2 with l1.
Qed.


Theorem Sorted_subseq :
  forall l1 l2, 
    subseq l1 l2 -> SortedList l2 -> SortedList l1.
Proof.
  firstorder.
  apply SortedList_sep1 with x; crush.
Qed.


(** functions: getFlag, getTime **)
Definition getFlag (s1 s2 : env) :=
  map flagOfSnap (sublist (trOfEnv s2) (List.length (trOfEnv s1))).


Definition getTime (s1 s2 : env) :=
  map timeOfSnap (sublist (trOfEnv s2) (List.length (trOfEnv s1))).


(** the predicate idle **)
Definition idle : trans := fun s1 s2 => 
  Inv s1 s2 /\
  (forall f, In f (getFlag s1 s2) -> f = false) /\ 
  (subseq (trOfEnv s1) (trOfEnv s2)) /\
  (forall t, In t (getTime s1 s2) -> (t >= timeOfEnv s1) /\ (t <= timeOfEnv s2)) /\
  (SortedList (getTime s1 s2)).


(** Lemma : idle s s **)
Theorem idle_self:
  forall (s : env), idle s s.
Proof.
  intros.  destruct s as (((n1, tr1), ttr1), f1). unfold idle; crush.
  + apply Inv_self.
  + unfold trOfEnv, getFlag in *; simpl in *.
    rewrite sublist_length in H; crush.
  + unfold trOfEnv; simpl.
    unfold subseq; exists []; rewrite app_nil_r; intuition.
  + unfold trOfEnv, getTime in *; simpl in *.
    rewrite sublist_length in H; crush.
  + unfold trOfEnv, getTime in *; simpl in *.
    rewrite sublist_length in H; crush.
  + unfold getTime, trOfEnv. simpl.
    rewrite sublist_length. crush. apply sort0.
Qed.


(** Lemma : idle ; idle = idle **)
Lemma in_app :
  forall (A : Type) (l l' : list A) (a:A),
    In a l \/ In a l' ->  In a (l++l').
Proof.
  crush.
Qed.

Lemma app_in :
  forall (A : Type) l l' (a:A),  
    In a (l++l') -> In a l \/ In a l'.
Proof.
 crush.
Qed.


Lemma flag_app :
  forall (l1 l2 : trace),
    map flagOfSnap l1 ++ map flagOfSnap l2 = map flagOfSnap (l1 ++ l2).
Proof.
  intros. induction l1; crush.
Qed.


Theorem time_app :
  forall (l1 l2 : trace),
    map timeOfSnap l1 ++ map timeOfSnap l2 = map timeOfSnap (l1 ++ l2).
Proof.
  intros. induction l1; crush.
Qed.


(** Lemma : idle s1 s2 -> idle s2 s3 -> idle s1 s3 **)
Lemma idle_flag_trans:
  forall s1 s2 s3, 
    Inv s1 s2 -> Inv s2 s3 -> Inv s1 s3 ->
    (forall f: bool, In f (getFlag s1 s2) -> f = false) ->
    (forall f: bool, In f (getFlag s2 s3) -> f = false) ->
    (forall f: bool, In f (getFlag s1 s3) -> f = false).
Proof.
  intros.
  destruct s1 as (((n1, t1), tr1), f1).
  destruct s2 as (((n2, t2), tr2), f2).
  destruct s3 as (((n3, t3), tr3), f3).
  unfold Inv, getFlag, getTime, trOfEnv in *; crush.
  replace (map flagOfSnap (sublist t3 (Datatypes.length t1))) with
    (map flagOfSnap (sublist t2 (Datatypes.length t1)) ++ map flagOfSnap (sublist t3 (Datatypes.length t2))) in *.
  apply app_in in H4; crush. 
  replace (sublist t3 (Datatypes.length t1)) with (sublist t2 (Datatypes.length t1) ++ sublist t3 (Datatypes.length t2)).
  apply flag_app. apply subseq_sublist_trans; crush.
Qed.


Lemma idle_subseq_trans:
  forall s1 s2 s3,
    Inv s1 s2 -> Inv s2 s3 -> Inv s1 s3 ->
    subseq (trOfEnv s1) (trOfEnv s2) ->
    subseq (trOfEnv s2) (trOfEnv s3) ->
    subseq (trOfEnv s1) (trOfEnv s3).
Proof.
  intros. 
  destruct s1 as (((n1, t1), tr1), f1).
  destruct s2 as (((n2, t2), tr2), f2).
  destruct s3 as (((n3, t3), tr3), f3).
  unfold Inv, trOfEnv in *; simpl in *. 
  apply subseq_trans with t2; intuition.
Qed.


Lemma idle_time_trans:
  forall s1 s2 s3, 
    Inv s1 s2 -> Inv s2 s3 -> Inv s1 s3 ->
    (forall t, In t (getTime s1 s2) -> t >=0 /\ t + timeOfEnv s1 <= timeOfEnv s2) ->
    (forall t, In t (getTime s2 s3) -> t >=0 /\ t + timeOfEnv s2 <= timeOfEnv s3) ->
    (forall t, In t (getTime s1 s3) -> t >=0 /\ t + timeOfEnv s1 <= timeOfEnv s3).
Proof.
  intros.
  destruct s1 as (((n1, t1), tr1), f1).
  destruct s2 as (((n2, t2), tr2), f2).
  destruct s3 as (((n3, t3), tr3), f3).
  unfold Inv, timeOfEnv, trOfEnv in *; simpl in *.
  unfold getTime, trOfEnv in *; simpl in *; crush.
  replace (map timeOfSnap (sublist t3 (Datatypes.length t1))) with
      (map timeOfSnap (sublist t2 (Datatypes.length t1)) ++ map timeOfSnap (sublist t3 (Datatypes.length t2))) in *.
  apply app_in in H4; crush.
  apply H2 in H1; crush. apply H3 in H1; crush.
  replace (sublist t3 (Datatypes.length t1)) with (sublist t2 (Datatypes.length t1) ++ sublist t3 (Datatypes.length t2)).
  apply time_app. apply subseq_sublist_trans; crush.
Qed.


Lemma idle_sorted_trans:
  forall s1 s2 s3, 
    Inv s1 s2 -> Inv s2 s3 -> Inv s1 s3 ->
    SortedList (getTime s1 s2) ->
    SortedList (getTime s2 s3) ->
    SortedList (getTime s1 s3).
Proof.
  intros.
  destruct s1 as (((n1, t1), tr1), f1).
  destruct s2 as (((n2, t2), tr2), f2).
  destruct s3 as (((n3, t3), tr3), f3).
  unfold Inv, trOfEnv, getTime, trOfEnv, timeOfEnv in *; simpl in *; crush.
  unfold subseq in *; crush. rewrite subseq_app; crush.
  rewrite H in H3. rewrite app_assoc in H3. 
  rewrite subseq_app in *; crush.
Admitted.



Lemma idle_trans:
  forall (s1 s2 s3 : env),
    idle s1 s2 -> idle s2 s3 -> idle s1 s3.
Proof.
Admitted.


(** idle ; idle = idle **)
Lemma idle_dseq_1:
  forall (s1 s2 : env),
    idle s1 s2 -> dseq idle idle s1 s2.
Proof.
  intros. unfold dseq. exists s1.
  crush. apply idle_self.
Qed.


Lemma idle_dseq_2:
  forall (s1 s2 : env),
    dseq idle idle s1 s2 -> idle s1 s2.
Proof.
  intros. unfold dseq in H. crush.
  apply idle_trans with x; crush.
Qed.



Theorem idle_iseq:
  dseq idle idle = idle.
Proof.
  do 2 (apply functional_extensionality; intros).
  apply EquivThenEqual; split.
  + apply idle_dseq_2.
  + apply idle_dseq_1; assumption.
Qed.



(** ----- auxiliary formula ini ------ **)
Definition ini : trans :=
  fun s1 s2 => 
    Inv s1 s2 /\
    timeOfEnv s1 = timeOfEnv s2 /\ 
    flagOfEnv s2 = true /\
    trOfEnv s1 = trOfEnv s2 /\ 
    ttrOfEnv s2 = tval (last (trOfEnv s1), last (trOfEnv s1)).


(** ----- auxiliary formula hold ----- **)
Definition holdw (n : nat) : trans :=
  fun s1 s2 =>
    Inv s1 s2 /\
    ttrOfEnv s2 = ttrOfEnv s1 /\ 
    (timeOfEnv s2) < (timeOfEnv s1 + n)%nat /\ 
    idle s1 s2.


Definition holdt (n : nat) : trans :=
  fun s1 s2 =>
    Inv s1 s2 /\
    ttrOfEnv s2 = ttrOfEnv s1 /\ 
    (timeOfEnv s2) = (timeOfEnv s1 + n)%nat /\ 
    idle s1 s2.


(** ------ auxiliary formula dassign ----- **)

(** update the value of the variables **)
Fixpoint fvalue_update (st : list fvalue) (e : id) (v : nat) :=
  match st with
  | nil => [(e, v)]
  | h :: st' =>
    if eq_id_dec (fst h) e then (e, v) :: st'
    else h :: fvalue_update st' e v
  end.


(** get all the ids **)
Definition fvalue_ids (st : list fvalue) :=
  map fst st.


(** get_fvalue **)
Fixpoint get_fvalue (st : list fvalue) (e : id) (default : nat) :=
  match st with
  | nil => default
  | h :: st' =>
    if eq_id_dec (fst h) e then snd h
    else get_fvalue st' e default
  end.


(** The function daeval computes the algebraic expression **)
Fixpoint daeval (st : list fvalue) (e : aexp) {struct e} : nat :=
  match e with
  | ANum n => n
  | AId x => get_fvalue st x 0
  | APlus a1 a2 => plus (daeval st a1) (daeval st a2)
  | AMinus a1 a2  => minus (daeval st a1) (daeval st a2)
  | AMult a1 a2 => mult (daeval st a1) (daeval st a2)
  end.


(** An example to test the fvalue_update **)
Module fvalue_example.

  Definition st := [(Id 0, 0); (Id 1, 1)].

  Eval simpl in (fvalue_update st (Id 1) 3).

  Eval simpl in (fvalue_update st (Id 2) 2).

  Eval simpl in (daeval st (AId (Id 1))).

  Eval simpl in (daeval st (APlus (AId (Id 1)) (ANum 45))).

End fvalue_example.


(** ----- the predicate dassign ----- **)
Definition dassign (x : id) (v : nat) : trans :=
  fun s1 s2 => Inv s1 s2 /\
    timeOfEnv s1 = timeOfEnv s2 /\
    trOfEnv s1 = trOfEnv s2 /\
    ttr1 (ttrOfEnv s1) = ttr1 (ttrOfEnv s2) /\ 
    flagOfEnv s2 = true /\
    ttr2 (ttrOfEnv s2) = fvalue_update (ttr2 (ttrOfEnv s1)) x v.


(** ----- auxiliary formula about time delay ----- **)
Definition delayw : trans :=
  fun s1 s2 =>
    Inv s1 s2 /\ trOfEnv s2 = trOfEnv s1 /\ 
    (timeOfEnv s2) = (timeOfEnv s1) /\ 
    ttrOfEnv s1 = tnil /\ ttrOfEnv s2 = tnil.


Definition delayt : trans :=
  fun s1 s2 =>
    Inv s1 s2 /\ trOfEnv s2 = trOfEnv s1 /\ 
    (timeOfEnv s2) = (timeOfEnv s1 + 1)%nat /\ 
    ttrOfEnv s1 = tnil /\ ttrOfEnv s2 = tnil.


(** ----- auxiliary formula about event guard ----- **)
Definition getfvalue (st : dstate) (v : id) :=
  get_fvalue st v 0.


Fixpoint dfire (g : guard) (st0 : dstate) (st1 : dstate) : bool :=
  match g with
  | gtrue => true
  | gfalse => false
  | gtcv (up v) => blt_nat (getfvalue st0 v) (getfvalue st1 v)
  | gtcv (down v) => blt_nat (getfvalue st1 v) (getfvalue st0 v)
  | gtcv (var v) => negb (beq_nat (getfvalue st0 v) (getfvalue st1 v))
  | or g1 g2 => orb (dfire g1 st0 st1) (dfire g2 st0 st1)
  | and g1 g2 => andb (dfire g1 st0 st1) (dfire g2 st0 st1)
  | nand g1 g2 => andb (dfire g1 st0 st1) (negb (dfire g2 st0 st1))
  end.


(** ----- auxiliary formula selftrig -----**)
Definition tselftriger (g : guard) : trans :=
  fun s1 s2  =>
    not ((ttrOfEnv s1) = tnil) /\
    dfire g (ttr1 (ttrOfEnv s1)) (ttr2 (ttrOfEnv s2)) = true /\ 
    I s1 s2.



(** selftriger(g1 or g2) = selftriger(g1) \/ selftriger(g2) **)
Theorem tselftriger_or :
  forall (g1 g2 : guard),
    tselftriger (or g1 g2) = ort (tselftriger g1) (tselftriger g2).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  apply EquivThenEqual; split.
  - intros. unfold tselftriger, ort in *; crush.
    apply Bool.orb_true_iff in H. crush. left; crush.
    right; crush.
  - intros. unfold tselftriger, ort in *; crush.
Qed.



(** ----- auxiliary formula about await ----- **)
Definition awaitrans1 (g : guard) : trans :=
  fun s1 s2 => 
    ttrOfEnv s1 = tnil \/
    dfire g (ttr1 (ttrOfEnv s1)) (ttr2 (ttrOfEnv s2)) = false /\ 
    I s1 s2.


(** tr' - tr **)
Definition subtr (s1 s2 : env) : trace :=
  sublist (trOfEnv s2) (List.length (trOfEnv s1)).


Definition lststate (s1 s2 : env) :=
  map stateOfSnap (subtr s1 s2).


Definition stateProp (s1 s2 : env) (g : guard) :=
  forall m n : nat,
      m < List.length (lststate s1 s2) /\
      n < List.length (lststate s1 s2) /\ 
      m < n -> 
          let s0 := nth_default nil (lststate s1 s2) m in
          let s1 := nth_default nil (lststate s1 s2) n in
          dfire g s0 s1 = false.



Definition awaitrans2 (g : guard) : trans :=
  fun s1 s2 =>
    idle s1 s2 /\ 
    ttrOfEnv s1 = ttrOfEnv s2 /\
    stateProp s1 s2 g.


(** ----- auxiliary formula about trig ----- **)
Definition trigtrans1 (g : guard) : trans :=
  fun s1 s2 =>
    dfire g (last (trOfEnv s1)) (last (trOfEnv s2)) = true /\
    timeOfEnv s1 = timeOfEnv s2 /\
    idle s1 s2 /\ ttrOfEnv s1 = ttrOfEnv s2 /\
    List.length (sublist (trOfEnv s2) (List.length (trOfEnv s1))) = 1.


Theorem trigtrans1_or :
  forall (g1 g2 : guard),
    trigtrans1 (or g1 g2) = ort (trigtrans1 g1) (trigtrans1 g2).
Proof.
  intros. do 2 (apply functional_extensionality; intros).
  apply EquivThenEqual; split.
  - intros. unfold trigtrans1, ort in *; crush.
    apply Bool.orb_true_iff in H0. crush.
  - intros. unfold trigtrans1, ort in *; crush.
Qed.


(** ------ assignment guard ----- **)
Definition trigtrans2 (x : id) (v : nat) : trans :=
  fun s1 s2 =>
    timeOfEnv s1 = timeOfEnv s2 /\
    trOfEnv s1 = trOfEnv s2 /\
    flagOfEnv s2 = false /\
    ttr1 (ttrOfEnv s2) = (last (trOfEnv s1)) /\
    ttr2 (ttrOfEnv s2) = fvalue_update (last (trOfEnv s1)) x v.


Definition stop2trans : trans :=
  fun s1 s2 =>
    idle s1 s2 /\ ttrOfEnv s1 = ttrOfEnv s2.


(** Now we define a triple to denote the design pattern **)

(** define the design **)
Definition command := trans.

Definition tripored := trans * trans * trans.

Definition qt (t : tripored) := fst (fst t).

Definition wt (t : tripored) := snd (fst t).

Definition tt (t : tripored) := snd t.

Definition II : tripored := (ttrue, tfalse, I).


(** define four operators in tripored **)
Definition seqtr (m n : tripored) : tripored :=
  (
    nott (ort (nott (qt m)) (dseq (tt m) (nott (qt n)))),
    ort (wt m) (dseq (tt m) (wt n)),
    dseq (tt m) (tt n)
  ).


Definition ifelsetr (b : env -> env -> bool) (m n : tripored) : tripored :=
  (
    ifelse b (qt m) (qt n),
    ifelse b (wt m) (wt n),
    ifelse b (tt m) (tt n)
  ).


Definition uniontr (m n : tripored) : tripored :=
  (
    andt (qt m) (qt n),
    ort (wt m) (wt n),
    ort (tt m) (tt n)
  ).


Definition andtr (m n : tripored) : tripored :=
  (
    ort (qt m) (qt n),
    andt (ort (nott (qt m)) (wt m)) (ort (nott (qt n)) (wt n)),
    andt (ort (nott (qt m)) (tt m)) (ort (nott (qt n)) (tt n))
  ).


(** theorems about the ifelsetr **)
Theorem ifelsetr_true :
  forall m n : tripored,
    ifelsetr (fun s1 s2 => true) m n = m.
Proof.
  intros. unfold ifelsetr.
  repeat rewrite ifelse_true.
  destruct m as ((m1, m2), m3).  reflexivity.
Qed.


Theorem ifelsetr_false :
  forall m n : tripored,
    ifelsetr (fun s1 s2 => false) m n = n.
Proof.
  intros. unfold ifelsetr.
  repeat rewrite ifelse_false.
  destruct n as ((n1, n2), n3). reflexivity.
Qed.


Notation "c1 ';' c2" := (seqtr c1 c2) 
                 (at level 40, no associativity).

Print NNPP.

(** Lemma: seqtr_comm **)
Theorem seqtr_comm:
  forall P Q R, (P; Q); R = P; (Q; R).
Proof.
  intros.
  destruct P as ((q1, w1), t1).
  destruct Q as ((q2, w2), t2).
  destruct R as ((q3, w3), t3).
  unfold seqtr. f_equal. f_equal.
  - unfold nott, ort, qt. crush.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    + intros. unfold dseq in *; crush.
      apply NNPP in H0. apply NNPP in H3. crush.
      * apply H4; crush. exists x1; crush.
      * apply H2; crush. exists x2; crush.
        exists x1; crush.
    + intros. unfold dseq in *; crush.
      apply NNPP in H1; apply NNPP in H0. crush.
      * apply H2. exists x1; crush.
      * apply H2. exists x2; crush. apply H6; exists x1; crush.
  - unfold nott, ort, wt, qt. crush.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    + intros. crush. 
      right. unfold dseq in *; crush.
      exists x1; crush.
      right. unfold dseq in *; crush.
      exists x2; crush. right; exists x1; crush.
    + intros. crush. 
      unfold dseq in *; crush. left. right.
      exists x1; crush.
      right. exists x2; crush. exists x1; crush.
  - unfold nott, ort, wt, tt. crush. symmetry.
    apply dseq_assoc.
Qed.



(** Certain properites about healthy formula **)

(** Theorem : seqtr P II = P **)
Theorem seqtr_ii :
  forall (P : tripored), P; II = P.
Proof.
  intros. destruct P as ((Q1, W1), T1).
  unfold seqtr. do 2 f_equal.
  + unfold II, qt; simpl.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - unfold dseq, nott, ort; simpl; intros H; crush.
      apply NNPP in H0; assumption.
    - intros; unfold dseq, nott, ort; simpl; crush.
      apply H2; unfold ttrue; crush.
  + unfold II, wt; simpl.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - unfold dseq, ort; simpl; crush.
    - intros; unfold dseq, ort, wt; simpl; crush.
  + unfold II, tt; simpl.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - unfold dseq, tt, II; crush.
    - unfold dseq, tt, II; crush.
      exists x0; crush. 
Qed.



(** Theorem : seqtr II P = P **)
Theorem ii_seqtr :
  forall (n : tripored),
    (qt n) = ttrue ->  II; n = n.
Proof.
  intros. destruct n as ((n1, n2), n3).
  unfold seqtr. do 2 f_equal.
  + do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - unfold II, qt, dseq, nott, ort; crush.
      unfold qt in H; simpl in H; rewrite H.
      apply NNPP; crush.
    - intros; unfold II, qt, dseq, nott, ort; crush.
       apply H2; unfold ttrue; crush.
  + do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - unfold II, wt, dseq, ort; crush.
    - intros; unfold dseq, ort, wt; crush.
      right; exists x; crush. 
  + do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - unfold dseq, tt, II; crush.
    - unfold dseq, tt, II; crush. exists x; crush.
Qed.


(** Theorem : tFalse ; P = tFalse **)
Definition tFalse := (tfalse, ttrue, tfalse).

Theorem tFalse_seqtr:
  forall (P : tripored), tFalse; P = tFalse.
Proof.
  intros. destruct P as ((Q1, W1), T1).
  unfold seqtr, tFalse. do 2 f_equal.
  + unfold qt, tt; simpl.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - unfold nott, ort; simpl; intros; crush.
    - unfold nott, ort, dseq; simpl; intros; crush.
  + unfold wt, tt; simpl.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - intros; unfold ttrue; crush.
    - unfold ort, dseq; simpl; intros; crush.
  + unfold tt; simpl.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - intros; rewrite dseq_tfalse_l in H; assumption.
    - intros; unfold tfalse in H; tauto.
Qed.


(** define the some healthy formula **)
Definition flash : tripored :=
  (ttrue, tfalse, tflash).

Definition hold (n : nat) : tripored :=
  (ttrue, holdw n, holdt n).

Definition init : tripored :=
  (ttrue, tfalse, ini).

Definition phase5 : tripored :=
  (ttrue, delayw, delayt).


(** Theorem : tflash; tflash = tflash has been verified **)
Theorem flash_equlity:
  flash; flash = flash.
Proof.
  unfold flash, seqtr. do 2 f_equal.
  + do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - unfold seqtr, qt, nott, qt; crush. unfold ttrue; crush.
    - intros; unfold nott, ort, qt, dseq; crush.
  + do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - unfold wt, ort, dseq; crush.
    - unfold wt, ort, dseq; crush. 
  + do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - unfold dseq, tt; crush.
      eapply tflash_trans; [apply H0 | apply H1].
    - unfold  tt; crush. apply tflash_dseq_1; assumption.
Qed.



(** Theorem : hold x; hold y = hold (x + y) **)
Lemma hold_equality_qt:
  forall (x y : nat) (s1 s2 : env),
    ((qt (seqtr (hold x) (hold y))) s1 s2) =
    ((qt (hold (x + y))) s1 s2).
Proof.
  intros. unfold seqtr, hold, qt; crush. 
  apply EquivThenEqual; split.
  - unfold dseq, nott, ort. crush. tauto.
  - unfold dseq, nott, ort. crush.
Qed.


Lemma hold_le:
  forall (x y: nat) (s1 s2: env),
    holdw (x + y) s1 s2 -> y <> 0 ->
    exists s', holdt x s1 s' /\ holdw y s' s2.
Proof.
Admitted.


Lemma hold_equality_wt:
  forall (x y : nat) (s1 s2 : env),
    (wt (seqtr (hold x) (hold y))) s1 s2 =
    (wt (hold (x + y))) s1 s2.
Proof.
Admitted.



Theorem hold_equality_tt:
  forall (x y : nat) (s1 s2 : env),
    (tt (seqtr (hold x) (hold y))) s1 s2 =
    (tt (hold (x + y))) s1 s2.
Proof.
Admitted.



Theorem hold_equality:
  forall (x y : nat), (hold x); (hold y) = hold (x + y).
Proof.
  intros. unfold seqtr, hold. do 2 f_equal.
  + do 2 (apply functional_extensionality; intros). 
    assert (((qt (seqtr (hold x) (hold y))) x0 x1) = ((qt (hold (x + y))) x0 x1)).
    apply hold_equality_qt. unfold hold, qt in H; crush.
  + do 2 (apply functional_extensionality; intros).
    assert (((wt (seqtr (hold x) (hold y))) x0 x1) = ((wt (hold (x + y))) x0 x1)).
    apply hold_equality_wt. unfold hold, wt in H; crush.
  +  do 2 (apply functional_extensionality; intros). 
    assert (((tt (seqtr (hold x) (hold y))) x0 x1) = ((tt (hold (x + y))) x0 x1)).
    apply hold_equality_tt. unfold hold, tt in H; crush.
Qed.


(** Certain properties about algebraic laws **)

(** ------ skip ----- **)
Definition skip_cond1 : env -> env -> bool :=
  fun s1 s2 : env =>  beq_ttr_dec (ttrOfEnv s1) tnil.


Definition skip_cond2 :=
  fun s1 s2 : env => flagOfEnv s1.


Definition Skip : tripored :=
  (
    ifelsetr skip_cond1 (II; ((hold 0); init))
      (ifelsetr skip_cond2 (II; II)
        (flash; ((hold 0); init)))
  ).



(** Theorem: skip; skip = skip has been verified **)

Lemma qt_hold_init_ttrue :
  qt (seqtr (hold 0) init) = ttrue.
Proof.
  unfold seqtr, hold, init, qt; simpl. 
  unfold ort, nott; crush.
  do 2 (apply functional_extensionality; intros).
  apply EquivThenEqual; intros; split.
  + intros; crush; tauto.
  + intros; crush; unfold dseq, holdt in H1; crush.
Qed.



Lemma qt_hold_init_self :
  forall e : env, qt (seqtr (hold 0) init) e e.
Proof.
  intros; rewrite qt_hold_init_ttrue; crush.
Qed.


Lemma skip_equlity_qt:
  forall (s1 s2: env),
    (qt (seqtr Skip Skip)) s1 s2 =
    (qt Skip) s1 s2.
Proof.
  intros. unfold seqtr. apply EquivThenEqual; split; intros. 
  - destruct s1 as (((n1, t1), tr1), f1).
    destruct s2 as (((n2, t2), tr2), f2).
    unfold seqtr, qt in H; simpl in H.
    unfold nott, ort, ifelsetr in *; simpl in *.
    unfold ttrOfEnv, ifelse, qt, nott in *; simpl in *.
    crush. tauto.
  - destruct s1 as (((n1, t1), tr1), f1).
    destruct s2 as (((n2, t2), tr2), f2).
    unfold Skip, qt, ifelse in *; simpl in *.
    unfold ifelse in *. 
    rewrite ii_seqtr in *. rewrite seqtr_ii in *.
    rewrite qt_hold_init_ttrue in *.
    repeat rewrite dseq_I. unfold skip_cond1 in *; simpl in *.
    unfold ttrOfEnv in *; simpl in *.
    remember (beq_ttr_dec tr1 tnil) as Hq. destruct Hq.
    { unfold nott, ort, ifelsetr, ifelse, qt; simpl. rewrite <- HeqHq.
      unfold dseq; simpl. crush. unfold nott, ort in H1; crush.
      rewrite <- HeqHq in *; crush.
      destruct x as (((n3, t3), tr3), f3); crush.
      remember (beq_ttr_dec tr3 tnil) as Hp; destruct Hp; crush.
      unfold nott, ort in H2; crush.
      destruct f3; crush.
      unfold nott, ort in H2; apply NNPP in H2; crush.
      apply H5. rewrite qt_hold_init_ttrue. unfold ttrue; tauto. }
    { unfold skip_cond2, ifelsetr, qt, nott, ort, dseq, ifelse in *; crush.
      rewrite <- HeqHq in H1. destruct f1; crush.
      rewrite <- HeqHq in *. destruct f1; crush. 
      unfold I in *; crush. rewrite <- HeqHq in H2. 
      apply H2; unfold ttrue; tauto.
      destruct x as (((n3, t3), tr3), f3); crush.
      unfold ini, ttrOfEnv, flagOfEnv in H4; crush.
      apply H2; unfold ttrue; tauto.
    }
    apply qt_hold_init_ttrue. apply qt_hold_init_ttrue.
Qed.



Lemma skip_equlity_wt:
  forall (s1 s2 : env),
    (wt (seqtr Skip Skip)) s1 s2 =
    (wt Skip) s1 s2.
Proof.
Admitted.



Lemma skip_equlity_tt:
  forall (s1 s2: env),
    (tt (seqtr Skip Skip)) s1 s2 =
    (tt Skip) s1 s2.
Proof.
Admitted.



Theorem skip_equlity :
  Skip; Skip = Skip.
Proof.
  unfold seqtr.
  assert (Skip = (qt Skip, wt Skip, tt Skip)).
  unfold Skip; crush.
  rewrite H at 9. do 2 f_equal.
  - assert (nott (ort (nott (qt Skip)) (dseq (tt Skip) (nott (qt Skip)))) = (qt (seqtr Skip Skip))).
    unfold seqtr. unfold qt at 3. crush.
    rewrite H0. do 2 (apply functional_extensionality; intros).
    apply skip_equlity_qt.
  - assert ((ort (wt Skip) (dseq (tt Skip) (wt Skip))) = (wt (seqtr Skip Skip))).
    unfold seqtr. unfold wt at 3. crush.
    rewrite H0. do 2 (apply functional_extensionality; intros).
    apply skip_equlity_wt.
  - assert (dseq (tt Skip) (tt Skip) = (tt (seqtr Skip Skip))).
    unfold seqtr. unfold tt at 3. crush.
    rewrite H0. do 2 (apply functional_extensionality; intros).
    apply skip_equlity_tt.
Qed.


(** assignment **)
Definition tassign (x : id) (n : nat) : tripored :=
  (ttrue, tfalse, dassign x n).


Definition sassign (x : id) (n : nat) : tripored := 
  Skip; tassign x n.


(** assign(x, x) = II **)
Lemma dassign_self:
  forall x st, 
    dassign x (daeval st (AId x)) = I.
Proof.
  intros. unfold dassign, I.
  do 2 (apply functional_extensionality; intros).
  crush. apply EquivThenEqual; split; intros; crush.
Admitted.


Theorem tassign_self:
  forall (x : id) (st : list fvalue),
    tassign x (daeval st (AId x)) = II. 
Proof.
  intros. unfold tassign, II. do 2 f_equal.
  apply dassign_self.
Qed.



Theorem assign_self_eq_skip:
  forall x st,
    sassign x (daeval st (AId x)) = Skip.
Proof.
  intros. unfold sassign. 
  rewrite tassign_self. rewrite seqtr_ii.
  reflexivity.
Qed.



(** conditions statement **)
Definition condition (b : env -> env -> bool) (M N : tripored) :=
  Skip; (ifelsetr b M N).



(** define delay **)
Definition mdelay (n : nat) : tripored :=
  flash; (hold (n - 1)); phase5.


(** #n; #m = # (n + m)  **)
Lemma medaly_flash:
  forall n, mdelay n; flash = mdelay n.
Proof.
  intros. unfold seqtr, mdelay.
  unfold seqtr at 11. f_equal. f_equal.
  - unfold nott, ort; crush.
    do 2 (apply functional_extensionality; intros). 
    apply EquivThenEqual; split; intros.
    + crush. apply NNPP in H0. 
      unfold seqtr, tflash, hold, nott, ort, qt in *; crush.
      apply NNPP in H0. 
      unfold seqtr, tflash, hold, nott, ort, qt in *; crush.
    + crush. apply NNPP in H0.
      unfold seqtr, tflash, hold, dseq, nott, ort, qt in *; crush.
  - unfold nott, ort; crush.
    do 2 (apply functional_extensionality; intros). 
    apply EquivThenEqual; split; intros.
    + crush. unfold seqtr, tflash, hold, dseq, nott, ort, wt in *; crush.
    + crush. unfold seqtr, tflash, hold, dseq, nott, ort, wt in *; crush.
      unfold seqtr, tflash, hold, dseq, nott, ort, wt in *; crush.
  - do 2 (apply functional_extensionality; intros). 
    apply EquivThenEqual; split; intros.
    + crush. unfold tflash, holdt, dseq, delayt in *; crush.
      exists x2; crush. exists x3; crush. rewrite <- H10. assumption.
      apply Inv_trans with x1; assumption.
      rewrite H9 in H4. simpl in H4. crush.
    + crush. unfold tflash, holdt, dseq, delayt in *; crush.
      exists x0; crush. exists x1; crush. exists x2; crush.
      rewrite <- H6; assumption. apply Inv_self.
Qed.



Lemma hold0_phase:
  hold 0; phase5 = hold 1.
Proof.
Admitted.



Theorem mdelay_equality:
  forall n m, n > 0 /\ m > 0 ->
    mdelay n; mdelay m = mdelay (n + m).
Proof.
  intros. unfold mdelay at 2. rewrite seqtr_comm.
  rewrite <- seqtr_comm. rewrite medaly_flash.
  unfold mdelay at 1. 
  replace (n - 1) with (n - 1 + 0)%nat.
  rewrite <- hold_equality. rewrite seqtr_comm.
  rewrite seqtr_comm. rewrite seqtr_comm.
  replace (hold 0; (phase5; (hold (m - 1); phase5))) with ((hold 0; phase5); (hold (m - 1); phase5)).
  rewrite hold0_phase.
  replace (hold 1; (hold (m - 1); phase5)) with ((hold 1; hold (m - 1)); phase5).
  rewrite hold_equality; crush.
  replace (hold (n - 1); (hold (S (m - 1)); phase5)) with ((hold (n - 1); hold (S (m - 1))); phase5).
  rewrite hold_equality; crush. unfold mdelay.
  replace (n - 1 + S (m - 1))%nat with (n + m - 1)%nat; crush.
  rewrite seqtr_comm; crush.
  rewrite seqtr_comm; crush.
  rewrite seqtr_comm; crush.
  rewrite seqtr_comm; crush.
  crush.
Qed.


(** another mdelay **)
Definition ndelay (n : nat) : tripored :=
  flash; (hold n).


Lemma ndelay_flash:
  forall n, ndelay n; flash = ndelay n.
Proof.
  intros. unfold seqtr, ndelay.
  unfold seqtr at -1. f_equal. f_equal.
  - unfold nott, ort; crush.
    do 2 (apply functional_extensionality; intros). 
    apply EquivThenEqual; split; intros.
    + crush. apply NNPP in H0. 
      unfold seqtr, tflash, hold, nott, ort, qt in *; crush.
      apply NNPP in H0. 
      unfold seqtr, tflash, hold, nott, ort, qt in *; crush.
    + crush. apply NNPP in H0.
      unfold seqtr, tflash, hold, dseq, nott, ort, qt in *; crush.
  - unfold nott, ort; crush.
    do 2 (apply functional_extensionality; intros). 
    apply EquivThenEqual; split; intros.
    + crush. unfold seqtr, tflash, hold, dseq, nott, ort, wt in *; crush.
    + crush. unfold seqtr, tflash, hold, dseq, nott, ort, wt in *; crush.
  - do 2 (apply functional_extensionality; intros). 
    apply EquivThenEqual; split; intros.
    + crush. unfold tflash, holdt, dseq in *; crush.
      exists x2; crush. rewrite <- H5. assumption.
      apply Inv_trans with x1; assumption.
Admitted.



Theorem ndelay_equality:
  forall n m, n > 0 /\ m > 0 ->
    ndelay n; ndelay m = ndelay (n + m).
Proof.
  intros. unfold ndelay at 2. rewrite <- seqtr_comm.
  rewrite ndelay_flash. unfold ndelay.
  rewrite seqtr_comm. rewrite hold_equality.
  reflexivity.
Qed.




(** chaos **)
Definition chaos :=
  (tfalse, ttrue, ttrue).


Theorem chaos_l :
  forall D W, chaos; (D, W, ttrue) = chaos.
Proof.
  intros. unfold seqtr, chaos.
  do 2 f_equal.
  - unfold nott, ort, qt; crush.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split; intros; crush.
  - unfold nott, ort, wt; crush.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split; intros; crush.
    unfold ttrue; tauto.
  - unfold dseq, tt; crush.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split; intros; crush.
    exists x0; unfold ttrue; crush.
Qed.




(** define selftrig **)
Definition selftrigsub (g : guard) :=
  (ttrue, tselftriger g, tselftriger g).


Definition selftriger (g : guard) :=
  seqtr (selftrigsub g) (andtr II flash).


Definition awaitsub1 (g : guard) :=
  (ttrue, awaitrans1 g, awaitrans1 g).


Definition awaitsub2 (g : guard) :=
  (ttrue, awaitrans2 g, awaitrans2 g).


Definition await (g : guard) :=
  (seqtr (awaitsub1 g) flash); (awaitsub2 g).

Definition trig (g : guard) :=
  (ttrue, tfalse, trigtrans1 g).


Definition triger (x : id) (e : nat) :=
  (ttrue, tfalse, trigtrans2 x e).



Definition guardawake (g : guard) :=
  uniontr (selftriger g) (seqtr (await g) (trig g)).


(** tselftriger (g1 or g2) = tselftriger g1 \/ tselftriger g2 **)
Theorem selftriger_or :
  forall g1 g2 : guard,
    selftriger (or g1 g2) = uniontr (selftriger g1) (selftriger g2).
Proof.
  intros. unfold selftriger, uniontr, seqtr.
  unfold nott, ort; simpl. do 2 f_equal.
  + unfold qt; simpl. crush. unfold andt.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - intros. crush. apply NNPP in H0.
      apply H1. unfold dseq in *; crush.
      exists x1; crush. unfold tselftriger in *; crush.
      apply NNPP in H0. unfold dseq, tselftriger in *; crush.
      apply H1. exists x1; crush.
    - intros. crush. unfold dseq in *; crush.
      rewrite tselftriger_or in H2. unfold ort in H2; crush.
      apply H3; exists x1; crush. apply H4; exists x1; crush.
  + unfold wt; simpl. crush.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - intros. crush. rewrite tselftriger_or in H0.
      unfold ort in H0. crush. unfold dseq in H0. crush.
      rewrite tselftriger_or in H0. unfold ort in H0; crush.
      left. right. unfold dseq; exists x1; crush.
      right. right. unfold dseq; exists x1; crush.
    - intros. crush. left. rewrite tselftriger_or.
      unfold ort. crush. rewrite tselftriger_or.
      right. unfold dseq in *; crush. exists x1; crush. unfold ort; crush.
      left. rewrite tselftriger_or; unfold ort; crush.
      right. unfold dseq in *; crush. exists x1; crush.
      rewrite tselftriger_or; unfold ort; crush.
  + do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split.
    - intros. unfold dseq in *. crush.
      rewrite tselftriger_or in H0. unfold ort in H0. crush.
      left. exists x1. crush. right. exists x1. crush.
    - intros. unfold dseq in *; crush.
      exists x1; crush. rewrite tselftriger_or. unfold ort; crush.
      exists x1; crush. rewrite tselftriger_or. unfold ort; crush.
 Qed.


Theorem trig_or :
   forall g1 g2 : guard,
    trig (or g1 g2) = uniontr (trig g1) (trig g2).
Proof.
  intros. unfold trig, uniontr, seqtr.
  unfold ort; simpl. do 2 f_equal.
  + unfold qt, andt; simpl. 
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split; intros; crush. 
  + unfold wt; simpl.
    do 2 (apply functional_extensionality; intros).
    apply EquivThenEqual; split; intros; crush. 
  + rewrite trigtrans1_or. unfold ort; crush.
Qed.




