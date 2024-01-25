(**
  @name Formalization of Verilog
  @version 0.1
  @authors Feng Sheng
  @date 27/12/2017
  @description 
  @version 1.0
 **)
Add LoadPath "/Users/blackcat/formalization_of_MDESL/".

Require Import Arith.
Require Import List.
Require Import String.
Require Import FunctionalExtensionality.
Require Import CpdtTactics.

Open Scope nat_scope.
Open Scope type_scope.
Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.


Inductive id : Set := 
| Id : nat -> id.


Theorem eq_id_dec :
  forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   - (* n1 = n2 *)
     left. rewrite Heq. reflexivity.
   - (* n1 <> n2 *)
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined.


Definition beq_id (id1 id2 : id) :=
  match (eq_id_dec id1 id2) with
  | left _ => true
  | right _ => false
  end.


Theorem ex_falso_quodlibet :
  forall (P : Prop), False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.



Lemma eq_id :
  forall (T:Type) x (p q:T),
    (if eq_id_dec x x then p else q) = p. 
Proof.
  intros T x p q. 
  destruct (eq_id_dec x x). 
  - (* x = x *) 
    reflexivity.
  - (* x <> x (impossible) *) 
    apply ex_falso_quodlibet; apply n; reflexivity.
Qed.


Lemma neq_id :
  forall (T:Type) x y (p q:T),
    x <> y -> (if eq_id_dec x y then p else q) = q. 
Proof.
  intros T x y p q H.
  destruct (eq_id_dec x y).
  - exfalso; apply H; assumption.
  - reflexivity.
Qed.


(* a state represents the current values of all the variables *)
Definition state := id -> nat.


Definition empty_state : state :=
  fun _ => 0.


Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.


Theorem update_eq :
  forall n x st, (update st x n) x = n.
Proof.
  intros n x st. unfold update; simpl. 
  rewrite eq_id. reflexivity.
Qed.


Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 -> (update st x2 n) x1 = (st x1).
Proof.
  intros x2 x1 n st H. unfold update; simpl.
  rewrite neq_id. reflexivity. assumption.
Qed.


Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
   (update (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  intros. unfold update.
  destruct (eq_id_dec x2 x1); reflexivity.
Qed.


Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  intros n1 x1 x2 st H.
  unfold update.
  destruct (eq_id_dec x1 x2).
  rewrite <-e, H. reflexivity. 
  reflexivity.
Qed.


Theorem update_permute : forall n1 n2 x1 x2 x3 st,
    x2 <> x1 ->
    (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  intros n1 n2 x1 x2 x3 st H.
  unfold update.
  destruct (eq_id_dec x1 x3).
  destruct (eq_id_dec x2 x3).
  apply ex_falso_quodlibet.
  apply H.
  rewrite e0, e.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.


Lemma state_eq :
  forall x y (st: state),
    (if eq_id_dec x y then st y else st x) = st x.
Proof.
  intros. destruct (eq_id_dec x y); crush.
Qed.


(* definitions for arithmetic expression and boolean expression *)
Inductive aexp : Type := 
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.


Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BGt : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BOr : bexp -> bexp -> bexp
  | BImp : bexp -> bexp -> bexp.


(* evaluation functions for arithmetic expression and boolean expression *)
Fixpoint aeval (st : state) (e : aexp) {struct e} : nat :=
  match e with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => plus (aeval st a1) (aeval st a2)
  | AMinus a1 a2  => minus (aeval st a1) (aeval st a2)
  | AMult a1 a2 => mult (aeval st a1) (aeval st a2)
  end.


Fixpoint ble_nat (n m : nat) {struct n} : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.


Definition blt_nat (n m : nat) := ble_nat (S n) m.

Fixpoint bgt_nat (n m : nat) {struct n} : bool :=
  match m with
  | O => true
  | S m' =>
      match n with
      | O => false
      | S n' => bgt_nat n' m'
      end
  end.

Fixpoint beval (st : state)(e : bexp) {struct e} : bool :=
  match e with 
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
  | BGt a1 a2 => bgt_nat (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  | BOr b1 b2 => orb (beval st b1) (beval st b2)
  | BImp b1 b2 => orb (negb (beval st b1)) (beval st b2)
  end.


(* ----- primitive commond ------ *)
Inductive pc : Type :=
| assign : id -> aexp -> pc
| skip : pc
| ato_assign : id -> aexp -> pc.


Notation "x '::=' e" :=
  (assign x e) (at level 60, no associativity).

Notation "'@(' x '::=' e ')' " :=
  (ato_assign x e) (at level 60, no associativity).


Fixpoint pceval (st : state) (p : pc) :=
  match p with
    | skip => st
    | assign x e => update st x (aeval st e)
    | ato_assign x e => update st x (aeval st e)
  end.


Lemma skip_equal_x :
  forall x st, pceval st skip = pceval st (x ::= (AId x)).
Proof.
  intros x st.
  simpl. apply functional_extensionality.
  intros x0. unfold update.
  destruct (eq_id_dec x x0).
  + rewrite e; reflexivity.
  + reflexivity.
Qed.


(* ----- time control statement ----- *)

Inductive tcv :=
| var : id -> tcv
| up : id -> tcv
| down : id -> tcv.


Inductive guard : Type :=
| gtrue : guard
| gfalse : guard
| gtcv : tcv -> guard
| or : guard -> guard -> guard
| and : guard -> guard -> guard
| nand : guard -> guard -> guard.


Inductive tcs : Type :=
| delay : nat -> tcs
| atomic : guard -> tcs.

(**
Inductive tcs : Type :=
| delay : {b : nat | 0 < b} -> tcs
| atomic : guard -> tcs.
**)

Notation "# n" :=
  (delay n) (at level 80, no associativity).

Notation "'@(' g ')'" :=
  (atomic g) (at level 80, no associativity).


(** ----- Verilog ----- **)
Inductive Verilog :=
| vass : pc -> Verilog
| vseq : Verilog -> Verilog -> Verilog
| vif : bexp -> Verilog -> Verilog -> Verilog
| vwhile : bexp -> Verilog -> Verilog
| vtc : tcs -> Verilog
| vpar : Verilog -> Verilog -> Verilog
| vnil : Verilog.


Notation "c1 ;; c2" :=
  (vseq c1 c2) (at level 90,right associativity).

Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'END'" :=
  (vif c1 c2 c3) (at level 90, right associativity).

Notation "'WHILE' b 'DO' c 'END'" :=
  (vwhile b c) (at level 90, right associativity).

Notation "c1 '//' c2" :=
  (vpar c1 c2) (at level 90, right associativity).


(** predicates fire to indicate the trnasition from state st0 to st1 **)

Fixpoint fire (g : guard) (st0 : state) (st1 : state) : bool :=
  match g with
  | gtrue => true
  | gfalse => false
  | gtcv (up v) => blt_nat (st0 v) (st1 v)
  | gtcv (down v) => blt_nat (st1 v) (st0 v)
  | gtcv (var v) => negb (beq_nat (st0 v) (st1 v))
  | or g1 g2 => orb (fire g1 st0 st1) (fire g2 st0 st1)
  | and g1 g2 => andb (fire g1 st0 st1) (fire g2 st0 st1)
  | nand g1 g2 => andb (fire g1 st0 st1) (negb (fire g2 st0 st1))
  end.


(** optional functions **)
Definition seq (p q : Verilog) :=
match p with
| vnil => q
| _ => p ;; q
end.


Definition par2 (p q : Verilog) :=
match p, q with
| vnil, vnil => vnil
| vnil, _ => q
| _, vnil => p
| _, _ => p // q
end.
