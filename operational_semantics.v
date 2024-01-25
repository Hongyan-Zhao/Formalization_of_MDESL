Add LoadPath "/Users/blackcat/formalization_of_MDESL/".

Require Export syntax.
Require Import List.
Require Import FunctionalExtensionality.
Require Export CpdtTactics.

Import Coq.Lists.List.ListNotations.

(** ----- configurations ----- **)

(** three different status **)
Inductive Init :=
| init : Init.

Inductive Flag :=
| one : Flag.

Inductive Endpoint :=
| zero : Endpoint.


Definition Index := list bool.

Definition emp : Index := []. 


(** config **)
Inductive Config  :=
| c1 : Verilog -> state -> Init -> Config
| c2 : Verilog -> state -> state -> Flag -> Index -> Config
| c3 : Verilog -> state -> state -> Endpoint -> Config.


(** Envirmonent **)
Inductive Env : Set := 
| e1 : state -> Init -> Env
| e2 : state -> state -> Flag -> Index -> Env
| e3 : state -> state -> Endpoint -> Env.


(** operational semnatics **)
(** including self transitions and operational semantics **)

Reserved Notation "c1 '\' st '|' c2 '\' st'"
         (at level 40, st at next level, c2 at next level, no associativity).





Inductive sred : Verilog -> Env -> Verilog -> Env -> Prop :=
(** ignore transition rules **)
(** assignment ***)
| assign1 : forall x e st st',
    st' = update st x (aeval st e) ->
    vass (x ::= e) \ (e1 st init) | vnil \ (e2 st st' one emp)
| assign2 : forall x e st st' st'' n, 
    aeval st' e = n ->
    update st' x n = st'' ->
    vass (x ::= e) \ (e2 st st' one emp) | vnil \ (e2 st st'' one emp)
| assign3 : forall x e st st',
    vass (x ::= e) \ (e3 st st' zero) | vass (x ::= e) \ (e1 st' init)
| assign4 : forall x e st st',
    vass (x ::= e) \ (e1 st init) | vass (x ::= e) \ (e1 st' init)
(** skip **)
| skip1 : forall st,
    vass skip \ (e1 st init) | vnil \ (e2 st st one emp)
| skip2 : forall st st',
    vass skip \ (e2 st st' one emp) | vnil \ (e2 st st' one emp)
| skip3 : forall st st',
    vass skip \ (e3 st st' zero) | vass skip \ (e1 st' init)
| skip4 : forall st st',
    vass skip \ (e1 st init) | vass skip \ (e1 st' init)
(** assign guard **)
| assignguard1 : forall x e st st',
    st' = update st x (aeval st e) ->
    vass (ato_assign x e) \ (e1 st init) | vnil \ (e3 st st' zero)
| assignguard2 : forall x e st st' seq,
    vass (ato_assign x e) \ (e2 st st' one seq) | vnil \ e3 st (update st' x (aeval st' e)) zero 
(** if there is a condition to trigger this transition  **)
| assignguard3 : forall x e st st',
    vass (ato_assign x e) \ (e3 st st' zero) | vass (ato_assign x e) \ (e1 st' init)
| assignguard4 : forall x e st st',
    vass (ato_assign x e) \ (e1 st init) | vass (ato_assign x e) \ (e1 st' init)
(* | assignguard5 : forall x e st st',
    vass (ato_assign x e) \ (e2 st st' one emp) | vass (ato_assign x e) \ (e3 st st' zero) *) 
(** guard conditions **)
| guard1 : forall g st st' seq,
    vtc (@(g)) \ (e2 st st' one seq) | vtc (@(g)) \ (e3 st st' zero)
| guard2 : forall g st st',
    fire g st st' = true ->
    vtc (@(g)) \ (e3 st st' zero) | vnil \ (e1 st' init)
| guard3 : forall g st st',
    fire g st st' = false ->
    vtc (@(g)) \ (e3 st st' zero) | vtc (@(g)) \ (e1 st' init)
| guard4 : forall g st st',
    fire g st st' = true ->
    vtc (@(g)) \ (e1 st init) | vnil \ (e1 st' init)
| guard5 : forall g st st',
    fire g st st' = false ->
    vtc (@(g)) \ (e1 st init) | vtc (@(g)) \ (e1 st' init)
| guard6 : forall g st,
    vtc (@(g)) \ (e1 st init) | vtc (@(g)) \ (e1 st init)
(** delay  **)
| delay1 : forall n st st' seq, 
    vtc (# S n) \ (e2 st st' one seq) | vtc (# S n) \ (e3 st st' zero)
| delay2 : forall n st st',
    vtc (# S n) \ (e3 st st' zero) | vtc (# S n) \ (e1 st' init)
| delay3 : forall n st st',
    vtc (# S n) \ (e1 st init) | vtc (# S n) \ (e1 st' init)
| delay4 : forall n st,
    n > 0 -> 
    vtc (# S n) \ (e1 st init) | vtc (# n) \ (e1 st init)
| delay5 : forall st,
    vtc (# 1) \ (e1 st init) | vnil \ (e1 st init)
(** if **)
| cond1 : forall b P Q st,
    beval st b = true ->
    (IFB b THEN P ELSE Q END) \ (e1 st init) | P \ (e2 st st one emp)
| cond2 : forall b P Q st,
    beval st b = false ->
    (IFB b THEN P ELSE Q END) \ (e1 st init) | Q \ (e2 st st one emp)
| cond3 : forall b P Q st st',
    beval st b = true ->
    (IFB b THEN P ELSE Q END) \ (e2 st st' one emp) | P \ (e2 st st' one emp)
| cond4 : forall b P Q st st',
    beval st b = false ->
    (IFB b THEN P ELSE Q END) \ (e2 st st' one emp) | Q \ (e2 st st' one emp)
| cond5 : forall b P Q st st',
    (IFB b THEN P ELSE Q END) \ (e3 st st' zero) | (IFB b THEN P ELSE Q END) \ (e1 st' init)
| cond6 : forall b P Q st st',
    (IFB b THEN P ELSE Q END) \ (e1 st init) | (IFB b THEN P ELSE Q END) \ (e1 st' init)
(** while **)
| iter1 : forall b P st,
    beval st b = true ->
    (WHILE b DO P END) \ (e1 st init) | (P;;WHILE b DO P END) \ (e2 st st one emp)
| iter2 : forall b P st,
    beval st b = false ->
    (WHILE b DO P END) \ (e1 st init) | vnil \ (e2 st st one emp)
| iter3 : forall b P st st',
    beval st b = true ->
    (WHILE b DO P END) \ (e2 st st' one emp) | (P;;WHILE b DO P END) \ (e2 st st' one emp)
| iter4 : forall b P st st',
    beval st b = false ->
    (WHILE b DO P END) \ (e2 st st' one emp) | vnil \ (e2 st st' one emp)
| iter5 : forall b P st st',
    (WHILE b DO P END) \ (e3 st st' zero) | (WHILE b DO P END) \ (e1 st' init)
| iter6 : forall b P st st',
    (WHILE b DO P END) \ (e1 st init) | (WHILE b DO P END) \ (e1 st' init)
(** sequences **)
| seq1 : forall p1 p1' p2 st st',
    p1 \ st | p1' \ st' -> p1' <> vnil ->
    (p1;;p2) \ st | (p1';;p2) \ st'
| seq2 : forall p1 p2 st st',
    p1 \ st | vnil \ st' -> 
    (p1;;p2) \ st | p2 \ st'
(** add transitive clourse**)
(**
| seq3 : forall p1 p1' p2 st st' st'',
    p1 \ st || p1' \ st' ->
    p1' \ st' || p2 \ st'' ->
    p1 \ st || p2 \ st''
**)
(** parallel **)
| paral1 :  forall P Q P' st st' idx,
    P \ (e1 st init) | P' \ (e2 st st' one idx) ->
    P' <> vnil ->
    (P // Q) \ (e1 st init) | (par2 P' Q) \ (e2 st st' one ( true :: idx))
| paral2 :  forall P Q P' st st' idx,
    P \ (e1 st init) | P' \ (e2 st st' one idx) ->
    P' <> vnil ->
    (Q // P) \ (e1 st init) | (par2 Q P') \ (e2 st st' one (false :: idx))
| paral3 : forall P Q st st' idx,
    P \ (e1 st init) | vnil \ (e2 st st' one idx) ->
    (P // Q) \ (e1 st init) | (par2 vnil Q) \ (e3 st st' zero)
| paral4 : forall P Q st st' idx,
    P \ (e1 st init) | vnil \ (e2 st st' one idx) ->
    (Q // P) \ (e1 st init) | (par2 Q vnil) \ (e3 st st' zero)
| paral5: forall P Q P' st st' st'' idx,
    P \ (e2 st st' one idx) | P' \ (e2 st st'' one idx) ->
    P' <> vnil ->
    (P // Q) \ (e2 st st' one (true :: idx)) | (par2 P' Q) \ (e2 st st'' one (true :: idx))
| paral6: forall P Q P' st st' st'' idx,
    P \ (e2 st st' one idx) | P' \ (e2 st st'' one idx) ->
    P' <> vnil ->
    (Q // P) \ (e2 st st' one (false :: idx)) | (par2 Q P') \ (e2 st st'' one (false :: idx))
| paral7: forall P Q st st' st'' idx,
    P \ (e2 st st' one idx) | vnil \ (e2 st st'' one idx) ->
    (P // Q) \ (e2 st st' one (true :: idx)) | (par2 vnil Q) \ (e3 st st'' zero)
| paral8: forall P Q st st' st'' idx,
    P \ (e2 st st' one idx) | vnil \ (e2 st st'' one idx) ->
    (Q // P) \ (e2 st st' one (false :: idx)) | (par2 Q vnil) \ (e3 st st'' zero)
| paral9: forall P Q P' st st' idx,
    P \ (e2 st st' one idx) | P' \ (e3 st st' zero) -> 
    (P // Q) \ (e2 st st' one (true :: idx)) | (par2 P' Q) \ (e3 st st' zero)
| paral10 :  forall P Q P' st st' idx,
    P \ (e2 st st' one idx) | P' \ (e3 st st' zero) ->
    (Q // P) \ (e2 st st' one (false :: idx)) | (par2 Q P') \ (e3 st st' zero)
| paral11 : forall P Q st st',
    (P // Q) \ (e2 st st' one emp) | (par2 P Q) \ (e3 st st' zero)
| paral12 : forall P Q P' st st',
    P \ (e1 st init) | P' \ (e3 st st' zero) ->
    (P // Q) \ (e1 st init) | (par2 P' Q) \ (e3 st st' zero)
| paral13 : forall P Q P' st st',
    P \ (e1 st init) | P' \ (e3 st st' zero) ->
    (Q // P) \ (e1 st init) | (par2 Q P') \ (e3 st st' zero)
| paral14 : forall P Q P' Q' st st',
    P \ (e3 st st' zero) | P' \ (e1 st' init) ->
    Q \ (e3 st st' zero) | Q' \ (e1 st' init) ->
    (P // Q) \ (e3 st st' zero) | (par2 P' Q') \ (e1 st' init)
| paral15 : forall P P' st st',
    P \ (e3 st st' zero) | P' \ (e1 st' init) ->
    (P // vnil) \ (e3 st st' zero) | (par2 P' vnil) \ (e1 st' init)
| paral16 : forall P P' st st',
    P \ (e3 st st' zero) | P' \ (e1 st' init) ->
    (vnil // P) \ (e3 st st' zero) | (par2 vnil P') \ (e1 st' init)
| paral17 :  forall P Q P' Q' st st',
    P \ (e1 st init) | P' \ (e1 st' init) ->
    Q \ (e1 st init) | Q' \ (e1 st' init) ->
    (P // Q) \ (e1 st init) | (par2 P' Q') \ (e1 st' init)
| paral18 :  forall P P' st st',
    P \ (e1 st init) | P' \ (e1 st' init) ->
    (P // vnil) \ (e1 st init) | (par2 P' vnil) \ (e1 st' init)
| paral19 :  forall P P' st st',
    P \ (e1 st init) | P' \ (e1 st' init) ->
    (vnil // P) \ (e1 st init) | (par2 vnil P') \ (e1 st' init)
(** guard choice //TODO **)
where "c1 '\' st '|' c2 '\' st'" := (sred c1 st c2 st').


(** //TODO 
 use the function to define the operational semantics.
 Fixpoint seval (cf : Config) (p : Verilog) (st : state) :=.
**)


(** clourse  **)
Inductive star : Verilog -> Env -> Verilog -> Env -> Prop :=
| star_self : forall p st, 
    star p st p st
| star_tran : forall p1 p1' p2 st st' st'',
    star p1 st p1' st' -> p1' \ st' | p2 \ st'' ->
    star p1 st p2 st''.

