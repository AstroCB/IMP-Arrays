Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From PLF Require Import Maps.
(* ################################################################# *)
(** * Expressions With Variables *)

(** Back to defining Imp.  The next thing we need to do is to enrich
    our arithmetic and boolean expressions with variables.  To keep
    things simple, we'll assume that all variables are global and that
    they only hold numbers. *)

(* ================================================================= *)
(** ** States *)

(** Since we'll want to look variables up to find out their current
    values, we'll reuse maps from the [Maps] chapter, and
    [string]s will be used to represent variables in Imp.

    A _machine state_ (or just _state_) represents the current values
    of _all_ variables at some point in the execution of a program. *)

(** For simplicity, we assume that the state is defined for
    _all_ variables, even though any given program is only going to
    mention a finite number of them.  The state captures all of the
    information stored in memory.  For Imp programs, because each
    variable stores a natural number, we can represent the state as a
    mapping from strings to [nat], and will use [0] as default value
    in the store. For more complex programming languages, the state
    might have more structure. *)

Definition state := total_map nat.
Definition array := list nat.
Definition mem : Type := state * array.

(* ================================================================= *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  (* ARR OPS *)
  | AHd
  | AInd (a1 : aexp)
  | ALen
.
(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
(* ARR VARS *)
Definition I : string := "I".
Definition J : string := "J".

(** (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in the chapters
    developed to Imp, this overloading should not cause confusion.) *)

(** The definition of [bexp]s is unchanged (except that it now refers
    to the new [aexp]s): *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BL (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BG (a1 a2 : aexp)
  | BGe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

(** To make Imp programs easier to read and write, we introduce some
    notations and implicit coercions.

    You do not need to understand exactly what these declarations do.
    Briefly, though, the [Coercion] declaration in Coq stipulates that
    a function (or constructor) can be implicitly used by the type
    system to coerce a value of the input type to a value of the
    output type.  For instance, the coercion declaration for [AId]
    allows us to use plain strings when an [aexp] is expected; the
    string will implicitly be wrapped with [AId]. *)

(** The notations below are declared in specific _notation scopes_, in
    order to avoid conflicts with other interpretations of the same
    symbols.  Again, it is not necessary to understand the details,
    but it is important to recognize that we are defining _new_
    interpretations for some familiar operators like [+], [-], [*],
    [=], [<=], etc. *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x < y" := (BL x y) (at level 70, no associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x > y" := (BG x y) (at level 70, no associativity) : imp_scope.
Notation "x >= y" := (BGe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.
(* ARR OPS *)
Notation "'HD'" := AHd : imp_scope.
Notation "'IND' a1" := (AInd a1) (at level 35) : imp_scope.
Notation "'LEN'" := ALen : imp_scope.

(* ================================================================= *)
(** ** Evaluation *)

(** The arith and boolean evaluators are extended to handle
    variables in the obvious way, taking a state as an extra
    argument: *)

Fixpoint aeval (m : mem) (a : aexp) : nat :=
  let (st, arr) := m in
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | APlus a1 a2 => (aeval m a1) + (aeval m a2)
  | AMinus a1 a2  => (aeval m a1) - (aeval m a2)
  | AMult a1 a2 => (aeval m a1) * (aeval m a2)
  (* ARR OPS *)
  | AHd => hd 0 arr
  | AInd a1 => nth (aeval m a1) arr 0
  | ALen => List.length arr
  end.

Fixpoint beval (m : mem) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval m a1) =? (aeval m a2)
  | BLe a1 a2   => (aeval m a1) <=? (aeval m a2)
  | BL a1 a2    => (aeval m a1) <? (aeval m a2)
  | BGe a1 a2   => negb ((aeval m a1) <? (aeval m a2))
  | BG a1 a2    => negb ((aeval m a1) <=? (aeval m a2))
  | BNot b1     => negb (beval m b1)
  | BAnd b1 b2  => andb (beval m b1) (beval m b2)
  end.

(** We specialize our notation for total maps to the specific case of
    states, i.e. using [(_ !-> 0)] as empty state. *)

Definition empty_st := (_ !-> 0).
Definition empty_mem : state * array := (empty_st, []).

Definition m_update (m: mem) (x : string) (v : nat) :=
  ((x !-> v; (fst m)), snd m).

(** Now we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

(* ################################################################# *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (sometimes called _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.

     c ::= SKIP | x ::= a | c ;; c | TEST b THEN c ELSE c FI
         | WHILE b DO c END

    (We choose this slightly awkward concrete syntax for the
    sake of being able to define Imp syntax using Coq's notation
    mechanism.  In particular, we use [TEST] to avoid conflicting with
    the [if] and [IF] notations from the standard library.)
    For example, here's factorial in Imp:

     Z ::= X;;
     Y ::= 1;;
     WHILE ~(Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END

   When this command terminates, the variable [Y] will contain the
   factorial of the initial value of [X]. *)

(** Here is the formal definition of the abstract syntax of
    commands: *)

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CCons (a : aexp)
  | CSet (a1 a2 : aexp).

(** As for expressions, we can use a few [Notation] declarations to
    make reading and writing Imp programs more convenient. *)

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.
Notation "'CONS' a" :=
  (CCons a) (at level 60, right associativity) : imp_scope.
Notation "'SET' a1 'TO' a2" :=
  (CSet a1 a2) (at level 70, right associativity) : imp_scope.

(** For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition fact_in_coq : com :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END)%imp.

(* ################################################################# *)
(** * Evaluating Commands *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [WHILE] loops don't necessarily terminate makes
    defining an evaluation function tricky... *)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., define it in [Prop] instead of [Type], as we
    did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a lot more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)

(** We'll use the notation [st =[ c ]=> st'] for the [ceval] relation:
    [st =[ c ]=> st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ SKIP ]=> st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   st =[ x := a1 ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                            (E_Seq)
                         st =[ c1;;c2 ]=> st''

                          beval st b1 = true
                           st =[ c1 ]=> st'
                ---------------------------------------                (E_IfTrue)
                st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st'

                         beval st b1 = false
                           st =[ c2 ]=> st'
                ---------------------------------------               (E_IfFalse)
                st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st'

                         beval st b = false
                    -----------------------------                  (E_WhileFalse)
                    st =[ WHILE b DO c END ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ WHILE b DO c END ]=> st''
                  --------------------------------                  (E_WhileTrue)
                  st  =[ WHILE b DO c END ]=> st''
*)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)


(* Allows insertion one past the length of the array, which allows
   adding elements by inserting at the length of the list. If n2 > 1 + len
   of the list, repl is a no-op. *)
Fixpoint repl (arr: array) (n1 n2 : nat) : array :=
  match arr with
  | [] => match n1 with O => [n2] | _ => [] end
  | h::t => match n1 with O => n2::t | S n => h::(repl t n n2) end
end.


Reserved Notation "m '=[' c ']=>' m'"
                  (at level 40).

Inductive ceval : com -> mem -> mem -> Prop :=
  | E_Skip : forall m,
      m =[ SKIP ]=> m
  | E_Ass  : forall m a1 n x,
      aeval m a1 = n ->
      m =[ x ::= a1 ]=> (m_update m x n)
  | E_Seq : forall c1 c2 m m' m'',
      m  =[ c1 ]=> m'  ->
      m' =[ c2 ]=> m'' ->
      m  =[ c1 ;; c2 ]=> m''
  | E_IfTrue : forall m m' b c1 c2,
      beval m b = true ->
      m =[ c1 ]=> m' ->
      m =[ TEST b THEN c1 ELSE c2 FI ]=> m'
  | E_IfFalse : forall m m' b c1 c2,
      beval m b = false ->
      m =[ c2 ]=> m' ->
      m =[ TEST b THEN c1 ELSE c2 FI ]=> m'
  | E_WhileFalse : forall b m c,
      beval m b = false ->
      m =[ WHILE b DO c END ]=> m
  | E_WhileTrue : forall m m' m'' b c,
      beval m b = true ->
      m  =[ c ]=> m' ->
      m' =[ WHILE b DO c END ]=> m'' ->
      m  =[ WHILE b DO c END ]=> m''
  | E_Cons : forall m a1 n,
      aeval m a1 = n ->
      m =[ CONS a1 ]=> ((fst m), (n::(snd m)))
  | E_Set : forall m a1 a2 n1 n2 arr,
      aeval m a1 = n1 ->
      aeval m a2 = n2 ->
      (repl (snd m) n1 n2) = arr ->
      m =[ SET a1 TO a2 ]=> ((fst m), arr)

  where "m =[ c ]=> m'" := (ceval c m m').


(* Here are some examples to demonstrate usage of IMP arrays *)
Definition tst :=
  (CONS 1)%imp.

Example cons :
  empty_mem =[ CONS 1 ]=> (empty_st, [1]).
Proof.
  apply E_Cons. simpl. reflexivity.
Qed.

Example cons' :
  (empty_st, [1]) =[ CONS 1 ]=> (empty_st, [1; 1]).
Proof.
  apply E_Cons. simpl. reflexivity.
Qed.

Example cons'' :
  (empty_st, [1]) =[ CONS 2 ]=> (empty_st, [2; 1]).
Proof.
  apply E_Cons. simpl. reflexivity.
Qed.

Example cons_fail :
  (empty_st, [1]) =[ CONS 3 ]=> (empty_st, [1; 3]).
Proof.
  Fail apply E_Cons.
Abort.

Example cons_hd :
  (empty_st, [1]) =[ CONS HD ]=> (empty_st, [1; 1]).
Proof.
  apply E_Cons. simpl. reflexivity.
Qed.

Example cons_ind :
  (empty_st, [1;2;3]) =[ CONS (IND 1) ]=> (empty_st, [2;1;2;3]).
Proof.
  apply E_Cons. simpl. reflexivity.
Qed.

Example set_1_3 :
  (empty_st, [1;2;3]) =[ SET 1 TO 3 ]=> (empty_st, [1;3;3]).
Proof.
  eapply E_Set; reflexivity.
Qed.

Example len_ex :
  (empty_st, [1;2;3]) =[ X ::= LEN ]=> (X !-> 3, [1;2;3]).
Proof.
  apply E_Ass. simpl. reflexivity.
Qed.

Definition repeat : com :=
  (WHILE ~(Z = 0) DO
        CONS X;;
        Z ::= Z - 1
  END)%imp.

Example rep_1_2 :
  ((X !-> 1; Z !-> 2), []) =[ repeat ]=>
    ((Z !-> 0; Z !-> 1; X !-> 1; Z !-> 2), [1;1]).
Proof.
  unfold repeat. eapply E_WhileTrue.
  - simpl. reflexivity.
  - eapply E_Seq. apply E_Cons. simpl. reflexivity.
    + simpl. eapply E_Ass. simpl. reflexivity.
  - eapply E_WhileTrue.
    + reflexivity.
    + eapply E_Seq. apply E_Cons. reflexivity.
      * simpl. eapply E_Ass. reflexivity.
    + simpl. apply E_WhileFalse. simpl. reflexivity.
Qed.

(* HOARE TRIPLES *)
Definition Assertion := mem -> Prop.
Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall m m',
     m =[ c ]=> m'  ->
     P m  ->
     Q m'.
Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall m, P m -> Q m.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.
Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall m, Q m) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros m m' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall m, ~ (P m)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros m m' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

Definition assn_sub X a P : Assertion :=
  fun (m : mem) =>
    P ((X !-> aeval m a ; (fst m)), snd m).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a m m' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. unfold m_update. assumption.  Qed.

(** Here's a first formal proof using this rule. *)

Example assn_sub_example :
  {{(fun m => (fst m) X < 5) [X |-> X + 1]}}
  X ::= X + 1
  {{fun m => (fst m) X < 5}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_asgn.  Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.
Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P m m' H HP. inversion H. subst.
  assumption.  Qed.
Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 m m' H12 Pre.
  inversion H12; subst.
  apply (H1 m'0 m'); try assumption.
  apply (H2 m m'0); assumption. Qed.

Definition bassn b : Assertion :=
  fun m => (beval m b = true).
Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.
Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.
Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare m m' He HP.
  remember (WHILE b DO c END)%imp as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *) 
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare m m'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(* HOARE RULE FOR SET *)
Definition set_sub a1 a2 P : Assertion :=
  fun (m : mem) => P ((fst m), (repl (snd m) (aeval m a1) (aeval m a2))).

Theorem hoare_set : forall (Q : Assertion) (a1 a2 : aexp),
{{set_sub a1 a2 Q}} SET a1 TO a2 {{Q}}.
Proof.
  unfold hoare_triple. intros.
  inversion H; subst.
  unfold set_sub in H0. assumption.
Qed.

(* HOARE ARR EXAMPLES *)
Example cons_hoare :
  {{fun m => (snd m) = []}} CONS 1 {{fun m => snd m = [1]}}.
Proof.
  unfold hoare_triple. intros. inversion H; subst. simpl. rewrite H0.
  destruct m. reflexivity.
Qed.

Example cons_assgn_hoare :
  {{ fun m => ((fst m) X = 1) /\ ((snd m) = []) }}
    CONS X
  {{ fun m => (snd m = [1]) }}.
Proof.
  unfold hoare_triple. intros. destruct H0. inversion H; subst. simpl. rewrite H1.
  destruct m. simpl in H0. rewrite H0. reflexivity.
Qed.

Example set_hoare :
  {{ fun m => (snd m) = [1;2;3] }}
    SET 1 TO 3
  {{ fun m => (snd m) = [1;3;3] }}.
Proof.
  unfold hoare_triple. intros. inversion H; subst. simpl. destruct m. simpl.
  simpl in H. simpl in H0. rewrite H0. simpl. reflexivity.
Qed.

Definition insertion_sort : com :=
  I ::= 1;;
  WHILE (I < LEN) DO
    X ::= IND I;;
    J ::= I - 1;;
    WHILE ((J >= 0) && ((IND J) > X)) DO
      SET (J+1) TO (IND J);;
      J ::= J - 1
    END;;
    SET (J+1) TO X;;
    I ::= I + 1
  END.

Inductive sorted: list nat -> Prop :=
| sorted_nil:
    sorted nil
| sorted_1: forall x,
    sorted (x::nil)
| sorted_cons: forall x y l,
   x <= y -> sorted (y::l) -> sorted (x::y::l).

Lemma and_split : forall a b, a && b = true -> a = true /\ b = true.
Proof.
  intros. split. destruct a. reflexivity. simpl in H. inversion H. destruct b.
  reflexivity. simpl in H. inversion H. destruct a in H. simpl in H. inversion H. simpl in H. inversion H.
Qed.

Example sorted_ex :
  {{ fun m => (snd m) = [2;3;1;4] }} insertion_sort {{ fun m => sorted (snd m) }}.
Proof.
  unfold insertion_sort. eapply hoare_seq. eapply hoare_consequence_post. apply hoare_while. eapply hoare_consequence_pre.
  eapply hoare_seq. eapply hoare_seq. eapply hoare_seq. eapply hoare_seq.
  - apply hoare_asgn.
  - apply hoare_set.
  - admit.
  - apply hoare_asgn.
  - apply hoare_asgn.
  - unfold assert_implies. intros. destruct H. simpl.


Theorem insertion_sort_correct :
  {{fun m => True}} insertion_sort {{ fun m => sorted (snd m) }}.
Proof.
  unfold insertion_sort. apply hoare_seq with (Q := (fun (m : mem) => (fst m) I = 1)).
  - eapply hoare_consequence_post. apply hoare_while. eapply hoare_consequence_pre.
    eapply hoare_seq. (*with (Q := (fun (m : mem) => (fst m) X = nth ((fst m) I) (snd m) 0)).*)
    apply hoare_seq with (Q := (fun (m : mem) => (fst m) J = ((fst m) I) - 1)).
    eapply hoare_seq. eapply hoare_seq.
    + apply hoare_asgn.
    + apply hoare_set.
    + admit.
    + apply hoare_asgn.
    + apply hoare_asgn.
    + admit.
    + unfold assert_implies. intros. destruct H. induction m. simpl. simpl in *. unfold bassn in *. 
   - unfold hoare_triple. intros. inversion H; subst. unfold m_update in *. simpl in *.
     destruct m in *. unfold t_update. simpl. reflexivity.



    + eapply hoare_consequence_post. apply hoare_while. eapply hoare_consequence_pre. eapply hoare_seq.
      * apply hoare_asgn.
      * apply hoare_set.
      * unfold bassn, set_sub, assert_implies. intros. destruct m. simpl in *. destruct H.
        unfold assn_sub. simpl. 
