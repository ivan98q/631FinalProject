(** *Extending the Lambda Calculus in different ways.*)
(**
   Author : Ivan Quiles
   Note:
   There is borrowed material from the Software Foundations
   Textbook series. Mainly from the 2nd textbook.
 *)

(** 
  Here I am extending the Lambda Calculus with both primitive values and
 primitive operations. So now we need a second concept of reduction where we handle
 turning these primitive operations into actual values in our Lambda Calculus.
 *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Init.Datatypes.
From LF Require Import Maps.

Definition relation (X: Type) := X -> X -> Prop.
Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  not (exists t', R t t').

Module Attempt1.
(**
   Here are the terms of our language. The first three terms are from the
   regular lambda calculus. However we now have new terms for constants and for
   procedures. Procedures are the built in functions of programming
   languages. We will soon define some built in procedures.

   The goal of defining it this way is to make it easier to define procedures
   If you want to attempt to add some go ahead! You need to add it to the
   def_proc type and also add it's actuall implementation to the
   inductive relation above relation.
 *)
Inductive term : Type :=
| tnum : nat -> term
| tbool : bool -> term
| tvar : string -> term
| tapp : term -> term -> term
| tabs : string -> term -> term
| tproc : procedure -> term
| tif : term -> term -> term -> term
  with
procedure : Type :=
| proc : string -> list term -> procedure.

(**
   Values are free variables, the constants we are adding to our language,
   and abstractions are also values.
 *)
Inductive value : term -> Prop :=
| v_var : forall s,
    value (tvar s)
| v_num: forall v,
    value (tnum v)
| v_bool : forall v,
    value (tbool v)
| v_abs : forall s x,
    value (tabs s x).
(**
   This is a very simple relation to determine what is a valid procedure. 
 *)
Inductive def_proc :  string -> Prop :=
| p_add1 :
    def_proc ("add1")
| p_sub1 :
    def_proc ("sub1")
| p_iszero :
    def_proc ("iszero")
| p_plus :
    def_proc ("+")
| p_sub :
    def_proc ("-")
| p_mul :
    def_proc ("*")
| p_or :
    def_proc "bor"
| p_and :
    def_proc "band"
| p_not:
    def_proc "bnot".

(**
This Fixpoint is important later on when defining step to see if everything
 in this list is a valid value. I only process procedures as soon as a list
 of terms is reduced to a list of values.
 *)
Fixpoint list_of_values (l:list term): Prop :=
  match l with
  | nil => True
  | x :: xs => (value x) /\ list_of_values xs
  end.

(**
   This is lambda calclus subsitution. Not very interestings besides
   that procedures get the subsitution applied to all parameters.
 *)
Reserved Notation "'[' x ':=' s ']' t" (at level 20).
Fixpoint subst (x:string) (s:term) (t:term) : term :=
  match t with
  | tbool x => tbool x
  | tnum x => tnum x
  | tvar x' =>
      if eqb x x' then s else t
  | tabs x' t1 =>
      tabs x' (if eqb x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 =>
    tapp ([x:=s] t1) ([x:=s] t2)
  | tproc p => match p with
              | p => match p with
                    | proc x ts => tproc (proc x (map (subst x s) ts))
                    end
              end
  | tif t1 t2 t3 => tif ([x:=s]t1) ([x:=s]t2) ([x:=s]t3)
  end
where "'[' x ':=' s ']' t" := (subst x s t).

Open Scope list_scope.
(**
   This is how procedures are converted into equivalent Coq expressions.
   This relation is used in the small step reduction of below.
   Includes:
   - add1
   - sub1
   - IsZero
   - +,-,*
   - And,Or, Not
 *)
Inductive procStep : procedure -> term -> Prop :=
| PROC_Add1 : forall x n,
    x = tnum n -> 
    procStep (proc "add1" (x::nil)) (tnum (n+1))
| PROC_Sub1 : forall x n ,
    x = tnum n -> 
    procStep (proc "sub1" (x::nil)) (tnum (n-1))
| PROC_Iszero : forall x n y,
    x = tnum n ->
    y = (if Nat.eqb n 0 then true else false) -> 
    procStep (proc "iszero" (x::nil)) (tbool y)
| PROC_add : forall x y n m,
    x = tnum n ->
    y = tnum m ->
    procStep (proc "+" (x::(y::nil))) (tnum(n+m))
| PROC_sub : forall x y n m,
    x = tnum n ->
    y = tnum m ->
    procStep (proc "-" (x::(y::nil))) (tnum(n-m))
| PROC_mult : forall x y n m,
    x = tnum n ->
    y = tnum m ->
    procStep (proc "*" (x:: (y::nil))) (tnum(n*m))
| PROC_band : forall x y a b,
    x = tbool a ->
    y = tbool b ->
    procStep (proc "band" (x::(y::nil))) (tbool (andb a b))
| PROC_bor : forall x y a b,
    x = tbool a ->
    y = tbool b ->
    procStep (proc "bor" (x::(y::nil))) (tbool (orb a b))
| PROC_bnot : forall x a ,
    x = tbool a ->
    procStep (proc "bor" (x::nil)) (tbool (negb a)).
(**
   This function will reduce lists of terms to values (hopefully)
   small step.
 *)
(**
   These next two definitions are shamelessy borrowed from
   Software Foundations SmallStep.v. To allow me to define a
   Multistep reduction easily.
 *)


(**
   Here we have our relation that defines a small step semantics.
   Currently handles:
   - All normal Lambda calculus application rules
   - Added If statements that worked with the constant  booleans.
   - Two procedure rules:
      + The first takes a list of values and a procedure name and
      converts the procedure into a satisfying term.
      + The second reduces a list of terms into a list of values. This
      is to make sure that all code that makes it to the procedure phase
      can actually be run by my procedure code.
 *)
Reserved Notation "t1 '==>' t2" (at level 40).
Inductive step : term -> term -> Prop :=
| ISWIM_App_Abs : forall x t1 v2,
    value v2 ->
    (tapp (tabs x t1) v2) ==> ([x:=v2]t1)
| ISWIM_APP_1 : forall t1 t1' t2,
    t1 ==> t1' ->
    (tapp t1 t2) ==> (tapp t1' t2)
| ISWIM_APP_2 : forall v1 t2 t2',
    value v1 -> 
    t2 ==> t2' ->
    (tapp v1 t2) ==> (tapp v1 t2')
| ISWIM_If_True : forall v1 t1 t2,
    value v1 ->
    v1 = (tbool true) ->
    (tif v1 t1 t2) ==> t1
| ISWIM_If_False: forall v1 t1 t2,
    value v1 ->
    v1 =(tbool false) ->
    (tif v1 t1 t2 ) ==> t2
| ISWIM_If_Abs: forall t1 t1' t2 t3,
    t1 ==> t1' -> 
    (tif t1 t2 t3 ) ==> (tif t1' t2 t3)
| ISWIM_Proc_Abs : forall vs name term,
    list_of_values vs ->
    def_proc name ->
    procStep (proc name vs) term ->
    (tproc (proc name vs)) ==> term
| ISWIM_Proc_App : forall  vs ts name,
    def_proc name ->
    reduceList ts vs ->
    (tproc (proc name ts)) ==> (tproc (proc name vs))
with
reduceList : list term -> list term -> Prop :=
| emptyList :
    reduceList [] []
| reducedTerm : forall v ts  xs,
    value v ->
    reduceList xs ts ->
    reduceList (v::xs) (v::ts)
| reduceTerm : forall  t ts x xs,
    x ==> t ->
    reduceList xs ts ->
    reduceList (x::xs) (t::ts)
where "t1 '==>' t2" := (step t1 t2).
(**
   Here added multi step. Again shamelessly borrowed from Software Foundations.
 *)
Hint Constructors step.
Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(**
   This first example just adds a constant by one.
 *)
Lemma proc_example1 :
  (tproc (proc "add1" [(tnum 5)])) ==>* (tnum 6).
Proof.
  eapply multi_step.
  apply ISWIM_Proc_Abs.
  - unfold list_of_values. split.
    constructor. constructor.
  - constructor.
  - apply PROC_Add1 with (x := (tnum 5)) .
    + simpl. reflexivity.
  - simpl. constructor.
Qed.

(**
 This next example takes two constants and multiplies them together
 *)
Lemma proc_example2 :
  (tproc (proc "*" [(tnum 2);(tnum 3)])) ==>* (tnum 6).
Proof.
  eapply multi_step.
  apply ISWIM_Proc_Abs.
  - repeat constructor.
  - constructor.
  - eapply PROC_mult.
    + simpl. reflexivity.
    + reflexivity.
  - simpl. constructor.
Qed.

(**
   This code tests reduction of the list of values. This takes a very simple
   Lambda function (\x.x) and applies it with a constant so it just returns the
   constant. 
 *)

Lemma proc_example3 :
  (tproc (proc "add1" [(tapp (tabs "x" (tvar "x")) (tnum 2))])) ==>* (tnum 3).
Proof.
  eapply multi_step.
  apply ISWIM_Proc_App.
  - constructor.
  - apply reduceTerm.
    + constructor. constructor.
    + constructor.
  - simpl. eapply multi_step.
    + constructor.
      * constructor. constructor. constructor.
      * constructor.
      * eapply PROC_Add1. constructor.
    + simpl. constructor.
Qed. 

(**
   This example is basically true /\ (iszero 1). Which returns false.
   Proving this example with multistep actually fixed a lot of bugs and
   ambiguitities in my implementation of step.
 *)
Lemma proc_example4 :
 (tproc (proc "band" [(tbool true);(tproc (proc "iszero" [(tnum 1)]))])) ==>* (tbool false).
Proof.
  eapply multi_step.
  apply ISWIM_Proc_App.
  - constructor.
  - try constructor; simpl. constructor.
    apply reduceTerm. try constructor; simpl.
    constructor. constructor. constructor.
    constructor. econstructor. constructor. constructor.
    constructor.
  - simpl. eapply multi_step.
    repeat constructor; simpl.
    simpl. constructor.
Qed.

(** The issue with adding arbitrary procedures is now we have very trivial
    stuck terms like this. Here we have a procedure named
    foo which doesn't actually exist in our language. If we actually
    were to attemp to prove this with multistep we wouldn't be able to get too far.
 *)

Definition stuck (t : term) : Prop :=
  (normal_form step t) /\ not (value t).

Example stuck_term : exists t, stuck t.
Proof.
  exists (tproc (proc "foo" [])). split.
  - unfold normal_form. intros F. destruct F.
    inversion H; subst. inversion H3; subst.
    inversion H2; subst.
  - intros F. inversion F.
Qed.

End Attempt1.

(**
   Now we are going to be smarter about the design of how we add procedures
   and while we are at it we are going to add Types to this language!
   Also a bunch of other stuff. The goal I wanted to achieve with this final
   project was to learn what is to get some practice with the stuff we learned
   in class. That attempt above was just me naively defining some things. 
 *)

Module Attempt2.

  Inductive type : Type :=
  | Unit : type
  | Bool : type
  | Nat : type
  | Arrow : type -> type -> type
  | List : type -> type
  | Prod : type -> type -> type.
(**
   This time instead of adding procedues and a weird coinductive type we are
   going to add the them into the terms of our language. This is going to
   lead to their being a lot of terms but it will simplify the step relation
   GREATLY.

   Also my original project was to do something similar to Scheme so I'm going
   to add some minor extensions so that I can get a little closer to that goal.
   Fixpoints, let bindings, pairs and of course Lists!
 *)
  Inductive term : Type :=
  (* Constants *)
  | tnum : nat -> term
  | tbool : bool -> term
  (* Base Lambda Calc*)
  | tvar : string -> term
  | tapp : term -> term -> term
  | tabs : string -> type -> term -> term
  (* If statement *)
  | tif : term -> term -> term -> term
  (*Lots of very basic procedures *)
  | tadd1 : term -> term
  | tsub1 : term -> term
  | tiszero : term -> term
  | tplus : term -> term -> term
  | tsub : term -> term -> term
  | tmul : term -> term -> term
  | tor : term -> term -> term
  | tand : term -> term -> term
  | tnot : term -> term
  (* Product Types*)
  | tpair : term -> term -> term
  | tfst : term -> term
  | tsnd : term -> term
  (* List constructors*)
  | tnil : type -> term
  | tcons : term -> term -> term
  | tlcase : term -> term -> string -> string -> term -> term
  (* Let bindings*)
  | tlet : string -> term -> term -> term
  (*Fixpoints!*)
  | tfix : term -> term
  | tunit : term (*Unit to allow sequencing*)
  | tsequence : term -> term -> term. (*Added sequencing but need state to make it work.*)

  (**
     Values are free variables, the constants we are adding to our language,
   and abstractions are also values.
   *)
  Inductive value : term -> Prop :=
  | v_var : forall s,
      value (tvar s)
  | v_num: forall v,
      value (tnum v)
  | v_bool : forall v,
      value (tbool v)
  | v_abs : forall s T t,
      value (tabs s T t)
  | v_nil : forall T,
      value (tnil T)
  | v_cons : forall v1 v2,
      value v1 -> value v2 -> value (tcons v1 v2)
  | v_pair : forall v1 v2,
      value v1 -> value v2 -> value (tpair v1 v2)
  | v_unit :
      value (tunit).
Hint Constructors value.
  (**
     Now we have to define subsitution, steps, and typing for all this!
     This is going to be a lot of typing
   *)
Reserved Notation "'[' x ':=' s ']' t" (at level 20).
Fixpoint subst (x:string) (s:term) (t:term) : term :=
  match t with
  | tbool x => tbool x
  | tnum x => tnum x
  | tvar x' =>
      if eqb x x' then s else t
  | tabs x' T t1 =>
      tabs x' T (if eqb x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 => tapp ([x:=s] t1) ([x:=s] t2)
  | tif t1 t2 t3 => tif ([x:=s]t1) ([x:=s]t2) ([x:=s]t3)
  | tadd1 t => tadd1 ([x:=s] t)
  | tsub1 t => tsub1 ([x:=s] t)
  | tiszero t => tiszero ([x:=s] t)
  | tplus t1 t2 => tplus ([x:=s] t1) ([x:=s] t2)
  | tsub t1 t2 => tsub([x:=s] t1) ([x:=s] t2)
  | tmul t1 t2 => tmul ([x:=s] t1) ([x:=s] t2)
  | tor t1 t2 => tor ([x:=s] t1) ([x:=s] t2)
  | tand t1 t2 => tand ([x:=s] t1) ([x:=s] t2)
  | tnot t => tnot ([x:=s] t) 
  | tpair t1 t2 => tpair ([x:=s] t1) ([x:=s] t2)
  | tfst t => tfst ([x:=s] t)
  | tsnd t => tsnd ([x:=s] t)
  | tnil T => tnil T
  | tcons t1 t2 => tcons ([x:=s] t1) ([x:=s] t2)
  | tlcase t1 t2 x1 x2 t3 =>
    tlcase ([x:=s] t1) ([x:=s] t2) x1 x2
           (if String.eqb x1 x then t3
            else if String.eqb x2 x then t3
                 else ([x:=s] t3))
  | tlet x1 t1 t2 =>
    tlet x1 (if String.eqb x1 x then t1 else ([x:=s]t1))
         (if String.eqb x1 x then t2 else ([x:=s]t2))
  | tfix t1 => ([x:=s] t1)
  | tunit => tunit
  | tsequence t1 t2 => tsequence ([x:=s]t1) ([x:=s]t2)
  end
where "'[' x ':=' s ']' t" := (subst x s t).


Reserved Notation "t1 '==>' t2" (at level 40).
Inductive step : term -> term -> Prop :=
| ISWIM_App_Abs : forall x t1 T v2,
    value v2 ->
    (tapp (tabs x T t1) v2) ==> ([x:=v2]t1)
| ISWIM_APP_1 : forall t1 t1' t2,
    t1 ==> t1' ->
    (tapp t1 t2) ==> (tapp t1' t2)
| ISWIM_APP_2 : forall v1 t2 t2',
    value v1 -> 
    t2 ==> t2' ->
    (tapp v1 t2) ==> (tapp v1 t2')
| ISWIM_If_True : forall v1 t1 t2,
    value v1 ->
    v1 = (tbool true) ->
    (tif v1 t1 t2) ==> t1
| ISWIM_If_False: forall v1 t1 t2,
    value v1 ->
    v1 = (tbool false) ->
    (tif v1 t1 t2 ) ==> t2
| ISWIM_If_Abs: forall t1 t1' t2 t3,
    t1 ==> t1' -> 
    (tif t1 t2 t3 ) ==> (tif t1' t2 t3)
(* Here Comes A LOT of procedure definitions!*)
| ISWIM_Add1_value : forall n,
  (tadd1 (tnum n)) ==> (tnum (n+1))
| ISWIM_Add1_Abs : forall t t',
    t ==> t' ->
    (tadd1 t) ==> (tadd1 t')
| ISWIM_Sub1_value : forall n,
  (tsub1 (tnum n)) ==> (tnum (n-1))
| ISWIM_Sub1_Abs : forall t t',
    t ==> t' ->
    (tsub1 t) ==> (tsub1 t')
| ISWIM_Iszero_value : forall n,
  (tiszero (tnum n)) ==> (tbool (Nat.eqb n 0 ))
| ISWIM_Iszero_Abs : forall t t',
    t ==> t' ->
    (tiszero t) ==> (tiszero t')
| ISWIM_Plus_Abs : forall n1 n2,
    (tplus (tnum n1) (tnum n2)) ==> (tnum (n1+n2))
| ISWIM_Plus_App1 : forall t1 t1' t2,
    t1 ==> t1' ->
    (tplus t1 t2) ==> (tplus t1' t2)
| ISWIM_Plus_App2 : forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    (tplus v1 t2) ==> (tplus v1 t2')
| ISWIM_Sub_Abs : forall n1 n2,
    (tsub (tnum n1) (tnum n2)) ==> (tnum (n1-n2))
| ISWIM_Sub_App1 : forall t1 t1' t2,
    t1 ==> t1' ->
    (tsub t1 t2) ==> (tsub t1' t2)
| ISWIM_Sub_App2 : forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    (tsub v1 t2) ==> (tsub v1 t2')
| ISWIM_Mul_Abs : forall n1 n2,
    (tmul (tnum n1) (tnum n2)) ==> (tnum (n1*n2))
| ISWIM_Mul_App1 : forall t1 t1' t2,
    t1 ==> t1' ->
    (tmul t1 t2) ==> (tmul t1' t2)
| ISWIM_Mul_App2 : forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    (tmul v1 t2) ==> (tmul v1 t2')
| ISWIM_Or_Abs : forall b1 b2,
    (tor (tbool b1) (tbool b2)) ==> (tbool (orb b1 b2))
| ISWIM_Or_App1 : forall t1 t1' t2,
    t1 ==> t1' ->
    (tor t1 t2) ==> (tor t1' t2)
| ISWIM_Or_App2 : forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    (tor v1 t2) ==> (tor v1 t2')
| ISWIM_And_Abs : forall b1 b2,
    (tand (tbool b1) (tbool b2)) ==> (tbool (andb b1 b2))
| ISWIM_And_App1 : forall t1 t1' t2,
    t1 ==> t1' ->
    (tand t1 t2) ==> (tand t1' t2)
| ISWIM_And_App2 : forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    (tand v1 t2) ==> (tand v1 t2')
| ISWIM_Not_Abs : forall b,
    (tnot (tbool b) ) ==> (tbool (negb b))
| ISWIM_Not_App1 : forall t1 t1' ,
    t1 ==> t1' ->
    (tnot t1) ==> (tnot t1')
(* Now comes the other things we added. First Pairs.*)
| ISWIM_Pair1 : forall t1 t1' t2,
    t1 ==> t1' ->
    (tpair t1 t2) ==> (tpair t1' t2)
| ISWIM_Pair2 : forall v1 t2 t2',
    value v1 -> 
    t2 ==> t2' ->
    (tpair v1 t2) ==> (tpair v1 t2')
| ISWIM_Fst_Abs : forall v1 v2,
    value v1 ->
    value v2 ->
    (tfst (tpair v1 v2)) ==> v1
| ISWIM_Fst_App : forall t1 t1',
    t1 ==> t1' ->
    (tfst t1) ==> (tfst t1')
| ISWIM_Snd_Abs : forall v1 v2,
    value v1 ->
    value v2 ->
    (tsnd (tpair v1 v2)) ==> v2
| ISWIM_Snd_App : forall t1 t1',
    t1 ==> t1' ->
    (tsnd t1) ==> (tsnd t1')
(*Lists are now coming up*)
| ISWIM_Cons_App1 : forall t1 t1' t2,
    t1 ==> t1' ->
    (tcons t1 t2) ==> (tcons t1' t2)
| ISWIM_Cons_App2 : forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    (tcons v1 t2) ==> (tcons v1 t2')
| ISWIM_Case_App1 : forall t1 t1' t2 x1 x2 t3,
    t1 ==> t1' ->
    (tlcase t1 t2 x1 x2 t3) ==> (tlcase t1' t2 x1 x2 t3)
| ISWIM_Case_App2 : forall T t2 x1 x2 t3,
    (tlcase (tnil T) t2 x1 x2 t3) ==> t2
| ISWIM_Case_App3 : forall v1 v2 t2 x1 x2 t3,
    value v1 ->
    value v2 ->
    (tlcase (tcons v1 v2) t2 x1 x2 t3) ==> ([x1:=v1]([x2:=v2]t3))
| ISWIM_Let_Abs : forall x v t,
    value v ->
    (tlet x v t) ==> ([x:=v]t)
| ISWIM_Let_App : forall x t1 t1' t2,
    t1 ==> t1' ->
    (tlet x t1 t2) ==> (tlet x t1' t2)
| ISWIM_Fixpoint_Abs : forall x1 T t1,
    (tfix (tabs x1 T t1)) ==> [x1:= (tfix (tabs x1 T t1))] t1
| ISWIM_Fixpoint_App : forall t1 t1',
    (tfix t1) ==> (tfix t1')
| ISWIM_Sequence_Abs : forall v1 t2 ,
    value v1 -> 
    (tsequence v1 t2) ==> t2
| ISWIM_Sequence_Convert : forall t1 t1' t2 ,
    t1 ==> t1' ->
    (tsequence t1 t2) ==> (tsequence t1' t2)
where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.
Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).
Hint Constructors multi.

Definition context := partial_map type.

Reserved Notation "Gamma '|-' t '∈' T" (at level 40).

Inductive has_type : context -> term -> type -> Prop :=
| T_Unit : forall Gamma,
    Gamma |- (tunit) ∈ Unit
| T_Num : forall Gamma n,
    Gamma |- (tnum n) ∈ Nat
| T_Bool: forall Gamma b,
    Gamma |- (tbool b) ∈ Bool
| T_Var : forall Gamma x T,
    Gamma x = Some T -> 
    Gamma |- (tvar x) ∈ T
| T_Abs : forall Gamma x T1 t T2,
    (update Gamma x T1) |- t ∈ T2 ->
    Gamma |- (tabs x T1 t) ∈ (Arrow T1 T2)
| T_App : forall T1 T2 Gamma t1 t2,
    Gamma |- t1 ∈ Arrow T1 T2 ->
    Gamma |- t2 ∈ T1 ->
    Gamma |-(tapp t1 t2) ∈T2
| T_Add1 : forall Gamma t1,
    Gamma |- t1 ∈ Nat ->
    Gamma |- (tadd1 t1) ∈ Nat
| T_Sub1 : forall Gamma t1,
    Gamma |- t1 ∈ Nat ->
    Gamma |- (tsub1 t1) ∈ Nat
| T_IsZero : forall Gamma t1,
    Gamma |- t1 ∈ Nat ->
    Gamma |- (tiszero t1) ∈ Bool
| T_Plus : forall Gamma t1 t2,
    Gamma |- t1 ∈ Nat ->
    Gamma |- t2 ∈ Nat ->
    Gamma |- (tplus t1 t2) ∈ Nat
| T_Sub : forall Gamma t1 t2,
    Gamma |- t1 ∈ Nat ->
    Gamma |- t2 ∈ Nat ->
    Gamma |- (tsub t1 t2) ∈ Nat
| T_Mul : forall Gamma t1 t2,
    Gamma |- t1 ∈ Nat ->
    Gamma |- t2 ∈ Nat ->
    Gamma |- (tmul t1 t2) ∈ Nat
| T_Or : forall Gamma t1 t2,
    Gamma |- t1 ∈ Bool->
    Gamma |- t2 ∈ Bool ->
    Gamma |- (tor t1 t2) ∈ Bool 
| T_And : forall Gamma t1 t2,
    Gamma |- t1 ∈ Bool->
    Gamma |- t2 ∈ Bool ->
    Gamma |- (tand t1 t2) ∈ Bool
| T_Not : forall Gamma t,
    Gamma |- t ∈ Bool->
    Gamma |- (tnot t) ∈ Bool
| T_Pair : forall Gamma t1 t2 T1 T2,
    Gamma |- t1 ∈ T1 ->
    Gamma |- t2 ∈ T2 ->
    Gamma |- (tpair t1 t2) ∈ Prod T1 T2
| T_Fst : forall Gamma t1 T1 T2,
    Gamma |- t1 ∈ Prod T1 T2 ->
    Gamma |- (tfst t1) ∈ T1
| T_Snd : forall Gamma t1 T1 T2,
    Gamma |- t1 ∈ Prod T1 T2 ->
    Gamma |- (tsnd t1) ∈ T2
| T_Nil : forall Gamma T,
    Gamma |- (tnil T) ∈ List T
| T_Cons : forall Gamma t1 t2 T,
    Gamma |- t1 ∈ T ->
    Gamma |- t2 ∈ (List T) ->
    Gamma |- (tcons t1 t2) ∈ (List T)
| T_LCase : forall Gamma t1 t2 x1 x2 t3 T1 T2,
    Gamma |- t1 ∈ List T1  ->
    Gamma |- t2 ∈ T2 ->
    (update (update Gamma x1 T1) x2 (List T1)) |- t3 ∈ T2 ->
    Gamma |- (tlcase t1 t2 x1 x2 t3) ∈ T2
| T_Let : forall Gamma x t1 T1 t2 T2,
    Gamma |- t1 ∈ T1 ->
    (update Gamma x T1) |- t2 ∈ T2 ->
    Gamma |- (tlet x t1 t2) ∈ T2
| T_Fix : forall Gamma t1 T,
    Gamma |- t1 ∈ (Arrow T T) ->
    Gamma |- (tfix t1) ∈ T
| T_Seq : forall Gamma t1 t2 T1 T2,
    Gamma |- t1 ∈ T1 ->
    Gamma |- t2 ∈ T2 ->
    Gamma |- (tsequence t1 t2) ∈ T2
where "Gamma '|-' t '∈' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* So now that we have all of these relations. Let's mess around with it a bit*)
(*The following is a lot of stupid sanity checks.*)

Example typechecking1 :
  empty |- (tnum 1) ∈ Nat.
Proof. auto. Qed.

Example typechecking2 :
  empty |- (tadd1 (tnum 2)) ∈ Nat.
Proof. auto. Qed.

Example typechecking3 :
  empty |- (tpair (tor (tbool true) (tbool false))
                 (tsub1 (tnum 3))) ∈ Prod Bool Nat.
Proof. auto. Qed.

Example typechecking4 :
  empty |- (tplus (tnum 2) (tnum 100)) ∈ Nat.
Proof. auto. Qed.

Example code1 :
  (tlet "x" (tnum 2) (tadd1 (tvar "x"))) ==>* (tnum 3).
Proof.
  eapply multi_step. eauto. simpl. eapply multi_step.
  eauto. simpl. eapply multi_refl.
Qed.

Theorem progress : forall t T,
    empty |- t ∈ T ->
    value t \/ exists t', t ==> t'.
Proof with auto.
  intros.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction H; intros; subst.
  - try (left; constructor).
  - try (left; constructor).
  - try (left; constructor).
  - try (left; constructor).
  - try (left; constructor).
  - right. destruct IHhas_type1; subst...
    + destruct IHhas_type2; subst...
      inversion H; subst; try solve_by_inverts 2.
      exists (subst x t2 t)...
      inversion H2; subst. exists (tapp t1 x)...
    + inversion H1; subst. exists (tapp x t2)...
  - right. destruct IHhas_type; subst...
    inversion H; subst; try solve_by_inverts 2.
    exists (tnum (n+1))...
    inversion H0; subst. exists (tadd1 x)...
  - right. destruct IHhas_type; subst...
    inversion H; subst; try solve_by_inverts 2.
    exists (tnum (n-1))... inversion H0;subst. exists(tsub1 x)...
  - right. destruct IHhas_type; subst...
    inversion H; subst; try solve_by_inverts 2.
    induction n. exists (tbool true)... constructor.
    exists (tbool false). constructor.
    inversion H0; subst. exists(tiszero x)...
  - right. destruct IHhas_type1; subst...
    destruct IHhas_type2; subst...
    inversion H; subst; try solve_by_inverts 2.
    inversion H0; subst; try solve_by_inverts 2.
    exists (tnum (n+n0))...
    inversion H2; subst. exists (tplus t1 x)...
    inversion H1; subst. exists (tplus x t2)...
  - right. destruct IHhas_type1; subst...
    destruct IHhas_type2; subst...
    inversion H; subst; try solve_by_inverts 2.
    inversion H0; subst; try solve_by_inverts 2.
    exists (tnum (n-n0))...
    inversion H2; subst. exists (tsub t1 x)...
    inversion H1; subst. exists (tsub x t2)...
  - right. destruct IHhas_type1; subst...
    destruct IHhas_type2; subst...
    inversion H; subst; try solve_by_inverts 2.
    inversion H0; subst; try solve_by_inverts 2.
    exists (tnum (n*n0))...
    inversion H2; subst. exists (tmul t1 x)...
    inversion H1; subst. exists (tmul x t2)...
 - right. destruct IHhas_type1; subst...
    destruct IHhas_type2; subst...
    inversion H; subst; try solve_by_inverts 2.
    inversion H0; subst; try solve_by_inverts 2.
    inversion H1; subst.
    exists (tbool (orb b b0))...
    inversion H2; subst. exists (tor t1 x)...
    inversion H1; subst. exists (tor x t2)...
 - right. destruct IHhas_type1; subst...
   destruct IHhas_type2; subst...
    inversion H; subst; try solve_by_inverts 2.
    inversion H0; subst; try solve_by_inverts 2.
    inversion H1; subst.
    exists (tbool (andb b b0))...
    inversion H2; subst. exists (tand t1 x)...
    inversion H1; subst. exists (tand x t2)...
 - right. destruct IHhas_type; subst...
   inversion H; subst; try solve_by_inverts 2.
   destruct b. exists (tbool false)... constructor.
   exists (tbool true)... constructor.
   inversion H0; subst.  exists(tnot x)...
 - destruct IHhas_type1...
   destruct IHhas_type2...
   + inversion H2; subst. right. exists (tpair t1 x)...
   + inversion H1; subst. right. exists (tpair x t2)...
 - destruct IHhas_type...
   inversion H; subst; try solve_by_inverts 2.
   inversion H0; subst; try solve_by_inverts 2.
   right. exists (t0)...
   inversion H0; subst. right. exists (tfst x)...
 - destruct IHhas_type...
   inversion H; subst; try solve_by_inverts 2.
   inversion H0; subst; try solve_by_inverts 2.
   right. exists (t2)...
   inversion H0; subst. right. exists (tsnd x)...
 - left. constructor.
 - destruct IHhas_type1...
   destruct IHhas_type2...
   inversion H2; subst.
   right. exists (tcons t1 x)...
   inversion H1; subst. right. exists( tcons x t2)...
 - right.
   destruct IHhas_type1...
   + inversion H; subst; try solve_by_inverts 2.
     * exists t2...
     * exists ([x1:=t0]([x2:= t4]t3))...
       inversion H2; subst; try solve_by_inverts 2.
       constructor...
   + inversion H2; subst.
     exists (tlcase x t2 x1 x2 t3)...
 - right.
   destruct IHhas_type1...
   exists([x:=t1]t2)...
   inversion H1;subst.  exists(tlet x x0 t2)...
 - right.
   destruct IHhas_type...
   inversion H0; subst; try solve_by_inverts 2.
   exists ([s:= (tfix (tabs s T0 t))] t)...
   inversion H0; subst. exists (tfix x)...
 - destruct IHhas_type1...
   + right. exists(t2)...
   + right. inversion H1;subst.
     exists(tsequence x t2)...
Qed.

(**
   Okay, I'm going to try to show that there is a term in this language that
   does not halt.
 *)
Definition halts (t:term) : Prop := exists t', t ==>* t' /\ value t'. 

Theorem does_not_normalize : exists t T, (has_type empty t T /\ not (halts t)).
Proof with auto.
  exists (tfix (tabs "f" (Arrow Nat Nat) (tabs "x" Nat (tplus (tnum 1) (tapp (tvar "f" )(tvar "x")))))).
  exists (Arrow Nat Nat).
  split.
  - repeat econstructor.
  - intros F. unfold halts in F.
    induction F; inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    + inversion H1.
    + inversion H2; subst. induction H1; subst; try solve_by_inverts 2.
      * inversion H2; subst; try solve_by_inverts 1.
End Attempt2.