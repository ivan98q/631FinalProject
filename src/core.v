(** *ISWIM: Lots of extensions to the Lambda Calculus*)
(**
   Author : Ivan Quiles
   Note:
   There is  borrowed material from the Software Foundations
   Textbook series. Mainly STLC.v and SmallStep.v
 *)

(** 
  ISWIM is an extension of the Lambda Calculus with both primitive values and
 primitive operations. So now we need a second concept of reduction where we handle
 turning these primitive operations into actual values in our Lambda Calculus.
 *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Init.Datatypes.


(**
   Here are the terms of our language. The first three terms are from the
   regular lambda calculus. However we now have new terms for constants and for
   procedures. Procedures are the built in functions of this ISWIM programming
   language. We will soon define some built in procedures.

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
   This relation is used in the small step reduction of ISWIM below.
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
Definition relation (X: Type) := X -> X -> Prop.
Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

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

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  not (exists t', R t t').

(**
   Small Lemma to show that values cannot be reduced any further.
 *)
Lemma value_is_nf : forall v, value v -> normal_form step v.
Proof.
  intros. unfold normal_form. intros F.
  induction H; destruct F;inversion H.
Qed.
