(** *ISWIM: An extension of the Lambda Calculus*)
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
  Here we define our new constants as a Type. Currently it's just booleans and
  natural numbers but this can be extended with other primitive values. 
 *)
Inductive constant : Type :=
| bnum : nat -> constant
| bbool : bool -> constant.

(**
   Here are the terms of our language. The first three terms are from the
   regular lambda calclus. However we now have new terms for constants and for
   procedures. Procedures are the built in functions of this ISWIM programming
   language. We will soon define some built in procedures.

   The goal of defining it this way is to make it easier to define procedures
   If you want to attempt to add some go ahead! You need to add it to the
   def_proc type and also add it's actuall implementation to the
   inductive relation above relation.
 *)
Inductive term : Type :=
| tvar : string -> term
| tapp : term -> term -> term
| tabs : string -> term -> term
| tconst : constant -> term
| tproc : procedure -> term 
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
| v_const : forall v,
    value (tconst v)
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
    def_proc ("*").

Fixpoint list_of_values (l:list term): Prop :=
  match l with
  | nil => True
  | x :: xs => (value x) /\ list_of_values xs
  end.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).
Fixpoint subst (x:string) (s:term) (t:term) : term :=
  match t with
  | tvar x' =>
      if eqb x x' then s else t
  | tabs x' t1 =>
      tabs x' (if eqb x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 =>
    tapp ([x:=s] t1) ([x:=s] t2)
  | tconst x => tconst x
  | tproc p => match p with
              | p => match p with
                    | proc x ts => tproc (proc x (map (subst x s) ts))
                    end
              end
  end
where "'[' x ':=' s ']' t" := (subst x s t).

Open Scope list_scope.
Inductive procStep : procedure -> term -> Prop :=
| PROC_Add1 : forall x n ts,
    1 = length ts ->
    In x ts -> 
    x = tconst (bnum n) -> 
    procStep (proc "add1" ts) ((tconst (bnum (n+1))))
| PROC_Sub1 : forall x n ts,
    1 = length ts ->
    In x ts -> 
    x = tconst (bnum n) -> 
    procStep (proc "sub1" ts) ((tconst (bnum (n-1))))
| PROC_Iszero : forall ts x n y,
    1 = length ts ->
    In x ts ->
    x = tconst(bnum n) ->
    y = (if Nat.eqb n 0 then true else false) -> 
    procStep (proc "iszero" ts) ((tconst (bbool y)))
| PROC_add : forall ts x y n m,
    2 = length ts ->
    In x ts /\ In y ts ->
    x = tconst(bnum n) ->
    y = tconst(bnum m) ->
    procStep (proc "+" ts) (tconst(bnum(n+m)))
| PROC_sub : forall ts x y n m,
    2 = length ts ->
    In x ts /\ In y ts ->
    x = tconst(bnum n) ->
    y = tconst(bnum m) ->
    procStep (proc "-" ts) (tconst(bnum(n-m)))
| PROC_mult : forall ts x y n m,
    2 = length ts ->
    In x ts /\ In y ts ->
    x = tconst(bnum n) ->
    y = tconst(bnum m) ->
    procStep (proc "*" ts) (tconst(bnum(n*m))).
(**
   This function will reduce lists of terms to values (hopefully)
   small step.
 *)
(**
   These next two definitions are shamelessy borrowed from
   Software Foundations SmallStep.v
 *)
Definition relation (X: Type) := X -> X -> Prop.
Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

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
| reduceTerm : forall  t ts x xs,
    x ==> t ->
    reduceList xs ts -> 
    reduceList (x::xs) (t::ts)
where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.
Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Lemma proc_example1 :
  (tproc (proc "add1" [(tconst (bnum 5))])) ==>* (tconst (bnum 6)).
Proof.
  eapply multi_step.
  apply ISWIM_Proc_Abs.
  - unfold list_of_values. split.
    constructor. constructor.
  - constructor.
  - apply PROC_Add1 with (x := tconst(bnum 5)) .
    + simpl. reflexivity.
    + simpl. left. reflexivity.
    + reflexivity.
  - simpl. constructor.
Qed.

Lemma proc_example2 :
  (tproc (proc "*" [(tconst (bnum 2));(tconst (bnum 3))])) ==>* (tconst (bnum 6)).
Proof.
  eapply multi_step.
  apply ISWIM_Proc_Abs.
  - repeat constructor.
  - constructor.
  - eapply PROC_mult.
    + simpl. reflexivity.
    + split.
      * simpl. left. reflexivity.
      * simpl. right. left. reflexivity.
    + reflexivity.
    + reflexivity.
  - simpl. constructor.
Qed.

Lemma proc_example3 :
  (tproc (proc "add1" [(tapp (tabs "x" (tvar "x")) (tconst (bnum 2)))])) ==>* (tconst (bnum 3)).
Proof.
  eapply multi_step.
  apply ISWIM_Proc_App.
  - constructor.
  - constructor.
    + constructor. constructor.
    + constructor.
  - simpl. eapply multi_step.
    + constructor.
      * repeat constructor.
      * constructor.
      * eapply PROC_Add1. simpl. constructor. constructor. reflexivity.
        reflexivity.
    + simpl. constructor.
Qed. 