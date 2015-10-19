Require Export SfLib.

Import SfLibmod.

(*Source Language: STLC + notions of program, ownership, code base*)
(*
Assumptions: 
1- code_bases map function names to closed lambda abstractions
   it is reflected in two places: in defining substitution [x:=s]t
   and in appear_free_in x t.
   Such an assuumption is declared in well-formed codebases!
2- levels of owners are assumed to be in a total order relation,
   rather that a partial order, for simplicity.
*)


(* 
types      
T ::= Unit | T -> T 
*)

Inductive ty : Type :=
  | TUnit : ty
  | TArrow : ty -> ty -> ty.

(*
terms:
t ::= x | f | \x:T.t | tt | unit | t;t
where x ranges over ordinary variable identifiers (id),
      f ranges over function name identifiers (fid).
*)


Inductive tm : Type :=
  | tvar : id -> tm
  | tfname : fid -> tm
  | tabs : id -> ty -> tm -> tm
  | tapp : tm -> tm -> tm
  | tunit : tm
  | tseq : tm -> tm -> tm.

Notation "t1 ';' t2" := (tseq t1 t2) (at level 15).


(*
values defined as propositions over terms:
v ::= f | \x:T.t | unit
*)

Inductive value: tm -> Prop :=
  | v_fname: forall (f: fid), value (tfname f)
  | v_abs : forall (x: id) (T: ty) (t: tm), value (tabs x T t)
  | v_unit : value tunit.

Hint Constructors value.


(*
Partial mappings: 
functions from identifiers (I) to some optial value of type A.
*)

Definition partial_map (I: Type) (A:Type) := I -> option A.

Definition empty  {I: Type} {A:Type} : partial_map I A := (fun _ => None). 

Definition extend_id {A:Type} (parMap : partial_map id A) 
                              (var:id) (val : A) :=
  fun var' => if eq_id_dec var var' then Some val else parMap var'.

Definition extend_fid {A:Type} 
                      (parMap : partial_map fid A) 
                      (fname: fid) 
                      (func : A) :=
  fun fname' => if eq_fid_dec fname fname' then 
                   Some func 
                else parMap fname'.



(*
Code base: 
Partial mapping from function names to terms:
C: fid -> option tm   (or, partial_map fid tm)
*)

Definition code_base : Type := partial_map fid tm.

(*
Programs: a triple of a term, an owner and a code base.
*)
Inductive prog : Type := 
   prg : tm -> ow -> code_base -> prog.

(*
lv: ow -> nat
gives the security level of the principal (owner).
*)
Definition lv (o: ow) : nat :=
  match o with
   OId m => m
  end.



(*=====================OPERATIONAL SEMANTICS============================*)

(* Substitution: [x:=s]t defined over terms *)

Reserved Notation " '[' x ':=' s ']' t " (at level 20).

Fixpoint subst (x: id) (s t: tm) : tm :=
  match t with
  | tvar y => if eq_id_dec x y then s else (tvar y)
  | tfname f => tfname f
  | tabs y T t' => if eq_id_dec x y then 
                      (tabs y T t') 
                   else tabs y T ([x:=s] t')
  | tapp t1 t2 => tapp ([x:=s] t1) ([x:=s] t2)
  | tunit => tunit
  | tseq t1 t2 => tseq ([x:=s] t1)([x:=s] t2)
  end
  where "'[' x ':=' s ']' t" := (subst x s t).


(*Definition trace_item := (option (nat * fid * tm)).*)


(*evaluation context:
  E ::= [] | Et | vE | E;t *)

Inductive eval_cntxt : Type :=
  | empty_ec : eval_cntxt
  | app1_ec  : eval_cntxt -> tm -> eval_cntxt
  | app2_ec  : tm -> eval_cntxt -> eval_cntxt
  | seq_ec   : eval_cntxt -> tm -> eval_cntxt.


(*slice*)

Inductive slice_prop : Type :=
  | Call_tr    : nat -> fid -> tm -> slice_prop
  | App_tr     : nat -> tm -> tm -> slice_prop
  | Seq_tr     : nat -> tm -> tm -> slice_prop
  | Context_tr : nat -> eval_cntxt -> slice_prop.


Definition slice := list slice_prop.




(* reduction single step:
   [pr]: t,n ==> t',n', slice
*)


Reserved Notation " '[' p ']:' p1 '==>' p2 " (at level 40).

Inductive step : prog -> (tm * nat) -> 
                         (tm * nat * slice) -> Prop :=
  | ST_AppAbs : forall (pr: prog) (x: id) (T: ty) (t v: tm) (n: nat),
                value v ->
                [pr]: (tapp (tabs x T t) v, n) ==> 
                      (subst x v t, n+1, (App_tr n (tabs x T t) v)::
                                         (Context_tr n empty_ec)::nil)
  | ST_AppFId : forall (tp: tm) (o: ow) (C: code_base) (f: fid) 
                       (x: id) (T: ty) (t v: tm) (n: nat),
                value v ->
                C f = Some (tabs x T t) ->
                [prg tp o C]: (tapp (tfname f) v, n) ==> 
                              (subst x v t, n+1, (Call_tr n f v)::
                                                 (Context_tr n empty_ec)::nil)
  | ST_App1   : forall (pr: prog) (t1 t1' t2: tm) (n n': nat)
                       (p: slice_prop) (E: eval_cntxt),
                [pr]: (t1, n) ==> (t1', n', p::(Context_tr n E)::nil) ->
                [pr]: (tapp t1 t2, n) ==> 
                      (tapp t1' t2, n', p::(Context_tr n (app1_ec E t2))::nil)
  | ST_App2   : forall (pr: prog) (v t2 t2': tm) (n n': nat)
                       (p: slice_prop) (E: eval_cntxt),
                value v ->
                [pr]: (t2, n) ==> (t2', n', p::(Context_tr n E)::nil) ->
                [pr]: (tapp v t2, n) ==> 
                      (tapp v t2', n', p::(Context_tr n (app2_ec v E))::nil)
  | ST_SeqUnit: forall (pr: prog) (t: tm) (n: nat),
                [pr]: (tseq tunit t, n) ==> 
                      (t, n, (Seq_tr n tunit t)::(Context_tr n empty_ec)::nil)
  | ST_Seq    : forall (pr: prog) (t1 t1' t2: tm) (n n': nat)
                       (p: slice_prop) (E: eval_cntxt),
                [pr]: (t1, n) ==> (t1', n', p::(Context_tr n E)::nil) ->
                [pr]: (tseq t1 t2, n) ==> 
                      (tseq t1' t2, n', p::(Context_tr n (seq_ec E t2))::nil)
  where "'[' pr ']:' p1 '==>' p2" := (step pr p1 p2).

Hint Constructors step.



Definition trace := list slice_prop.


(*reflexive transitive closure of single step reduction*)

Reserved Notation "'[' pr ']:' p1 '==>*' p2" (at level 40).

Inductive multistep : prog -> (tm * nat) ->
                      (tm * nat * trace) -> 
                      Prop :=
  | multi_refl: forall (pr: prog) (t: tm) (n: nat),
                [pr]: (t, n) ==>* (t, n, nil)
  | multi_step: forall (pr: prog) (t t' t'': tm) (n n' n'': nat)
                       (theta: slice) (Theta: trace),
                [pr]: (t, n) ==> (t', n', theta) ->
                [pr]: (t', n') ==>* (t'', n'', Theta) ->
                [pr]: (t, n) ==>* (t'', n'', (theta ++ Theta))
  where "'[' pr ']:' p1 '==>*' p2" := (multistep pr p1 p2).




(*=====================TYPING RULES================================*)

(* the notion free variables of a term: 
   function names and unit have no free variables.
*)

Inductive appears_free_in_term : id -> tm -> Prop :=
  | afi_var   : forall (x: id),
                appears_free_in_term x (tvar x)
  | afi_abs   : forall (x y: id) (T: ty) (t: tm),
                x <> y ->
                appears_free_in_term x t ->
                appears_free_in_term x (tabs y T t)
  | afi_app1  : forall (x: id) (t1 t2: tm),
                appears_free_in_term x t1 ->
                appears_free_in_term x (tapp t1 t2)
  | afi_app2  : forall (x: id) (t1 t2: tm),
                appears_free_in_term x t2 ->
                appears_free_in_term x (tapp t1 t2)
  | afi_seq1  : forall (x: id) (t1 t2: tm),
                appears_free_in_term x t1 ->
                appears_free_in_term x (tseq t1 t2)
  | afi_seq2  : forall (x: id) (t1 t2: tm),
                appears_free_in_term x t2 ->
                appears_free_in_term x (tseq t1 t2).


Hint Constructors appears_free_in_term.



(* the notion of closed terms *)

Definition closed_term (t: tm) : Prop :=
  ~ exists x: id, appears_free_in_term x t.


(* well-formedness of codebases: |= C *)

Reserved Notation "'|=' C" (at level 40).

Inductive wellformed_codebase: code_base -> Prop :=
  | wf_empty    : |= empty
  | wf_nonempty : forall (C: code_base) (f: fid) (t: tm),
                  |= C ->
                  C f = None -> 
                  closed_term t ->
                  |= (extend_fid C f t)
  where " '|=' C " :=  (wellformed_codebase C).


Lemma wellformed_closeness:
  forall (C: code_base) (f: fid) (t: tm),
  |= C -> C f = Some t -> closed_term t.

Proof.
  intros.
  generalize dependent t.
  generalize dependent f.
  induction H.
  Case "empty".
    intros.
    unfold empty in H0.
    inversion H0.
  Case "nonempty".
    intros.
    unfold extend_fid in H2.
    destruct (eq_fid_dec f f0).
    SCase "f = f0".
      inversion H2.
      subst.
      assumption.
    SCase "f != f0".
      apply IHwellformed_codebase with f0.
      assumption.
  Qed.



(* typing context for variable identifiers (Gamma ranges over it) *)
Definition context := partial_map id ty.


(*typing rules: in each |= of codebase is also added as a premise. *)
Reserved Notation " '[' pr ']:' Gamma '|-' p 'in' T " (at level 40).

Inductive has_type : prog -> context -> tm -> ty -> Prop :=
  | T_Var   : forall (tp: tm) (o: ow) (C: code_base) 
                     (Gamma: context) (x: id) (T: ty),
              |= C ->
              Gamma x = Some T ->
              [prg tp o C]: Gamma |- (tvar x) in T
  | T_FName : forall (tp: tm) (o: ow) (C: code_base)
                     (Gamma: context) (f: fid) (t: tm) (T1 T2: ty),
              C f = Some t ->
              [prg tp o C]: Gamma |- t in (TArrow T1 T2) ->
              [prg tp o C]: Gamma |- (tfname f) in (TArrow T1 T2)
  | T_Abs   : forall (pr: prog)
                     (Gamma: context) (x: id) (t: tm) (T1 T2: ty),
              [pr]: extend_id Gamma x T1 |- t in T2 ->
              [pr]: Gamma |- (tabs x T1 t) in (TArrow T1 T2)
  | T_App   : forall (pr: prog)
                     (Gamma: context) (t1 t2: tm) (T1 T2: ty),
              [pr]: Gamma |- t1 in (TArrow T1 T2) ->
              [pr]: Gamma |- t2 in T1 ->
              [pr]: Gamma |- (tapp t1 t2) in T2
  | T_Unit  : forall (tp: tm) (o: ow) (C: code_base)
                     (Gamma: context),
              |= C ->
              [prg tp o C]: Gamma |- tunit in TUnit
  | T_Seq   : forall (pr: prog)
                     (Gamma: context) (t1 t2: tm) (T: ty),
              [pr]: Gamma |- t1 in TUnit ->
              [pr]: Gamma |- t2 in T ->
              [pr]: Gamma |- tseq t1 t2 in T
  where " '[' pr ']:' Gamma '|-' p 'in' T " := (has_type pr Gamma p T).

Hint Constructors has_type.



(*=====================PROGRESS================================*)

Theorem progress:
  forall (pr: prog) (t: tm) (T: ty),
  [pr]: empty |- t in T -> 
  value t \/ exists t' n n' theta, [pr]: (t, n) ==> (t', n', theta).

Proof.
  Admitted.


(*=====================PRESERVATION================================*)

(* free variables are present in context*)

Lemma free_in_context:
  forall (x: id) (t: tm) (pr: prog) (Gamma: context) (T: ty),
  appears_free_in_term x t ->
  [pr]: Gamma |- t in T ->
  exists T': ty, Gamma x = Some T'.

Proof.
  Admitted.

Corollary typable_empty_closed:
  forall (pr: prog) (t: tm) (T: ty),
  [pr]: empty |- t in T ->
  closed_term t.

Proof.
  Admitted.


Lemma context_invariance:
  forall (Gamma Gamma': context) (pr: prog) (t: tm) (T: ty),
  [pr]: Gamma |- t in T ->
  (forall (x: id), appears_free_in_term x t -> Gamma x = Gamma' x) ->
  [pr]: Gamma' |- t in T.

Proof.
  Admitted.


Lemma substitution_preseves_typing:
  forall (pr: prog) (Gamma: context) (x: id) (t s: tm) (T S: ty),
  [pr]: extend_id Gamma x S |- t in T -> 
  [pr]: empty |- s in S ->
  [pr]: Gamma |- subst x s t in T.

Proof.
  Admitted.

Lemma preservation:
  forall (pr: prog) (t t': tm) (T: ty) (n n': nat) (theta: slice),
  [pr]: empty |- t in T ->
  [pr]: (t, n) ==> (t', n', theta) ->
  [pr]: empty |- t' in T.

Proof.
  Admitted.






(*=====================SOUNDNESS================================*)

(* normal form programs *)
Definition normal_form (t: tm) : Prop :=
  forall (pr: prog) (n n': nat) (theta: slice), 
  ~ exists t', [pr]: (t, n) ==> (t', n', theta).


(* stuck programs *)
Definition stuck (t: tm) : Prop :=
  (normal_form t) /\ ~ value t.


Corollary soundness:
  forall (pr: prog) (t t': tm) (n n': nat) 
         (Theta: trace) (T: ty),
  [pr]: empty |- t in T ->
  [pr]: (t, n) ==>* (t', n', Theta) ->
  ~ stuck t'.

Proof.
  Admitted.

(*=========================== traceof prgram ===========================*)

(*modified: not to ensure being evaluated!*)
Inductive traceof: prog -> trace -> Prop :=
  traceof_constr: forall (tp t: tm) (o: ow) (C: code_base) (n: nat) 
                         (Theta: trace),
                         [prg tp o C]: (tp, 0) ==>* (t, n, Theta) ->
                         traceof (prg tp o C) Theta.

