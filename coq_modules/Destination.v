Require Export SfLib.

Import SfLibmod.

(*Destination Language: STLC + notions of program, ownership, code base,
  and events to log temporarily and permanently.*)
(*
Assumptions: 
1- code_bases map function names to closed lambda abstractions
   it is reflected in two places: in defining substitution [x:=s]t
   and in appear_free_in x t.
   Such an assuumption is declared in well-formed codebases!

2- Excluded middle is correct! (defined in SfLib)

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
t ::= x | f | \x:T.t | tt | unit | ev[f] t | lev[f] t | t;t
where x ranges over ordinary variable identifiers (id),
      f ranges over function name identifiers (fid),
      ev[f] t is the event to log function call temporarily,
      lev[f] t is the event to log function call permanently.
*)


Inductive tm : Type :=
  | tvar : id -> tm
  | tfname : fid -> tm
  | tabs : id -> ty -> tm -> tm
  | tapp : tm -> tm -> tm
  | tunit : tm
  | tev : fid -> tm -> tm
  | tlev : fid -> tm -> tm
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

Definition empty  {I A:Type} : partial_map I A := (fun _ => None). 

Definition extend_id {A:Type} (parMap : partial_map id A) 
                              (var:id) (val : A) :=
  fun var' => if eq_id_dec var var' then 
                 Some val 
              else parMap var'.

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









(*=====================   LOGGING POLICIES   ============================*)

(*Extending nat with variables*)
Inductive ext_nat : Type :=
  | proper_nat : nat -> ext_nat
  | nat_var :    id -> ext_nat.

(* 
propositions: 
p ::= LoggedCall(n,f, arg)| Call(n, f, args) | 
     | n < n' | p /\ p | p <- p | forall x, p | exists x, p
     | truth | falsom.
*)

Inductive prop : Type :=
  | LoggedCall : ext_nat -> fid -> tm -> prop
  | Call       : ext_nat -> fid -> tm -> prop
  | Lt         : ext_nat -> ext_nat -> prop
  | AND        : prop -> prop -> prop
  | ARROW      : prop -> prop -> prop
  | FORALL     : id -> prop -> prop
  | EXISTS     : id -> prop -> prop
  | TOP        : prop
  | BOT        : prop.




(* 
logical context as a set of props:
Delta ranges over it.
*)

Definition logical_context := list prop.


(*
logic proof theory judgment: Dela ||- p
*)
Reserved Notation " Delta '||-' p " (at level 40).

Inductive entails : logical_context -> prop -> Prop :=
  (*dummy def! not implemented!*)
  dummy_entail_constr : forall (Delta: logical_context) (p: prop),
                        Delta ||- p
  where " Delta '||-' p " := (entails Delta p).


(* negation notation*)
Definition NOT (p: prop) : prop := ARROW p BOT.

Lemma weakening : 
  forall (Delta Delta': logical_context) (p: prop),
  sublist Delta Delta' ->
  Delta ||- p ->
  Delta' ||- p.

Proof.
  Admitted.

Lemma weakening_cons:
  forall (Delta: logical_context) (p p': prop),
  Delta ||- p ->
  (p'::Delta) ||- p.

Proof.
  intros.
  remember(sublist_cons2 p' Delta) as HH.
  clear HeqHH.
  apply (weakening Delta (p'::Delta) p HH H).
  Qed.

(*
logging policy event (lp_ev) is a function identifier,
for which f ranges over.

logging policy triggers (lp_trigs) is a list of function identifiers,
for which gs ranges over.

logging policy level (lp_level) is the upper bound level for owner.
*)

Definition lp_ev : Type := fid.
Definition lp_trigs : Type := list fid.
Definition lp_level : Type := nat.

(*
logging policy condition (phi ranges over it):
Call(?n, f, ?arg) /\
Call(?n'1, g1, ?arg1) /\ Lt(?n'1,?n) /\ ... /\ 
Call(?n'm, gm, ?argm) /\ Lt(?n'm,?n).

logging policy pattern (psi ranges over it):
Call(?n, f, ?arg) /\ 
Call(?n'1, g1, ?arg1) /\ Lt(?n'1,?n) /\ ... /\ 
Call(?n'm, gm, ?argm) /\ Lt(?n'm,?n) -> LoggedCall(?n, f, ?arg).

logging policy condition type (lp_cond):
prog -> nat -> tm -> ow -> list nat -> list tm -> prop.

logging policy pattern type (lp_patt):
prog -> nat -> tm -> ow -> list nat -> list tm -> prop.

lp_trig_condition_mk iteratively generates the section of
conditions about triggers (psi ranges over it):
Call(?n'1, g1, ?args21) /\ Lt(n'1,n) /\ ... /\ 
Call(?n'm, gm, ?args2m) /\ Lt(n'm,n).

lp_condition_mk generates the logging policy condition
by calling lp_trig_condition_mk.

lp_pattern_mk generates the whole logging policy pattern
by calling lp_condition_mk.
*)


Fixpoint lp_trig_condition_mk_numbered (gs: lp_trigs) (n: ext_nat) (i: nat)
         : prop :=
  match gs with
  | [] =>  TOP
  | g :: gs' => let ni := nat_var ((Id i)) in
                let argi := tvar (Id (i+1)) in
                EXISTS (Id i) (EXISTS (Id (i+1)) 
                (AND (Call ni g argi) (AND (Lt ni n) 
                 (lp_trig_condition_mk_numbered gs' n (i+2))))
                )
  end.

Fixpoint lp_trig_condition_mk (gs: lp_trigs) (n: ext_nat) : prop :=
  lp_trig_condition_mk_numbered gs n 10.

Fixpoint lp_condition_mk (f: lp_ev) (gs: lp_trigs) (n: ext_nat) (arg: tm) 
           : prop :=
  AND (Call n f arg) (lp_trig_condition_mk gs n).

Fixpoint lp_pattern_mk (f: lp_ev) (gs: lp_trigs) : prop :=
  let n := nat_var (Id 5) in
  let arg := tvar (Id 6) in
  FORALL (Id 5) (FORALL (Id 6) 
  (ARROW (LoggedCall n f arg) (lp_condition_mk f gs n arg))).

(*
Eval simpl in (lp_trig_condition_mk ((FId 2)::(FId 3)::nil) (proper_nat 2)).

Eval simpl in 
  (lp_condition_mk  (FId 1) ((FId 2)::(FId 3)::nil) (proper_nat 2) tunit).

Eval simpl in 
  (lp_pattern_mk  (FId 1) ((FId 2)::(FId 3)::nil)).
*)




(*
logging policy refinement (kappa ranges over it):
LoggedCall(?n, f, ?arg)

logging policy refinement type (lp_refin):
nat -> tm -> prop

lp_refinement_mk generates logging policy refinement.

*)

Definition lp_refin := ext_nat -> fid -> tm -> prop.
Definition lp_refinement_mk := LoggedCall.
Check lp_refinement_mk.


(*
logging policy is a 5-ary tuple of 
1) a logging event, 
2) a list of logging triggers, 
3) a logging policy level, 
4) a logging policy pattern, and 
5) a logging policy refinement.

lp ranges over logpol elements.
*)

Inductive logpol : Type :=
  lgpl : lp_ev -> lp_trigs -> lp_level -> prop -> lp_refin -> logpol.

(*
wellformedness of logging polcies
are the ones whose both pattern and refinement 
are wellformed:
*)
Inductive wellformed_lp : logpol -> Prop :=
  wf_lp: forall (f: lp_ev) (gs: lp_trigs) 
                (l: lp_level) (psi: prop) (kappa: lp_refin),
         (forall (gi: fid), inlist gi gs -> f <>gi) ->
         psi =  lp_pattern_mk f gs ->
         kappa =  lp_refinement_mk ->
         wellformed_lp (lgpl f gs l psi kappa).


Definition LogCondition (lp: logpol) (n: ext_nat) (arg: tm) : prop :=
  match lp with
  lgpl f gs l psi kappa => lp_condition_mk f gs n arg
  end.


Axiom logcondition_entail:
  forall (Delta: list prop) (f: lp_ev) (gs: lp_trigs) (l: lp_level)
         (psi: prop) (kappa: lp_refin) (n: nat) (arg: tm),
  Delta ||- LogCondition (lgpl f gs l psi kappa) (proper_nat n) arg ->
  inlist (Call (proper_nat n) f arg) Delta /\
  forall (gi: fid), inlist gi gs ->
  exists (ni: nat) (vi: tm), inlist (Call (proper_nat ni) gi vi) Delta /\
                             true = ble_nat ni n /\ ni <> n.



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
  | tev f t' => tev f ([x:=s] t')
  | tlev f t' => tlev f ([x:=s] t')
  | tseq t1 t2 => tseq ([x:=s] t1)([x:=s] t2)
  end
  where "'[' x ':=' s ']' t" := (subst x s t).


(* reduction single step:
   [pr, lp]: t,n,X,L ==> t',n',X',L' 
*)

Reserved Notation " '[' pr ',' lp ']:' p1 '==>' p2 " (at level 40).

Inductive step : prog -> logpol -> (tm * nat * list prop * list prop) -> 
                                   (tm * nat * list prop * list prop) -> 
                                   Prop :=
  | ST_AppAbs : forall (pr: prog) (lp: logpol) (x: id) (T: ty)
                       (t v: tm) (n: nat) (X L: list prop),
                wellformed_lp lp->
                value v ->
                [pr, lp]: (tapp (tabs x T t) v, n, X, L) ==> 
                          (subst x v t, n+1, X, L)
  | ST_AppFId : forall (tp: tm) (lp: logpol) (o: ow) 
                       (C: code_base) (f: fid) (x: id) (T: ty)
                       (v t: tm) (n: nat) (X L: list prop),
                wellformed_lp lp->
                value v ->
                C f = Some (tabs x T t) ->
                [prg tp o C, lp]: (tapp (tfname f) v, n, X, L) ==> 
                                  (subst x v t, n+1, X, L)
  | ST_App1   : forall (pr: prog) (lp: logpol) (t1 t1' t2: tm) (n1 n2: nat) 
                       (X X' L L': list prop),
                wellformed_lp lp->
                [pr, lp]: (t1, n1, X, L) ==> (t1', n2, X', L') ->
                [pr, lp]: (tapp t1 t2, n1, X, L) ==> 
                          (tapp t1' t2, n2, X', L')
  | ST_App2   : forall (pr: prog) (lp: logpol) (v t2 t2': tm) (n1 n2: nat)
                       (X X' L L': list prop),
                wellformed_lp lp->
                value v ->
                [pr, lp]: (t2, n1, X, L) ==> (t2', n2, X', L') ->
                [pr, lp]: (tapp v t2, n1, X, L) ==> 
                          (tapp v t2', n2, X', L')
  | ST_EvVal  : forall (pr: prog) (lp: logpol) (f: fid) (v: tm) (n: nat)
                       (X L: list prop),
                wellformed_lp lp->
                value v ->
                [pr, lp]: (tev f v, n, X, L) ==> 
                          (tunit, n, ((Call (proper_nat (n-1)) f v)::X), L)
  | ST_Ev     : forall (pr: prog) (lp: logpol) (f: fid) (t t': tm) 
                       (n n': nat) (X X' L L': list prop),
                wellformed_lp lp->
                [pr, lp]: (t, n, X, L) ==> (t', n', X', L') ->
                [pr, lp]: (tev f t, n, X, L) ==> (tev f t', n', X', L')
  | ST_LevVal1 : forall (tp: tm) (o: ow) (C: code_base) (f: lp_ev) 
                 (gs: lp_trigs) (l: lp_level) (psi: prop) (kappa: lp_refin)
                 (v: tm) (n: nat) (X L: list prop),
                 wellformed_lp (lgpl f gs l psi kappa)->
                 X ||- LogCondition (lgpl f gs l psi kappa) 
                                    (proper_nat (n-1)) v ->
                 value v ->
                 [(prg tp o C), (lgpl f gs l psi kappa)]: 
                   (tlev f v, n, X, L) ==> 
                   (tunit, n, X, ((LoggedCall (proper_nat (n-1)) f v)::L))
  | ST_LevVal2 : forall (tp: tm) (o: ow) (C: code_base) (f: lp_ev) 
                 (gs: lp_trigs) (l: lp_level) (psi: prop) (kappa: lp_refin)
                 (v: tm) (n: nat) (X L: list prop),
                 wellformed_lp (lgpl f gs l psi kappa)->
                 ~ (X ||- LogCondition (lgpl f gs l psi kappa) 
                                    (proper_nat (n-1)) v )->
                 value v ->
                 [(prg tp o C), (lgpl f gs l psi kappa)]: 
                   (tlev f v, n, X, L) ==> 
                   (tunit, n, X, L)
  | ST_Lev    : forall (pr: prog) (lp: logpol) (f: fid) 
                       (t t': tm) (n n': nat) (X X' L L': list prop),
                wellformed_lp lp->
                [pr, lp]: (t, n, X, L) ==> (t', n', X', L') ->
                [pr, lp]: (tlev f t, n, X, L) ==> (tlev f t', n', X', L')
  | ST_SeqUnit: forall (pr: prog) (lp: logpol) (t: tm) (n: nat)
                       (X L: list prop),
                wellformed_lp lp->
                [pr, lp]: (tseq tunit t, n, X, L) ==> (t, n, X, L)
  | ST_Seq    : forall (pr: prog) (lp: logpol) (t1 t1' t2: tm) 
                       (n n': nat) (X X' L L': list prop),
                wellformed_lp lp->
                [pr, lp]: (t1, n, X, L) ==> (t1', n', X', L') ->
                [pr, lp]: (tseq t1 t2, n, X, L) ==> 
                          (tseq t1' t2, n', X', L')
  where "'[' pr ',' lp ']:' p1 '==>' p2" := (step pr lp p1 p2).

Hint Constructors step.



(*reflexive transitive closure of single step reduction*)

Reserved Notation "'[' pr ',' lp ']:' p1 '==>*' p2" (at level 40).

Inductive multistep : prog -> logpol -> 
                      (tm * nat * list prop * list prop) -> 
                      (tm * nat * list prop * list prop) -> 
                      Prop :=
  | multi_refl: forall (pr: prog) (lp: logpol) (t: tm) (n: nat)
                       (X L: list prop),
                wellformed_lp lp ->
                [pr, lp]: (t, n, X, L) ==>* (t, n, X, L)
  | multi_step: forall (pr: prog) (lp: logpol) (t t' t'': tm) 
                       (n n' n'': nat)
                       (X X' X'' L L' L'': list prop),
                wellformed_lp lp ->
                [pr, lp]: (t, n, X, L) ==> (t', n', X', L') ->
                [pr, lp]: (t', n', X', L') ==>* (t'', n'', X'', L'') ->
                [pr, lp]: (t, n, X, L) ==>* (t'', n'', X'', L'')
  where "'[' pr ',' lp ']:' p1 '==>*' p2" := (multistep pr lp p1 p2).


Lemma multistep_implies_lp_wf:
  forall (pr: prog) (lp: logpol) (t t': tm) 
         (n n': nat) (X X' L L': list prop),
  [pr, lp]: (t, n, X, L) ==>* (t', n', X', L') ->
  wellformed_lp lp.

Proof.
  intros.
  inversion H.
  subst.
  assumption.
  subst.
  assumption.
  Qed.
  




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
  | afi_ev    : forall (x: id) (f: fid) (t: tm),
                appears_free_in_term x t ->
                appears_free_in_term x (tev f t)
  | afi_lev   : forall (x: id) (f: fid) (t: tm),
                appears_free_in_term x t ->
                appears_free_in_term x (tlev f t)
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
              |= C ->
              C f = Some t ->
              [prg tp o C]: Gamma |- t in (TArrow T1 T2) ->
              [prg tp o C]: Gamma |- (tfname f) in (TArrow T1 T2)
  | T_Abs   : forall (tp: tm) (o: ow) (C: code_base) 
                     (Gamma: context) (x: id) (t: tm) (T1 T2: ty),
              |= C ->
              [prg tp o C]: extend_id Gamma x T1 |- t in T2 ->
              [prg tp o C]: Gamma |- (tabs x T1 t) in (TArrow T1 T2)
  | T_App   : forall (tp: tm) (o: ow) (C: code_base)
                     (Gamma: context) (t1 t2: tm) (T1 T2: ty),
              |= C ->
              [prg tp o C]: Gamma |- t1 in (TArrow T1 T2) ->
              [prg tp o C]: Gamma |- t2 in T1 ->
              [prg tp o C]: Gamma |- (tapp t1 t2) in T2
  | T_Unit  : forall (tp: tm) (o: ow) (C: code_base)
                     (Gamma: context),
              |= C ->
              [prg tp o C]: Gamma |- tunit in TUnit
  | T_Ev    : forall (tp: tm) (o: ow) (C: code_base)
                     (Gamma: context) (f: fid) (t: tm) (T1 T2: ty),
              |= C ->
              [prg tp o C]: Gamma |- (tfname f) in TArrow T1 T2 ->
              [prg tp o C]: Gamma |- t in T1 ->
              [prg tp o C]: Gamma |- (tev f t) in TUnit
  | T_Lev  : forall (tp: tm) (o: ow) (C: code_base)
                     (Gamma: context) (f: fid) (t: tm) (T1 T2: ty),
              |= C ->
              [prg tp o C]: Gamma |- (tfname f) in TArrow T1 T2 ->
              [prg tp o C]: Gamma |- t in T1 ->
              [prg tp o C]: Gamma |- (tlev f t) in TUnit
  | T_Seq   : forall (tp: tm) (o: ow) (C: code_base)
                     (Gamma: context) (t1 t2: tm) (T: ty),
              |= C ->
              [prg tp o C]: Gamma |- t1 in TUnit ->
              [prg tp o C]: Gamma |- t2 in T ->
              [prg tp o C]: Gamma |- tseq t1 t2 in T
  where " '[' pr ']:' Gamma '|-' p 'in' T " := (has_type pr Gamma p T).

Hint Constructors has_type.





(*=====================PROGRESS================================*)

Theorem progress:
  forall (pr: prog) (t: tm) (T: ty) (lp: logpol),
  [pr]: empty |- t in T -> 
  wellformed_lp lp ->
  value t \/ 
  exists t' n n' X X' L L', [pr, lp]: (t, n, X, L) ==> (t', n', X', L').

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
  unfold closed_term, not.
  intros.
  inversion H0.
  remember (free_in_context x t pr empty T H1 H) as HH.
  clear HeqHH.
  inversion HH.
  rename x into T'.
  unfold empty in H2.
  inversion H2.
  Qed.



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
  forall (pr: prog) (t t': tm) (T: ty) 
         (lp: logpol) (n n': nat) (X X' L L': list prop),
  [pr]: empty |- t in T ->
  [pr, lp]: (t, n, X, L) ==> (t', n', X', L') ->
  [pr]: empty |- t' in T.

Proof.
  Admitted.




(*=====================SOUNDNESS================================*)

(* normal form programs *)
Definition normal_form (t: tm) : Prop :=
  forall (pr: prog) (lp: logpol) 
         (n n': nat) (X X' L L': list prop), 
  ~ exists t', [pr, lp]: (t,n, X, L) ==> (t',n', X', L').


(* stuck programs *)
Definition stuck (t: tm) : Prop :=
  (normal_form t) /\ ~ value t.


Corollary soundness:
  forall (pr: prog) (lp: logpol) (t t': tm) 
         (n n': nat) (T: ty) (X X' L L': list prop),
  [pr]: empty |- t in T ->
  [pr, lp]: (t, n, X, L) ==>* (t', n', X', L') ->
  ~ stuck t'.

Proof.
  Admitted.


Lemma normalization:
  forall pr lp t n X L t' n' X' L',
  [pr, lp]: (t,n,X,L) ==> (t',n',X',L') ->
  ~ exists X'' L'', 
    [pr, lp]: (t',n',X',L') ==>* (t,n,X'',L'').

Proof. Admitted.


(*========================== LOG GENERATION ======================*)

(* program generating some permanent log: pr ~~> L*)
(*modified: not to ensure being evaluated!*)
Inductive prog_gen_log : logpol -> prog -> list prop -> Prop :=
  | pgl_constr: forall (lp: logpol) (t t': tm) (o: ow) (C: code_base)
                (n: nat) (X L: list prop),
                [prg t o C, lp]: (t,0,nil,nil) ==>* (t', n, X, L) ->
                prog_gen_log lp (prg t o C) L.

Notation " '|' lp '|:' pr '~~>' L " := 
         (prog_gen_log lp pr L) (at level 14).


