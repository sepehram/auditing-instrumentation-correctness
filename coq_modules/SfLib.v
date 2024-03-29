(** * SfLib: Software Foundations Library *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

(** Here we collect together several useful definitions and theorems
    from Basics.v, List.v, Poly.v, Ind.v, and Logic.v that are not
    already in the Coq standard library.  From now on we can [Import]
    or [Export] this file, instead of cluttering our environment with
    all the examples and false starts in those files. *)

(** * From the Coq Standard Library *)

Module SfLibmod.

Require Omega.   (* needed for using the [omega] tactic *)
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

(** * From Basics.v *)

Definition admit {T: Type} : T.  Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Theorem andb_true_elim1 : forall b c,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

Theorem andb_true_elim2 : forall b c,
  andb b c = true -> c = true.
Proof.
(* An exercise in Basics.v *)
Admitted.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
(* An exercise in Lists.v *)
Admitted.

(** * From Props.v *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** * From Logic.v *)

Theorem andb_true : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H.  Qed.

Theorem false_beq_nat: forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof. 
(* An exercise in Logic.v *)
Admitted.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
(* An exercise in Logic.v *)
Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
(* An exercise in Logic.v *)
Admitted.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
(* An exercise in Logic.v *)
Admitted.

Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

(** * From Later Files *)

Definition relation (X:Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Inductive multi (X:Type) (R: relation X) 
                            : X -> X -> Prop :=
  | multi_refl  : forall (x : X),
                 multi X R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi X R y z ->
                    multi X R x z.
Implicit Arguments multi [[X]]. 

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> multi R x y.
Proof.
  intros X R x y r.
  apply multi_step with y. apply r. apply multi_refl.   Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  (* FILL IN HERE *) Admitted.

(**  Identifiers and polymorphic partial maps. *)

Inductive id : Type := 
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined. 

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x); try reflexivity. 
  apply ex_falso_quodlibet; auto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  (* FILL IN HERE *) Admitted.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

Notation "'\empty'" := empty.

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id; auto. 
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x2 <> x1 ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto. 
Qed.

Lemma extend_shadow : forall A (ctxt: partial_map A) t1 t2 x1 x2,
  extend (extend ctxt x2 t1) x2 t2 x1 = extend ctxt x2 t2 x1.
Proof with auto.
  intros. unfold extend. destruct (eq_id_dec x2 x1)...
Qed.

(** -------------------- *)

(** * Some useful tactics *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=  
  match goal with  
  | H : _ |- _ => solve [ inversion H; subst; t ] 
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.


(*Sepehr: additional*)

Inductive fid : Type :=
  FId : nat -> fid.


Theorem eq_fid_dec : forall fid1 fid2 : fid, {fid1 = fid2} + {fid1 <> fid2}.
Proof.
   intros fid1 fid2.
   destruct fid1 as [n1]. destruct fid2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined. 

Lemma eq_fid : forall (T:Type) x (p q:T), 
              (if eq_fid_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_fid_dec x x); try reflexivity. 
  apply ex_falso_quodlibet; auto.
Qed.

Lemma neq_fid : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  (* FILL IN HERE *) Admitted.


(*Owners: a set of owners*)
Inductive ow: Type :=
  OId : nat -> ow.

(* being a memebr of list defined as a proposition *)
Inductive inlist {A: Type} : A -> list A -> Prop :=
  | in_head: forall (x: A) (xs: list A),
             inlist x (x::xs)
  | in_tail: forall (x: A) (y: A) (xs: list A),
             inlist x xs ->
             inlist x (y::xs).

Definition sublist {A: Type} (l1: list A) (l2: list A) : Prop :=
  forall (x: A), inlist x l1 -> inlist x l2.

Lemma sublist_identity:
  forall {A: Type} (l: list A),
  sublist l l.

Proof.
  intros.
  unfold sublist.
  intros.
  assumption.
  Qed.

Lemma sublist_cons: 
  forall {A: Type} (x: A) (l1 l2: list A),
  sublist l1 l2 ->
  sublist (x::l1) (x::l2).

Proof.
  intros.
  unfold sublist.
  intros.
  remember (x::l1) as L.
  generalize dependent l1.
  generalize dependent l2.
  generalize dependent x.
  destruct H0.
  intros.
  inversion HeqL.
  subst.
  apply in_head.
  intros.
  inversion HeqL.
  subst.
  apply in_tail.
  apply H.
  assumption.
  Qed.

Lemma sublist_cons2:
  forall {A: Type} (x: A) (l: list A),
  sublist l (x::l).

Proof.
  intros.
  unfold sublist.
  intros.
  inversion H.
  apply in_tail.
  apply in_head.
  apply in_tail.
  apply in_tail.
  assumption.
  Qed.

Lemma sublist_transitive:
  forall {A:Type} (l1 l2 l3: list A),
  sublist l1 l2 ->
  sublist l2 l3 ->
  sublist l1 l3.

Proof.
  Admitted.

Lemma cons_not_eq_list:
  forall {A: Type} (x: A) (l: list A),
  ~ (l = x::l).

Proof.
  Admitted.

Definition inlist_subtract {A: Type} (x: A) (l1: list A) (l2: list A) :=
  inlist x l1 /\ ~(inlist x l2).

Lemma sublist_subtract:
  forall {A: Type} (x: A) (l0 l1 l2: list A),
  sublist l0 l1 ->
  sublist l1 l2 ->
  inlist_subtract x l2 l0 ->
  ~(inlist_subtract x l2 l1) ->
  inlist_subtract x l1 l0.

Proof.
  Admitted.

Lemma inlist_subtract_cons:
  forall {A: Type} (x y: A) (l: list A),
  inlist_subtract x (y::l) l ->
  x= y.

Proof. Admitted.

Definition subtract_sublist {A: Type} (l1 l2 l3: list A) :=
  forall (x: A), inlist_subtract x l1 l2 -> inlist x l3.


Lemma sublists_append:
  forall {A: Type} (l1 l2 l3 L L': list A),
  sublist l1 l2 ->
  sublist l2 l3 ->
  subtract_sublist l3 l2 L ->
  subtract_sublist l2 l1 L' ->
  subtract_sublist l3 l1 (L' ++ L).

Proof. Admitted.


Lemma inlist_subtract_head:
  forall {A: Type} (x: A) (l: list A),
  inlist_subtract x (x::l) l.

Proof. Admitted.


Lemma inlist_append:
  forall {A: Type} (x: A) (l1 l2: list A),
  inlist x (l1 ++ l2) -> 
  inlist x l1 \/ inlist x l2.

Proof. Admitted.


Lemma inlist_subtract_inlist_bigger:
  forall {A: Type} (x: A) (l1 l2 l3: list A),
  sublist l1 l2 ->
  sublist l2 l3 ->
  inlist_subtract x l2 l1 ->
  inlist_subtract x l3 l1.

Proof. Admitted.


Lemma inlist_subtract_inlist_bigger2:
  forall {A: Type} (x: A) (l1 l2 l3: list A),
  sublist l1 l2 ->
  sublist l2 l3 ->
  inlist_subtract x l3 l2 ->
  inlist_subtract x l3 l1.

Proof. Admitted.

Lemma inlist_bigger:
  forall {A: Type} (x: A) (l1 l2: list A),
  inlist x l2 ->
  inlist x (l1 ++ l2).

Proof. Admitted.


Lemma not_inlist_neq:
  forall {A: Type} (x y: A) (l: list A),
  ~ inlist x (y::l) ->
  x <> y.

Proof. Admitted.


Definition list_equality {A: Type} (l1 l2: list A): Prop :=
  forall (x: A), inlist x l1 <-> inlist x l2.


Lemma inlist_subtract_sublist:
  forall {A: Type} (x: A) (l1 l2 l3: list A),
  inlist_subtract x l2 l1 ->
  sublist l2 l3 ->
  inlist x l3.

Proof. Admitted.
  
  

(* being a member of list of fid's, defined as a function *)
Fixpoint in_fid_list (g: fid) (gs: list fid) : bool :=
  match gs with
  | nil => false
  | cons h t => if eq_fid_dec g h then true else in_fid_list g t
  end.


Axiom excluded_middle:
  forall P: Prop, P \/ ~P.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall(x: X), f x = g x) -> f = g.


Lemma func_ext_inv:
  forall (X Y: Type) (f g: X -> Y),
  f = g -> forall (x: X), f x = g x.

Proof.
  intros.
  subst.
  reflexivity.
  Qed.


Fixpoint blt_nat (n m : nat) : bool :=
  match (n, m) with
  | (O, S _) => true
  | (S n', S m') => blt_nat n' m'
  | (_, _) => false
  end.

Lemma dummy:
  forall (n: nat),
  n + 1 - 1 = n.

Proof. Admitted.



End SfLibmod.