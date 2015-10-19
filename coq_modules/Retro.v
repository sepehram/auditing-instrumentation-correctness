Require Export SfLib.
Require Export Source.
Require Export Destination.

Import SfLibmod.

(*============================== RETROFITTING ==========================*)

(*
transforming types, terms, codebases, and programs
from the source language to the destination language
*)
Fixpoint type_transform (T: Source.ty) : ty :=
  match T with
  | Source.TUnit => TUnit
  | Source.TArrow T1 T2 => TArrow (type_transform T1) (type_transform T2)
  end.

Lemma type_trans_one_to_one : 
  forall (T1 T2: Source.ty),
  type_transform T1 = type_transform T2 ->
  T1 = T2.

Proof.
  intro T1.
  induction T1.
  intros.
  simpl in H.
  destruct T2.
  reflexivity.
  simpl in H.
  inversion H.
  destruct T2.
  intros.
  simpl in H.
  inversion H.
  intros.
  simpl in H.
  inversion H.
  apply IHT1_1 in H1.
  apply IHT1_2 in H2.
  subst.
  reflexivity.
  Qed.

Fixpoint term_transform (t: Source.tm) : tm :=
  match t with
  | Source.tvar x => tvar x
  | Source.tfname f => tfname f
  | Source.tabs x T t => tabs x (type_transform T) (term_transform t)
  | Source.tapp t1 t2 => tapp (term_transform t1)(term_transform t2)
  | Source.tunit => tunit
  | Source.tseq t1 t2 => tseq (term_transform t1)(term_transform t2)
  end.

Lemma term_transform_subst:
  forall (x: id) (t v: Source.tm),
  term_transform (Source.subst x v t) = subst x 
    (term_transform v) (term_transform t).

Proof.
  intros.
  induction t.
  simpl.
  destruct(eq_id_dec x i).
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  destruct(eq_id_dec x i).
  simpl.
  reflexivity.
  simpl.
  rewrite IHt.
  reflexivity.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
  Qed.

Lemma term_trans_one_to_one : 
  forall (t1 t2: Source.tm),
  term_transform t1 = term_transform t2 ->
  t1 = t2.

Proof.
  intro t1.
  induction t1.
  Case "var".
    rename i into x.
    intros.
    simpl in H.
    destruct t2; simpl in H; inversion H.
    reflexivity.
  Case "fname".
    intros.
    simpl in H.
    destruct t2; simpl in H; inversion H.
    reflexivity.
  Case "abs".
    rename i into x.
    intros.
    simpl in H.
    destruct t2; simpl in H; inversion H.
    rename t into T.
    rename t0 into T0.
    apply type_trans_one_to_one in H2.
    apply IHt1 in H3.
    subst.
    reflexivity.
  Case "app".
    intros.
    simpl in H.
    destruct t2; simpl in H; inversion H.
    apply IHt1_1 in H1.
    apply IHt1_2 in H2.
    subst.
    reflexivity.
  Case "unit".
    intros.
    simpl in H.
    destruct t2; simpl in H; inversion H.
    reflexivity.
  Case "seq".
    intros.
    simpl in H.
    destruct t2; simpl in H; inversion H.
    apply IHt1_1 in H1.
    apply IHt1_2 in H2.
    subst.
    reflexivity.
  Qed.

Lemma term_transform_value:
  forall (v: Source.tm),
  Source.value v ->
  value (term_transform v).

Proof. Admitted.


Lemma term_transform_normal_form:
  forall (v: Source.tm),
  Source.normal_form v ->
  normal_form (term_transform v).

Proof. Admitted.


Definition codebase_transform (C: Source.code_base) : code_base :=
  fun (f: fid) => match C f with
                  | None => None
                  | Some t => Some (term_transform t)
                  end.


Lemma codebase_trans_one_to_one :
  forall (C1 C2: Source.code_base),
  codebase_transform C1  = codebase_transform C2 ->
  C1 = C2.

Proof.
  intros.
  apply functional_extensionality.
  intros.
  rename x into f.
  remember (func_ext_inv fid (option tm) (codebase_transform C1)
                     (codebase_transform C2) H f).
  clear Heqe.
  unfold codebase_transform in e.
  destruct (C1 f).
  Case "C1 f = Some _".
    destruct (C2 f).
    inversion e.
    apply term_trans_one_to_one in H1.
    subst.
    reflexivity.
    inversion e.
  Case "C1 f = None".
    destruct (C2 f).
    inversion e.
    reflexivity.
  Qed.


Definition program_transform (pr: Source.prog) : prog :=
  match pr with
   Source.prg t o C => prg (term_transform t) o (codebase_transform C)
  end.

Lemma prog_trans_one_to_one :
  forall (pr1 pr2: Source.prog),
  program_transform pr1 = program_transform pr2 ->
  pr1 = pr2.

Proof.
  intros.
  destruct pr1.
  destruct pr2.
  simpl in H.
  inversion H.
  apply term_trans_one_to_one in H1.
  apply codebase_trans_one_to_one in H3.
  subst.
  reflexivity.
  Qed.

(*Retrofitting programs of source language*)
Inductive retro_codebase: lp_ev -> lp_trigs -> 
                          code_base -> code_base -> Prop :=
  rt_cb : forall (f: lp_ev) (gs: lp_trigs) (C C': code_base),
          (forall (x: id) (T: ty) (t: tm), C f = Some (tabs x T t) -> 
           C' f = Some (tabs x T ((tev f (tvar x)); 
                                          ((tlev f (tvar x)); t)))) ->
          (forall (g: fid) (x: id) (T: ty) (t: tm), inlist g gs -> 
           C g = Some (tabs x T t) ->
           C' g = Some (tabs x T ((tev g (tvar x)); t))) ->
          (forall (h: fid), ~ inlist h (f::gs) -> 
          C h = C' h) -> retro_codebase f gs C C'.


Inductive retro: Source.prog -> logpol -> prog -> Prop :=
  | rt_pr1 : forall (t: Source.tm) (o: ow) (Cs: Source.code_base)
                    (C C': code_base) (f: lp_ev) (gs: lp_trigs) 
                    (l: lp_level) (psi: prop) (kappa: lp_refin),
             true = ble_nat (lv o) l ->
             C = codebase_transform Cs ->
             retro_codebase f gs C C' ->
             retro (Source.prg t o Cs) (lgpl f gs l psi kappa)
                   (prg (term_transform t) o C').




(*============================ TRACE GENERATION =======================*)

Fixpoint trace_to_props (Theta: trace)
         : list prop :=
  match Theta with
  | nil => nil
  | (Call_tr n f t)::Theta' => 
    (Call (proper_nat n) f (term_transform t))::(trace_to_props Theta')
  | _::Theta' => (trace_to_props Theta')
  end.

Inductive traceof : Source.prog -> list prop -> Prop :=
  tr_constr: forall (pr: Source.prog)
                    (Theta: trace) (tr: list prop),
             Source.traceof pr Theta ->
             tr = trace_to_props Theta ->
             traceof pr tr.


Lemma trace_to_props_append:
  forall (tr1 tr2: trace),
  trace_to_props (tr1 ++ tr2) = trace_to_props tr1 ++ trace_to_props tr2.

Proof. Admitted.


(*======================== proofs of correctness ======================*)

Lemma logs_get_bigger_single:
  forall (pr: prog) (lp: logpol) (t t': tm)
         (n n': nat) (X X' L L': list prop),
  [pr, lp]: (t,n,X,L) ==> (t',n',X',L') ->
  sublist X X' /\ sublist L L'.

Proof.
  intros.
  remember (t,n,X,L) as tnxl.
  remember (t',n',X',L') as tnxl'.
  generalize dependent Heqtnxl.
  generalize dependent Heqtnxl'.
  generalize dependent L'.
  generalize dependent L.
  generalize dependent X'.
  generalize dependent X.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t'.
  generalize dependent t.
  induction H.
  Case "AppAbs".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    split.
    apply sublist_identity.
    apply sublist_identity.
  Case "AppFId".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    split.
    apply sublist_identity.
    apply sublist_identity.
  Case "App1".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t1 t1' n n'.
    reflexivity.
    reflexivity.
  Case "App2".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t2 t2' n n'.
    reflexivity.
    reflexivity.
  Case "EvVal".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    split.
    apply sublist_cons2.
    apply sublist_identity.
  Case "Ev".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t t' n0 n'0.
    reflexivity.
    reflexivity.
  Case "LevVal1".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    split.
    apply sublist_identity.
    apply sublist_cons2.
  Case "LevVal2".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    split.
    apply sublist_identity.
    apply sublist_identity.
  Case "Lev".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t t' n0 n'0.
    reflexivity.
    reflexivity.
  Case "SeqUnit".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    split.
    apply sublist_identity.
    apply sublist_identity.
  Case "Seq".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t1 t1' n0 n'0.
    reflexivity.
    reflexivity.
  Qed.
  


Lemma logs_get_bigger_multi:
  forall (pr: prog) (lp: logpol) (t t': tm)
         (n n': nat) (X X' L L': list prop),
  [pr, lp]: (t,n,X,L) ==>* (t',n',X',L') ->
  sublist X X' /\ sublist L L'.

Proof.
  intros.
  remember (t,n,X,L) as tnxl.
  remember (t',n',X',L') as tnxl'.
  generalize dependent Heqtnxl.
  generalize dependent Heqtnxl'.
  generalize dependent L'.
  generalize dependent L.
  generalize dependent X'.
  generalize dependent X.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t'.
  generalize dependent t.
  induction H.
  Case "multi_refl".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    split.
    apply sublist_identity.
    apply sublist_identity.
  Case "multi_step".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    remember (IHmultistep t' t'0 n' n'0 X' X'0 L' L'0 
                          eq_refl eq_refl) as IH.
    clear HeqIH.
    inversion IH.
    apply logs_get_bigger_single in H0.
    inversion H0.
    split.
    apply sublist_transitive with X'.
    assumption.
    assumption.
    apply sublist_transitive with L'.
    assumption.
    assumption.
  Qed.



Lemma inlist_subtract_cons_single :
  forall (pr:prog) (lp: logpol)(f: lp_ev) (gs: lp_trigs) 
         (l:lp_level) (psi: prop) 
         (kappa: lp_refin) (t t' v: tm)
         (n n' m: nat) (X X' L L': list prop),
  lp =(lgpl f gs l psi kappa) ->
  [pr, lp]: (t,n,X,L) ==> (t',n',X',L') ->
  inlist_subtract (LoggedCall (proper_nat m) f v ) L' L ->
  L' = (LoggedCall (proper_nat m) f v )::L.

Proof.
  intros.
  remember (t,n,X,L) as tnxl.
  remember (t', n', X', L') as tnxl'.
  generalize dependent Heqtnxl.
  generalize dependent Heqtnxl'.
  generalize dependent L'.
  generalize dependent L.
  generalize dependent X'.
  generalize dependent X.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t'.
  generalize dependent t.
  induction H0.
  Case "AppAbs".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    unfold inlist_subtract in H2.
    inversion H2.
    apply H3 in H.
    inversion H.
  Case "AppFId".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    unfold inlist_subtract in H3.
    inversion H3.
    apply H4 in H.
    inversion H.
  Case "App1".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t1 t1' n n' X0 X'0.
    reflexivity.
    assumption.
    reflexivity.
    reflexivity.
  Case "App2".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t2 t2' n n' X0 X'0.
    reflexivity.
    assumption.
    reflexivity.
    reflexivity.
  Case "EvVal".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    unfold inlist_subtract in H2.
    inversion H2.
    apply H3 in H.
    inversion H.
  Case "Ev".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t t' n0 n'0 X0 X'0.
    reflexivity.
    assumption.
    reflexivity.
    reflexivity.
  Case "LevVal1".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    remember (inlist_subtract_cons (LoggedCall (proper_nat m) f v)
      (LoggedCall (proper_nat (n' - 1)) f0 v0) L0 H3) as H'.
    clear HeqH'.
    rewrite H'.
    reflexivity.
  Case "LevVal2".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    unfold inlist_subtract in H3.
    inversion H3.
    apply H5 in H4.
    inversion H4.
  Case "Lev".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t t' n0 n'0 X0 X'0.
    reflexivity.
    assumption.
    reflexivity.
    reflexivity.
  Case "SeqUnit".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    unfold inlist_subtract in H1.
    inversion H1.
    apply H2 in H.
    inversion H.
  Case "Seq".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t1 t1' n0 n'0 X0 X'0.
    reflexivity.
    assumption.
    reflexivity.
    reflexivity.
  Qed.



Lemma temp_log_entails_logcondition_single:
  forall (pr:prog) (lp: logpol)(f: lp_ev) (gs: lp_trigs) 
         (l:lp_level) (psi: prop) 
         (kappa: lp_refin) (t t' v: tm)
         (n n' m: nat) (X X' L:list prop),
  lp =(lgpl f gs l psi kappa) ->
  [pr, lp]: (t,n,X,L) ==> (t',n',X',(LoggedCall (proper_nat m) f v)::L) ->
  X' ||- LogCondition lp (proper_nat m) v /\ m = n - 1.

Proof.
  intros.
  remember (t,n,X,L) as tnxl.
  remember (t', n', X', LoggedCall (proper_nat m) f v :: L) as tnxl'.
  generalize dependent Heqtnxl.
  generalize dependent Heqtnxl'.
  generalize dependent L.
  generalize dependent X'.
  generalize dependent X.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t'.
  generalize dependent t.
  induction H0.
  Case "AppAbs".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    apply cons_not_eq_list in H5.
    inversion H5.
  Case "AppFId".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    apply cons_not_eq_list in H6.
    inversion H6.
  Case "App1".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t1 t1' n' X0 L0.
    reflexivity.
    reflexivity.
    reflexivity.
  Case "App2".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t2 t2' n' X0 L0.
    reflexivity.
    reflexivity.
    reflexivity.
  Case "EvVal".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    apply cons_not_eq_list in H5.
    inversion H5.
  Case "Ev".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t t' n'0 X0 L0.
    reflexivity.
    reflexivity.
    reflexivity.
  Case "LevVal1".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    split.
    assumption.
    reflexivity.
  Case "LevVal2".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    apply cons_not_eq_list in H7.
    inversion H7.
  Case "Lev".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t t' n'0 X0 L0.
    reflexivity.
    reflexivity.
    reflexivity.
  Case "SeqUnit".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    apply cons_not_eq_list in H4.
    inversion H4.
  Case "Seq".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply IHstep with t1 t1' n'0 X0 L0.
    reflexivity.
    reflexivity.
    reflexivity.
  Qed.



Lemma temp_log_entails_logcondition_multi:
  forall (pr:prog) (lp: logpol)(f: lp_ev) (gs: lp_trigs) 
         (l:lp_level) (psi: prop) 
         (kappa: lp_refin) (t t' v: tm)
         (n n' m: nat) (X X' L L':list prop),
  lp =(lgpl f gs l psi kappa) ->
  inlist_subtract (LoggedCall (proper_nat m) f v) L' L ->
  [pr, lp]: (t,n,X,L) ==>* (t',n',X',L') ->
  X' ||- LogCondition lp (proper_nat m) v.

Proof.
  intros.
  remember (t,n,X,L) as tnxl.
  remember (t',n',X',L') as tnxl'.
  generalize dependent Heqtnxl.
  generalize dependent Heqtnxl'.
  generalize dependent L'.
  generalize dependent L.
  generalize dependent X'.
  generalize dependent X.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t'.
  generalize dependent t.
  induction H1.
  Case "multi_refl".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    unfold inlist_subtract in H1.
    inversion H1.
    apply H2 in H.
    inversion H.
  Case "multi_step".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    remember (excluded_middle 
      (inlist_subtract (LoggedCall (proper_nat m) f v) L'0 L')) as H.
    clear HeqH.
    destruct H.
    SCase "LoggedCall in L'0 - L'".
      remember (IHmultistep 
        eq_refl t' t'0 n' n'0 X' X'0 L' L'0 H eq_refl eq_refl).
      assumption.
    SCase "LoggedCall notin L'0 - L'".
      clear Heqtnxl.
      clear Heqtnxl'.
      remember H1 as H1'.
      clear HeqH1'.
      apply logs_get_bigger_single in H1'.
      inversion H1'.
      clear H1' H4.
      remember H2 as H2'.
      clear HeqH2'.
      apply logs_get_bigger_multi in H2'.
      inversion H2'.
      clear H2'.
      remember (sublist_subtract 
        (LoggedCall (proper_nat m) f v) L0 L' L'0 H5 H6 H3 H) as H'.
      clear HeqH'.
      remember (inlist_subtract_cons_single pr 
        (lgpl f gs l psi kappa) f gs l psi kappa 
        t0 t' v n0 n' m X0 X' L0 L' eq_refl H1 H') as H''.
      clear HeqH''.
      rewrite H'' in H1.
      remember (temp_log_entails_logcondition_single
        pr (lgpl f gs l psi kappa) f gs l psi kappa 
        t0 t' v n0 n' m X0 X' L0 eq_refl H1) as H'''.
      clear HeqH'''.
      inversion H'''.
      clear H''' H8.
      eapply weakening.
      apply H4.
      assumption.
  Qed.

Corollary full_temp_log_entails_logcondition:
  forall (pr:prog) (lp: logpol)(f: lp_ev) (gs: lp_trigs) 
         (l:lp_level) (psi: prop) 
         (kappa: lp_refin) (t t' v: tm)
         (n m: nat) (X L :list prop),
  lp =(lgpl f gs l psi kappa) ->
  inlist (LoggedCall (proper_nat m) f v) L ->
  [pr, lp]: (t,0,nil,nil) ==>* (t',n,X,L) ->
  X ||- LogCondition lp (proper_nat m) v.

Proof.
  intros.
  remember (temp_log_entails_logcondition_multi pr lp f gs l psi kappa
            t t' v 0 n m nil X nil L H) as H'.
  clear HeqH'.
  apply H'.
  unfold inlist_subtract.
  split.
  assumption.
  unfold not.
  intro.
  inversion H2.
  assumption.
  Qed.



Lemma aux_multi_app1:
  forall (pr: prog) (lp:logpol) (t1 t1' t2: tm) 
  (n n': nat) (X X' L L': list prop),
  [pr, lp]: (t1,n,X,L) ==>* (t1',n',X',L') ->
  [pr, lp]: (tapp t1 t2,n,X,L) ==>* (tapp t1' t2,n',X',L').

Proof.
  intros.
  remember (t1,n,X,L) as tnxl.
  remember (t1',n',X',L') as tnxl'.
  generalize dependent Heqtnxl.
  generalize dependent Heqtnxl'.
  generalize dependent L'.
  generalize dependent L.
  generalize dependent X'.
  generalize dependent X.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t1'.
  generalize dependent t1.
  induction H.
  Case "multi_refl".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply Destination.multi_refl.
    assumption.
  Case "multi_step".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    remember (IHmultistep t' t1' n' n'0 
      X' X'0 L' L'0 eq_refl eq_refl) as H'.
    clear IHmultistep HeqH'.
    eapply Destination.multi_step.
    assumption.
    eapply ST_App1.
    assumption.
    apply H0.
    assumption.
  Qed.
    


Lemma aux_multi_app2:
  forall (pr: prog) (lp:logpol) (v t2 t2': tm) 
  (n n': nat) (X X' L L': list prop),
  value v ->
  [pr, lp]: (t2,n,X,L) ==>* (t2',n',X',L') ->
  [pr, lp]: (tapp v t2,n,X,L) ==>* (tapp v t2',n',X',L').

Proof.
  intros.
  remember (t2,n,X,L) as tnxl.
  remember (t2',n',X',L') as tnxl'.
  generalize dependent Heqtnxl.
  generalize dependent Heqtnxl'.
  generalize dependent L'.
  generalize dependent L.
  generalize dependent X'.
  generalize dependent X.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t2'.
  generalize dependent t2.
  induction H0.
  Case "multi_refl".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply Destination.multi_refl.
    assumption.
  Case "multi_step".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    remember (IHmultistep t' t2' n' n'0 
      X' X'0 L' L'0 eq_refl eq_refl) as H'.
    clear IHmultistep HeqH'.
    eapply Destination.multi_step.
    assumption.
    eapply ST_App2.
    assumption.
    assumption.
    apply H1.
    assumption.
  Qed.



Lemma aux_multi_seq:
  forall (pr: prog) (lp:logpol) (t1 t1' t2: tm) 
  (n n': nat) (X X' L L': list prop),
  [pr, lp]: (t1,n,X,L) ==>* (t1',n',X',L') ->
  [pr, lp]: (tseq t1 t2,n,X,L) ==>* (tseq t1' t2,n',X',L').

Proof.
  intros.
  remember (t1,n,X,L) as tnxl.
  remember (t1',n',X',L') as tnxl'.
  generalize dependent Heqtnxl.
  generalize dependent Heqtnxl'.
  generalize dependent L'.
  generalize dependent L.
  generalize dependent X'.
  generalize dependent X.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t1'.
  generalize dependent t1.
  induction H.
  Case "multi_refl".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    apply Destination.multi_refl.
    assumption.
  Case "multi_step".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    remember (IHmultistep t' t1' n' n'0 
      X' X'0 L' L'0 eq_refl eq_refl) as H'.
    clear IHmultistep HeqH'.
    eapply Destination.multi_step.
    assumption.
    eapply ST_Seq.
    assumption.
    apply H0.
    assumption.
  Qed.


Lemma aux_multi_step_transitivity:
  forall (pr: prog) (lp: logpol) (t t' t'': tm)
         (n n' n'': nat) (X X' X'' L L' L'': list prop),
  [pr, lp]: (t,n,X,L) ==>* (t',n',X',L') ->
  [pr, lp]: (t',n',X',L') ==>* (t'',n'',X'',L'') ->
  [pr, lp]: (t,n,X,L) ==>* (t'',n'',X'',L'').

Proof.
  intros.
  induction H.
  assumption.
  apply IHmultistep in H0.
  eapply Destination.multi_step.
  assumption.
  apply H1.
  assumption.
  Qed.
  




Lemma temp_log_subtract_sublist_slice:
  forall (pr: Source.prog) (pr': prog) (lp: logpol)
         (t t': Source.tm) (n n': nat) (theta: slice)
         (X L: list prop),
  retro pr lp pr' ->
  [pr]: (t,n) ==> (t',n',theta) ->
  wellformed_lp lp ->
  exists (X' L': list prop),
    [pr', lp]: (term_transform t,n,X,L) ==>* (term_transform t',n',X',L') 
    /\ subtract_sublist X' X (trace_to_props theta).

Proof.
  intros.
  remember (t,n) as tn.
  remember (t',n',theta) as tnt'.
  generalize dependent theta.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t'.
  generalize dependent t.
  induction H0.
  Case "AppAbs".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    eexists.
    eexists.
    simpl.
    split.
    rewrite term_transform_subst.
    eapply Destination.multi_step.
    assumption.
    apply ST_AppAbs.
    assumption.
    apply term_transform_value.
    assumption.
    apply Destination.multi_refl.
    assumption.
    unfold subtract_sublist.
    intros.
    rename x0 into p.
    unfold inlist_subtract in H2.
    inversion H2.
    apply H4 in H3.
    inversion H3.
  Case "AppFId".
    intros.
    destruct pr'.
    rename t1 into tp'.
    rename o0 into o'.
    rename c into C'.
    inversion H.
    subst.
    rename f into h.
    rename f0 into f.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    inversion H12.
    subst.
    remember (excluded_middle (inlist h (f::gs))) as H'.
    clear HeqH'.
    destruct H'.
    SCase "inlist h (f::gs)".
      inversion H6.
      SSCase "h = f".
        subst.
        remember (excluded_middle 
          ((Call (proper_nat (n0 + 1 - 1)) f (term_transform v) :: X)
          ||- LogCondition (lgpl f gs l psi kappa) (proper_nat (n0 + 1 - 1))
          (term_transform v)
          )) as H'.
        clear HeqH'.
        inversion H'.
        SSSCase "X ||- LogCondition".
          eexists.
          eexists.
          split.
          simpl.
          rewrite term_transform_subst.
          eapply Destination.multi_step.
          assumption.
          eapply ST_AppFId.
          assumption.
          apply term_transform_value.
          assumption.
          apply H3.
          unfold codebase_transform.
          rewrite H2.
          simpl.
          reflexivity.
          simpl.
          rewrite eq_id.
          eapply Destination.multi_step.
          assumption.
          eapply ST_Seq.
          assumption.
          eapply ST_EvVal.
          assumption.
          apply term_transform_value.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_SeqUnit.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_Seq.
          assumption.
          eapply ST_LevVal1.
          assumption.
          assumption.
          apply term_transform_value.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_SeqUnit.
          assumption.
          eapply Destination.multi_refl.
          assumption.
          unfold subtract_sublist.
          intros.
          rename x0 into p.
          apply inlist_subtract_cons in H9.
          subst.
          rewrite dummy.
          simpl.
          constructor.
        SSSCase "~ X ||- LogCondition".
          eexists.
          eexists.
          split.
          simpl.
          rewrite term_transform_subst.
          eapply Destination.multi_step.
          assumption.
          eapply ST_AppFId.
          assumption.
          apply term_transform_value.
          assumption.
          apply H3.
          unfold codebase_transform.
          rewrite H2.
          simpl.
          reflexivity.
          simpl.
          rewrite eq_id.
          eapply Destination.multi_step.
          assumption.
          eapply ST_Seq.
          assumption.
          eapply ST_EvVal.
          assumption.
          apply term_transform_value.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_SeqUnit.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_Seq.
          assumption.
          eapply Destination.ST_LevVal2.
          assumption.
          assumption.
          apply term_transform_value.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_SeqUnit.
          assumption.
          eapply Destination.multi_refl.
          assumption.
          unfold subtract_sublist.
          intros.
          rename x0 into p.
          apply inlist_subtract_cons in H9.
          subst.
          rewrite dummy.
          simpl.
          constructor.
      SSCase "h in gs".
        subst.
        eexists.
        eexists.
        split.
        simpl.
        rewrite term_transform_subst.
        eapply Destination.multi_step.
        assumption.
        eapply ST_AppFId.
        assumption.
        apply term_transform_value.
        assumption.
        apply H4.
        assumption.
        unfold codebase_transform.
        rewrite H2.
        simpl.
        reflexivity.
        simpl.
        rewrite eq_id.
        eapply Destination.multi_step.
        assumption.
        eapply ST_Seq.
        assumption.
        eapply ST_EvVal.
        assumption.
        apply term_transform_value.
        assumption.
        eapply Destination.multi_step.
        assumption.
        eapply ST_SeqUnit.
        assumption.
        eapply Destination.multi_refl.
        assumption.
        unfold subtract_sublist.
        intros.
        rename x0 into p.
        apply inlist_subtract_cons in H7.
        subst.
        rewrite dummy.
        simpl.
        constructor.
    SCase "~ inlist h (f::gs)".
      eexists.
      eexists.
      split.
      simpl.
      rewrite term_transform_subst.
      eapply Destination.multi_step.
      assumption.
      eapply ST_AppFId.
      assumption.
      apply term_transform_value.
      assumption.
      apply H5 in H6.
      rewrite <- H6.
      unfold codebase_transform.
      rewrite H2.
      simpl.
      reflexivity.
      eapply Destination.multi_refl.
      assumption.
      unfold subtract_sublist.
      intros.
      rename x0 into p.
      unfold inlist_subtract in H7.
      inversion H7.
      apply H10 in H9.
      inversion H9.
  Case "App1".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    remember (IHstep H t1 t1' n0 eq_refl n'0 
      (p::(Context_tr n0 E)::nil) eq_refl) as H'.
    clear HeqH' IHstep.
    inversion H'.
    inversion H2.
    rename x into X'.
    rename x0 into L'.
    inversion H3.
    clear H' H2 H3.
    eexists.
    eexists.
    split.
    simpl.
    apply aux_multi_app1.
    eapply H4.
    simpl in H5.
    simpl.
    assumption.
  Case "App2".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    remember (IHstep H t2 t2' n0 eq_refl n'0 
      (p::(Context_tr n0 E)::nil) eq_refl) as H'.
    clear HeqH' IHstep.
    inversion H'.
    inversion H3.
    rename x into X'.
    rename x0 into L'.
    inversion H4.
    clear H' H3 H4.
    eexists.
    eexists.
    split.
    simpl.
    apply aux_multi_app2.
    apply term_transform_value.
    assumption.
    eapply H5.
    simpl in H6.
    simpl.
    assumption.
  Case "SeqUnit".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    eexists.
    eexists.
    simpl.
    split.
    eapply Destination.multi_step.
    assumption.
    apply ST_SeqUnit.
    assumption.
    apply Destination.multi_refl.
    assumption.
    unfold subtract_sublist.
    intros.
    rename x into p.
    unfold inlist_subtract in H0.
    inversion H0.
    apply H3 in H2.
    inversion H2.
  Case "Seq".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    remember (IHstep H t1 t1' n0 eq_refl n'0 
      (p::(Context_tr n0 E)::nil) eq_refl) as H'.
    clear HeqH' IHstep.
    inversion H'.
    inversion H2.
    rename x into X'.
    rename x0 into L'.
    inversion H3.
    clear H' H2 H3.
    eexists.
    eexists.
    split.
    simpl.
    apply aux_multi_seq.
    eapply H4.
    simpl in H5.
    simpl.
    assumption.
  Qed.



Lemma temp_log_subtract_sublist_trace:
  forall (pr: Source.prog) (pr': prog) (lp: logpol)
         (t t': Source.tm) (n n': nat) (Theta: trace)
         (X L: list prop),
  retro pr lp pr' ->
  [pr]: (t,n) ==>* (t',n',Theta) ->
  wellformed_lp lp ->
  exists (X' L': list prop),
    [pr', lp]: (term_transform t,n,X,L) ==>* (term_transform t',n',X',L') 
    /\ subtract_sublist X' X (trace_to_props Theta).


Proof.
  intros.
  remember (t,n) as tn.
  remember (t',n',Theta) as tnT'.
  generalize dependent L.
  generalize dependent X.
  generalize dependent Theta.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t'.
  generalize dependent t.
  induction H0.
  Case "multi_refl".
    intros.
    inversion Heqtn.
    subst.
    inversion HeqtnT'.
    subst.
    clear Heqtn HeqtnT'.
    eexists.
    eexists.
    split.
    eapply Destination.multi_refl.
    assumption.
    simpl.
    unfold subtract_sublist.
    intros.
    rename x into p.
    unfold inlist_subtract in H0.
    inversion H0.
    apply H3 in H2.
    inversion H2.
  Case "multi_step".
    intros.
    inversion Heqtn.
    subst.
    inversion HeqtnT'.
    subst.
    clear Heqtn HeqtnT'.
    remember (temp_log_subtract_sublist_slice pr pr' lp 
      t0 t' n0 n' theta X L H H0 H1) as H'.
    inversion H'.
    inversion H3.
    rename x into X'.
    rename x0 into L'.
    inversion H4.
    clear H' HeqH' H3 H4.
    remember (IHmultistep H t' t'0 n' eq_refl 
      n'0 Theta eq_refl X' L') as H'.
    inversion H'.
    inversion H3.
    rename x into X''.
    rename x0 into L''.
    inversion H4.
    clear IHmultistep H' HeqH' H3 H4.
    eexists.
    eexists.
    split.
    eapply aux_multi_step_transitivity.
    apply H5.
    apply H7.
    apply logs_get_bigger_multi in H5.
    inversion H5.
    apply logs_get_bigger_multi in H7.
    inversion H7.
    rewrite trace_to_props_append.
    eapply sublists_append.      
    apply H3.
    assumption.
    assumption.
    assumption.
  Qed.




Corollary full_temp_log_sublist_trace:
  forall (pr: Source.prog) (pr': prog) (lp: logpol)
         (t t': Source.tm) (n: nat) (Theta: trace),
  retro pr lp pr' ->
  [pr]: (t,0) ==>* (t',n,Theta) ->
  wellformed_lp lp ->
  exists (X L: list prop),
    [pr', lp]: (term_transform t,0,nil,nil) ==>* (term_transform t',n,X,L) 
    /\ sublist X (trace_to_props Theta).

Proof.
  intros.
  remember (temp_log_subtract_sublist_trace pr pr' lp 
    t t' 0 n Theta nil nil H H0 H1) as H'.
  inversion H'.
  inversion H2.
  rename x into X.
  rename x0 into L.
  inversion H3.
  clear H' HeqH' H2 H3.
  eexists.
  eexists.
  split.
  apply H4.
  unfold subtract_sublist in H5.
  unfold sublist.
  intros.
  rename x into p.
  apply H5.
  unfold inlist_subtract.
  split.
  assumption.
  unfold not.
  intros.
  inversion H3.
  Qed.


Lemma temp_log_gathers_triggers_event_single:
  forall (pr: Source.prog) (pr': prog) (lp: logpol)
         (f: lp_ev) (gs: lp_trigs) (l: lp_level) (psi: prop)
         (kappa: lp_refin) (h: fid)(t t': Source.tm)
         (v: tm) (n n' m: nat) (theta: slice)
         (X L: list prop),
  retro pr lp pr' ->
  lp = lgpl f gs l psi kappa ->
  wellformed_lp lp ->
  inlist h (f::gs) -> 
  [pr]: (t,n) ==> (t',n',theta) ->
  inlist (Call (proper_nat m) h v) (trace_to_props theta) ->
  exists (X' L': list prop),
    [pr', lp]: (term_transform t,n,X,L) ==>* (term_transform t',n',X',L') 
    /\ inlist_subtract (Call (proper_nat m) h v) X' X.

Proof.
  intros.
  remember (t,n) as tn.
  remember (t',n',theta) as tnt'.
  generalize dependent theta.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t'.
  generalize dependent t.
  induction H3.
  Case "AppAbs".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    simpl in H4.
    inversion H4.
  Case "AppFId".
    intros.
    destruct pr'.
    rename t1 into tp'.
    rename o0 into o'.
    rename c into C'.
    inversion H.
    subst.
    inversion H10.
    subst.
    clear H10.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    simpl in H5.
    inversion H5.
    SCase "inlist Call [x]".
      subst.
      rename f0 into h.
      clear H5.
      inversion H15.
      subst.
      inversion H2.
      SSCase "h = f".
        subst.
        remember (excluded_middle 
          ((Call (proper_nat (n0 + 1 - 1)) f (term_transform v0) :: X)
          ||- LogCondition (lgpl f gs l psi kappa) (proper_nat (n0 + 1 - 1))
          (term_transform v0)
          )) as H'.
        clear HeqH'.
        inversion H'.
        SSSCase "X ||- LogCondition".
          eexists.
          eexists.
          split.
          simpl.
          rewrite term_transform_subst.
          eapply Destination.multi_step.
          assumption.
          eapply ST_AppFId.
          assumption.
          apply term_transform_value.
          assumption.
          apply H0.
          unfold codebase_transform.
          rewrite H4.
          simpl.
          reflexivity.
          simpl.
          rewrite eq_id.
          eapply Destination.multi_step.
          assumption.
          eapply ST_Seq.
          assumption.
          eapply ST_EvVal.
          assumption.
          apply term_transform_value.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_SeqUnit.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_Seq.
          assumption.
          eapply ST_LevVal1.
          assumption.
          assumption.
          apply term_transform_value.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_SeqUnit.
          assumption.
          eapply Destination.multi_refl.
          assumption.
          rewrite dummy.
          apply inlist_subtract_head.
        SSSCase "~ X ||- LogCondition".
          eexists.
          eexists.
          split.
          simpl.
          rewrite term_transform_subst.
          eapply Destination.multi_step.
          assumption.
          eapply ST_AppFId.
          assumption.
          apply term_transform_value.
          assumption.
          apply H0.
          unfold codebase_transform.
          rewrite H4.
          simpl.
          reflexivity.
          simpl.
          rewrite eq_id.
          eapply Destination.multi_step.
          assumption.
          eapply ST_Seq.
          assumption.
          eapply ST_EvVal.
          assumption.
          apply term_transform_value.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_SeqUnit.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_Seq.
          assumption.
          eapply Destination.ST_LevVal2.
          assumption.
          assumption.
          apply term_transform_value.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_SeqUnit.
          assumption.
          eapply Destination.multi_refl.
          assumption.
          rewrite dummy.
          apply inlist_subtract_head.
      SSCase "h in gs".
        subst.
        eexists.
        eexists.
        split.
        simpl.
        rewrite term_transform_subst.
        eapply Destination.multi_step.
        assumption.
        eapply ST_AppFId.
        assumption.
        apply term_transform_value.
        assumption.
        apply H5.
        assumption.
        unfold codebase_transform.
        rewrite H4.
        simpl.
        reflexivity.
        simpl.
        rewrite eq_id.
        eapply Destination.multi_step.
        assumption.
        eapply ST_Seq.
        assumption.
        eapply ST_EvVal.
        assumption.
        apply term_transform_value.
        assumption.
        eapply Destination.multi_step.
        assumption.
        eapply ST_SeqUnit.
        assumption.
        eapply Destination.multi_refl.
        assumption.
        rewrite dummy.
        apply inlist_subtract_head.
    SCase "inlist Call []".
      inversion H7.
  Case "App1".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    simpl in H4.
    remember (IHstep H t1 t1' n0 eq_refl n'0 
      (p::(Context_tr n0 E)::nil) eq_refl) as H'.
    simpl in H'.
    remember (H' H4) as H''.
    clear HeqH'' H' HeqH' IHstep.
    rename H'' into H'.
    inversion H'.
    inversion H0.
    rename x into X'.
    rename x0 into L'.
    inversion H5.
    clear H' H0 H5.
    eexists.
    eexists.
    split.
    simpl.
    apply aux_multi_app1.
    eapply H6.
    assumption.
  Case "App2".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    simpl in H5.
    remember (IHstep H t2 t2' n0 eq_refl n'0 
      (p::(Context_tr n0 E)::nil) eq_refl) as H'.
    simpl in H'.
    remember (H' H5) as H''.
    clear HeqH'' H' HeqH' IHstep.
    rename H'' into H'.
    inversion H'.
    inversion H0.
    rename x into X'.
    rename x0 into L'.
    inversion H6.
    clear H' H0 H6.
    eexists.
    eexists.
    split.
    simpl.
    apply aux_multi_app2.
    apply term_transform_value.
    assumption.
    eapply H7.
    assumption.
  Case "SeqUnit".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    simpl in H4.
    inversion H4.
  Case "Seq".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    simpl in H4.
    remember (IHstep H t1 t1' n0 eq_refl n'0 
      (p::(Context_tr n0 E)::nil) eq_refl) as H'.
    simpl in H'.
    remember (H' H4) as H''.
    clear HeqH'' H' HeqH' IHstep.
    rename H'' into H'.
    inversion H'.
    inversion H0.
    rename x into X'.
    rename x0 into L'.
    inversion H5.
    clear H' H0 H5.
    eexists.
    eexists.
    split.
    simpl.
    apply aux_multi_seq.
    eapply H6.
    assumption.
  Qed.




Lemma temp_log_gathers_triggers_event_multi:
  forall (pr: Source.prog) (pr': prog) (lp: logpol)
         (f: lp_ev) (gs: lp_trigs) (l: lp_level) (psi: prop)
         (kappa: lp_refin) (h: fid)(t t': Source.tm)
         (v: tm) (n n' m: nat) (Theta: trace)
         (X L: list prop),
  retro pr lp pr' ->
  lp = lgpl f gs l psi kappa ->
  wellformed_lp lp ->
  inlist h (f::gs) -> 
  [pr]: (t,n) ==>* (t',n',Theta) ->
  inlist (Call (proper_nat m) h v) (trace_to_props Theta) ->
  exists (X' L': list prop),
    [pr', lp]: (term_transform t,n,X,L) ==>* (term_transform t',n',X',L') 
    /\ inlist_subtract (Call (proper_nat m) h v) X' X.

Proof.
  intros.
  remember (t,n) as tn.
  remember (t',n',Theta) as tnT'.
  generalize dependent L.
  generalize dependent X.
  generalize dependent Theta.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t'.
  generalize dependent t.
  induction H3.
  Case "multi_refl".
    intros.
    inversion Heqtn.
    subst.
    inversion HeqtnT'.
    subst.
    clear Heqtn HeqtnT'.
    inversion H4.
  Case "multi_step".
    intros.
    inversion Heqtn.
    subst.
    inversion HeqtnT'.
    subst.
    clear Heqtn HeqtnT'.
    rewrite trace_to_props_append in H5.
    apply inlist_append in H5.
    inversion H5.
    SCase "inlist Call theta".
      remember (temp_log_gathers_triggers_event_single pr pr' 
        (lgpl f gs l psi kappa) f gs l psi kappa h t0 t' v 
        n0 n' m theta X L H eq_refl H1 H2 H3 H0) as H'.
      inversion H'.
      inversion H6.
      rename x into X'.
      rename x0 into L'.
      inversion H7.
      clear H' HeqH' H6 H7.
      remember (temp_log_subtract_sublist_trace pr pr' 
        (lgpl f gs l psi kappa) t' t'0 n' n'0 Theta X' L' H H4 H1) as H''.
      inversion H''.
      inversion H6.
      rename x into X''.
      rename x0 into L''.
      inversion H7.
      clear H'' HeqH'' H6 H7 H11.
      eexists.
      eexists.
      split.
      eapply aux_multi_step_transitivity.
      apply H8.
      apply H10.
      apply logs_get_bigger_multi in  H8.
      inversion H8.
      apply logs_get_bigger_multi in  H10.
      inversion H10.
      eapply inlist_subtract_inlist_bigger.
      apply H6.
      assumption.
      assumption.
    SCase "inlist Call Theta".
      remember (temp_log_subtract_sublist_slice pr pr' 
        (lgpl f gs l psi kappa) t0 t' n0 n' theta X L H H3 H1) as H'.
      inversion H'.
      inversion H6.
      rename x into X'.
      rename x0 into L'.
      inversion H7.
      clear H' HeqH' H6 H7.
      remember (IHmultistep H t' t'0 n' eq_refl 
        n'0 Theta eq_refl H0 X' L') as H'.
      inversion H'.
      inversion H6.
      rename x into X''.
      rename x0 into L''.
      inversion H7.
      clear H' HeqH' H6 H7.
      eexists.
      eexists.
      split.
      eapply aux_multi_step_transitivity.
      apply H8.
      apply H10.
      apply logs_get_bigger_multi in H8.
      inversion H8.
      apply logs_get_bigger_multi in H10.
      inversion H10.
      eapply inlist_subtract_inlist_bigger2.
      apply H6.
      assumption.
      assumption.
  Qed.




Corollary full_temp_log_gathers_triggers_event:
  forall (pr: Source.prog) (pr': prog) (lp: logpol)
         (f: lp_ev) (gs: lp_trigs) (l: lp_level) (psi: prop)
         (kappa: lp_refin) (h: fid)(t t': Source.tm)
         (v: tm) (n m: nat) (Theta: trace),
  retro pr lp pr' ->
  lp = lgpl f gs l psi kappa ->
  wellformed_lp lp ->
  inlist h (f::gs) -> 
  [pr]: (t,0) ==>* (t',n,Theta) ->
  inlist (Call (proper_nat m) h v) (trace_to_props Theta) ->
  exists (X L: list prop),
    [pr', lp]: (term_transform t,0,nil,nil) ==>* (term_transform t',n,X,L) 
    /\ inlist (Call (proper_nat m) h v) X.

Proof.
  intros.
  remember (temp_log_gathers_triggers_event_multi pr pr' lp 
    f gs l psi kappa h t t' v 0 n m Theta nil nil H H0 H1 H2 H3 H4) as H'.
  inversion H'.
  inversion H5.
  inversion H6.
  rename x into X.
  rename x0 into L.
  eexists.
  eexists.
  split.
  apply H7.
  unfold inlist_subtract in H8.
  inversion H8.
  assumption.
  Qed.




Lemma destruct_trace:
  forall (pr: Source.prog) (lp: logpol) (f: lp_ev)
         (gs: lp_trigs) (l:lp_level) (psi: prop) 
         (kappa: lp_refin) (t t': Source.tm)
         (v: tm) (n n' m: nat) (Theta: trace),
  lp = lgpl f gs l psi kappa ->
  [pr]: (t, n) ==>* (t', n', Theta) ->
  inlist (Call (proper_nat m) f v) (trace_to_props Theta) ->
  (forall (gi: fid), inlist gi gs -> 
    exists (ni: nat) (vi: tm), 
    inlist (Call (proper_nat ni) gi vi) (trace_to_props Theta)
    /\ true = ble_nat ni m /\ ni <> m) ->
  exists (t'': Source.tm) (n'': nat) (Theta': trace),
    [pr]: (t, n) ==>* (t'', n'', Theta') /\
    (forall (gi: fid), inlist gi gs ->
      exists (ni: nat) (vi: tm), 
      inlist (Call (proper_nat ni) gi vi) (trace_to_props Theta')
      /\ true = ble_nat ni m /\ ni <> m) /\
  exists (t''': Source.tm) (n''': nat) (theta: slice),
    [pr]: (t'', n'') ==> (t''', n''', theta) /\
    inlist (Call (proper_nat m) f v) (trace_to_props theta) /\
  exists (Theta'': trace), [pr]: (t''', n''') ==>* (t', n', Theta'') /\
    Theta = Theta'' ++ theta ++ Theta'.

Proof.
  intros.
  remember (t,n) as tn.
  remember (t',n',Theta) as tnT'.
  generalize dependent Theta.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t'.
  generalize dependent t.
  induction H0.
  Case "multi_refl".
    intros.
    inversion Heqtn.
    subst.
    inversion HeqtnT'.
    subst.
    clear Heqtn HeqtnT'.
    simpl in H1.
    inversion H1.
  Case "multi_step".
    intros.
    inversion Heqtn.
    subst.
    inversion HeqtnT'.
    subst.
    clear Heqtn HeqtnT'.
    rename t0 into t1.
    rename n0 into n1.
    rename t' into t2.
    rename n' into n2.
    rename t'0 into t3.
    rename n'0 into n3.
    rewrite trace_to_props_append in H3.
    remember (excluded_middle
      ((forall gi : fid,
       inlist gi gs ->
       exists (ni : nat) (vi : tm),
       inlist (Call (proper_nat ni) gi vi)
         (trace_to_props Theta)
        /\ true = ble_nat ni m /\ ni <> m) /\
       inlist (Call (proper_nat m) f v) (trace_to_props Theta))) as H'.
    clear HeqH'.
    destruct H'.
    SCase "Calls in Theta".
      inversion H.
      clear H.
      remember (IHmultistep t2 t3 n2 eq_refl n3 
        Theta eq_refl H5 H4) as H'.
      clear HeqH'.
      inversion H'.
      clear H'.
      rename x into t4.
      inversion H.
      clear H.
      rename x into n4.
      inversion H6.
      clear H6.
      rename x into Theta1.
      inversion H.
      clear H.
      inversion H7.
      clear H7.
      inversion H8.
      clear H8.
      rename x into t5.
      inversion H7.
      clear H7.
      rename x into n5.
      inversion H8.
      clear H8.
      rename x into theta0.
      inversion H7.
      clear H7.
      inversion H9.
      clear H9.
      inversion H10.
      clear H10.
      rename x into Theta2.
      inversion H9.
      clear H9.
      
      eexists.
      eexists.
      eexists.
      split.
      eapply Source.multi_step.
      apply H0.
      apply H6.
      split.
      intros.
      apply H in H9.
      inversion H9.
      clear H9.
      rename x into ni.
      inversion H12.
      clear H12.
      rename x into vi.
      inversion H9.
      clear H9.
      inversion H13.
      clear H13.
      eexists.
      eexists.
      split.
      rewrite trace_to_props_append.
      apply inlist_bigger.
      apply H12.
      split.
      assumption.
      assumption.
      eexists.
      eexists.
      eexists.
      split.
      apply H8.
      split.
      assumption.
      eexists.
      split.
      apply H10.
      admit. (*lists as sets, append as union*)
    SCase "Calls notin Theta".
      Admitted. (*similar to previous case, by calling IH*)
      



Lemma loggedcall_in_log:
  forall (pr: Source.prog) (pr': prog) (lp: logpol)
         (f: lp_ev) (gs: lp_trigs) (l: lp_level)
         (psi: prop) (kappa: lp_refin) (t t': Source.tm)
         (v: tm) (n n' m: nat)
         (theta: slice) (X L: list prop),
  retro pr lp pr' ->
  lp = lgpl f gs l psi kappa ->
  wellformed_lp lp ->
  [pr]: (t,n) ==> (t',n',theta) ->
  inlist (Call (proper_nat m) f v) (trace_to_props theta) ->
  (forall (gi: fid), inlist gi gs -> 
    exists (ni: nat) (vi: tm), 
    inlist (Call (proper_nat ni) gi vi) X 
    /\ true = ble_nat ni m /\ ni <> m) ->
  exists (X' L': list prop),
  [pr', lp]: (term_transform t,n,X,L) ==>* (term_transform t',n',X',L')  /\
  inlist_subtract (LoggedCall (proper_nat m) f v) L' L.

Proof.
  intros.
  remember (t,n) as tn.
  remember (t',n',theta) as tnt'.
  generalize dependent theta.
  generalize dependent n'.
  generalize dependent n.
  generalize dependent t'.
  generalize dependent t.
  induction H2.
  Case "AppAbs".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn Heqtnt'.
    simpl in H3.
    inversion H3.
  Case "AppFId".
    intros.
    destruct pr'.
    rename t1 into tp'.
    rename o0 into o'.
    rename c into C'.
    inversion H.
    subst.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    inversion H10.
    subst.
    clear H11.
    rename f0 into h.
    inversion H15.
    subst.
    remember (excluded_middle (inlist h (f::gs))) as H'.
    clear HeqH'.
    destruct H'.
    SCase "inlist h (f::gs)".
      inversion H8.
      SSCase "h = f".
        subst.
        remember (excluded_middle 
          ((Call (proper_nat (n0 + 1 - 1)) f (term_transform v0) :: X)
          ||- LogCondition (lgpl f gs l psi kappa) (proper_nat (n0 + 1 - 1))
          (term_transform v0)
          )) as H'.
        clear HeqH'.
        inversion H'.
        SSSCase "X ||- LogCondition".
          eexists.
          eexists.
          split.
          simpl.
          rewrite term_transform_subst.
          eapply Destination.multi_step.
          assumption.
          eapply ST_AppFId.
          assumption.
          apply term_transform_value.
          assumption.
          apply H0.
          unfold codebase_transform.
          rewrite H3.
          simpl.
          reflexivity.
          simpl.
          rewrite eq_id.
          eapply Destination.multi_step.
          assumption.
          eapply ST_Seq.
          assumption.
          eapply ST_EvVal.
          assumption.
          apply term_transform_value.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_SeqUnit.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_Seq.
          assumption.
          eapply ST_LevVal1.
          assumption.
          assumption.
          apply term_transform_value.
          assumption.
          eapply Destination.multi_step.
          assumption.
          eapply ST_SeqUnit.
          assumption.
          eapply Destination.multi_refl.
          assumption.
          simpl in H5.
          inversion H5.
          SSSSCase "inlist in head".
            subst.
            rewrite dummy.
            apply inlist_subtract_head.
          SSSSCase "inlist in tail".
            subst.
            inversion H13.
        SSSCase "~ X ||- LogCondition".
          admit. (*Since X ||- LogCondition holds as all triggers show up in X,
                   it comes from proof theory. (not implemented!)*)
      SSCase "h in gs".
        subst.
        eexists.
        eexists.
        split.
        simpl.
        rewrite term_transform_subst.
        eapply Destination.multi_step.
        assumption.
        eapply ST_AppFId.
        assumption.
        apply term_transform_value.
        assumption.
        apply H6.
        assumption.
        unfold codebase_transform.
        rewrite H3.
        simpl.
        reflexivity.
        simpl.
        rewrite eq_id.
        eapply Destination.multi_step.
        assumption.
        eapply ST_Seq.
        assumption.
        eapply ST_EvVal.
        assumption.
        apply term_transform_value.
        assumption.
        eapply Destination.multi_step.
        assumption.
        eapply ST_SeqUnit.
        assumption.
        eapply Destination.multi_refl.
        assumption.
        simpl in H5.
        inversion H5.
        SSSCase "inlist in head".
          subst.
          inversion H1.
          subst.
          apply H14 in H12.
          unfold not in H12.
          apply ex_falso_quodlibet.
          apply H12.
          reflexivity.
        SSSCase "inlist in tail".
          subst.
          inversion H13.
    SCase "~ inlist h (f::gs)".
      eexists.
      eexists.
      split.
      simpl.
      rewrite term_transform_subst.
      eapply Destination.multi_step.
      assumption.
      eapply ST_AppFId.
      assumption.
      apply term_transform_value.
      assumption.
      apply H7 in H8.
      rewrite <- H8.
      unfold codebase_transform.
      rewrite H3.
      simpl.
      reflexivity.
      eapply Destination.multi_refl.
      assumption.
      simpl in H5.
      inversion H5.
      SSSCase "inlist in head".
        subst.
        apply not_inlist_neq in H8.
        unfold not in H8.
        apply ex_falso_quodlibet.
        apply H8.
        reflexivity.
      SSSCase "inlist in tail".
        subst.
        inversion H12.
  Case "App1".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    simpl in H3.
    remember (IHstep H t1 t1' n0 eq_refl n'0 
      (p::(Context_tr n0 E)::nil) eq_refl) as H'.
    simpl in H'.
    remember (H' H3) as H''.
    clear HeqH'' HeqH' H' IHstep.
    rename H'' into H'.
    inversion H'.
    inversion H0.
    rename x into X'.
    rename x0 into L'.
    inversion H5.
    clear H' H0 H5.
    eexists.
    eexists.
    split.
    simpl.
    apply aux_multi_app1.
    eapply H6.
    assumption.
  Case "App2".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    simpl in H5.
    remember (IHstep H t2 t2' n0 eq_refl n'0 
      (p::(Context_tr n0 E)::nil) eq_refl) as H'.
    simpl in H'.
    remember (H' H5) as H''.
    clear HeqH'' H' HeqH' IHstep.
    rename H'' into H'.
    inversion H'.
    inversion H0.
    rename x into X'.
    rename x0 into L'.
    inversion H6.
    clear H' H0 H6.
    eexists.
    eexists.
    split.
    simpl.
    apply aux_multi_app2.
    apply term_transform_value.
    assumption.
    eapply H7.
    assumption.
  Case "SeqUnit".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn Heqtnt'.
    simpl in H3.
    inversion H3.
  Case "Seq".
    intros.
    inversion Heqtn.
    subst.
    inversion Heqtnt'.
    subst.
    clear Heqtn.
    clear Heqtnt'.
    simpl in H3.
    remember (IHstep H t1 t1' n0 eq_refl n'0 
      (p::(Context_tr n0 E)::nil) eq_refl) as H'.
    simpl in H'.
    remember (H' H3) as H''.
    clear HeqH'' H' HeqH' IHstep.
    rename H'' into H'.
    inversion H'.
    inversion H0.
    rename x into X'.
    rename x0 into L'.
    inversion H5.
    clear H' H0 H5.
    eexists.
    eexists.
    split.
    simpl.
    apply aux_multi_seq.
    eapply H6.
    assumption.
  Qed.




(*========================= LEAST HERBRAND =======================*)
Fixpoint LHM  (props: list prop) : list prop := 
   props. (*not implemented, this is a dummy def!*)

Axiom LHM_trace_is_trace:
  forall (pr: Source.prog) (tp v: Source.tm) (n: nat)
         (Theta: trace),
  [pr]: (tp, 0) ==>* (v, n, Theta) ->
  trace_to_props Theta = LHM (trace_to_props Theta).

Axiom sublist_LHM:
  forall (l1: list prop) (l2: list prop),
  sublist l1 l2 ->
  sublist (LHM l1) (LHM l2).



Axiom sublist_log_LHM:
  forall (n: nat) (f: lp_ev) (arg: tm) (Delta: list prop)
         (gs: lp_trigs) (psi:prop) (Theta: trace), 
  (inlist (Call (proper_nat n) f arg) Delta /\
     (forall gi : fid,
      inlist gi gs ->
      exists (ni : nat) (vi : tm),
        inlist (Call (proper_nat ni) gi vi) Delta /\
        true = ble_nat ni n /\ ni <> n)) ->
  sublist Delta (LHM (psi::(trace_to_props Theta))) ->
  (inlist (Call (proper_nat n) f arg) (LHM (psi::(trace_to_props Theta))) /\
     (forall gi : fid,
      inlist gi gs ->
      exists (ni : nat) (vi : tm),
        inlist (Call (proper_nat ni) gi vi) (LHM (psi::(trace_to_props Theta))) 
        /\ inlist (Lt (proper_nat ni) (proper_nat n)) 
                  (LHM (psi::(trace_to_props Theta))) )).


Axiom LHM_contains1:
  forall n f arg psi Theta gs ,
  (inlist (Call (proper_nat n) f arg) (LHM (psi :: trace_to_props Theta)) /\
     (forall gi : fid,
      inlist gi gs ->
      exists (ni : nat) (vi : tm),
       inlist (Call (proper_nat ni) gi vi)
       (LHM (psi :: trace_to_props Theta)) /\
       inlist (Lt (proper_nat ni) (proper_nat n))
         (LHM (psi :: trace_to_props Theta)))) ->
  inlist (LoggedCall (proper_nat n) f arg) (LHM (psi :: trace_to_props Theta)).


Axiom LHM_contains2:
  forall lp n f arg psi Theta gs l kappa,
  lp = lgpl f gs l psi kappa ->
  (inlist (LoggedCall (proper_nat n) f arg) 
    (LHM (psi :: trace_to_props Theta))) ->
  (inlist (Call (proper_nat n) f arg) (LHM (psi :: trace_to_props Theta))) /\
  (forall (gi : fid), inlist gi gs -> exists (ni : nat) (vi : tm),
    inlist (Call (proper_nat ni) gi vi) (LHM (psi :: trace_to_props Theta)) 
    /\ inlist (Lt (proper_nat ni) (proper_nat n))
         (LHM (psi :: trace_to_props Theta))) .


Axiom Calls_LHM_trace:
  forall n f arg psi Theta gs,
  inlist (Call (proper_nat n) f arg) (LHM (psi :: trace_to_props Theta)) /\
     (forall gi : fid,
      inlist gi gs ->
      exists (ni : nat) (vi : tm),
        inlist (Call (proper_nat ni) gi vi)
          (LHM (psi :: trace_to_props Theta)) /\
        inlist (Lt (proper_nat ni) (proper_nat n))
          (LHM (psi :: trace_to_props Theta))) ->
  inlist (Call (proper_nat n) f arg) (trace_to_props Theta) /\
  (forall (gi: fid), inlist gi gs -> 
    exists (ni: nat) (vi: tm), 
    inlist (Call (proper_nat ni) gi vi) (trace_to_props Theta)
    /\ true = ble_nat ni n /\ ni <> n).




(*========================= LANG OVER PREDICATE ==================*)
Definition Lang (kappa: lp_refin) : list prop :=
   nil. (*not implemented, this is a dummy def!*)


Axiom Lang_contain:
  forall (n: nat) (f: lp_ev) (arg: tm),
  inlist (LoggedCall (proper_nat n) f arg) (Lang LoggedCall).





Lemma full_temp_log_in_LHM:
  forall (pr: Source.prog) (pr': prog) (lp: logpol) (f: lp_ev)
         (gs: lp_trigs) (l:lp_level) (psi: prop) (kappa: lp_refin) 
         (tp v: Source.tm) (o: ow) (C: Source.code_base)
         (n: nat) (Theta: trace),
  pr = Source.prg tp o C ->
  retro pr lp pr' ->
  lp = lgpl f gs l psi kappa ->
  wellformed_lp lp ->
  [pr]: (tp, 0) ==>* (v, n, Theta) ->
  exists (X L: list prop),
  [pr', lp]: (term_transform tp, 0, nil, nil) ==>* 
             (term_transform v, n, X, L) /\
  sublist X (LHM (psi::(trace_to_props Theta))).

Proof.
  intros.
  remember H3 as H3'.
  clear HeqH3'.
  apply LHM_trace_is_trace in H3'.
  remember (sublist_LHM (trace_to_props Theta) 
    (psi :: trace_to_props Theta)
    (sublist_cons2 psi (trace_to_props Theta))) as H'.
  clear HeqH'.
  rewrite <- H3' in H'.
  remember (full_temp_log_sublist_trace pr pr' lp 
    tp v n Theta H0 H3 H2) as H''.
  clear HeqH''.
  inversion H''.
  inversion H4.
  rename x into X.
  rename x0 into L.
  inversion H5.
  clear H'' H4 H5.
  eexists.
  eexists.
  split.
  apply H6.
  eapply sublist_transitive.
  apply H7.
  assumption.
  Qed.




Lemma aux_reduction_determinacy_single:
  forall pr lp t n X L t' n' X' L' t'' n'' X'' L'',
  [pr, lp]: (t,n,X,L) ==> (t',n',X',L') ->
  [pr, lp]: (t,n,X,L) ==> (t'',n'',X'',L'') ->
  t' = t'' /\ n' = n'' /\ X' = X'' /\ L' = L''.

Proof.
  intros.
  remember (t,n,X,L) as tnxl.
  remember (t',n',X',L') as tnxl'.
  generalize dependent L''.
  generalize dependent X''.
  generalize dependent n''.
  generalize dependent t''.
  generalize dependent L'.
  generalize dependent X'.
  generalize dependent n'.
  generalize dependent t'.
  generalize dependent L.
  generalize dependent X.
  generalize dependent n.
  generalize dependent t.
  induction H.
  Case "AppAbs".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    inversion H1.
    subst.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
    subst.
    inversion H14.
    subst.
    inversion H0.
    subst.
    inversion H15.
    subst.
    inversion H15.
    subst.
    inversion H15.
  Case "AppFId".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    inversion H2.
    subst.
    rewrite H1 in H18.
    inversion H18.
    subst.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
    subst.
    inversion H15.
    subst.
    inversion H0.
    subst.
    inversion H16.
    subst.
    inversion H16.
    subst.
    inversion H16.
  Case "App1".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    inversion H1.
    subst.
    inversion H0.
    subst.
    inversion H0.
    subst.
    remember (IHstep t1 n X0 L0 eq_refl t1' n' X'0 L'0 eq_refl).
    apply a in H14.
    inversion H14.
    inversion H3.
    inversion H5.
    subst.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
    subst.
    inversion H14.
    subst.
    inversion H0.
    subst.
    inversion H0.
    subst.
    inversion H0.
  Case "App2".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    inversion H2.
    subst.
    inversion H15.
    subst.
    inversion H1.
    subst.
    inversion H1.
    subst.
    inversion H1.
    subst.
    inversion H15.
    subst.
    inversion H1.
    subst.
    inversion H1.
    subst.
    inversion H1.
    subst.
    inversion H0.
    subst.
    inversion H15.
    subst.
    inversion H15.
    subst.
    inversion H15.
    subst.
    remember (IHstep t2 n X0 L0 eq_refl t2' n' X'0 L'0 eq_refl).
    apply a in H16.
    inversion H16.
    inversion H4.
    inversion H6.
    subst.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
  Case "EvVal".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    inversion H1.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
    subst.
    inversion H0.
    subst.
    inversion H14.
    subst.
    inversion H14.
    subst.
    inversion H14.
  Case "Ev".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    inversion H1.
    subst.
    inversion H14.
    subst.
    inversion H0.
    subst.
    inversion H0.
    subst.
    inversion H0.
    subst.
    remember (IHstep t n0 X0 L0 eq_refl t' n'0 X'0 L'0 eq_refl).
    apply a in H14.
    inversion H14.
    inversion H3.
    inversion H5.
    subst.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
  Case "LevVal1".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    inversion H2.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
    subst.
    apply H20 in H0.
    inversion H0.
    subst.
    inversion H1.
    subst.
    inversion H15.
    subst.
    inversion H15.
    subst.
    inversion H15.
  Case "LevVal2".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    inversion H2.
    subst.
    apply H0 in H20.
    inversion H20.
    subst.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
    subst.
    inversion H1.
    subst.
    inversion H15.
    subst.
    inversion H15.
    subst.
    inversion H15.
  Case "Lev".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    inversion H1.
    subst.
    inversion H15.
    subst.
    inversion H0.
    subst.
    inversion H0.
    subst.
    inversion H0.
    subst.
    inversion H15.
    subst.
    inversion H0.
    subst.
    inversion H0.
    subst.
    inversion H0.
    subst.
    remember (IHstep t n0 X0 L0 eq_refl t' n'0 X'0 L'0 eq_refl).
    apply a in H14.
    inversion H14.
    inversion H3.
    inversion H5.
    subst.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
  Case "SeqUnit".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    inversion H0.
    subst.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
    subst.
    inversion H13.
  Case "Seq".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    inversion H1.
    subst.
    inversion H0.
    subst.
    remember (IHstep t1 n0 X0 L0 eq_refl t1' n'0 X'0 L'0 eq_refl).
    apply a in H14.
    inversion H14.
    inversion H3.
    inversion H5.
    subst.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
  Qed.



Lemma aux_reduction_determinacy_multi:
  forall pr lp t n X L v' n' X' L' v'' n'' X'' L'',
  [pr, lp]: (t,n,X,L) ==>* (v',n',X',L') ->
  normal_form v' ->
  [pr, lp]: (t,n,X,L) ==>* (v'',n'',X'',L'') ->
  normal_form v'' ->
  X' = X'' /\ L' = L''.

Proof.
  intros.
  remember (t,n,X,L) as tnxl.
  remember (v',n',X',L') as vnxl'.
  generalize dependent L''.
  generalize dependent X''.
  generalize dependent n''.
  generalize dependent v''.
  generalize dependent L'.
  generalize dependent X'.
  generalize dependent n'.
  generalize dependent v'.
  generalize dependent L.
  generalize dependent X.
  generalize dependent n.
  generalize dependent t.
  induction H.
  Case "multi_refl".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqvnxl'.
    subst.
    clear Heqtnxl Heqvnxl'.
    inversion H1.
    subst.
    split. reflexivity.
    reflexivity.
    subst.
    unfold normal_form in H0.
    remember (H0 pr lp n' n'0 X' X'0 L' L'0).
    unfold not in n.
    apply ex_falso_quodlibet.
    apply n.
    eexists.
    apply H14.
  Case "multi_step".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqvnxl'.
    subst.
    clear Heqtnxl Heqvnxl'.
    inversion H4.
    subst.
    unfold normal_form in H3.
    remember (H3 pr lp n''0 n' X''0 X' L''0 L').
    unfold not in n.
    apply ex_falso_quodlibet.
    apply n.
    eexists.
    apply H0.
    subst.
    remember (aux_reduction_determinacy_single pr lp t0 n0 X0 L0 
      t' n' X' L' t'0 n'1 X'1 L'1 H0 H16).
    inversion a.
    inversion H6.
    inversion H8.
    subst.
    remember (IHmultistep t'0 n'1 X'1 L'1 eq_refl v' H2 n'0 X'0 L'0 eq_refl
      v'' H3).
    apply a in H17.
    assumption.
  Qed.




Corollary aux_reduction_determinacy:
  forall pr lp t v1 n1 X1 L1 v2 n2 X2 L2,
  [pr, lp]: (t,0,nil,nil) ==>* (v1,n1,X1,L1) ->
  normal_form v1 ->
  [pr, lp]: (t,0,nil,nil) ==>* (v2,n2,X2,L2) ->
  normal_form v2 ->
  X1 = X2.

Proof.
  intros.
  remember (aux_reduction_determinacy_multi pr lp t 0 nil nil
    v1 n1 X1 L1 v2 n2 X2 L2 H H0 H1 H2).
  inversion a.
  assumption.
  Qed.
  



Lemma aux_reduction_determinacy1:
  forall pr lp t v1 n1 X1 L1 v2 n2 X2 L2,
  [pr, lp]: (t,0,nil,nil) ==>* (v1,n1,X1,L1) ->
  normal_form v1 ->
  [pr, lp]: (t,0,nil,nil) ==>* (v2,n2,X2,L2) ->
  normal_form v2 ->
  L1 = L2.

Proof.
  intros.
  remember (aux_reduction_determinacy_multi pr lp t 0 nil nil
    v1 n1 X1 L1 v2 n2 X2 L2 H H0 H1 H2).
  inversion a.
  assumption.
  Qed.




  


Lemma aux_refl:
  forall pr lp t n X L X' L',
  [pr, lp]: (t,n,X,L) ==>* (t,n,X',L') ->
  X = X' /\ L = L'.

Proof.
  intros.
  remember (t,n,X,L) as tnxl.
  remember (t,n,X',L') as tnxl'.
  generalize dependent L'.
  generalize dependent X'.
  generalize dependent L.
  generalize dependent X.
  generalize dependent n.
  generalize dependent t.
  induction H.
  Case "multi_refl".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    split. reflexivity. reflexivity.
  Case "multi_step".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    apply normalization in H0.
    apply ex_falso_quodlibet.
    apply H0.
    eexists.
    eexists.
    apply H1.
  Qed.
  



Lemma aux_reduction_determinacy_multi2:
  forall pr lp t n X L t' n' X' L' X'' L'',
  [pr, lp]: (t,n,X,L) ==>* (t',n',X',L') ->
  [pr, lp]: (t,n,X,L) ==>* (t',n',X'',L'') ->
  X' = X'' /\ L' = L''.

Proof.
  intros.
  remember (t,n,X,L) as tnxl.
  remember (t',n',X',L') as tnxl'.
  generalize dependent L''.
  generalize dependent X''.
  generalize dependent L'.
  generalize dependent X'.
  generalize dependent n'.
  generalize dependent t'.
  generalize dependent L.
  generalize dependent X.
  generalize dependent n.
  generalize dependent t.
  induction H.
  Case "multi_refl".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    eapply aux_refl.
    apply H0.
  Case "multi_step".
    intros.
    inversion Heqtnxl.
    subst.
    inversion Heqtnxl'.
    subst.
    clear Heqtnxl Heqtnxl'.
    remember (IHmultistep t' n' X' L' eq_refl t'0 n'0 X'0 L'0 eq_refl) as H'.
    clear HeqH'.
    inversion H2.
    subst.
    remember (Destination.multi_step pr lp t'0 t' t'0 n'0 n' n'0 
      X''0 X' X'0 L''0 L' L'0 H H0 H1) as H''.
    clear HeqH''.
    apply aux_refl in H''.
    inversion H''.
    clear H''.
    subst.
    split. reflexivity. reflexivity.
    subst.
    remember (aux_reduction_determinacy_single pr lp t0 n0 X0 L0
      t' n' X' L' t'1 n'1 X'1 L'1 H0 H14) as H''.
    clear HeqH''.
    inversion H''.
    inversion H4.
    inversion H6.
    subst.
    clear H''.
    apply H' in H15.
    assumption.
  Qed.
    




Corollary full_temp_log_gathers_triggers_event2:
  forall (pr: Source.prog) (pr': prog) (lp: logpol)
         (f: lp_ev) (gs: lp_trigs) (l: lp_level) (psi: prop)
         (kappa: lp_refin) (t v: Source.tm)
         (n m: nat) (Theta: trace),
  retro pr lp pr' ->
  lp = lgpl f gs l psi kappa ->
  wellformed_lp lp ->
  (forall gi : fid,
      inlist gi gs ->
      exists (ni : nat) (vi : tm),
        inlist (Call (proper_nat ni) gi vi) (trace_to_props Theta) /\
        true = ble_nat ni m /\ ni <> m) -> 
  [pr]: (t,0) ==>* (v,n,Theta) ->
  exists (X L: list prop),
    [pr', lp]: (term_transform t,0,nil,nil) ==>* (term_transform v,n,X,L) 
    /\ 
    (forall gi : fid,
      inlist gi gs ->
      exists (ni : nat) (vi : tm),
        inlist (Call (proper_nat ni) gi vi) X /\
        true = ble_nat ni m /\ ni <> m).

(*similar to full_temp_log_gathers_triggers_event, but stated
 differently.*)

Proof.
  intros.
  remember (excluded_middle (exists gi, inlist gi gs)) as H'.
  clear HeqH'.
  inversion H'.
  Case "exists gi, gi in gs".
      clear H'.
      inversion H4.
      clear H4.
      rename x into gi.
      remember H5 as H5'.
      clear HeqH5'.
      apply H2 in H5.
      inversion H5.
      rename x into ni.
      clear H5.
      inversion H4.
      rename x into vi.
      clear H4.
      inversion H5.
      clear H5.
      remember (in_tail gi f gs H5') as H'.
      clear HeqH' H5'.
      remember (full_temp_log_gathers_triggers_event pr pr' lp
        f gs l psi kappa gi t v vi n ni Theta H H0 H1 H' H3 H4) as H''.
      clear HeqH''.
      inversion H''.
      rename x into X.
      clear H''.
      inversion H5.
      rename x into L.
      clear H5.
      inversion H7.
      clear H7.
      eexists.
      eexists.
      split.
      apply H5.
      intros.
      remember H7 as H7'.
      clear HeqH7'.
      apply H2 in H7.
      inversion H7.
      rename x into ni0.
      clear H7.
      inversion H9.
      rename x into vi0.
      clear H9.
      inversion H7.
      clear H7.
      remember (in_tail gi0 f gs H7') as H''.
      clear HeqH'' H7'.
      remember (full_temp_log_gathers_triggers_event pr pr' lp
        f gs l psi kappa gi0 t v vi0 n ni0 Theta H H0 H1 H'' H3 H9) as H'''.
      clear HeqH'''.
      inversion H'''.
      rename x into X'.
      clear H'''.
      inversion H7.
      rename x into L'.
      clear H7.
      inversion H11.
      clear H11.
      remember (aux_reduction_determinacy_multi2 pr' lp (term_transform t) 
        0 nil nil (term_transform v) n X L X' L' H5 H7) as H'''.
      clear HeqH'''.
      inversion H'''.
      clear H'''.
      subst.
      eexists.
      eexists.
      split.
      apply H12.
      assumption.
  Case "~ exists gi, gi in gs".
    clear H'.
    remember (full_temp_log_sublist_trace pr pr' lp t v n Theta H H3 H1) as H'.
    clear HeqH'.
    inversion H'.
    rename x into X.
    clear H'.
    inversion H5.
    rename x into L.
    clear H5.
    inversion H6.
    clear H6 H7.
    eexists.
    eexists.
    split.
    apply H5.
    intros.
    apply ex_falso_quodlibet.
    apply H4.
    eexists.
    apply H6.
  Qed.


(*simlog: to connect trace with log for a program*)
Inductive simlog : logpol -> Source.prog -> prog -> trace -> list prop -> Prop :=
  | sl_constr: forall (lp: logpol) (pr': prog)
                      (tp t: Source.tm) (n: nat) (C: Source.code_base)
                      (o: ow) (Theta: trace) (X L:list prop),
               retro (Source.prg tp o C) lp pr' ->               
               [Source.prg tp o C]: (tp, 0) ==>* (t,n, Theta) ->
               [pr', lp]: (term_transform tp, 0, nil, nil) ==>* 
                          (term_transform t, n, X, L) ->
                simlog lp (Source.prg tp o C) pr' Theta L.




Lemma full_log_LHM_Lang:
  forall (pr: Source.prog) (pr': prog) (lp: logpol) (f: lp_ev)
         (gs: lp_trigs) (l:lp_level) (psi: prop) (kappa: lp_refin) 
         (Theta: trace) (L: list prop) (n: nat) (arg: tm),
  retro pr lp pr' ->
  lp = lgpl f gs l psi kappa ->
  wellformed_lp lp ->
  simlog lp pr pr' Theta L ->
  (inlist (LoggedCall (proper_nat n) f arg) L <->
   inlist (LoggedCall (proper_nat n) f arg) (LHM (psi::(trace_to_props Theta))) 
   /\ inlist (LoggedCall (proper_nat n) f arg) (Lang kappa)).

Proof.
  intros.
  split.
  Case "->".
    intros.
    inversion H2.
    subst.
    inversion H.
    subst.
    remember (full_temp_log_entails_logcondition (prg (term_transform tp) o C') 
      (lgpl f gs l psi kappa) f gs l psi kappa (term_transform tp) 
      (term_transform t) arg n0 n 
      X L eq_refl H3 H6) as H'.
    clear HeqH'.
    apply logcondition_entail in H'.
    remember (sublist_log_LHM n f arg X gs psi Theta H') as H''.
    clear HeqH''.
    remember (full_temp_log_in_LHM (Source.prg tp o C) 
      (prg (term_transform tp) o C')
      (lgpl f gs l psi kappa) f gs l psi kappa tp t o C n0 Theta
      eq_refl H eq_refl H1 H5) as H'''.
    clear HeqH'''.
    inversion H'''.
    inversion H0.
    rename x into X'.
    rename x0 into L'.
    inversion H7.
    clear H''' H0 H7.
    (*old: apply term_transform_normal_form in H9.*)
    remember (aux_reduction_determinacy_multi2 
      (prg (term_transform tp) o C') (lgpl f gs l psi kappa)
      (term_transform tp) 0 nil nil (term_transform t) n0 X L X' L' H6 H8).
    inversion a.
    clear Heqa a.
    rewrite <- H0 in H9.
    apply H'' in H9.
    clear H' H''.
    apply LHM_contains1 in H9.
    split.
    assumption.
    inversion H1.
    subst.
    unfold lp_refinement_mk.
    apply Lang_contain.
  Case "<-".
    intros.
    inversion H2.
    subst.
    inversion H.
    subst.
    inversion H3.
    clear H3.
    remember (LHM_contains2 (lgpl f gs l psi kappa) 
      n f arg psi Theta gs l kappa eq_refl H0) as H'.
    clear HeqH'.
    apply Calls_LHM_trace in H'.
    inversion H'.
    clear H'.
    remember (destruct_trace (Source.prg tp o C) 
      (lgpl f gs l psi kappa) f gs l psi kappa 
      tp t arg 0 n0 n Theta eq_refl H5 H3 H8) as H'.
    clear HeqH'.
    inversion H'.
    rename x into t''.
    clear H'.
    inversion H9.
    rename x into n''.
    clear H9.
    inversion H10.
    rename x into Theta'.
    clear H10.
    inversion H9.
    clear H9.
    inversion H11.
    clear H11.
    inversion H12.
    rename x into t'''.
    clear H12.
    inversion H11.
    rename x into n'''.
    clear H11.
    inversion H12.
    rename x into theta.
    clear H12.
    inversion H11.
    clear H11.
    inversion H13.
    clear H13.
    inversion H14.
    rename x into Theta''.
    clear H14.
    inversion H13.
    clear H13.
    
    remember (full_temp_log_gathers_triggers_event2
      (Source.prg tp o C) (prg (term_transform tp) o C')
      (lgpl f gs l psi kappa) f gs l psi kappa tp t'' n'' n Theta'
      H eq_refl H1 H9 H10) as H'.
    clear HeqH'.
    inversion H'.
    inversion H13.
    clear H' H13.
    rename x into X'.
    rename x0 into L'.
    inversion H18.
    clear H18.
    remember (loggedcall_in_log (Source.prg tp o C) 
      (prg (term_transform tp) o C')
      (lgpl f gs l psi kappa) f gs l psi kappa
      t'' t''' arg n'' n''' n theta X' L' H
      eq_refl H1 H12 H11 H19) as H'.
    clear HeqH'.
    inversion H'.
    rename x into X''.
    clear H'.
    inversion H18.
    rename x into L''.
    clear H18.
    inversion H20.
    clear H20.
    remember (temp_log_subtract_sublist_trace (Source.prg tp o C) 
      (prg (term_transform tp) o C') (lgpl f gs l psi kappa) t''' t
      n''' n0 Theta'' X'' L'' H H14 H1) as H'.
    clear HeqH'.
    inversion H'.
    rename x into X'''.
    clear H'.
    inversion H20.
    rename x into L'''.
    clear H20.
    inversion H22.
    clear H22.
    remember (aux_multi_step_transitivity (prg (term_transform tp) o C')
      (lgpl f gs l psi kappa) (term_transform tp)
      (term_transform t'') (term_transform t''') 0 n'' n''' nil X' X''
      nil L' L'' H13 H18) as H'.
    clear HeqH'.
    remember (aux_multi_step_transitivity (prg (term_transform tp) o C')
      (lgpl f gs l psi kappa) (term_transform tp)
      (term_transform t''') (term_transform t) 0 n''' n0 nil X'' X'''
      nil L'' L''' H' H20) as H''.
    clear H' HeqH''.
    (*apply term_transform_normal_form in H7.*)
    remember (aux_reduction_determinacy_multi2 (prg (term_transform tp) o C')
      (lgpl f gs l psi kappa) (term_transform tp) 0 nil nil
      (term_transform t) n0 X L X''' L''' H6 H'').
    clear Heqa.
    inversion a.
    clear a.
    apply logs_get_bigger_multi in H20.
    inversion H20.
    clear H25.
    rewrite <- H24 in H26.
    eapply inlist_subtract_sublist.
    apply H21.
    assumption.
  Qed.
    
    














