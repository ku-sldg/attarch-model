Require Import Privilege.

Require Import Ctl.BinaryRelations.
Require Import Glib.Glib.

Open Scope string_scope.

(* Partial mappings of variable names to heterogeneous values paired with access controls *)


Definition any : Type := Σ t: Type, t.
Definition box {t} (x: t) : any := existT (λ x, x) t x.

Definition unbox {A} (b: any) (elim: forall t, t -> A) : A :=
  elim (projT1 b) (projT2 b).

(* TODO: abstract as a section variable? *)
Definition var  := string.
Definition comp := string.

Definition env := var -> option (access × any).

Declare Scope env_scope.
(* Delimit Scope env_scope with env. *)
Bind Scope env_scope with env.
Open Scope env_scope.


Definition env_empty: env := λ _, None.
Notation "•" := env_empty : env_scope.

Definition env_singleton {V} var (acc: access) (v: V): env := λ lookup,
  if lookup =? var then Some (acc, box v) else None.
Notation "var ↦ v" := (env_singleton var allAcc v)
  (at level 55, right associativity) : env_scope.

Definition map_access (Γ: env) (acc: access): env := λ lookup, 
  match Γ lookup with 
  | Some (_, v) => Some (acc, v)
  | None => None
  end.
Notation "acc ? Γ" := (map_access Γ acc)
  (at level 60) : env_scope.
  (* (at level 60, format "acc ?  Γ") : env_scope. *)

(* First env shadows definitions in second *)
Definition env_concat (Γ1 Γ2: env) : env := λ lookup,
  match Γ1 lookup with 
  | Some v => Some v 
  | None => Γ2 lookup
  end.
Notation "Γ1 ;; Γ2" := (env_concat Γ1 Γ2)
  (at level 65, right associativity) : env_scope.

Definition read {V} (Γ: env) (c: comp) (name: var) (v: V) : Prop :=
  exists acc: access, 
    Γ name = Some (acc, box v) /\
    acc c p_read.

Definition write {V} (Γ: env) (c: comp) (name: var) (v: V) (Γ': env) : Prop :=
  exists (acc: access) curr,
    Γ name = Some (acc, curr) /\ 
    acc c p_write /\ 
    Γ' = acc ? name ↦ v ;; Γ.

Definition remove_var (Γ: env) var : env := λ lookup,
  if lookup =? var then None else Γ lookup.

Lemma map_acc_env_singleton : forall acc x V (v: V),
  (acc ? x ↦ v) = env_singleton x acc v.
Proof using.
  intros *.
  extensionality y.
  unfold env_singleton.
  replace (
    acc ? (λ lookup, 
      if lookup =? x
      then Some (allAcc, box v) 
      else None))
  with
    (λ lookup, 
      if lookup =? x
      then Some (acc, box v) 
      else None
  ).
  - reflexivity.
  - extensionality lookup.
    unfold map_access.
    follows destruct (lookup =? x).
Qed.

Lemma refl_string_eq : forall x y,
  x =? y ->
  x = y.
Proof using.
  intros * ?.
  follows destruct (eqb_spec x y).
Qed.

Theorem concat_assoc : forall Γ1 Γ2 Γ3,
  (Γ1;; Γ2);; Γ3 = Γ1;; (Γ2;; Γ3).
Proof using.
  intros *.
  extensionality s.
  cbv.
  follows destruct (Γ1 s).
Qed.

Theorem env_singleton_inv : forall acc x y V (v: V) v',
  (acc ? x ↦ v) y = Some v' ->
  x = y /\ v' = (acc, box v).
Proof using.
  intros * H.
  rewrite map_acc_env_singleton in H.
  unfold env_singleton in H.
  destruct (y =? x) eqn:case; [|discriminate].
  apply refl_string_eq in case as ->.
  follows inv H.
Qed.

Theorem env_prepend_singleton_unchanged : forall (Γ: env) x y acc V (v: V),
  x <> y ->
  Γ y = (acc ? x ↦ v ;; Γ) y.
Proof using.
  intros * Hneq.
  unfold env_concat.
  destruct ((acc ? x ↦ v) y) eqn:case. 
  - apply env_singleton_inv in case as [-> _].
    contradiction.
  - reflexivity.
Qed.

(* Theorem write_unchanged : forall Γ Γ' x y c V (v: V), *)
Theorem write_unchanged {Γ Γ' x y c V} {v: V}:
  write Γ c x v Γ' ->
  x <> y ->
  Γ y = Γ' y.
Proof using.
  intros * Hwrite Hneq.
  destruct Hwrite as (acc & curr & ? & ? & ->).
  follows apply env_prepend_singleton_unchanged.
Qed.

(* Theorem write_unchanged_read : forall Γ Γ' x y c c' V (v: V) V' (v': V'), *)
Theorem write_unchanged_read {Γ Γ' x y c c' V V'} {v: V} {v': V'}:
  x <> y ->
  write Γ c x v Γ' ->
  read Γ c' y v' ->
  read Γ' c' y v'.
Proof using. 
  intros Hneq Hwrite Hread.
  unfold read in *.
  destruct Hread as (acc & Hlookup & Hacc).
  exists acc.
  split.
  - rewrite <- Hlookup.
    symmetry.
    follows eapply write_unchanged.
  - assumption.
Qed.

(* Theorem write_unchanged_read' : forall Γ Γ' x y c c' V (v: V) V' (v': V'), *)
Theorem write_unchanged_read' {Γ Γ' x y c c' V V'} {v: V} {v': V'}:
  x <> y ->
  write Γ c x v Γ' ->
  read Γ' c' y v' ->
  read Γ c' y v'.
Proof using. 
  intros Hneq Hwrite Hread.
  unfold read in *.
  destruct Hread as (acc & Hlookup & Hacc).
  exists acc.
  split.
  - rewrite <- Hlookup.
    follows eapply write_unchanged.
  - assumption.
Qed.

Theorem no_lookup_no_read {Γ c x V} {v: V}:
  Γ x = None -> ~ read Γ c x v.
Proof using.
  intros * Heq Hread.
  destruct Hread as (acc & Heq' & _).
  rewrite Heq in Heq'.
  discriminate Heq'.
Qed.

Theorem wrong_lookup_no_read {Γ acc c x V} {w v: V}:
  Γ x = Some (acc, box w) ->
  w <> v ->
  ~ read Γ c x v.
Proof using.
  intros * Heq Hneq (? & Heq' & ?).
  rewritec Heq' in Heq.
  follows inject Heq.
Qed.

Theorem good_lookup_read {Γ acc c x V} {w v: V}:
  Γ x = Some (acc, box w) ->
  read Γ c x v ->
  w = v.
Proof using.
  intros * Heq (? & Heq' & ?).
  rewritec Heq' in Heq.
  follows inject Heq.
Qed.

Theorem good_lookup_read_replace {Γ acc c x V} {w v: V}:
  Γ x = Some (acc, box w) ->
  read Γ c x v ->
  read Γ c x w.
Proof using.
  intros * Heq Hread.
  inv Hread as (? & Heq' & ?).
  rewritec Heq' in Heq.
  follows inject Heq.
Qed.
  
Corollary wrong_lookup_no_read_single_hyp {Γ c x V} {v: V}:
  (exists acc (w: V), Γ x = Some (acc, box w) /\ w <> v) ->
  ~ read Γ c x v.
Proof using.
  intros H.
  repeat destructr H.
  follows eapply wrong_lookup_no_read.
Qed.

Theorem read_concat_inv {V}: forall Γ1 Γ2 c x (v: V),
  read (Γ1 ;; Γ2) c x v ->
  read Γ1 c x v \/ (Γ1 x = None /\ read Γ2 c x v).
Proof using.
  intros * H.
  unfold read in H.
  destruct (Γ1 x) eqn:case; [left|right].
  - destruct H as (acc & lookup & H).
    unfold env_concat in lookup.
    follows rewrite case in lookup.
  - destruct H as (acc & lookup & H).
    unfold env_concat in lookup.
    follows rewrite case in lookup.
Qed. 

Theorem read_concat_inv_l {V Γ1 Γ2 c x l} {v: V}:
  Γ1 x = Some l ->
  read (Γ1 ;; Γ2) c x v ->
  read Γ1 c x v.
Proof using.
  intros * Heq Hread.
  unfold read, env_concat in Hread.
  rewrite Heq in Hread.
  destruct Hread as (acc & [=->] & Hread).
  tedious.
Qed.

Theorem read_concat_inv_l_negative {V Γ1 Γ2 c x} {v: V}:
  Γ1 x <> None ->
  read (Γ1 ;; Γ2) c x v ->
  read Γ1 c x v.
Proof using.
  intros * Hneq Hread.
  destruct (Γ1 x) eqn:case.
  - clear Hneq.
    unfold read, env_concat in Hread.
    rewrite case in Hread.
    destruct Hread as (acc & [=->] & Hread).
    tedious.
  - follows contradict Hneq.
Qed.

Theorem read_concat_inv_r {V Γ1 Γ2 c x} {v: V}:
  Γ1 x = None ->
  read (Γ1 ;; Γ2) c x v ->
  read Γ2 c x v.
Proof using.
  intros * Heq Hread.
  unfold read, env_concat in Hread.
  follows rewrite Heq in Hread.
Qed. 
 

Ltac lookup_read H Heq :=
  match type of H with 
  | read ?Γ _ ?x _ =>
      let lookup := eval cbn in (Γ x) in
      first [
        (match lookup with 
        | Some _ => idtac
        | None => idtac
        end)
      | fail 1 "(" Γ x ") does not reduce to a canonical form"];
      pose proof (eq_refl : Γ x = lookup) as Heq
  end.

Ltac clookup Γ x cont :=
  let lookup := eval cbn in (Γ x) in
  first [
    (match lookup with 
    | Some _ => idtac
    | None => idtac
    end)
  | fail 1 "(" Γ x ") does not reduce to a canonical form"];
  cont lookup.

Ltac simpl_read H :=
  match type of H with 
  | read (?Γ1 ;; ?Γ2) _ ?x _ =>
      clookup Γ1 x ltac:(fun lookup =>
        match lookup with
        | Some ?l => simple apply (read_concat_inv_l (eq_refl : Γ1 x = Some l)) in H
        | None => simple apply (read_concat_inv_r (eq_refl : Γ1 x = None)) in H
        end
      )
  | read ?Γ _ ?x _ =>
      clookup Γ x ltac:(fun lookup =>
        let Heq := fresh "Heq" in
        pose proof (eq_refl : Γ x = lookup) as Heq;
        match lookup with 
        | Some (_, box _) =>
            (* This branch should also add to the environment that the reading 
               component obeys the access rule we found *)
            let veq := fresh in 
            let veq_term := constr:(good_lookup_read Heq H) in
            lazymatch type of veq_term with 
            | ?x = ?x => fail
            | _ => idtac
            end;
            pose new proof veq_term as veq;
            try discriminate veq;
            subst          
        | None => exact (False_rect _ (no_lookup_no_read Heq H))
        end;
        try clear Heq
      )
  end.

Ltac simpl_reads := repeat find simpl_read.


Theorem no_lookup_no_write {Γ c x V} {v: V} {Γ'}:
  Γ x = None -> ~ write Γ c x v Γ'.
Proof using.
  intros * Heq (? & ? & lookup & _).
  rewrite Heq in lookup.
  discriminate lookup.
Qed.

Theorem good_lookup_write {Γ acc c x l V} {v: V} {Γ'}:
  Γ x = Some (acc, l) ->
  write Γ c x v Γ' ->
  Γ' = acc ? x ↦ v;; Γ.
Proof using.
  intros * Heq (acc' & curr & lookup & ? & ->).
  rewritec Heq in lookup.
  follows inject lookup.
Qed.

Ltac simpl_write H :=
  match type of H with 
  | write ?Γ _ ?x _ ?Γ' =>
      clookup Γ x ltac:(fun lookup =>
        let Heq := fresh "Heq" in
        pose proof (eq_refl : Γ x = lookup) as Heq;
        match lookup with 
        | Some (_, _) => 
            let Γeq := fresh in 
            let Γeq_term := constr:(good_lookup_write Heq H) in
            lazymatch type of Γeq_term with 
            | ?x = ?x => fail
            | _ => idtac
            end;
            pose new proof Γeq_term as Γeq;
            try discriminate Γeq;
            subst
        | None => exact (False_rect _ (no_lookup_no_write Heq H))
        end;
        try clear Heq
      )
  end.

Ltac simpl_writes := repeat find simpl_write.

Ltac write_unchanged_facts :=
  repeat match goal with 
  | Hwrite : write ?Γ _ ?x _ ?Γ' |- _ =>
      repeat match goal with 
      | Hread : read Γ _ ?y _ |- _ =>
          let Heq := fresh "Heq" in
          assert (Heq: x <> y) by discriminate;
          pose new proof (write_unchanged_read Heq Hwrite Hread);
          try clear Heq
      | Hread  : read Γ' _ ?y _ |- _ =>
          let Heq := fresh "Heq" in
          assert (Heq: x <> y) by discriminate;
          pose new proof (write_unchanged_read' Heq Hwrite Hread);
          try clear Heq
      | lookup : context[Γ ?y] |- _ =>
          let Heq := fresh "Heq" in
          assert (Heq: x <> y) by discriminate;
          pose new proof (write_unchanged Hwrite Heq);
          try clear Heq
      | lookup : context[Γ' ?y] |- _ =>
          let Heq := fresh "Heq" in
          assert (Heq: x <> y) by discriminate;
          pose new proof (write_unchanged Hwrite Heq);
          try clear Heq
      | |- context[Γ ?y] =>
          let Heq := fresh "Heq" in
          assert (Heq: x <> y) by discriminate;
          pose new proof (write_unchanged Hwrite Heq);
          try clear Heq
      | |- context[Γ' ?y] =>
          let Heq := fresh "Heq" in
          assert (Heq: x <> y) by discriminate;
          pose new proof (write_unchanged Hwrite Heq);
          try clear Heq
      end
  end.

Ltac simpl_rws := repeat find (fun H => simpl_read H || simpl_write H).

Tactic Notation "simpl_rws!" := 
  repeat (simpl_rws || write_unchanged_facts).

Close Scope env_scope.
Close Scope string_scope.
