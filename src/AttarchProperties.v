Require Import TransitionSystems.
Require Import Privilege.
Require Import AttarchTrans.

Require Import Ctl.Ctl.
Require Import Glib.Glib.

Open Scope string_scope.
Open Scope tprop_scope.
Open Scope env_scope.

Definition useram_key_secure : tprop attarch_state := <[λ '(l, _),
    forall Γ l' s c,
      l = sel4_run (l', Γ) s ->
      read Γ c "useram_key" good_useram_key -> 
      c = "useram"
  ]>.

Definition diverged : tprop attarch_state :=
  <[λ '(l, _), l = attarch_bot]>.

Ltac star_notation := 
  repeat change (clos_refl_trans_n1 _ ?R) with (R^*) in *.


Theorem useram_key_never_compromised:
  attarch_trans @attarch_init_state ⊨ AG useram_key_secure.
Proof.
  apply star__AG.
  intros * Hstar.
  induct! Hstar; star_notation.
  - follows tentails!.
  - invc H.
    + tentails!.
      intros * [=] H'; subst!.
      follows econtradiction no_lookup_no_read.
    + tentails!.
      intros * [=] H'; subst!.
      follows econtradiction no_lookup_no_read.
    + invc H.
      * tentails! in *.
        intros * [=] H'; subst!.
        eapply IHHstar.
       -- reflexivity.
       -- follows eapply write_unchanged_read'.
      * tentails! in *.
        intros * [=] H'; subst!.
        follows eapply IHHstar.
    + invc H.
      invc H0.
      tentails! in *.
      intros * [=] H'; subst!.
      follows eapply IHHstar.
    + follows tentails!.
Qed.
(* Print Assumptions useram_key_never_compromised. *)


Theorem useram_key_never_compromised':
  attarch_trans @attarch_init_state ⊨ A[useram_key_secure W diverged].
Proof.
  apply AW_intro; split.
  - left. follows tentails!.
  - intros s' seq IH s'' step.
    invc step.
    + left.
      tentails!.
      intros * [=] H'; subst!.
      follows econtradiction no_lookup_no_read.
    + left.
      tentails!.
      intros * [=] H'; subst!.
      follows econtradiction no_lookup_no_read.
    + left.
      invc H.
      * especialize IH; forward IH by apply in_seq_head.
        destruct IH as [IH _].
        tentails! in *.
        intros * [=] H'; subst!.
        eapply IH; [reflexivity|].
        follows eapply write_unchanged_read'.
      * especialize IH; forward IH by apply in_seq_head.
        destruct IH as [IH _].
        tentails! in *.
        intros * [=] H'; subst!.
        follows eapply IH.
    + left.
      invc H.
      invc H0.
      especialize IH; forward IH by apply in_seq_head.
      destruct IH as [IH _].
      tentails! in *.
      intros * [=] H'; subst!.
      follows eapply IH.
    + right.
      follows tentails!.
Qed.
(* Print Assumptions useram_key_never_compromised'. *)

Close Scope tprop_scope.
Close Scope string_scope.