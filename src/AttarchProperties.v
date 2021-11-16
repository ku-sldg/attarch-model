Require Import Privilege.
Require Import Env.
Require Import AttarchTrans.

Require Import Ctl.Ctl.
Require Import Glib.Glib.

Open Scope string_scope.
Open Scope tprop_scope.
Open Scope env_scope.

Definition useram_key_secure : tprop attarch_state := <[λ '(_, Γ),
  forall c,
    read Γ c "useram_key" good_useram_key -> 
    c = "useram"
]>.

Definition diverged : tprop attarch_state :=
  <[λ '(l, _), l = attarch_bot]>.

Ltac star_notation := 
  repeat change (clos_refl_trans_n1 _ ?R) with (R^*) in *.
  
Theorem useram_key_never_compromised:
  attarch_trans @attarch_good_init_state ⊨ AG useram_key_secure.
Proof.
  tcut (AG <[λ '(_, Γ), forall acc b, Γ "useram_key" = Some (acc, b) ->
             acc = private "useram"]>).
  { apply AG_weaken.
    intros [l Γ].
    tintro H.
    tentails! in *.
    intros * (acc & Hlookup & Hacc).
    do 2 especialize H; forward H by eassumption.
    subst.
    unfold private in Hacc.
    follows apply refl_string_eq in Hacc. }
  apply star__AG.
  intros * Hstar.
  induct! Hstar; star_notation.
  - follows tentails!.
  - invc H.
    + follows tentails!.
    + follows tentails!.
    + invc H;
      tentails! in *;
      intros;
      eapply IHHstar;
      follows write_unchanged_facts.
    + invc H.
      invc H0.
      tentails! in *.
      intros.
      destruct H5 as (acc' & curr & Hlookup & Hacc & ->).
      tedious.
    + follows tentails! in *.
Qed.
      
(* Theorem useram_key_never_compromised':
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
Qed. *)

(* Theorems:
   1. platam key always secure 
   2. useram key perfectly secure until release 
     - This may be trivial since useram doesn't have key until release
     - Maybe not, if the theorem talks about the internal representation 
       stored by the useram
   3. Useram key leak is observed unless malicious component acts, steals, 
      and repairs before platAM notices
   4. useram evidence is trustworthy unless malicious actor interferes 
      and useram interacts before the platform am checks in
 *)

(* Definition platam_key_secure : tprop attarch_state := <[λ '(l, _),
    forall Γ l' s c,
      l = sel4_run (l', Γ) s ->
      read Γ c "useram_key" good_useram_key -> 
      c = "useram"
  ]>. *)


(* Doesn't separation of gammas make this difficult to talk about *every* environment?
   Joining of gammas isn't necessarily at odds with composition. Just need to redefine.
*)


Close Scope tprop_scope.
Close Scope string_scope.