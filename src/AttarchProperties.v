Require Import Privilege.
Require Import Env.
Require Import AttarchTrans.

Require Import Ctl.Ctl.
Require Import Glib.Glib.

Open Scope string_scope.
Open Scope tprop_scope.
Open Scope env_scope.


Ltac star_notation := 
  repeat change (clos_refl_trans_n1 _ ?R) with (R^*) in *.


Definition diverged : tprop attarch_state :=
  <[λ '(l, _), l = attarch_bot]>.


Definition platam_key_secure : tprop attarch_state := <[λ '(_, Γ),
  forall c key_t (key: key_t),
    read Γ c "platam_key" key -> 
    c = "platam"
]>.

Theorem platam_key_uncompromised: forall s0,
  is_init_attarch_state s0 ->
  attarch_trans @s0 ⊨ AG platam_key_secure.
Proof.
  intros s0 s0_init.
  apply star__AG.
  intros s Hstar.
  induct! Hstar; star_notation.
  - destruct or s0_init;
    rewritec s0_init;
    follows tentails!.
  - invc H; try rw_solver.
    + invc H; try rw_solver.
      tentails! in *.
      intros .
      destruct H5 as (acc & a & lookup & Hacc & ->).
      unbox a.
      simpl_rws.
      follows eapply IHHstar.
    + invc H; invc H0; rw_solver.
Qed.


Definition useram_key_secure : tprop attarch_state := <[λ '(_, Γ),
  forall c,
    read Γ c "useram_key" good_useram_key -> 
    c = "useram"
]>.

(* Definition useram_key_released : tprop attarch_state := <[λ '(l, _),
  exists vl, l = sel4_run platam_listen vl
]>. *)

Definition useram_key_released : tprop attarch_state := <[λ '(l, _),
  exists pl ul,
    l = sel4_run pl (vm_run ul) /\ 
    ul <> useram_wait_key
]>.

Theorem useram_key_uncompromised_setup : forall s0,
  is_init_attarch_state s0 ->
  attarch_trans @s0 ⊨ A[useram_key_secure W useram_key_released].
Proof.
  intros s0 s0_init.
  apply AW_weaken_left
    with (P := <[λ '(_, Γ), forall acc v,
      Γ "useram_key" = Some (acc, box v) ->
      v <> good_useram_key
    ]>).
  { intros [l Γ].
    tintro H.
    tentails! in *.
    intros.
    exfalso.
    destruct H0 as (? & ? & ?).
    follows eapply H. }
  apply AW_intro_weak.
  - left.
    destruct or s0_init; 
    rewrite s0_init;
    rw_solver.
  - intros * Hstar Hs' * H.
    destruct Hs' as [Hs'l Hs'r].
    invc H.
    + left. rw_solver with find inject.
    + left. rw_solver with find inject.
    + invc H; left; rw_solver.
    + invc H; invc H0; try (left + right; rw_solver).
      left.
      tentails! in *.
      destruct H as (acc & V & v & lookup & ->).
      intros acc' key Hacc'.
      inject Hacc'.
      eapply Hs'l.
      eassumption.
    + left. rw_solver.
Qed.
 

Close Scope tprop_scope.
Close Scope string_scope.