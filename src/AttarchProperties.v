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
      destruct a as [? a]; change ⟨_, a⟩ with (box a) in *.
      simpl_rws.
      follows eapply IHHstar.
    + invc H; invc H0; rw_solver.
Qed.


Definition useram_key_secure : tprop attarch_state := <[λ '(_, Γ),
  forall c key_t (key: key_t),
    read Γ c "useram_key" key -> 
    c = "useram"
]>.

(* Definition finish_setup : tprop attarch_state := <[λ '(l, _),
  exists l', l = sel4_run l' (vm_run useram_listen)
]>. *)

Definition setup_finished : tprop attarch_state := <[λ '(l, _),
  exists pl ul, 
    l = sel4_run pl (vm_run ul) /\
    ul <> useram_wait_key
]>.

Theorem useram_key_uncompromised_setup : forall s0,
  is_init_attarch_state s0 ->
  attarch_trans @s0 ⊨ A[useram_key_secure W setup_finished].
Proof.
  intros s0 s0_init.
  apply AW_intro_weak.
  - left.
    destruct or s0_init; rewritec s0_init;
    follows tentails!.
  - intros * Hstar [Hsecure Hnot_finished] * H.
    invc H; try (left; rw_solver).
    + left. invc H; rw_solver. 
    + invc H; invc H0; try (left + right; rw_solver).
      (* not true at the moment. Need platam to inspect useram
         before releasing key!
       *)
Abort.

Close Scope tprop_scope.
Close Scope string_scope.