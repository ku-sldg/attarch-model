Require Import Privilege.
Require Import Env.
Require Import AttarchTrans.

Require Import Ctl.Ctl.
Require Import Glib.Glib.

Open Scope string_scope.
Open Scope tprop_scope.
Open Scope env_scope.


Definition diverged : tprop attarch_state :=
  ⟨λ '(l, _), l = attarch_bot⟩.


Definition image_is_good : tprop attarch_state := ⟨λ '(_, Γ),
  exists acc, Γ "good_image" = Some (acc, box true)
⟩.

(* Definition platam_key_is_good : tprop attarch_state := ⟨λ '(_, Γ),
  read Γ "platam" "platam_key" good_platam_key
⟩.

Theorem platam_good_key_good_image : forall s0,
  attarch_trans @s0 ⊨
    is_init_state -->
    image_is_good -->
    AF (platam_key_is_good || diverged).
Proof using.
  intros [l Γ].
  tintros is_init image_good.
  tentails! in *.
  destruct exists image_good acc_image.

  tsimpl.
  intros *.
  destruct or is_init; repeat find inject; [|discriminate].
  
  pose proof (ex_destruct_path _ _ p) as [r peq].
  inv r.
Abort. *)


Lemma good_boot_token_good_image : forall s0,
  attarch_trans @s0 ⊨ 
    is_init_state -->
    AG (
      ⟨λ '(_, Γ), exists acc, Γ "boot_token" = Some (acc, box good_boot_token)⟩ --> 
      image_is_good
    ).
Proof using.
  intros *.
  tintro Hs0.
  apply star__AG.
  intros * Hstar.
  induct! Hstar; star_notation; [|attarch_step_inv];
    try (tintro; tforward IHHstar; rw_solver!).
  { tintro boot_token_lookup.
    tentails! in *.
    follows destruct Hs0 as [->| ->]; simpl in *. }
  { rw_solver!. }
  Unshelve.
  tedious.
Qed.

Lemma good_decrypt_platam_key_inv : forall key token,
  decrypt_platam_key key token = good_platam_key ->
  key = encr_platam_key /\ token = good_boot_token.
Proof using.
  intros * ?.
  follows destruct key, token.
Qed.

Definition platam_key_good : tprop attarch_state := ⟨λ '(_, Γ),
  exists acc, Γ "platam_key" = Some (acc, box good_platam_key)
⟩.

Theorem platam_good_key_good_image : forall s0,
  attarch_trans @s0 ⊨
    is_init_state -->
    AG (platam_key_good --> image_is_good).
Proof using.
  intros *.
  tintro Hs0.
  apply star__AG.
  intros * Hstar.
  induct! Hstar; star_notation; [|attarch_step_inv];
    try (tintro; tforward IHHstar; rw_solver!).
  - tintro H.
    exfalso.
    destruct s0.
    destruct or Hs0; inject Hs0; rw_solver.
  - tintro H.
    tentails!.
    tentails! in H.
    destruct exists H acc.
    destruct H5 as (? & ? & ? & ? & ->).
    inject H.
    apply good_decrypt_platam_key_inv in H as [-> ->].
    unfold decrypt_platam_key.
    clear IHHstar.
    assert (attarch_trans @(sel4_run platam_init x, Γ) ⊨ image_is_good).
    + apply star_in_path in Hstar as [p Hin].
      after etapply good_boot_token_good_image.
      rw_solver!.
    + rw_solver!.
Qed.


Definition platam_key_secure : tprop attarch_state := ⟨λ '(_, Γ),
  forall c key_t (key: key_t),
    read Γ c "platam_key" key -> 
    c = "platam"
⟩.

Theorem platam_key_uncompromised: forall s0,
  attarch_trans @s0 ⊨ 
    is_init_state -->
    AG platam_key_secure.
Proof.
  intros s0.
  tintro s0_init.
  apply star__AG.
  intros s Hstar.
  induct! Hstar; star_notation; [|attarch_step_inv]; try rw_solver.
  - destruct or s0_init;
    rewritec s0_init;
    follows tentails!.
  - tentails! in *.
    intros .
    destruct H5 as (acc & a & lookup & Hacc & ->).
    unbox a.
    simpl_rws.
    follows eapply IHHstar.
Qed.


Definition useram_key_secure : tprop attarch_state := ⟨λ '(_, Γ),
  forall c,
    read Γ c "useram_key" good_useram_key -> 
    c = "useram"
⟩.

Definition useram_key_released : tprop attarch_state := ⟨λ '(l, _),
  exists pl ul,
    l = sel4_run pl (vm_run ul) /\ 
    ul <> useram_wait_key
⟩.

Theorem useram_key_uncompromised_setup : forall s0,
  attarch_trans @s0 ⊨
    is_init_state -->
    A[useram_key_secure W useram_key_released].
Proof.
  intros s0.
  tintros s0_init.
  apply AW_weaken_left
    with (P := ⟨λ '(_, Γ), forall acc v,
      Γ "useram_key" = Some (acc, box v) ->
      v <> good_useram_key
    ⟩).
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
    attarch_step_inv; solve[left + right; rw_solver!].
Qed.


Definition os_corrupted : tprop attarch_state := ⟨λ '(_, Γ),
  exists acc, Γ "good_os" = Some (acc, box false)
⟩.

Theorem os_corrupted_permanent' : forall pl vl Γ,
  attarch_trans @(sel4_run pl vl, Γ) ⊨ os_corrupted --> AG os_corrupted.
Proof using.
  intros *.
  tintro H.
  tentails! in H.
  destruct H as [acc lookup].
  apply star__AG.
  intros * Hstar.
  induct! Hstar; star_notation.
  - follows tentails!.
  - attarch_step_inv; 
      try (invc Hstar; find (fun H => solve[inversion H]));
      rw_solver!.
Qed.

Theorem os_corrupted_permanent : forall s0,
  attarch_trans @s0 ⊨ 
    is_init_state -->
    AG (os_corrupted --> AG os_corrupted).
Proof using.
  intros s0.
  tintros Hs0.
  apply star__AG.
  intros * Hstar.
  induct! Hstar; star_notation.
  - tintro.
    exfalso.
    destruct or Hs0; rewrite Hs0 in *;
      follows tentails! in *.
  - attarch_step_inv; try apply os_corrupted_permanent'.
    clear.
    tintro H.
    apply star__AG.
    intros * Hstar.
    induct! Hstar; star_notation; [|attarch_step_inv]; 
      try (invc Hstar; find (fun H => solve[inversion H]));
      rw_solver!.
Qed.


Definition deep_attesting : tprop attarch_state := ⟨λ '(l, _),
  l = sel4_run platam_deep_attest (vm_run useram_deep_attest)
⟩.

Definition starting_shallow_attest : tprop attarch_state := ⟨λ '(l, _),
  exists pl, l = sel4_run pl (vm_run useram_shallow_attest)
⟩.

Definition finished_shallow_attest : tprop attarch_state := ⟨λ '(l, _),
  exists pl, l = sel4_run pl (vm_run useram_listen)
⟩.

Definition trustworthy_attest_result : tprop attarch_state := ⟨λ '(_, Γ),
  forall acc acc' (b: bool),
    Γ "shallow_attest_result" = Some (acc, box b) ->
    Γ "good_target" = Some (acc', box b)
⟩.

Theorem deep_attest_corruption_window_aux : forall Γ,
  attarch_trans @(sel4_run platam_deep_attest (vm_run useram_listen), Γ) ⊨
    A[(starting_shallow_attest -->
      A[(finished_shallow_attest --> trustworthy_attest_result) W os_corrupted])
    W os_corrupted].
Proof using.
  intros *.
  apply AW_intro_weak.
  - left. rw_solver.
  - intros * Hstar [Htrust Hnot_corrupt] * H.
    invc H; try (left; rw_solver).
    + invc H.
      * left.
        tintros.
        tentails! in *.
        destruct H as [? H].
        inject H.
 
(* 
  intros *.
  apply AW_intro; split.
  - left. rw_solver.
  (* - intros * [Htrust Hnot_corrupt] * Hstep. *)
  - intros * H * Hstep.
    invc Hstep; try (left; rw_solver).
    + invc H0.
      *  *)
Abort.


Theorem deep_attest_corruption_window :
  attarch_trans @attarch_good_init_state ⊨
    AG (deep_attesting -->
      A[(starting_shallow_attest -->
        A[(finished_shallow_attest --> trustworthy_attest_result) W os_corrupted])
      W os_corrupted]).
Proof using.
  intros.
Abort.

(* ⊨ os_corrupted --> AG os_corrupted *)

(* ⊨ AG (deep_attesting --> A[(ul = useram_shallow_attest) --> A[(ul = useram_listen --> good_meas_value) W mal] W mal]) *)

(* Definition foo : tprop attarch_state := <[λ '(l, Γ),
]>. *)


(* ⊨ AG (deep_attest --> A[trustworthy_attest W os_corruption]) *)


(* ⊨ A[(os_corruption --> EF detect_corruption) W diverged] *)
(* ⊨ A[(useram_leak --> EF detect_leak) W diverged] *)


Close Scope tprop_scope.
Close Scope string_scope.
