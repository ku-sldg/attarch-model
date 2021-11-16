Require Import Privilege.
Require Import Env.

Require Import Ctl.BinaryRelations.
Require Import Ctl.Definition.
Require Import Glib.Glib.

Open Scope string_scope.
Open Scope env_scope.


(* value types *)

Inductive boot_token_t :=
  | good_boot_token
  | bad_boot_token.
Inductive vm_ev_t :=
  | good_vm_ev
  | bad_vm_ev.
Inductive platam_key_t :=
  | good_platam_key
  | encr_platam_key
  | bad_platam_key.
Inductive useram_key_t :=
  | good_useram_key
  | encr_useram_key
  | bad_useram_key.
Inductive useram_key_decr_key_t :=
  | good_decr_key
  | encr_decr_key
  | bad_decr_key.


(* Transition definitions *)

Inductive platam_label :=
  | platam_init 
  | platam_meas_release
  | platam_listen.

Definition platam_init_env : env :=
  private "platam" ? (
    "platam_key" ↦ encr_platam_key ;;
    "useram_key_decr_key" ↦ encr_decr_key
  ).

Definition decrypt_platam_key key token : platam_key_t := 
  match (key, token) with 
  | (encr_platam_key, good_boot_token) => good_platam_key
  | _ => bad_platam_key
  end.

Definition decrypt_useram_key_decr_key decr_key platam_key : useram_key_decr_key_t := 
  match (decr_key, platam_key) with 
  | (encr_decr_key, good_platam_key) => good_decr_key
  | _ => bad_decr_key
  end.

Inductive platam_trans : relation (platam_label × env) := 
  | platam_unlock_key : forall Γ Γ' key token,
      read  Γ "platam" "platam_key" key ->
      read  Γ "platam" "boot_token" token ->
      write Γ "platam" "platam_key" (decrypt_platam_key key token) Γ' ->
      platam_trans 
        (platam_init, Γ)
        (platam_meas_release, Γ')
  | platam_measure_release : forall Γ Γ' platam_key decr_key,
      read  Γ "platam" "good_image" true ->
      read  Γ "platam" "useram_key_decr_key" decr_key ->
      read  Γ "platam" "platam_key" platam_key -> 
      write Γ "platam" "vmm_dataport" (decrypt_useram_key_decr_key decr_key platam_key) Γ' ->
      platam_trans 
        (platam_meas_release, Γ)
        (platam_listen, Γ').

(* TODO, bad_platam_trans, *)

Inductive useram_label := 
  | useram_wait_key
  | useram_listen.

Definition useram_init_env : env := 
  private "useram" ? "useram_key" ↦ encr_useram_key.

Definition decrypt_useram_key key decr_key : useram_key_t := 
  match (key, decr_key) with 
  | (encr_useram_key, good_decr_key) => good_useram_key
  | _ => bad_useram_key
  end.

Inductive useram_trans : relation (useram_label × env) :=
  | useram_get_key : forall Γ Γ' encr_key decr_key,
      read  Γ "useram" "useram_key" encr_key ->
      read  Γ "useram" "vmm_dataport" decr_key ->
      write Γ "useram" "useram_key" (decrypt_useram_key encr_key decr_key) Γ' ->
      useram_trans 
        (useram_wait_key, Γ)
        (useram_listen, Γ').

Inductive vm_label := 
  | vm_run : useram_label -> vm_label.

Inductive vm_trans : relation (vm_label × env) := 
  | useram_step : forall x y Γ Γ',
      useram_trans (x, Γ) (y, Γ') ->
      vm_trans (vm_run x, Γ) (vm_run y, Γ').

Inductive attarch_label :=
  | boot
  | sel4_run : platam_label -> vm_label -> attarch_label
  | attarch_bot.

Definition attarch_state := attarch_label × env.

Inductive attarch_trans : relation attarch_state :=
  | boot_good : forall Γ,
      read Γ "root_of_trust" "good_image" true -> 
      attarch_trans
        (boot, Γ)
        (sel4_run platam_init (vm_run useram_wait_key),
          allReadOnly ? "boot_token" ↦ good_boot_token ;;
          platam_init_env ;;
          useram_init_env ;;
          Γ
        )
  | boot_bad : forall Γ,
      read Γ "root_of_trust" "good_image" false -> 
      attarch_trans
        (boot, Γ)
        (sel4_run platam_init (vm_run useram_wait_key),
          allReadOnly ? "boot_token" ↦ bad_boot_token ;;
          platam_init_env ;;
          useram_init_env ;;
          Γ
        )
  | platam_step : forall x l l' Γ Γ',
      platam_trans (l, Γ) (l', Γ') ->
      attarch_trans 
        (sel4_run l x, Γ)
        (sel4_run l' x, Γ')
  | vm_step : forall x l l' Γ Γ',
      vm_trans (l, Γ) (l', Γ') ->
      attarch_trans 
        (sel4_run x l, Γ)
        (sel4_run x l', Γ')
 | attarch_diverge : forall l Γ,
      attarch_trans (l, Γ) (attarch_bot, Γ).

Definition attarch_good_init_state : attarch_state := 
  (boot, allReadOnly ? "good_image" ↦ true).

Definition attarch_bad_init_state : attarch_state := 
  (boot, allReadOnly ? "good_image" ↦ false).

Lemma attarch_trans_serial : 
  serial_witness attarch_trans.
Proof using.
  follows cbv.
  (* unfold serial_witness.
  intros [l ?].
  eexists.
  apply attarch_diverge. *)
Defined.

Instance transition__attarch_trans : transition attarch_trans :=
  { trans_serial := attarch_trans_serial }.

Close Scope env_scope.
Close Scope string_scope.
