Require Import Ctl.BinaryRelations.

Require Import Glib.Glib.
Require Import Coq.Strings.String.

Require Export Coq.Strings.String.

Open Scope string_scope.


Inductive privilege : Set :=
  | p_read 
  | p_write.
  (* | exec. *)

Definition comp := string.

Definition access := comp -> privilege -> bool.


Definition acc_union (a1 a2: access) : access := λ c p,
  orb (a1 c p) (a2 c p).
Notation "a1 ⊔ a2" := (acc_union a1 a2)
  (at level 50, left associativity).

Definition acc_inter (a1 a2: access) : access := λ c p,
  andb (a1 c p) (a2 c p).
Notation "a1 ⊓ a2" := (acc_inter a1 a2)
  (at level 40, left associativity).

Definition acc_le (a1 a2: access) : Prop := forall c p,
  (* Bool.le (a1 c p) (a2 c p). *)
  (a1 c p) -> (a2 c p).
Notation "a1 ⊑ a2" := (acc_le a1 a2)
  (at level 70).

Definition acc_bot : access := λ _ _, false.

Definition acc_top : access := λ _ _, true.


Lemma acc_union_assoc : forall a1 a2 a3,
  a1 ⊔ (a2 ⊔ a3) = a1 ⊔ a2 ⊔ a3.
Proof using.
  intros *.
  extensionality c p.
  apply Bool.orb_assoc.
Qed.

Lemma acc_union_comm : forall a1 a2,
  a1 ⊔ a2 = a2 ⊔ a1.
Proof using.
  intros *.
  extensionality c p.
  apply Bool.orb_comm.
Qed.

Lemma acc_bot_union_l : forall a,
  acc_bot ⊔ a = a.
Proof using.
  intros *.
  extensionality c p.
  follows cbn.
Qed.

Lemma acc_bot_union_r : forall a,
  a ⊔ acc_bot = a.
Proof using.
  intros *.
  rewrite acc_union_comm.
  apply acc_bot_union_l.
Qed.

Lemma acc_top_union_l : forall a,
  acc_top ⊔ a = acc_top.
Proof using.
  intros *.
  extensionality c p.
  follows cbn.
Qed.

Lemma acc_top_union_r : forall a,
  a ⊔ acc_top = acc_top.
Proof using.
  intros *.
  rewrite acc_union_comm.
  apply acc_top_union_l.
Qed.

Lemma acc_inter_assoc : forall a1 a2 a3,
  a1 ⊓ (a2 ⊓ a3) = a1 ⊓ a2 ⊓ a3.
Proof using.
  intros *.
  extensionality c p.
  apply Bool.andb_assoc.
Qed.

Lemma acc_inter_comm : forall a1 a2,
  a1 ⊓ a2 = a2 ⊓ a1.
Proof using.
  intros *.
  extensionality c p.
  apply Bool.andb_comm.
Qed.

Lemma acc_bot_inter_l : forall a,
  acc_bot ⊓ a = acc_bot.
Proof using.
  intros *.
  extensionality c p.
  follows cbn.
Qed.

Lemma acc_bot_inter_r : forall a,
  a ⊓ acc_bot = acc_bot.
Proof using.
  intros *.
  rewrite acc_inter_comm.
  apply acc_bot_inter_l.
Qed.

Lemma acc_top_inter_l : forall a,
  acc_top ⊓ a = a.
Proof using.
  intros *.
  extensionality c p.
  follows cbn.
Qed.

Lemma acc_top_inter_r : forall a,
  a ⊓ acc_top = a.
Proof using.
  intros *.
  rewrite acc_inter_comm.
  apply acc_top_inter_l.
Qed.

Lemma acc_bot_le : forall a,
  acc_bot ⊑ a.
Proof using.
  tedious.
Qed.

Lemma acc_le_top : forall a,
  a ⊑ acc_top.
Proof using.
  unfold acc_le.
  intros *.
  follows destruct (a c p).
Qed.

Lemma acc_union_le_l : forall a1 a2,
  a1 ⊑ a1 ⊔ a2.
Proof using.
  unfold acc_le, acc_union.
  intros *.
  follows destruct (a1 c p).
Qed.

Lemma acc_union_le_r : forall a1 a2,
  a2 ⊑ a1 ⊔ a2.
Proof using.
  unfold acc_le, acc_union.
  intros *.
  follows destruct (a1 c p), (a2 c p).
Qed.

Lemma acc_inter_le_l : forall a1 a2,
  a1 ⊓ a2 ⊑ a1.
Proof using.
  unfold acc_le, acc_inter.
  intros *.
  follows destruct (a1 c p), (a2 c p).
Qed.

Lemma acc_inter_le_r : forall a1 a2,
  a1 ⊓ a2 ⊑ a2.
Proof using.
  unfold acc_le, acc_inter.
  intros *.
  follows destruct (a1 c p), (a2 c p).
Qed.


Definition readable : access := λ _ p,
  match p with 
  | p_read => true 
  | _    => false 
  end.

Definition canRead (c: comp) : access := λ c' p,
  match p with 
  | p_read => c =? c'
  | _ => false
  end.

Definition writable : access := λ _ p,
  match p with 
  | p_write => true 
  | _    => false 
  end.

Definition canWrite (c: comp) : access := λ c' p,
  match p with 
  | p_write => c =? c'
  | _ => false
  end.

Definition only (c: comp) : access := λ c' _, c =? c'.
 
Close Scope string_scope.