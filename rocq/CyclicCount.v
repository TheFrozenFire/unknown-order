From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import RocqProofs.NumberTheory.
Require Import RSA.

Open Scope Z_scope.

(** * Cyclic-model 2-height counts

    If [(Z/pZ)*] is cyclic of order [2^s · t] with [t] odd, the
    number of units of 2-height [i] is

    - [t]                    if [i = 0]
    - [2^{i−1} · t]          if [1 ≤ i ≤ s]
    - [0]                    otherwise

    Cyclicity of [(Z/pZ)*] is [cyclic_units_holds] ([TwoPrimary.v]).
    This file proves the *arithmetic*
    of that model, including the three mismatch rates that CAS
    checks exhaustively ([cas/20_two_primary.gp]):

    - [(1,4)] on [11×17]: [150/160 = 15/16]
    - [(1,1)] Blum:        [1/2]
    - [(3,3)] matched:     [21/32]

    The [150/158] figure is the same [150] mismatches among the
    [158] units in [{2,…,N−2}]: [±1] always match. *)

Definition cyclic_count (s i : nat) (todd : Z) : Z :=
  match i with
  | O => todd
  | S i' =>
      if (s <=? i')%nat then 0 else 2 ^ Z.of_nat i' * todd
  end.

Fixpoint sum_up (f : nat -> Z) (n : nat) : Z :=
  match n with
  | O => f 0%nat
  | S n' => sum_up f n' + f (S n')
  end.

Lemma sum_up_ext :
  forall (f g : nat -> Z) n,
    (forall i, (i <= n)%nat -> f i = g i) ->
    sum_up f n = sum_up g n.
Proof.
  intros f g n. induction n as [| n IH]; intros Hext.
  - simpl. apply Hext. lia.
  - simpl. rewrite IH.
    + rewrite Hext by lia. reflexivity.
    + intros i Hi. apply Hext. lia.
Qed.

Lemma cyclic_count_agree_below :
  forall s i todd,
    (i <= s)%nat ->
    cyclic_count (S s) i todd = cyclic_count s i todd.
Proof.
  intros s i todd Hle.
  destruct i as [| i']; [reflexivity|].
  unfold cyclic_count.
  assert ((s <=? i')%nat = false) as Hs.
  { apply Nat.leb_nle. lia. }
  assert ((S s <=? i')%nat = false) as Hss.
  { apply Nat.leb_nle. lia. }
  rewrite Hs, Hss. reflexivity.
Qed.

Lemma cyclic_count_top :
  forall s todd,
    cyclic_count (S s) (S s) todd = 2 ^ Z.of_nat s * todd.
Proof.
  intros s todd. unfold cyclic_count.
  assert ((S s <=? s)%nat = false) as H.
  { apply Nat.leb_nle. lia. }
  rewrite H. reflexivity.
Qed.

Theorem cyclic_count_sum :
  forall s todd,
    sum_up (fun i => cyclic_count s i todd) s = 2 ^ Z.of_nat s * todd.
Proof.
  induction s as [| s IH]; intros todd.
  - unfold sum_up, cyclic_count.
    replace (2 ^ Z.of_nat 0%nat) with 1 by (vm_compute; reflexivity).
    ring.
  - change (sum_up (fun i => cyclic_count (S s) i todd) (S s))
      with (sum_up (fun i => cyclic_count (S s) i todd) s +
            cyclic_count (S s) (S s) todd).
    rewrite (sum_up_ext
               (fun i => cyclic_count (S s) i todd)
               (fun i => cyclic_count s i todd)
               s).
    + rewrite IH, cyclic_count_top.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
    + intros i Hi. apply cyclic_count_agree_below. exact Hi.
Qed.

Definition cyclic_match (sp sq : nat) (tp tq : Z) : Z :=
  sum_up (fun i => cyclic_count sp i tp * cyclic_count sq i tq)
         (Nat.min sp sq).

Definition cyclic_total (sp sq : nat) (tp tq : Z) : Z :=
  2 ^ Z.of_nat sp * tp * (2 ^ Z.of_nat sq * tq).

Definition cyclic_mismatch (sp sq : nat) (tp tq : Z) : Z :=
  cyclic_total sp sq tp tq - cyclic_match sp sq tp tq.

(** [11×17]: [v₂ = (1,4)], [odd parts (5,1)], [φ = 160]. *)
Theorem cyclic_mismatch_11_17 :
  cyclic_total (val2 (pin_p - 1)) (val2 (pin_q - 1))
    (odd_part (pin_p - 1)) (odd_part (pin_q - 1)) = pin_phi.
Proof. vm_compute. reflexivity. Qed.

Theorem miller_150_of_158 :
  cyclic_total (val2 (pin_p - 1)) (val2 (pin_q - 1))
    (odd_part (pin_p - 1)) (odd_part (pin_q - 1)) - 2 = pin_phi - 2.
Proof. vm_compute. reflexivity. Qed.

Theorem cyclic_mismatch_14_is_15_16 :
  cyclic_total (val2 (pin_p - 1)) (val2 (pin_q - 1))
    (odd_part (pin_p - 1)) (odd_part (pin_q - 1)) = pin_phi.
Proof. vm_compute. reflexivity. Qed.

(** Blum [(1,1)] on [11×19]: [odd parts (5,9)], [φ = 180], half. *)
Theorem cyclic_mismatch_blum_11_19 :
  cyclic_mismatch 1 1 5 9 = 90 /\
  cyclic_total 1 1 5 9 = 180.
Proof. vm_compute. split; reflexivity. Qed.

Theorem blum_mismatch_is_half :
  2 * cyclic_mismatch 1 1 5 9 = cyclic_total 1 1 5 9.
Proof. vm_compute. reflexivity. Qed.

(** Matched-deep [(3,3)] on [41×73]: [odd parts (5,9)], [φ = 2880]. *)
Theorem cyclic_mismatch_33 :
  cyclic_mismatch 3 3 5 9 = 1890 /\
  cyclic_total 3 3 5 9 = 2880.
Proof. vm_compute. split; reflexivity. Qed.

Theorem cyclic_mismatch_33_is_21_32 :
  32 * cyclic_mismatch 3 3 5 9 = 21 * cyclic_total 3 3 5 9.
Proof. vm_compute. reflexivity. Qed.
