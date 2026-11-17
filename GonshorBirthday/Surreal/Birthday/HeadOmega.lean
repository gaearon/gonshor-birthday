/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadPerturbation

import GonshorBirthday.Surreal.Birthday.HeadMidpoint
import GonshorBirthday.Surreal.Birthday.Omega
import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient

/-!
# Varying-exponent canonical right prefixes after higher heads

A canonical right exponent below the entire head transports through that head.
When right-exponent values have no least element and one lies below the head,
these actual headed prefixes form a coinitial gap-halving family.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem realCast_inv_two_pow (n : ℕ) :
    Real.toSurreal ((2 : ℝ)⁻¹ ^ n) = (2 : Surreal.{u})⁻¹ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.toSurreal_mul, ih, Real.toSurreal_inv]
    norm_num only [Real.toSurreal_ofNat]
    rw [pow_succ]

/-- A right exponent below the head gives a headed canonical right prefix. -/
theorem head_wpow_mem_rightPrefixes (K : Surreal.{u}) {s w : Surreal.{u}}
    (hw : w ∈ rightPrefixes s) (hK : K.support ⊆ Ioi w) :
    K + ω^ w ∈ rightPrefixes (K + ω^ s) := by
  have hp := birthdayTruncation_wpow_birthdayTruncation s w.birthday
  rw [(mem_rightPrefixes_iff.mp hw).1] at hp
  have hsw := wpow_lt_wpow.mpr (mem_rightPrefixes_iff.mp hw).2
  have hpre := birthdayTruncation_head_add_of_abs_sub_le_real_mul_wpow hK hp (1 : ℝ)
    (show |ω^ s - ω^ w| ≤ ((1 : ℝ) : Surreal) * ω^ w by
      rw [Real.toSurreal_one, one_mul, abs_of_neg (sub_neg.mpr hsw)]
      have hs := wpow_nonneg s
      linarith only [hs])
  exact mem_rightPrefixes_iff.mpr ⟨hpre, add_lt_add_right hsw K⟩

/-- Sufficiently small right exponents give a coinitial headed right-prefix family. -/
theorem exists_head_wpow_le_of_mem_rightPrefixes (K s : Surreal.{u})
    (hR : (rightPrefixes s).Nonempty)
    (hsmall : ∀ v ∈ rightPrefixes s, ∃ u ∈ rightPrefixes s,
      u < v ∧ K.support ⊆ Ioi u)
    {p : Surreal.{u}} (hp : p ∈ rightPrefixes (K + ω^ s)) :
    ∃ u ∈ rightPrefixes s, K.support ⊆ Ioi u ∧ K + ω^ u ≤ p := by
  rcases exists_rightPrefixes_add_le hp with ⟨q, hq, hqp⟩ | ⟨q, hq, hqp⟩
  · obtain ⟨v, hv⟩ := hR
    obtain ⟨u, hu, _, hKu⟩ := hsmall v hv
    have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hKu
      (birthday_lt_of_mem_rightPrefixes hq) (1 : ℝ)
    rw [Real.toSurreal_one, one_mul,
      abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hq).2)] at hg
    refine ⟨u, hu, hKu, ?_⟩
    have hs := wpow_nonneg s
    linarith only [hg, hs, hqp]
  · obtain ⟨v, hv, n, hvq⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hq
    obtain ⟨u, hu, huv, hKu⟩ := hsmall v hv
    have ht := mul_wpow_lt_mul_wpow_of_pos (1 : ℝ)
      (show 0 < (2 : ℝ)⁻¹ ^ n by positivity) huv
    rw [Real.toSurreal_one, one_mul, realCast_inv_two_pow] at ht
    exact ⟨u, hu, hKu, (add_le_add_right (ht.le.trans hvq) K).trans hqp⟩

/-- Sufficiently small right exponents give a headed right prefix with less than half the gap. -/
theorem exists_head_wpow_rightPrefix_half_gap (K s : Surreal.{u})
    (hR : (rightPrefixes s).Nonempty)
    (hsmall : ∀ v ∈ rightPrefixes s, ∃ u ∈ rightPrefixes s,
      u < v ∧ K.support ⊆ Ioi u)
    {p : Surreal.{u}} (hp : p ∈ rightPrefixes (K + ω^ s)) :
    ∃ u ∈ rightPrefixes s, K.support ⊆ Ioi u ∧
      K + ω^ u ∈ rightPrefixes (K + ω^ s) ∧
      2 * ((K + ω^ u) - (K + ω^ s)) < p - (K + ω^ s) := by
  obtain ⟨v, hv, _, hvp⟩ := exists_head_wpow_le_of_mem_rightPrefixes K s hR hsmall hp
  obtain ⟨u, hu, huv, hKu⟩ := hsmall v hv
  refine ⟨u, hu, hKu, head_wpow_mem_rightPrefixes K hu hKu, ?_⟩
  have hmul := mul_wpow_lt_mul_wpow_of_pos (2 : ℝ) (show (0 : ℝ) < 1 by norm_num) huv
  have h2 : ((2 : ℝ) : Surreal.{u}) = 2 := by norm_num
  rw [h2, Real.toSurreal_one, one_mul] at hmul
  have hs := wpow_pos s
  linarith only [hmul, hs, hvp]

/-- A right-exponent family with no least value gives coinitial headed gap-halving prefixes. -/
theorem exists_head_wpow_rightPrefix_half_gap_of_no_min (K s : Surreal.{u})
    (hboundary : ∃ v ∈ rightPrefixes s, K.support ⊆ Ioi v)
    (hnoMin : ∀ v ∈ rightPrefixes s, ∃ u ∈ rightPrefixes s, u < v)
    {p : Surreal.{u}} (hp : p ∈ rightPrefixes (K + ω^ s)) :
    ∃ u ∈ rightPrefixes s, K.support ⊆ Ioi u ∧
      K + ω^ u ∈ rightPrefixes (K + ω^ s) ∧
      2 * ((K + ω^ u) - (K + ω^ s)) < p - (K + ω^ s) := by
  obtain ⟨v0, hv0, hK0⟩ := hboundary
  apply exists_head_wpow_rightPrefix_half_gap K s ⟨v0, hv0⟩ _ hp
  intro v hv
  by_cases hvv0 : v ≤ v0
  · obtain ⟨u, hu, huv⟩ := hnoMin v hv
    exact ⟨u, hu, huv, fun i hi ↦ (huv.trans_le hvv0).trans (hK0 hi)⟩
  · obtain ⟨u, hu, huv0⟩ := hnoMin v0 hv0
    exact ⟨u, hu, huv0.trans (lt_of_not_ge hvv0),
      fun i hi ↦ huv0.trans (hK0 hi)⟩

/-- One right exponent below the entire head suffices for a canonical half-gap right prefix. -/
theorem exists_rightPrefix_half_gap_of_head_boundary (K s : Surreal.{u})
    (hboundary : ∃ v ∈ rightPrefixes s, K.support ⊆ Ioi v)
    {p : Surreal.{u}} (hp : p ∈ rightPrefixes (K + ω^ s)) :
    ∃ q ∈ rightPrefixes (K + ω^ s),
      2 * (q - (K + ω^ s)) < p - (K + ω^ s) := by
  classical
  by_cases hmin : ∃ w ∈ rightPrefixes s, ∀ v ∈ rightPrefixes s, w ≤ v
  · obtain ⟨w, hw, hmin⟩ := hmin
    obtain ⟨v0, hv0, hK0⟩ := hboundary
    have hKw : K.support ⊆ Ioi w := fun i hi ↦ (hmin v0 hv0).trans_lt (hK0 hi)
    obtain ⟨N, hN, hcof, hhalf⟩ :=
      exists_head_shifted_reciprocal_wpow_halving_family_of_min_rightPrefix K w hKw
        (a := (0 : ℝ)) (by simp) hw hmin
    simp only [Real.toSurreal_zero, zero_mul, zero_add] at hN hcof hhalf
    obtain ⟨n, hn, hnp⟩ := hcof p hp
    refine ⟨_, hN (n + 1) (by omega), ?_⟩
    have hh := hhalf n hn
    linarith only [hh, hnp]
  · have hnoMin : ∀ v ∈ rightPrefixes s, ∃ u ∈ rightPrefixes s, u < v := by
      intro v hv
      by_contra hn
      apply hmin
      refine ⟨v, hv, fun u hu ↦ ?_⟩
      exact le_of_not_gt (fun huv ↦ hn ⟨u, hu, huv⟩)
    obtain ⟨u, _, _, hu, hgap⟩ :=
      exists_head_wpow_rightPrefix_half_gap_of_no_min K s hboundary hnoMin hp
    exact ⟨_, hu, hgap⟩

/-- A dyadic coefficient at any right-exponent boundary admits a canonical half-gap prefix. -/
theorem exists_rightPrefix_half_gap_of_dyadic_coefficient_boundary
    (K w : Surreal.{u}) (hK : K.support ⊆ Ioi w) {a : ℝ}
    (ha : (a : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {s : Surreal.{u}} (hw : w ∈ rightPrefixes s) {p : Surreal.{u}}
    (hp : p ∈ rightPrefixes (K + ((a : Surreal) * ω^ w + ω^ s))) :
    ∃ q ∈ rightPrefixes (K + ((a : Surreal) * ω^ w + ω^ s)),
      2 * (q - (K + ((a : Surreal) * ω^ w + ω^ s))) <
        p - (K + ((a : Surreal) * ω^ w + ω^ s)) := by
  classical
  by_cases hex : ∃ u ∈ rightPrefixes s, u < w
  · obtain ⟨u, hu, huw⟩ := hex
    have hsupp : (K + (a : Surreal) * ω^ w).support ⊆ Ioi u := by
      intro i hi
      exact huw.trans_le (support_head_real_mul_wpow_subset K w hK a hi)
    have hboundary : ∃ v ∈ rightPrefixes s,
        (K + (a : Surreal) * ω^ w).support ⊆ Ioi v := ⟨u, hu, hsupp⟩
    have ht := exists_rightPrefix_half_gap_of_head_boundary (K + (a : Surreal) * ω^ w)
      s hboundary (by simpa only [add_assoc] using hp)
    simpa only [add_assoc] using ht
  · have hmin : ∀ v ∈ rightPrefixes s, w ≤ v := by
      intro v hv
      exact le_of_not_gt (fun hvw ↦ hex ⟨v, hv, hvw⟩)
    obtain ⟨N, hN, hcof, hhalf⟩ :=
      exists_head_shifted_reciprocal_wpow_halving_family_of_min_rightPrefix K w hK ha hw hmin
    obtain ⟨n, hn, hnp⟩ := hcof p hp
    refine ⟨_, hN (n + 1) (by omega), ?_⟩
    have hh := hhalf n hn
    linarith only [hh, hnp]

end Surreal
