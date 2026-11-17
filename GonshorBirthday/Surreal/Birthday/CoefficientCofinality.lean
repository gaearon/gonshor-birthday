/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientShift
public import GonshorBirthday.Surreal.Birthday.ProductCut

import GonshorBirthday.Surreal.Birthday.OmegaBlock
import GonshorBirthday.Surreal.Birthday.Real

/-!
# Canonical coefficient product cofinality
-/

universe u
public noncomputable section
namespace Surreal
open Set IGame

/-- Nonnegative real multiples of a monomial left prefix are bounded by another left prefix. -/
theorem exists_leftPrefixes_wpow_ge_real_mul {r : ℝ} (hr : 0 ≤ r)
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    ∃ b ∈ leftPrefixes (ω^ x), (r : Surreal) * a ≤ b := by
  obtain rfl | ⟨v, hv, n, han⟩ := exists_natCast_mul_wpow_ge_of_mem_leftPrefixes ha
  · exact ⟨0, zero_mem_leftPrefixes (wpow_pos x), by simp⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (r * (n : ℝ))
  refine ⟨(m : Surreal) * ω^ v, natCast_mul_wpow_mem_leftPrefixes hv m, ?_⟩
  have hcoeff : (r : Surreal.{u}) * (n : Surreal) ≤ (m : Surreal) := by
    exact_mod_cast hm.le
  calc
    (r : Surreal) * a ≤ (r : Surreal) * ((n : Surreal) * ω^ v) :=
      mul_le_mul_of_nonneg_left han (Real.toSurreal_nonneg_iff.mpr hr)
    _ = ((r : Surreal) * (n : Surreal)) * ω^ v := (mul_assoc _ _ _).symm
    _ ≤ (m : Surreal) * ω^ v := mul_le_mul_of_nonneg_right hcoeff (wpow_nonneg v)

/-- The sum of two left prefixes of a monomial is bounded by another left prefix. -/
theorem exists_leftPrefix_wpow_ge_add {s a b : Surreal.{u}}
    (ha : a ∈ leftPrefixes (ω^ s)) (hb : b ∈ leftPrefixes (ω^ s)) :
    ∃ c ∈ leftPrefixes (ω^ s), a + b ≤ c := by
  have hm : max a b ∈ leftPrefixes (ω^ s) := (max_choice a b).elim
    (fun h ↦ h.symm ▸ ha) (fun h ↦ h.symm ▸ hb)
  obtain ⟨c, hc, h⟩ := exists_leftPrefixes_wpow_ge_real_mul (r := 2) (by norm_num) hm
  rw [show ((2 : ℝ) : Surreal.{u}) = 2 by norm_num, two_mul] at h
  exact ⟨c, hc, (add_le_add (le_max_left a b) (le_max_right a b)).trans h⟩

/-- The plus counts of monomial left prefixes suffice to bound a whole coefficient block. -/
theorem oadd_wpow_plusCount_le_of_leftPrefixes (s : Surreal.{u}) (A B : NatOrdinal.{u})
    (h : ∀ a ∈ leftPrefixes (ω^ s), NatOrdinal.of (A.val + (plusCount a).val) < B) :
    NatOrdinal.of (A.val + (ω^ plusCount s).val) ≤ B := by
  apply NatOrdinal.val.le_iff_le.mp
  rw [NatOrdinal.val_of]
  apply (Ordinal.add_le_iff (NatOrdinal.val.strictMono (NatOrdinal.wpow_pos _)).ne').mpr
  intro d hd
  have hd' : NatOrdinal.of d < plusCount (ω^ s) := by rwa [plusCount_wpow]
  obtain ⟨a, ha, hda⟩ := exists_leftPrefixes_plusCount_ge hd'
  exact (add_le_add_right (NatOrdinal.val.monotone hda) _).trans_lt
    (NatOrdinal.val.strictMono (h a ha))

private theorem realCast_inv_two_pow (n : ℕ) :
    Real.toSurreal ((2 : ℝ)⁻¹ ^ n) = (2 : Surreal.{u})⁻¹ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.toSurreal_mul, ih, Real.toSurreal_inv]
    norm_num only [Real.toSurreal_ofNat]
    rw [pow_succ]

/-- Positive real multiples of a monomial right prefix bound another right prefix. -/
theorem exists_rightPrefixes_wpow_le_real_mul {r : ℝ} (hr : 0 < r)
    {x a : Surreal.{u}} (ha : a ∈ rightPrefixes (ω^ x)) :
    ∃ b ∈ rightPrefixes (ω^ x), b ≤ (r : Surreal) * a := by
  obtain ⟨v, hv, n, hna⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes ha
  have hpos : 0 < r * (2 : ℝ)⁻¹ ^ n := mul_pos hr (by positivity)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (show (2 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨(2 : Surreal)⁻¹ ^ m * ω^ v, inv_two_pow_mul_wpow_mem_rightPrefixes hv m, ?_⟩
  have hcoeff : (2 : Surreal.{u})⁻¹ ^ m ≤ (r : Surreal) * (2 : Surreal)⁻¹ ^ n := by
    have ht := Real.toSurreal_le_iff.mpr hm.le
    simpa only [Real.toSurreal_mul, realCast_inv_two_pow] using ht
  calc
    (2 : Surreal)⁻¹ ^ m * ω^ v ≤ ((r : Surreal) * (2 : Surreal)⁻¹ ^ n) * ω^ v :=
      mul_le_mul_of_nonneg_right hcoeff (wpow_nonneg v)
    _ = (r : Surreal) * ((2 : Surreal)⁻¹ ^ n * ω^ v) := mul_assoc _ _ _
    _ ≤ (r : Surreal) * a :=
      mul_le_mul_of_nonneg_left hna (Real.toSurreal_nonneg_iff.mpr hr.le)

/-- Every real multiple of a monomial is below each canonical right monomial prefix. -/
theorem real_mul_wpow_lt_of_mem_rightPrefixes {r : ℝ} {x a : Surreal.{u}}
    (ha : a ∈ rightPrefixes (ω^ x)) : (r : Surreal) * ω^ x < a := by
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hcoeff : (r : Surreal.{u}) ≤ (n : Surreal) := by exact_mod_cast hn.le
  exact (mul_le_mul_of_nonneg_right hcoeff (wpow_nonneg x)).trans_lt
    (natCast_mul_wpow_lt_of_mem_rightPrefixes ha n)

private theorem exists_real_of_prefix {r : ℝ} {c : Surreal.{u}}
    (hp : birthdayTruncation (r : Surreal) c.birthday = c) :
    ∃ s : ℝ, (s : Surreal) = c := by
  have ht := birthdayTruncation_real_mem_range_real r c.birthday
  rwa [hp] at ht

/-- Right prefixes of a positive real coefficient monomial bound old or reflected prefixes. -/
theorem exists_rightPrefixes_real_mul_wpow_le {r : ℝ} (hr : 0 < r)
    {x z : Surreal.{u}} (hz : z ∈ rightPrefixes ((r : Surreal) * ω^ x)) :
    (∃ a ∈ rightPrefixes (ω^ x), a ≤ z) ∨
      ∃ s : ℝ, 0 < s ∧ (s : Surreal.{u}) ∈ rightPrefixes (r : Surreal.{u}) ∧
        ∃ a ∈ leftPrefixes (ω^ x), (s : Surreal) * ω^ x - a ≤ z := by
  rcases exists_rightPrefixes_mul_le hz with ⟨c, hc, b, hb, hcb⟩ | ⟨c, hc, b, hb, hcb⟩
  · obtain ⟨s, hs⟩ := exists_real_of_prefix (mem_leftPrefixes_iff.mp hc).1
    have hsr : s < r := Real.toSurreal_lt_iff.mp (by rw [hs]; exact (mem_leftPrefixes_iff.mp hc).2)
    obtain ⟨a, ha, hab⟩ := exists_rightPrefixes_wpow_le_real_mul (sub_pos.mpr hsr) hb
    have hs0 : 0 ≤ (s : Surreal.{u}) := by
      rw [hs]
      exact nonneg_of_mem_leftPrefixes (Real.toSurreal_pos_iff.mpr hr) hc
    left
    refine ⟨a, ha, hab.trans ?_⟩
    rw [Real.toSurreal_sub]
    have he : ((r : Surreal) - (s : Surreal)) * b ≤
        c * ω^ x + (r : Surreal) * b - c * b := by rw [← hs]; nlinarith only [hs0, wpow_nonneg x]
    exact he.trans hcb
  · obtain ⟨s, hs⟩ := exists_real_of_prefix (mem_rightPrefixes_iff.mp hc).1
    have hrs : r < s := Real.toSurreal_lt_iff.mp
      (by rw [hs]; exact (mem_rightPrefixes_iff.mp hc).2)
    obtain ⟨a, ha, hba⟩ := exists_leftPrefixes_wpow_ge_real_mul (sub_pos.mpr hrs).le hb
    right
    refine ⟨s, hr.trans hrs, by rwa [hs], a, ha, ?_⟩
    rw [Real.toSurreal_sub] at hba
    have he : (s : Surreal) * ω^ x - a ≤
        c * ω^ x + (r : Surreal) * b - c * b := by rw [← hs]; nlinarith only [hba]
    exact he.trans hcb

/-- Left prefixes of a positive real coefficient monomial are bounded by old or shifted prefixes. -/
theorem exists_leftPrefixes_real_mul_wpow_ge {r : ℝ} (hr : 0 < r)
    {x z : Surreal.{u}} (hz : z ∈ leftPrefixes ((r : Surreal) * ω^ x)) :
    (∃ a ∈ leftPrefixes (ω^ x), z ≤ a) ∨
      ∃ s : ℝ, 0 < s ∧ (s : Surreal.{u}) ∈ leftPrefixes (r : Surreal.{u}) ∧
        ∃ a ∈ leftPrefixes (ω^ x), z ≤ (s : Surreal) * ω^ x + a := by
  rcases exists_leftPrefixes_mul_ge hz with ⟨c, hc, b, hb, hcb⟩ | ⟨c, hc, b, hb, hcb⟩
  · obtain ⟨s, hs⟩ := exists_real_of_prefix (mem_leftPrefixes_iff.mp hc).1
    have hsr : s < r := Real.toSurreal_lt_iff.mp
      (by rw [hs]; exact (mem_leftPrefixes_iff.mp hc).2)
    have hs0 : 0 ≤ s := by
      apply Real.toSurreal_nonneg_iff.mp
      rw [hs]
      exact nonneg_of_mem_leftPrefixes (Real.toSurreal_pos_iff.mpr hr) hc
    obtain ⟨a, ha, hba⟩ := exists_leftPrefixes_wpow_ge_real_mul (sub_pos.mpr hsr).le hb
    rw [Real.toSurreal_sub] at hba
    obtain rfl | hspos := hs0.eq_or_lt
    · left
      refine ⟨a, ha, ?_⟩
      rw [← hs] at hcb
      simp only [Real.toSurreal_zero, zero_mul, zero_add, sub_zero] at hcb hba
      exact hcb.trans hba
    · right
      refine ⟨s, hspos, by rwa [hs], a, ha, ?_⟩
      rw [← hs] at hcb
      nlinarith only [hcb, hba]
  · obtain ⟨s, hs⟩ := exists_real_of_prefix (mem_rightPrefixes_iff.mp hc).1
    have hrs : r < s := Real.toSurreal_lt_iff.mp
      (by rw [hs]; exact (mem_rightPrefixes_iff.mp hc).2)
    have hdelta : 0 < s - r := sub_pos.mpr hrs
    have ht := real_mul_wpow_lt_of_mem_rightPrefixes (r := s / (s - r)) hb
    have hmul := mul_lt_mul_of_pos_left ht (Real.toSurreal_pos_iff.mpr hdelta)
    have he : (s - r) * (s / (s - r)) = s := by field_simp [ne_of_gt hdelta]
    have he' := congrArg (fun t : ℝ ↦ (t : Surreal.{u})) he
    rw [Real.toSurreal_mul] at he'
    rw [← mul_assoc, he'] at hmul
    rw [Real.toSurreal_sub] at hmul
    have hz0 := nonneg_of_mem_leftPrefixes
      (mul_pos (Real.toSurreal_pos_iff.mpr hr) (wpow_pos x)) hz
    rw [← hs] at hcb
    exfalso
    nlinarith only [hmul, hcb, hz0]


end Surreal
