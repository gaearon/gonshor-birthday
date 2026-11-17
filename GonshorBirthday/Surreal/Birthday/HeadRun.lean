/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadPerturbation
public import GonshorBirthday.Surreal.Birthday.Relative
public import GonshorBirthday.Surreal.Birthday.Minus

import GonshorBirthday.Surreal.Birthday.SupportGap
import GonshorBirthday.Surreal.Birthday.OmegaBlock
import GonshorBirthday.Surreal.Birthday.CoefficientCofinality

/-!
# Exact pure runs after an arbitrary normal-form head

If s is the least supported exponent of H, adding a canonical left prefix of omega^s
appends only plus signs, with length its original plus count. Subtraction appends the
corresponding minus run. The normal-form support-gap theorem supplies right-prefix
cofinality; intrinsic canonical cuts and relative birthdays identify the exact run.
In particular this extends the headed finite-monomial family to every nonzero real
last coefficient, of either sign, with no restriction on the earlier head.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- Cofinal old right prefixes prevent new right prefixes in a translated left-prefix stage. -/
theorem rightPrefixes_add_leftPrefix_of_cofinal_rightPrefixes
    {H x a : Surreal.{u}} (hx : 0 < x) (ha : a ∈ leftPrefixes x)
    (hhead : birthdayTruncation (H + a) H.birthday = H)
    (hcof : ∀ b ∈ rightPrefixes x, ∃ p ∈ rightPrefixes H, p ≤ H + b) :
    rightPrefixes (H + a) = rightPrefixes H := by
  have ha0 := nonneg_of_mem_leftPrefixes hx ha
  apply Set.Subset.antisymm
  · intro z hz
    have liftRight : ∀ w ∈ rightPrefixes H, w ≤ z → z ∈ rightPrefixes H := by
      intro w hw hwz
      have hws := rightPrefixes_subset_of_birthdayTruncation_eq hhead hw
      have hsumw := (mem_rightPrefixes_iff.mp hws).2
      have hzpre := (mem_rightPrefixes_iff.mp hz).1
      have ht := birthdayTruncation_eq_of_right_between
        (birthday_lt_of_mem_rightPrefixes hz).le hsumw.le (by rwa [hzpre])
      rw [hzpre] at ht
      exact mem_rightPrefixes_iff.mpr
        ⟨birthdayTruncation_eq_trans (mem_rightPrefixes_iff.mp hw).1 ht,
          (mem_rightPrefixes_iff.mp hw).2.trans_le hwz⟩
    rcases exists_rightPrefixes_add_le hz with ⟨w, hw, hwz⟩ | ⟨w, hw, hwz⟩
    · exact liftRight w hw ((le_add_of_nonneg_right ha0).trans hwz)
    · have hwx := rightPrefixes_subset_of_birthdayTruncation_eq
        (mem_leftPrefixes_iff.mp ha).1 hw
      obtain ⟨p, hp, hpw⟩ := hcof w hwx
      exact liftRight p hp (hpw.trans hwz)
  · exact rightPrefixes_subset_of_birthdayTruncation_eq hhead

/-- A lower monomial prefix lies inside every younger gap of a higher-scale head. -/
theorem leftPrefix_wpow_lt_abs_head_gap {H s a p : Surreal.{u}}
    (hH : H.support ⊆ Ici s) (ha : a ∈ leftPrefixes (ω^ s))
    (hp : p.birthday < H.birthday) : a < |p - H| := by
  rcases exists_natCast_mul_wpow_ge_of_mem_leftPrefixes ha with rfl | ⟨v, hv, n, han⟩
  · apply abs_pos.mpr
    exact sub_ne_zero.mpr (fun he ↦ hp.ne (congrArg birthday he))
  · exact han.trans_lt (natCast_mul_wpow_lt_abs_sub_of_birthday_lt hH hp
      (mem_leftPrefixes_iff.mp hv).2 n)

/-- Adding a lower monomial prefix preserves the canonical head. -/
theorem birthdayTruncation_head_add_leftPrefix_wpow {H s a : Surreal.{u}}
    (hH : H.support ⊆ Ici s) (ha : a ∈ leftPrefixes (ω^ s)) :
    birthdayTruncation (H + a) H.birthday = H := by
  have ha0 := nonneg_of_mem_leftPrefixes (wpow_pos s) ha
  have ht := birthdayTruncation_add_of_prefix_of_head_gaps (K := H) (a := a) (b := 0)
    (by simp) (fun p hp ↦ ?_) (fun p hp ↦ ?_)
  · simpa using ht
  · have hpH := (mem_leftPrefixes_iff.mp hp).2
    linarith only [hpH, ha0]
  · have hg := leftPrefix_wpow_lt_abs_head_gap hH ha (birthday_lt_of_mem_rightPrefixes hp)
    rw [abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hp).2)] at hg
    simpa using (show H + a < p + 0 by linarith only [hg])

/-- Earlier translated lower prefixes remain canonical prefixes of every later stage. -/
theorem birthdayTruncation_head_add_of_leftPrefix_wpow {H s a z : Surreal.{u}}
    (hH : H.support ⊆ Ici s) (ha : a ∈ leftPrefixes (ω^ s)) (hz : z ∈ leftPrefixes a) :
    birthdayTruncation (H + a) (H + z).birthday = H + z := by
  have hza := (mem_leftPrefixes_iff.mp hz).2
  have hzs := leftPrefixes_subset_of_birthdayTruncation_eq (mem_leftPrefixes_iff.mp ha).1 hz
  have hz0 := nonneg_of_mem_leftPrefixes (wpow_pos s) hzs
  apply birthdayTruncation_add_of_prefix_of_head_gaps (mem_leftPrefixes_iff.mp hz).1
  · intro p hp
    have hpH := (mem_leftPrefixes_iff.mp hp).2
    linarith only [hza, hpH]
  · intro p hp
    have hg := leftPrefix_wpow_lt_abs_head_gap hH ha (birthday_lt_of_mem_rightPrefixes hp)
    rw [abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hp).2)] at hg
    linarith only [hg, hz0]

/-- Cofinal old right prefixes give the exact translated pure plus run. -/
theorem appendPluses_head_leftPrefix_wpow_of_cofinal_rightPrefixes
    {H s a : Surreal.{u}} (hH : H.support ⊆ Ici s) (ha : a ∈ leftPrefixes (ω^ s))
    (hcof : ∀ b ∈ rightPrefixes (ω^ s), ∃ p ∈ rightPrefixes H, p ≤ H + b) :
    appendPluses H (plusCount a).val = H + a := by
  have hla : ∀ z ∈ leftPrefixes (appendPlus a), z ∈ leftPrefixes (ω^ s) := by
    intro z hz
    rw [leftPrefixes_appendPlus] at hz
    rcases hz with rfl | hz
    · exact ha
    · exact leftPrefixes_subset_of_birthdayTruncation_eq (mem_leftPrefixes_iff.mp ha).1 hz
  have ha0 := nonneg_of_mem_leftPrefixes (wpow_pos s) ha
  have hR : ∀ z ∈ leftPrefixes (appendPlus a), rightPrefixes (H + z) = rightPrefixes H := by
    intro z hz
    exact rightPrefixes_add_leftPrefix_of_cofinal_rightPrefixes (wpow_pos s) (hla z hz)
      (birthdayTruncation_head_add_leftPrefix_wpow hH (hla z hz)) hcof
  have hP : ∀ z ∈ leftPrefixes (appendPlus a),
      birthdayTruncation (H + a) (H + z).birthday = H + z := by
    intro z hz
    rw [leftPrefixes_appendPlus] at hz
    rcases hz with rfl | hz
    · exact birthdayTruncation_birthday _
    · exact birthdayTruncation_head_add_of_leftPrefix_wpow hH ha hz
  have hB : ∀ z ∈ leftPrefixes (appendPlus a), H + z ≤ H + a := by
    intro z hz
    rw [leftPrefixes_appendPlus] at hz
    rcases hz with rfl | hz
    · exact le_rfl
    · exact add_le_add_right (mem_leftPrefixes_iff.mp hz).2.le H
  have hG : ∀ z ∈ leftPrefixes (appendPlus a), ∀ p ∈ leftPrefixes H, p + z ≤ H := by
    intro z hz p hp
    have hg := leftPrefix_wpow_lt_abs_head_gap hH (hla z hz) (birthday_lt_of_mem_leftPrefixes hp)
    rw [abs_of_neg (sub_neg.mpr (mem_leftPrefixes_iff.mp hp).2), neg_sub] at hg
    linarith only [hg]
  have hx : 0 < appendPlus a := ha0.trans_lt (lt_appendPlus a)
  have hmem : a ∈ leftPrefixes (appendPlus a) := by rw [leftPrefixes_appendPlus]; simp
  have hb := birthday_add_left_prefix_eq_of_stage_rightPrefixes hx hR hP hB hG hmem
  exact (appendPluses_eq_iff _ _ _).mpr ⟨hb, hR a hmem⟩

private theorem realCast_inv_two_pow (n : ℕ) :
    Real.toSurreal ((2 : ℝ)⁻¹ ^ n) = (2 : Surreal.{u})⁻¹ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.toSurreal_mul, ih, Real.toSurreal_inv]
    norm_num only [Real.toSurreal_ofNat]
    rw [pow_succ]

/-- A supported exponent gives old right prefixes below every translated right monomial option. -/
theorem exists_rightPrefix_le_add_of_mem_support {H s : Surreal.{u}}
    (hs : s ∈ H.support) {b : Surreal.{u}} (hb : b ∈ rightPrefixes (ω^ s)) :
    ∃ p ∈ rightPrefixes H, p ≤ H + b := by
  obtain ⟨w, hw, n, hnb⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hb
  obtain ⟨p, hp, hgap⟩ := exists_rightPrefix_sub_lt_real_mul_wpow_of_support hs hw
    (show 0 < (2 : ℝ)⁻¹ ^ n by positivity)
  rw [realCast_inv_two_pow] at hgap
  refine ⟨p, hp, ?_⟩
  linarith only [hgap, hnb]

/-- Adding a left prefix at the least supported scale appends its exact pure plus run. -/
theorem appendPluses_eq_add_leftPrefix_wpow {H s a : Surreal.{u}}
    (hH : H.support ⊆ Ici s) (hs : s ∈ H.support) (ha : a ∈ leftPrefixes (ω^ s)) :
    appendPluses H (plusCount a).val = H + a :=
  appendPluses_head_leftPrefix_wpow_of_cofinal_rightPrefixes hH ha
    (fun _ hb ↦ exists_rightPrefix_le_add_of_mem_support hs hb)

/-- Negation preserves Conway normal-form support. -/
@[simp] theorem support_neg (x : Surreal.{u}) : (-x).support = x.support := by
  rw [← support_coeff, coeff_neg]
  simp only [Function.support_neg, support_coeff]

/-- Subtracting a left prefix at the least supported scale appends its exact pure minus run. -/
theorem appendMinuses_eq_sub_leftPrefix_wpow {H s a : Surreal.{u}}
    (hH : H.support ⊆ Ici s) (hs : s ∈ H.support) (ha : a ∈ leftPrefixes (ω^ s)) :
    appendMinuses H (plusCount a).val = H - a := by
  have hneg : (-H).support ⊆ Ici s := by simpa only [support_neg] using hH
  have hsneg : s ∈ (-H).support := by simpa only [support_neg] using hs
  rw [appendMinuses_eq_neg, appendPluses_eq_add_leftPrefix_wpow hneg hsneg ha]
  ring

/-- Finite lower monomials append their exact pure-power plus blocks after a head. -/
theorem appendPluses_head_natCast_mul_wpow {H s v : Surreal.{u}}
    (hH : H.support ⊆ Ici s) (hs : s ∈ H.support) (hv : v ∈ leftPrefixes s) (n : ℕ) :
    appendPluses H ((ω^ (plusCount v)).val * (n : Ordinal)) = H + (n : Surreal) * ω^ v := by
  have ht := appendPluses_eq_add_leftPrefix_wpow hH hs (natCast_mul_wpow_mem_leftPrefixes hv n)
  simpa only [plusCount_natCast_mul_wpow, plusCount_wpow, NatOrdinal.val_of] using ht

/-- Finite lower monomials append their exact pure-power minus blocks after a head. -/
theorem appendMinuses_head_natCast_mul_wpow {H s v : Surreal.{u}}
    (hH : H.support ⊆ Ici s) (hs : s ∈ H.support) (hv : v ∈ leftPrefixes s) (n : ℕ) :
    appendMinuses H ((ω^ (plusCount v)).val * (n : Ordinal)) = H - (n : Surreal) * ω^ v := by
  have ht := appendMinuses_eq_sub_leftPrefix_wpow hH hs (natCast_mul_wpow_mem_leftPrefixes hv n)
  simpa only [plusCount_natCast_mul_wpow, plusCount_wpow, NatOrdinal.val_of] using ht

/-- A nonzero last monomial coefficient supplies its exponent to the headed support. -/
theorem mem_support_head_real_mul_wpow (K s : Surreal.{u})
    (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : r ≠ 0) :
    s ∈ (K + (r : Surreal) * ω^ s).support := by
  have hKs : K.coeff s = 0 := notMem_support_iff.mp (fun hs ↦ (lt_irrefl s) (hK hs))
  have hm : ((r : Surreal.{u}) * ω^ s).toHahnSeries = SurrealHahnSeries.single s r :=
    toHahnSeries_eq (SurrealHahnSeries.toSurreal_single s r)
  have hcoeff : ((r : Surreal.{u}) * ω^ s).coeff s = r := by
    rw [← coeff_toHahnSeries, hm, SurrealHahnSeries.coeff_single]
    simp
  apply mem_support_iff.mpr
  rw [coeff_add, Pi.add_apply, hKs, hcoeff, zero_add]
  exact hr

/-- The headed monomial perturbation plus formula holds for every nonzero real last coefficient. -/
theorem appendPluses_head_real_mul_wpow (K s : Surreal.{u})
    (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : r ≠ 0)
    {v : Surreal.{u}} (hv : v ∈ leftPrefixes s) (n : ℕ) :
    appendPluses (K + (r : Surreal) * ω^ s) ((ω^ (plusCount v)).val * (n : Ordinal)) =
      K + (r : Surreal) * ω^ s + (n : Surreal) * ω^ v :=
  appendPluses_head_natCast_mul_wpow (support_head_real_mul_wpow_subset K s hK r)
    (mem_support_head_real_mul_wpow K s hK hr) hv n

/-- The headed monomial perturbation minus formula holds for every nonzero real last coefficient. -/
theorem appendMinuses_head_real_mul_wpow (K s : Surreal.{u})
    (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : r ≠ 0)
    {v : Surreal.{u}} (hv : v ∈ leftPrefixes s) (n : ℕ) :
    appendMinuses (K + (r : Surreal) * ω^ s) ((ω^ (plusCount v)).val * (n : Ordinal)) =
      K + (r : Surreal) * ω^ s - (n : Surreal) * ω^ v :=
  appendMinuses_head_natCast_mul_wpow (support_head_real_mul_wpow_subset K s hK r)
    (mem_support_head_real_mul_wpow K s hK hr) hv n

end Surreal
