/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Minus
public import GonshorBirthday.Surreal.Birthday.Real

public import GonshorBirthday.Surreal.Birthday.CoefficientShift
import GonshorBirthday.Surreal.Birthday.OmegaBlock

/-!
# Pure runs after a dyadic monomial coefficient

A lower canonical monomial prefix appends only plus signs after a nonzero dyadic
coefficient monomial; subtracting it appends only minus signs. The run length is
its original plus count. These statements concern one monomial, without a higher head.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- The canonical plus successor of a dyadic real remains real. -/
theorem exists_real_appendPlus_of_birthday_lt_omega0 {r : ℝ}
    (hr : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ∃ s : ℝ, (s : Surreal.{u}) = appendPlus (r : Surreal.{u}) := by
  have hf : (appendPlus (r : Surreal.{u})).birthday < NatOrdinal.of Ordinal.omega0 := by
    rw [birthday_appendPlus]
    obtain ⟨n, hn⟩ := NatOrdinal.lt_omega0.mp hr
    rw [hn]
    exact_mod_cast NatOrdinal.natCast_lt_omega0 (n + 1)
  obtain ⟨q, hq⟩ := birthday_lt_omega0_iff.mp hf
  refine ⟨(q.toRat : ℝ), ?_⟩
  simpa only [Real.toSurreal_ratCast] using hq

/-- A lower canonical monomial prefix gives a pure plus run below a real coefficient prefix. -/
theorem appendPluses_real_mul_wpow_of_coef_prefix {r s : ℝ}
    (hr : 0 < r) (hrs : r < s)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = r)
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    appendPluses ((r : Surreal) * ω^ x) (plusCount a).val = (r : Surreal) * ω^ x + a := by
  exact (appendPluses_eq_iff _ _ _).mpr
    ⟨birthday_real_mul_wpow_add_leftPrefix hr hrs hp ha,
      rightPrefixes_real_mul_wpow_add_leftPrefix hr hrs hp ha⟩

/-- A lower canonical monomial prefix appends a pure plus run after a positive
dyadic monomial. -/
theorem appendPluses_real_mul_wpow_of_birthday_lt_omega0 {r : ℝ} (hr : 0 < r)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    appendPluses ((r : Surreal) * ω^ x) (plusCount a).val = (r : Surreal) * ω^ x + a := by
  obtain ⟨s, hs⟩ := exists_real_appendPlus_of_birthday_lt_omega0 hf
  apply appendPluses_real_mul_wpow_of_coef_prefix hr (s := s) _ _ ha
  · apply Real.toSurreal_lt_iff.mp
    rw [hs]
    exact lt_appendPlus _
  · rw [hs]
    exact birthdayTruncation_appendPlus _

/-- The canonical minus successor of a dyadic real remains real. -/
theorem exists_real_appendMinus_of_birthday_lt_omega0 {r : ℝ}
    (hr : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ∃ s : ℝ, (s : Surreal.{u}) = appendMinus (r : Surreal.{u}) := by
  have hf : (appendMinus (r : Surreal.{u})).birthday < NatOrdinal.of Ordinal.omega0 := by
    rw [birthday_appendMinus]
    obtain ⟨n, hn⟩ := NatOrdinal.lt_omega0.mp hr
    rw [hn]
    exact_mod_cast NatOrdinal.natCast_lt_omega0 (n + 1)
  obtain ⟨q, hq⟩ := birthday_lt_omega0_iff.mp hf
  refine ⟨(q.toRat : ℝ), ?_⟩
  simpa only [Real.toSurreal_ratCast] using hq

/-- A lower canonical monomial prefix gives a pure minus run above a real coefficient prefix. -/
theorem appendMinuses_real_mul_wpow_of_coef_prefix {r s : ℝ}
    (hs : 0 < s) (hsr : s < r)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = r)
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    appendMinuses ((r : Surreal) * ω^ x) (plusCount a).val = (r : Surreal) * ω^ x - a := by
  apply neg_injective
  apply eq_of_birthday_eq_of_rightPrefixes_eq
  · rw [birthday_neg, birthday_neg, birthday_appendMinuses]
    exact (birthday_real_mul_wpow_sub_leftPrefix hs hsr hp ha).symm
  · rw [rightPrefixes_neg, rightPrefixes_neg, leftPrefixes_appendMinuses,
      leftPrefixes_real_mul_wpow_sub_leftPrefix hs hsr hp ha]

/-- Subtracting a lower canonical prefix appends a pure minus run after a positive
dyadic monomial. -/
theorem appendMinuses_real_mul_wpow_of_birthday_lt_omega0 {r : ℝ} (hr : 0 < r)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    appendMinuses ((r : Surreal) * ω^ x) (plusCount a).val = (r : Surreal) * ω^ x - a := by
  obtain ⟨s, hs⟩ := exists_real_appendMinus_of_birthday_lt_omega0 hf
  have hspos : 0 < s := by
    apply Real.toSurreal_pos_iff.mp
    rw [hs]
    exact lt_appendMinus_of_mem_leftPrefixes
      (zero_mem_leftPrefixes (Real.toSurreal_pos_iff.mpr hr))
  apply appendMinuses_real_mul_wpow_of_coef_prefix hspos (s := s) _ _ ha
  · apply Real.toSurreal_lt_iff.mp
    rw [hs]
    exact appendMinus_lt _
  · rw [hs]
    exact birthdayTruncation_appendMinus _

/-- A lower canonical prefix appends a pure plus run after a nonzero
dyadic monomial. -/
theorem appendPluses_nonzero_real_mul_wpow_of_birthday_lt_omega0 {r : ℝ}
    (hr : r ≠ 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    appendPluses ((r : Surreal) * ω^ x) (plusCount a).val = (r : Surreal) * ω^ x + a := by
  rcases hr.lt_or_gt with hr | hr
  · have hn : ((-r : ℝ) : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
      simpa only [Real.toSurreal_neg, birthday_neg] using hf
    have ht := appendMinuses_real_mul_wpow_of_birthday_lt_omega0 (neg_pos.mpr hr) hn ha
    rw [Real.toSurreal_neg, neg_mul, appendMinuses_eq_neg, neg_neg] at ht
    have he := congrArg Neg.neg ht
    simpa only [neg_neg, neg_sub, sub_neg_eq_add, add_comm] using he
  · exact appendPluses_real_mul_wpow_of_birthday_lt_omega0 hr hf ha

/-- Subtracting a lower canonical prefix appends a pure minus run after a nonzero
dyadic monomial. -/
theorem appendMinuses_nonzero_real_mul_wpow_of_birthday_lt_omega0 {r : ℝ}
    (hr : r ≠ 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    appendMinuses ((r : Surreal) * ω^ x) (plusCount a).val = (r : Surreal) * ω^ x - a := by
  have hn : ((-r : ℝ) : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
    simpa only [Real.toSurreal_neg, birthday_neg] using hf
  have ht := appendPluses_nonzero_real_mul_wpow_of_birthday_lt_omega0 (neg_ne_zero.mpr hr) hn ha
  rw [Real.toSurreal_neg, neg_mul] at ht
  rw [appendMinuses_eq_neg, ht]
  ring

/-- Finite lower monomial multiples append their exact pure-power plus block. -/
theorem appendPluses_real_mul_wpow_natCast_mul_wpow {r : ℝ} (hr : r ≠ 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {s v : Surreal.{u}} (hv : v ∈ leftPrefixes s) (n : ℕ) :
    appendPluses ((r : Surreal) * ω^ s) ((ω^ (plusCount v)).val * (n : Ordinal)) =
      (r : Surreal) * ω^ s + (n : Surreal) * ω^ v := by
  have ht := appendPluses_nonzero_real_mul_wpow_of_birthday_lt_omega0 hr hf
    (natCast_mul_wpow_mem_leftPrefixes hv n)
  simpa only [plusCount_natCast_mul_wpow, plusCount_wpow, NatOrdinal.val_of] using ht

/-- Finite lower monomial multiples append their exact pure-power minus block. -/
theorem appendMinuses_real_mul_wpow_natCast_mul_wpow {r : ℝ} (hr : r ≠ 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {s v : Surreal.{u}} (hv : v ∈ leftPrefixes s) (n : ℕ) :
    appendMinuses ((r : Surreal) * ω^ s) ((ω^ (plusCount v)).val * (n : Ordinal)) =
      (r : Surreal) * ω^ s - (n : Surreal) * ω^ v := by
  have ht := appendMinuses_nonzero_real_mul_wpow_of_birthday_lt_omega0 hr hf
    (natCast_mul_wpow_mem_leftPrefixes hv n)
  simpa only [plusCount_natCast_mul_wpow, plusCount_wpow, NatOrdinal.val_of] using ht

end Surreal
