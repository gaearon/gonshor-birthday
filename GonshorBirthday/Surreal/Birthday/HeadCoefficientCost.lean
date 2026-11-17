/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCostPrefix
public import GonshorBirthday.Surreal.Birthday.ReplacementCost
public import GonshorBirthday.Surreal.Birthday.ReducedCostCoefficient
public import GonshorBirthday.Surreal.Birthday.RealMultiplication

import GonshorBirthday.NatOrdinal.FiniteBlocks

/-!
# Complete term costs after a normal-form head

The native reduced monomial cost is followed by the real coefficient's original
tail. A zero coefficient contributes nothing. Monomial product bounds extend to
these costs for all real coefficients, and finite coefficient sums fit ordinary
concatenations of their costs, including when coefficients cancel.
-/

universe u
open scoped Ordinal
public noncomputable section
namespace Surreal

/-- The length that the term `r * ω^ s` adds to the sign sequence of `H`. It is `0` if `r = 0`,
and otherwise the ordinal sum of `headOmegaCost H s` and `ω^ plusCount s * (birthday r - 1)`. -/
def headCoefficientCost (H s : Surreal.{u}) (r : ℝ) : NatOrdinal.{u} :=
  if r = 0 then 0 else NatOrdinal.of
    ((headOmegaCost H s).val + (ω^ plusCount s).val * ((r : Surreal.{u}).birthday.val - 1))

/-- A zero coefficient contributes no term cost. -/
theorem headCoefficientCost_zero (H s : Surreal.{u}) : headCoefficientCost H s 0 = 0 := by
  rw [headCoefficientCost, ite_eq_left rfl]

/-- A nonzero coefficient contributes its reduced monomial and original coefficient tail. -/
theorem headCoefficientCost_of_ne_zero (H s : Surreal.{u}) {r : ℝ} (hr : r ≠ 0) :
    headCoefficientCost H s r = NatOrdinal.of
      ((headOmegaCost H s).val + (ω^ plusCount s).val * ((r : Surreal.{u}).birthday.val - 1)) := by
  rw [headCoefficientCost, ite_eq_right hr]

/-- A unit coefficient has exactly the reduced monomial cost. -/
theorem headCoefficientCost_one (H s : Surreal.{u}) :
    headCoefficientCost H s 1 = headOmegaCost H s := by
  rw [headCoefficientCost_of_ne_zero H s one_ne_zero]
  simp only [Real.toSurreal_one, birthday_one, NatOrdinal.val_one, Ordinal.sub_self,
    mul_zero, add_zero, NatOrdinal.of_val]

/-- The head cost and coefficient birthday determine the complete term cost. -/
theorem headCoefficientCost_congr {H K s : Surreal.{u}} {r t : ℝ}
    (hH : headOmegaCost H s = headOmegaCost K s)
    (hc : (r : Surreal.{u}).birthday = (t : Surreal.{u}).birthday) :
    headCoefficientCost H s r = headCoefficientCost K s t := by
  have hz : r = 0 ↔ t = 0 := by
    rw [← Real.toSurreal_eq_zero_iff.{u}, ← birthday_eq_zero,
      ← Real.toSurreal_eq_zero_iff.{u}, ← birthday_eq_zero, hc]
  by_cases hr : r = 0
  · rw [hr, hz.mp hr, headCoefficientCost_zero, headCoefficientCost_zero]
  · rw [headCoefficientCost_of_ne_zero H s hr,
      headCoefficientCost_of_ne_zero K s (mt hz.mpr hr), hH, hc]

/-- Simultaneous negation of a head and coefficient preserves the complete term cost. -/
theorem headCoefficientCost_neg (H s : Surreal.{u}) (r : ℝ) :
    headCoefficientCost (-H) s (-r) = headCoefficientCost H s r := by
  apply headCoefficientCost_congr (headOmegaCost_neg H s)
  rw [Real.toSurreal_neg, birthday_neg]

/-- Positive normal-form replacement preserves every complete term cost. -/
theorem headCoefficientCost_trunc_normalFormBirthdayReplacement {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (x s : Surreal.{u}) :
    headCoefficientCost ((normalFormBirthdayReplacement τ x).normalFormTrunc s) s
      ((normalFormBirthdayReplacement τ x).coeff s) =
        headCoefficientCost (x.normalFormTrunc s) s (x.coeff s) :=
  headCoefficientCost_congr (headOmegaCost_trunc_normalFormBirthdayReplacement hτpos hτ x s)
    (birthday_coeff_normalFormBirthdayReplacement hτ x s)

private theorem exists_birthday_nat_succ {r : ℝ} (hr : r ≠ 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ∃ n : ℕ, (r : Surreal.{u}).birthday = ((n + 1 : ℕ) : NatOrdinal.{u}) := by
  obtain ⟨n, hn⟩ := NatOrdinal.lt_omega0.mp hf
  cases n with
  | zero =>
    have hz : (r : Surreal.{u}) = 0 := birthday_eq_zero.mp (by simpa only [Nat.cast_zero] using hn)
    exact (hr (Real.toSurreal_eq_zero_iff.mp hz)).elim
  | succ n => exact ⟨n, hn⟩

private theorem ordinal_nat_succ_sub_one (n : ℕ) :
    (((n + 1 : ℕ) : Ordinal.{u}) - 1) = (n : Ordinal) := by
  simpa only [Nat.cast_one, Nat.add_sub_cancel] using (Ordinal.natCast_sub (n + 1) 1).symm

private theorem ordinal_omega0_sub_one : Ordinal.omega0 - (1 : Ordinal.{u}) = Ordinal.omega0 := by
  calc
    _ = (1 + Ordinal.omega0) - 1 := by simp
    _ = _ := Ordinal.add_sub_cancel 1 _

/-- A reduced monomial product bound extends to complete costs for all real coefficients. -/
theorem headCoefficientCost_mul_le {H K L a b : Surreal.{u}}
    (hcell : headOmegaCost L (a + b) ≤ headOmegaCost H a * headOmegaCost K b)
    (r t : ℝ) :
    headCoefficientCost L (a + b) (r * t) ≤
      headCoefficientCost H a r * headCoefficientCost K b t := by
  by_cases hr : r = 0
  · rw [hr, zero_mul, headCoefficientCost_zero, headCoefficientCost_zero, zero_mul]
  by_cases ht : t = 0
  · rw [ht, mul_zero, headCoefficientCost_zero, headCoefficientCost_zero, mul_zero]
  rw [headCoefficientCost_of_ne_zero L (a + b) (mul_ne_zero hr ht),
    headCoefficientCost_of_ne_zero H a hr, headCoefficientCost_of_ne_zero K b ht]
  have hP := wpow_plusCount_le_headOmegaCost H a
  have hQ := wpow_plusCount_le_headOmegaCost K b
  have hPQ := wpow_plusCount_add_le_mul a b
  have hprod : ((r * t : ℝ) : Surreal.{u}).birthday ≤
      (r : Surreal.{u}).birthday * (t : Surreal.{u}).birthday := by
    simpa only [Real.toSurreal_mul] using birthday_real_mul_le.{u} r t
  by_cases hinf : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 ∨
      (t : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0
  · have htail : Ordinal.omega0 ≤ (r : Surreal.{u}).birthday.val - 1 ∨
        Ordinal.omega0 ≤ (t : Surreal.{u}).birthday.val - 1 := by
      rcases hinf with hh | hh
      · left; rw [hh, NatOrdinal.val_of, ordinal_omega0_sub_one]
      · right; rw [hh, NatOrdinal.val_of, ordinal_omega0_sub_one]
    apply le_trans _ (NatOrdinal.coefficient_cell_omega_le hP hQ hcell hPQ _ _ htail)
    apply NatOrdinal.of.monotone
    apply add_le_add le_rfl
    apply mul_le_mul_right
    exact (Ordinal.sub_le_self _ _).trans (NatOrdinal.val.monotone (birthday_real_le_omega0 _))
  · have hrfin := (birthday_real_le_omega0 r).lt_of_ne (fun hh ↦ hinf (Or.inl hh))
    have htfin := (birthday_real_le_omega0 t).lt_of_ne (fun hh ↦ hinf (Or.inr hh))
    obtain ⟨m, hm⟩ := exists_birthday_nat_succ hr hrfin
    obtain ⟨n, hn⟩ := exists_birthday_nat_succ ht htfin
    rw [hm, hn, NatOrdinal.val_natCast, NatOrdinal.val_natCast,
      ordinal_nat_succ_sub_one, ordinal_nat_succ_sub_one]
    apply le_trans _ (NatOrdinal.coefficient_cell_natCast_le hP hQ hcell hPQ m n)
    apply NatOrdinal.of.monotone
    apply add_le_add le_rfl
    apply mul_le_mul_right
    apply Ordinal.sub_le.mpr
    have h := NatOrdinal.val.monotone hprod
    rw [hm, hn, ← Nat.cast_mul, NatOrdinal.val_natCast] at h
    have he : (((m + 1) * (n + 1) : ℕ) : Ordinal.{u}) =
        1 + ((m + n + m * n : ℕ) : Ordinal.{u}) := by
      rw [show (m + 1) * (n + 1) = 1 + (m + n + m * n) by ring]
      simp only [Nat.cast_add, Nat.cast_one]
    exact h.trans_eq he

/-- Increasing the coefficient birthday increases the term cost under a fixed head. -/
theorem headCoefficientCost_mono_birthday (H s : Surreal.{u}) {r t : ℝ}
    (hrt : (r : Surreal.{u}).birthday ≤ (t : Surreal.{u}).birthday) :
    headCoefficientCost H s r ≤ headCoefficientCost H s t := by
  by_cases hr : r = 0
  · rw [hr, headCoefficientCost_zero]
    exact zero_le
  have ht : t ≠ 0 := by
    intro ht
    rw [ht, Real.toSurreal_zero, birthday_zero] at hrt
    exact hr (Real.toSurreal_eq_zero_iff.mp (birthday_eq_zero.mp (le_antisymm hrt zero_le)))
  rw [headCoefficientCost_of_ne_zero H s hr, headCoefficientCost_of_ne_zero H s ht]
  apply NatOrdinal.of.monotone
  apply add_le_add le_rfl
  apply mul_le_mul_right
  exact Ordinal.sub_le.mpr ((NatOrdinal.val.monotone hrt).trans (Ordinal.le_add_sub _ _))

/-- Every real coefficient tail fits the omega-length tail. -/
theorem headCoefficientCost_le_omega_tail (H s : Surreal.{u}) (r : ℝ) :
    headCoefficientCost H s r ≤ NatOrdinal.of
      ((headOmegaCost H s).val + (ω^ plusCount s).val * Ordinal.omega0) := by
  by_cases hr : r = 0
  · rw [hr, headCoefficientCost_zero]
    exact zero_le
  rw [headCoefficientCost_of_ne_zero H s hr]
  apply NatOrdinal.of.monotone
  apply add_le_add le_rfl
  apply mul_le_mul_right
  exact (Ordinal.sub_le_self _ _).trans (NatOrdinal.val.monotone (birthday_real_le_omega0 _))

/-- The cost of a coefficient sum fits the ordinary concatenation of its two term costs. -/
theorem headCoefficientCost_add_le (H s : Surreal.{u}) (r t : ℝ) :
    headCoefficientCost H s (r + t) ≤ NatOrdinal.of
      ((headCoefficientCost H s r).val + (headCoefficientCost H s t).val) := by
  by_cases hr : r = 0
  · rw [hr, zero_add, headCoefficientCost_zero, NatOrdinal.val_zero, zero_add, NatOrdinal.of_val]
  by_cases ht : t = 0
  · rw [ht, add_zero, headCoefficientCost_zero, NatOrdinal.val_zero, add_zero, NatOrdinal.of_val]
  by_cases hout : r + t = 0
  · rw [hout, headCoefficientCost_zero]
    exact zero_le
  by_cases hinf : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 ∨
      (t : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0
  · have hh := headCoefficientCost_le_omega_tail H s (r + t)
    rcases hinf with hh0 | hh0
    · have he : headCoefficientCost H s r = NatOrdinal.of
          ((headOmegaCost H s).val + (ω^ plusCount s).val * Ordinal.omega0) := by
        rw [headCoefficientCost_of_ne_zero H s hr, hh0,
          NatOrdinal.val_of, ordinal_omega0_sub_one]
      rw [← he] at hh
      exact hh.trans (NatOrdinal.of.monotone le_self_add)
    · have he : headCoefficientCost H s t = NatOrdinal.of
          ((headOmegaCost H s).val + (ω^ plusCount s).val * Ordinal.omega0) := by
        rw [headCoefficientCost_of_ne_zero H s ht, hh0,
          NatOrdinal.val_of, ordinal_omega0_sub_one]
      rw [← he] at hh
      exact hh.trans (NatOrdinal.of.monotone le_add_self)
  · have hrfin := (birthday_real_le_omega0 r).lt_of_ne (fun hh ↦ hinf (Or.inl hh))
    have htfin := (birthday_real_le_omega0 t).lt_of_ne (fun hh ↦ hinf (Or.inr hh))
    obtain ⟨m, hm⟩ := exists_birthday_nat_succ hr hrfin
    obtain ⟨n, hn⟩ := exists_birthday_nat_succ ht htfin
    rw [headCoefficientCost_of_ne_zero H s hout,
      headCoefficientCost_of_ne_zero H s hr, headCoefficientCost_of_ne_zero H s ht,
      hm, hn, NatOrdinal.val_natCast, NatOrdinal.val_natCast,
      ordinal_nat_succ_sub_one, ordinal_nat_succ_sub_one, NatOrdinal.val_of, NatOrdinal.val_of]
    apply le_trans _ (NatOrdinal.coefficient_two_cells_le
      (wpow_plusCount_le_headOmegaCost H s) m n)
    apply NatOrdinal.of.monotone
    apply add_le_add le_rfl
    apply mul_le_mul_right
    apply Ordinal.sub_le.mpr
    have hsum := NatOrdinal.val.monotone (birthday_add_le (r : Surreal.{u}) (t : Surreal))
    rw [← Real.toSurreal_add, hm, hn, ← Nat.cast_add, NatOrdinal.val_natCast] at hsum
    have he : (((m + 1) + (n + 1) : ℕ) : Ordinal.{u}) =
        1 + ((m + n + 1 : ℕ) : Ordinal.{u}) := by
      rw [show (m + 1) + (n + 1) = 1 + (m + n + 1) by omega]
      simp only [Nat.cast_add, Nat.cast_one]
    exact hsum.trans_eq he

/-- A finite coefficient sum fits the ordinary concatenation of its listed term costs. -/
theorem headCoefficientCost_list_sum_le (H s : Surreal.{u}) (l : List ℝ) :
    headCoefficientCost H s l.sum ≤
      NatOrdinal.of ((l.map (fun r ↦ (headCoefficientCost H s r).val)).sum) := by
  induction l with
  | nil =>
    simp only [List.sum_nil, headCoefficientCost_zero, List.map_nil, NatOrdinal.of_zero, le_refl]
  | cons r l ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons]
    apply (headCoefficientCost_add_le H s r l.sum).trans
    apply NatOrdinal.of.monotone
    exact add_le_add le_rfl (by simpa only [NatOrdinal.val_of] using NatOrdinal.val.monotone ih)

/-- A finite coefficient sum fits the lexicographic sum of its indexed term costs. -/
theorem headCoefficientCost_fin_sum_le (H s : Surreal.{u}) {n : ℕ} (r : Fin n → ℝ) :
    headCoefficientCost H s (∑ i, r i) ≤
      NatOrdinal.of (typeLT (Σₗ i : Fin n, (headCoefficientCost H s (r i)).val.ToType)) := by
  have h := headCoefficientCost_list_sum_le H s (List.ofFn r)
  rw [Ordinal.type_fin_sigma]
  simp only [Ordinal.type_toType]
  simpa only [List.sum_ofFn, List.map_ofFn, Function.comp_def] using h

/-- A nondyadic source coefficient supplies an exact omega-length pure-power tail. -/
theorem headCoefficientCost_nondyadic_tail {H s : Surreal.{u}} {r : ℝ}
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    (headCoefficientCost H s r).val =
      (headOmegaCost H s).val + (ω^ (plusCount s)).val * Ordinal.omega0 := by
  have hr0 : r ≠ 0 := by
    intro he
    rw [he, Real.toSurreal_zero, birthday_zero] at hr
    exact (NatOrdinal.of.strictMono Ordinal.omega0_pos).ne
      (by simpa only [NatOrdinal.of_zero] using hr)
  have hsub : Ordinal.omega0.{u} - 1 = Ordinal.omega0 := by
    calc
      Ordinal.omega0 - 1 = (1 + Ordinal.omega0) - 1 := by rw [Ordinal.one_add_omega0]
      _ = _ := Ordinal.add_sub_cancel 1 _
  rw [headCoefficientCost_of_ne_zero H s hr0, NatOrdinal.val_of, hr, NatOrdinal.val_of, hsub]

end Surreal
