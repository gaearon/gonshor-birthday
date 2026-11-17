/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostHead
public import GonshorBirthday.Surreal.Birthday.CoefficientRight
public import GonshorBirthday.Surreal.Birthday.ReducedCostInterval

import GonshorBirthday.Surreal.Birthday.ReducedCostPositive

/-!
# Final coefficient minuses forced by reduced-cost endpoints

A lowered-cutoff gap window gives a last term with nonzero dyadic coefficient.
Cofinal right-prefix birthdays exclude a final coefficient plus, except for the
positive unit. The positive-unit gap-halving theorem excludes that remaining case.
Thus the last coefficient ends in a canonical minus, including predecessor zero.
-/

universe u
public noncomputable section
namespace Surreal

/-- A gap window with cofinal right-prefix birthdays ends in a real coefficient minus. -/
theorem exists_last_coefficient_minus_of_gap_window {z e d : Surreal.{u}}
    (hz : birthdayTruncation e z.birthday = z)
    (hcof : ∀ a < z.birthday, ∃ p ∈ rightPrefixes z, a < p.birthday)
    (hdel : ∀ w ∈ rightPrefixes z, z + d < w)
    (hne : ∃ w ∈ rightPrefixes z, w ≤ e + d) :
    ∃ K s : Surreal.{u}, ∃ r t : ℝ,
      K.support ⊆ Set.Ioi s ∧ r ≠ 0 ∧
      (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ∧
      (r : Surreal.{u}) = appendMinus (t : Surreal.{u}) ∧
      z = K + (r : Surreal) * ω^ s := by
  obtain ⟨K, s, r, hK, hr, hf, rfl⟩ := exists_dyadic_last_term_of_gap_window hz hdel hne
  obtain hr1 | ⟨t, hsrc⟩ :=
    real_coefficient_eq_one_or_minus_successor_of_head_rightPrefixes_cofinal
      K s hK hr hf hcof
  · subst r
    simp only [Real.toSurreal_one, one_mul] at hz hcof hdel hne
    exact (not_gap_window_of_head_add_wpow_cofinal K s hK hcof hz hdel hne).elim
  · exact ⟨K, s, r, t, hK, hr, hf, hsrc, rfl⟩

/-- A pure reduced-cost endpoint with cofinal retained minuses has a final coefficient minus. -/
theorem exists_last_coefficient_minus_of_pure_endpoint
    (a b d z : Surreal.{u}) (hd : 0 ≤ d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    (hz : z ∈ leftPrefixes (a + b)) {p : NatOrdinal.{u}}
    (hp : plusCount z < p)
    (hH : reducedOmegaCost (a + b + d) z = ω^ p)
    (hM : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b = ω^ p)
    (hcof : ∀ j < z.birthday,
      ∃ w ∈ rightPrefixes z, j < w.birthday ∧ w ≤ a + b + d) :
    ∃ K s : Surreal.{u}, ∃ r t : ℝ,
      K.support ⊆ Set.Ioi s ∧ r ≠ 0 ∧
      (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ∧
      (r : Surreal.{u}) = appendMinus (t : Surreal.{u}) ∧
      z = K + (r : Surreal) * ω^ s := by
  have hne : ∃ w ∈ rightPrefixes z, w ≤ a + b + d := by
    by_cases hb : 0 < z.birthday
    · obtain ⟨w, hw, _, hwC⟩ := hcof 0 hb
      exact ⟨w, hw, hwC⟩
    · have hz0 : z = 0 := birthday_eq_zero.mp (le_antisymm (le_of_not_gt hb) bot_le)
      subst z
      simp only [reducedOmegaCost_zero] at hH
      have hpl : 0 < p := by simpa only [plusCount_zero] using hp
      have hpow : 1 < ω^ p := by
        simpa only [NatOrdinal.wpow_zero] using NatOrdinal.wpow_lt_wpow.mpr hpl
      exact (hpow.ne hH).elim
  exact exists_last_coefficient_minus_of_gap_window (mem_leftPrefixes_iff.mp hz).1
    (fun j hj ↦ by obtain ⟨w, hw, hjw, _⟩ := hcof j hj; exact ⟨w, hw, hjw⟩)
    (rightPrefixes_gt_shifted_cutoff_of_pure_eq hd ih hz hp hH hM) hne

/-- A normalized pure-cost gap window ends in a coefficient minus and one full plus block. -/
theorem exists_full_block_last_term_of_pure_gap_window
    (a b d z : Surreal.{u}) (hzpos : 0 < z.birthday)
    {α β : NatOrdinal.{u}} {ρ : Ordinal.{u}} (hρpos : 0 < ρ)
    (hA : reducedOmegaCost (a + d) a = ω^ α)
    (hB : reducedOmegaCost (b + d) b = ω^ β)
    (hH : reducedOmegaCost (a + b + d) z = ω^ (α + β))
    (he : a + b = appendPluses z ρ)
    (hcof : ∀ j < z.birthday,
      ∃ w ∈ rightPrefixes z, j < w.birthday ∧ w ≤ a + b + d)
    (hdel : ∀ w ∈ rightPrefixes z, z + d < w) :
    ∃ K s : Surreal.{u}, ∃ r t : ℝ,
      K.support ⊆ Set.Ioi s ∧ r ≠ 0 ∧
      (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ∧
      (r : Surreal.{u}) = appendMinus (t : Surreal.{u}) ∧
      z = K + (r : Surreal) * ω^ s ∧
      ρ = (ω^ (plusCount s)).val ∧
      plusCount (a + b) = α + β ∧ α = plusCount a ∧ β = plusCount b ∧
      reducedOmegaCost (a + d) a = ω^ plusCount a ∧
      reducedOmegaCost (b + d) b = ω^ plusCount b := by
  have hz : birthdayTruncation (a + b) z.birthday = z := by
    rw [he]
    exact birthdayTruncation_appendPluses z ρ
  have hne : ∃ w ∈ rightPrefixes z, w ≤ a + b + d := by
    obtain ⟨w, hw, _, hwC⟩ := hcof 0 hzpos
    exact ⟨w, hw, hwC⟩
  obtain ⟨K, s, r, t, hK, hr, hf, hsrc, rfl⟩ :=
    exists_last_coefficient_minus_of_gap_window hz
      (fun j hj ↦ by obtain ⟨w, hw, hjw, _⟩ := hcof j hj; exact ⟨w, hw, hjw⟩) hdel hne
  exact ⟨K, s, r, t, hK, hr, hf, hsrc, rfl,
    full_block_and_baseline_of_head_coefficient_minus a b d K s hK hr hsrc hρpos
      hA hB hH he hcof hdel⟩

end Surreal
