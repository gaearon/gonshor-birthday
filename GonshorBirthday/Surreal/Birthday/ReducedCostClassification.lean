/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.GapWindow
public import GonshorBirthday.Surreal.Birthday.ReducedCostInterval

import GonshorBirthday.Surreal.Birthday.CoefficientRun

/-!
# Final coefficient minuses forced by reduced-cost endpoints

The cutoff gives a right gap less than twice every other right gap. At its scale the
limit prefix ends at a dyadic coefficient minus. The following pluses account for a
full coefficient block.
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
  obtain ⟨w, hw, hw'⟩ := hne
  apply exists_last_minus_of_right_gap hw _ hcof
  intro v hv
  have hev := (mem_rightPrefixes_iff.mp
    (rightPrefixes_subset_of_birthdayTruncation_eq hz hv)).2
  linarith only [hw', hev, hdel v hv]

/-- When lowering the cutoff to `z+d` deletes every old minus, the next dyadic
coefficient is a prefix of the output. Its plus count bounds the last power at `z`. -/
theorem exists_dyadic_prefix_of_final_power {e z d : Surreal.{u}} {γ : NatOrdinal.{u}}
    (hZ : reducedOmegaCost (e + d) z = ω^ γ) (hpre : birthdayTruncation e z.birthday = z)
    (hcof : ∀ j < z.birthday, ∃ w ∈ rightPrefixes z, j < w.birthday ∧ w ≤ e + d)
    (hd : 0 < d) (hdel : ∀ w ∈ rightPrefixes z, z + d < w) (hV : e + d ∈ rightPrefixes z) :
    ∃ (K s : Surreal.{u}) (r t : ℝ) (q : Dyadic), K.support ⊆ Set.Ioi s ∧
      (r : Surreal.{u}) = appendMinus (t : Surreal) ∧
      ((q.toRat : ℝ) : Surreal.{u}) = appendPlus (r : Surreal) ∧ z = K + (r : Surreal) * ω^ s ∧
      let y := K + (q : Surreal) * ω^ s
      appendPluses z (ω^ (plusCount s)).val = y ∧ birthdayTruncation e y.birthday = y ∧
        γ ≤ plusCount y := by
  have hR : ∀ j < z.birthday, ∃ w ∈ rightPrefixes z, j < w.birthday := fun j hj ↦ by
    obtain ⟨w, hw, hjw, _⟩ := hcof j hj
    exact ⟨w, hw, hjw⟩
  obtain ⟨K, s, r, t, hK, hr, hf, hsrc, rfl⟩ :=
    exists_last_coefficient_minus_of_gap_window hpre hR hdel ⟨_, hV, le_rfl⟩
  obtain ⟨q, _, hq, hblock⟩ := exists_dyadic_head_coefficient_plus_block K s hK hr hf
  let y := K + (q : Surreal) * ω^ s
  have hplus : ((q.toRat : ℝ) : Surreal.{u}) = appendPlus (r : Surreal.{u}) := by
    simpa only [Real.toSurreal_ratCast] using hq
  have hprefix : birthdayTruncation e y.birthday = y := by
    simpa only [y, ← Real.toSurreal_ratCast] using
      (coefficient_plus_prefix_iff_exists_margin K s hK hr hsrc hplus hpre).2
        ⟨d, hd, hdel, e + d, hV, le_rfl⟩
  have hbound := pure_cost_exponent_le_next_coefficient K s hK hsrc hZ hcof
  change γ ≤ plusCount _ at hbound
  rw [hblock] at hbound
  exact ⟨K, s, r, t, q, hK, hsrc, hplus, rfl, hblock, hprefix, hbound⟩

end Surreal
