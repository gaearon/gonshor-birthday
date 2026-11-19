/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.GapWindow
public import GonshorBirthday.Surreal.Birthday.ReducedCostInterval

import GonshorBirthday.Surreal.Birthday.ReducedCostLower
import GonshorBirthday.Surreal.Birthday.LastMinusFamily
import GonshorBirthday.Surreal.Birthday.CoefficientStep
import GonshorBirthday.Surreal.Birthday.CoefficientRun

/-!
# Final coefficient minuses forced by reduced-cost endpoints

The cutoff gives a right gap less than twice every other right gap. At its scale the
limit prefix ends at a dyadic coefficient minus. The following pluses account for a
full coefficient block. Two nearby dyadics bound its right gaps from above and below.
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
        γ ≤ plusCount y ∧ (plusCount y ≤ γ → ω^ (plusCount s) = plusCount s) := by
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
  change γ ≤ plusCount _ ∧ (plusCount _ ≤ γ → ω^ (plusCount s) = plusCount s) at hbound
  rw [hblock] at hbound
  obtain ⟨hupper, hfixed⟩ := hbound
  change γ ≤ plusCount y at hupper
  exact ⟨K, s, r, t, q, hK, hsrc, hplus, rfl, hblock, hprefix, hupper, hfixed⟩

/-- A last Cantor power exhausted before a run of pluses determines the plus count
and puts the right gaps of that prefix, measured from `e`, at a fraction of a monomial. -/
theorem fractional_right_gaps_of_final_power {e z d : Surreal.{u}} {ρ : Ordinal.{u}}
    {γ : NatOrdinal.{u}} (he : e = appendPluses z ρ) (hp : plusCount e ≤ γ)
    (hZ : reducedOmegaCost (e + d) z = ω^ γ) (hpre : birthdayTruncation e z.birthday = z)
    (hcof : ∀ j < z.birthday, ∃ w ∈ rightPrefixes z, j < w.birthday ∧ w ≤ e + d)
    (hd : 0 < d) (hdel : ∀ w ∈ rightPrefixes z, z + d < w) (hV : e + d ∈ rightPrefixes z) :
    plusCount e = γ ∧ ∃ s : Surreal.{u}, ω^ (plusCount s) = plusCount s ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ k : ℝ, k < 1 ∧
      (∀ w ∈ rightPrefixes z, e + (δ : Surreal) * ω^ s < w) ∧
      ∃ V ∈ rightPrefixes z, V ≤ e + (k : Surreal) * ω^ s := by
  obtain ⟨K, s, r, t, q, hK, hsrc, hplus, rfl, hblock, hprefix, hupper, hfixed⟩ :=
    exists_dyadic_prefix_of_final_power hZ hpre hcof hd hdel hV
  let y := K + (q : Surreal) * ω^ s
  change birthdayTruncation e y.birthday = y at hprefix
  have hb : y.birthday ≤ e.birthday := by
    simpa only [hprefix] using birthday_birthdayTruncation_le_birthday e y.birthday
  have hlo := plusCount_birthdayTruncation_le e hb
  rw [hprefix] at hlo
  have heq : e = y := by
    have h := (hp.trans hupper).antisymm hlo
    change e = K + (q : Surreal) * ω^ s
    change plusCount e = plusCount (K + (q : Surreal) * ω^ s) at h
    rw [he, ← hblock] at h ⊢
    exact congrArg _ ((strictMono_plusCount_appendPluses _).injective h)
  have hrq : r < (q.toRat : ℝ) := Real.toSurreal_lt_iff.mp (hplus ▸ lt_appendPlus _)
  have ht : (t : Surreal.{u}) ∈ rightPrefixes (r : Surreal) := by
    rw [hsrc]
    exact mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus _, appendMinus_lt _⟩
  have hqt : (q.toRat : ℝ) < t := by
    apply Real.toSurreal_lt_iff.mp
    apply (mem_rightPrefixes_iff.mp ?_).2
    rw [hplus, rightPrefixes_appendPlus]
    exact ht
  let c := t - (q.toRat : ℝ)
  have hc : 0 < c := sub_pos.mpr hqt
  have hg := right_gaps_at_coefficient_minus K s hK hsrc (q.toRat : ℝ)
  rw [Real.toSurreal_ratCast, ← show e = K + (q : Surreal) * ω^ s from heq] at hg
  refine ⟨hp.antisymm (hupper.trans hlo), s, hfixed (hlo.trans hp), c / 2, half_pos hc, c, ?_,
    hg.1 (c / 2) (half_lt_self hc), _, hg.2, le_rfl⟩
  dsimp only [c]
  linarith only [hrq, real_sub_le_one_of_eq_appendMinus hsrc]

end Surreal
