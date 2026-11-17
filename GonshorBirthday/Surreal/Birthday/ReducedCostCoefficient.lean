/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCost
public import GonshorBirthday.NatOrdinal.CoefficientBudget

import GonshorBirthday.Surreal.Birthday.Addition

/-!
# Coefficient tails after a reduced-cost product estimate

Any reduced-cost estimate for an exponent pair extends to its finite or
infinite real-coefficient tails. The hypotheses refer to the actual input
and output cutoffs. No Cantor-support condition is needed for this step.
-/

universe u

public noncomputable section

namespace Surreal

/-- The omega-power baseline of an exponent sum fits the natural product of the input baselines. -/
theorem wpow_plusCount_add_le_mul (a b : Surreal.{u}) :
    ω^ plusCount (a + b) ≤ ω^ plusCount a * ω^ plusCount b := by
  rw [← NatOrdinal.wpow_add]
  exact NatOrdinal.wpow_le_wpow.mpr (plusCount_add_le a b)

/-- A reduced-cost product estimate also pays for arbitrary finite coefficient tails. -/
theorem reducedOmegaCost_coefficient_natCast_le (a b A B C : Surreal.{u})
    (hJ : reducedOmegaCost C (a + b) ≤ reducedOmegaCost A a * reducedOmegaCost B b)
    (m n : ℕ) :
    NatOrdinal.of ((reducedOmegaCost C (a + b)).val +
      (ω^ plusCount (a + b)).val * ((m + n + m * n : ℕ) : Ordinal.{u})) ≤
      NatOrdinal.of ((reducedOmegaCost A a).val +
        (ω^ plusCount a).val * (m : Ordinal)) *
      NatOrdinal.of ((reducedOmegaCost B b).val +
        (ω^ plusCount b).val * (n : Ordinal)) :=
  NatOrdinal.coefficient_cell_natCast_le (wpow_plusCount_le_reducedOmegaCost A a)
    (wpow_plusCount_le_reducedOmegaCost B b) hJ (wpow_plusCount_add_le_mul a b) m n

/-- An infinite input coefficient tail supplies the omega-length output coefficient tail. -/
theorem reducedOmegaCost_coefficient_omega_le (a b A B C : Surreal.{u})
    (hJ : reducedOmegaCost C (a + b) ≤ reducedOmegaCost A a * reducedOmegaCost B b)
    (t u : Ordinal.{u}) (hinf : Ordinal.omega0 ≤ t ∨ Ordinal.omega0 ≤ u) :
    NatOrdinal.of ((reducedOmegaCost C (a + b)).val +
      (ω^ plusCount (a + b)).val * Ordinal.omega0) ≤
      NatOrdinal.of ((reducedOmegaCost A a).val + (ω^ plusCount a).val * t) *
      NatOrdinal.of ((reducedOmegaCost B b).val + (ω^ plusCount b).val * u) :=
  NatOrdinal.coefficient_cell_omega_le (wpow_plusCount_le_reducedOmegaCost A a)
    (wpow_plusCount_le_reducedOmegaCost B b) hJ (wpow_plusCount_add_le_mul a b) t u hinf

/-- Repeated monomial baselines pay for the first signs lost when finite cell coefficients merge. -/
theorem reducedOmegaCost_coefficient_fibre_natCast_le (C e : Surreal.{u})
    (l : List ℕ) (hne : l ≠ []) :
    NatOrdinal.of ((reducedOmegaCost C e).val + (ω^ plusCount e).val *
      (((l.map (fun n ↦ n + 1)).sum - 1 : ℕ) : Ordinal.{u})) ≤
      NatOrdinal.of ((l.map (fun n : ℕ ↦
        (reducedOmegaCost C e).val + (ω^ plusCount e).val * (n : Ordinal.{u}))).sum) :=
  NatOrdinal.coefficient_fibre_natCast_le (wpow_plusCount_le_reducedOmegaCost C e) l hne

/-- An infinite cell tail pays for the whole infinite tail after an equal-exponent fibre merges. -/
theorem reducedOmegaCost_coefficient_fibre_omega_le (C e : Surreal.{u})
    (l : List Ordinal.{u}) (hinf : ∃ t ∈ l, Ordinal.omega0 ≤ t) :
    NatOrdinal.of ((reducedOmegaCost C e).val + (ω^ plusCount e).val * Ordinal.omega0) ≤
      NatOrdinal.of ((l.map (fun t ↦
        (reducedOmegaCost C e).val + (ω^ plusCount e).val * t)).sum) :=
  NatOrdinal.coefficient_fibre_omega_le _ _ l hinf

end Surreal
