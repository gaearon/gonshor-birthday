/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.HahnSeries.BirthdayAdd

/-!
# Sharp-addition support clients

The cancelled constant term of `(ω+1)+(-1)` demonstrates that the sharp
plus-count hypothesis cannot be omitted from the support theorem.
-/

public noncomputable section

namespace Tests

open Set Surreal

/-- Cancellation below the last output exponent prevents sharp plus-count addition. -/
theorem plusCount_not_sharp_after_constant_cancellation :
    plusCount ((ω^ (1 : Surreal) + 1) + -1) ≠
      plusCount (ω^ (1 : Surreal) + 1) + plusCount (-1 : Surreal) := by
  intro hc
  have hs : ((ω^ (1 : Surreal) + 1) + -1).support ⊆ Ioi 0 := by
    simp
  have hx := (support_subset_Ioi_of_plusCount_add_eq _ _ 0 hs hc).1
  have hz : (0 : Surreal) ∈ (ω^ (1 : Surreal) + 1).support := by
    simp [mem_support_iff, coeff_add, coeff_wpow, coeff_one]
  exact (lt_irrefl (0 : Surreal)) (hx hz)

end Tests
