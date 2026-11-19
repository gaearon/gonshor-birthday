/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Head

import GonshorBirthday.Surreal.Birthday.HeadMidpoint

/-!
# Right gaps at a dyadic coefficient boundary

When the final positive monomial exponent ends in a minus, shifted reciprocal
monomials give a right gap smaller than half any given right gap.
-/

universe u

public noncomputable section

namespace Surreal

/-- A dyadic boundary has a canonical right gap smaller than half any given right gap. -/
theorem exists_rightPrefix_half_gap_of_dyadic_boundary
    (K s : Surreal.{u}) (hK : K.support ⊆ Set.Ioi s) {r : ℝ}
    (hr : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {w : Surreal.{u}}
    (hw : w ∈ rightPrefixes (K + ((r : Surreal) * ω^ s + ω^ (appendMinus s)))) :
    ∃ v ∈ rightPrefixes (K + ((r : Surreal) * ω^ s + ω^ (appendMinus s))),
      2 * (v - (K + ((r : Surreal) * ω^ s + ω^ (appendMinus s)))) <
        w - (K + ((r : Surreal) * ω^ s + ω^ (appendMinus s))) := by
  obtain ⟨N, hN, hcof, hhalf⟩ :=
    exists_head_shifted_reciprocal_wpow_halving_family K s hK hr
  obtain ⟨n, hn, hnw⟩ := hcof w hw
  refine ⟨_, hN (n + 1) (by omega), ?_⟩
  exact (hhalf n hn).trans_le (sub_le_sub_right hnw _)

end Surreal
