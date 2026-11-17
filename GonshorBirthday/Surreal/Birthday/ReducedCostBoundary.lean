/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostHead

import GonshorBirthday.Surreal.Birthday.HeadMidpoint

/-!
# Excluding a dyadic coefficient boundary at the output endpoint

When the final positive monomial exponent is a canonical minus successor,
shifted reciprocal monomials give canonical right gaps that can be halved.
The preceding coefficient may be any dyadic real, including zero, and the
earlier normal-form head is arbitrary. The lowered-cutoff obstruction then
excludes this endpoint without a sign-deletion or block-length assumption.
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

/-- A dyadic predecessor boundary cannot satisfy the lowered-cutoff gap window. -/
theorem not_gap_window_of_dyadic_boundary
    (K s : Surreal.{u}) (hK : K.support ⊆ Set.Ioi s) {r : ℝ}
    (hr : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {e d : Surreal.{u}}
    (hz : birthdayTruncation e
      (K + ((r : Surreal) * ω^ s + ω^ (appendMinus s))).birthday =
        K + ((r : Surreal) * ω^ s + ω^ (appendMinus s)))
    (hdel : ∀ w ∈ rightPrefixes (K + ((r : Surreal) * ω^ s + ω^ (appendMinus s))),
      K + ((r : Surreal) * ω^ s + ω^ (appendMinus s)) + d < w)
    (hne : ∃ w ∈ rightPrefixes (K + ((r : Surreal) * ω^ s + ω^ (appendMinus s))),
      w ≤ e + d) : False := by
  apply not_coinitial_halving_rightPrefixes_of_gap_window hz hdel hne
    (rightPrefixes (K + ((r : Surreal) * ω^ s + ω^ (appendMinus s))))
    (Set.Subset.refl _) ?_ ?_
  · intro w hw
    exact ⟨w, hw, le_rfl⟩
  · exact fun w hw ↦ exists_rightPrefix_half_gap_of_dyadic_boundary K s hK hr hw

/-- Smaller-pair induction excludes the pure-cost endpoint at a dyadic predecessor boundary. -/
theorem not_pure_endpoint_of_dyadic_boundary
    (a b d K s : Surreal.{u}) {r : ℝ} (hd : 0 ≤ d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ m : Surreal.{u}, 0 < m → reducedOmegaCost (x + y + m) (x + y) ≤
        reducedOmegaCost (x + m) x * reducedOmegaCost (y + m) y)
    (hK : K.support ⊆ Set.Ioi s)
    (hr : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hz : K + ((r : Surreal) * ω^ s + ω^ (appendMinus s)) ∈ leftPrefixes (a + b))
    {p : NatOrdinal.{u}}
    (hp : plusCount (K + ((r : Surreal) * ω^ s + ω^ (appendMinus s))) < p)
    (hcost : reducedOmegaCost (a + b + d)
      (K + ((r : Surreal) * ω^ s + ω^ (appendMinus s))) = ω^ p)
    (hbudget : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b = ω^ p)
    (hne : ∃ w ∈ rightPrefixes (K + ((r : Surreal) * ω^ s + ω^ (appendMinus s))),
      w ≤ a + b + d) : False := by
  exact not_gap_window_of_dyadic_boundary K s hK hr (mem_leftPrefixes_iff.mp hz).1
    (rightPrefixes_gt_shifted_cutoff_of_pure_eq hd ih hz hp hcost hbudget) hne

end Surreal
