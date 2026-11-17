/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostCofinality

import GonshorBirthday.NatOrdinal.FinalPower

/-!
# A pure input factor in a common-margin failure

Directional cofinality and the uniform natural-product bound force one input
cost to be a pure omega power. The opposite input has cofinal retained-prefix
costs and a nonzero limit cost. The common margin is unchanged here.
-/

universe u

public noncomputable section

namespace Surreal

/-- Cofinal retained-prefix product costs force the other nonzero factor to be a pure power. -/
theorem exists_eq_wpow_of_retained_rightPrefix_products_cofinal {C x : Surreal.{u}}
    {Y : NatOrdinal.{u}} (hY : Y ≠ 0)
    (hprod : ∀ S < reducedOmegaCost C x * Y, ∃ y ∈ rightPrefixes x,
      y ≤ C ∧ S < reducedOmegaCost C y * Y) : ∃ p, Y = ω^ p := by
  have hx : reducedOmegaCost C x ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (one_le_reducedOmegaCost C x))
  apply NatOrdinal.exists_eq_wpow_of_products_cofinal hx hY
  intro S hS
  obtain ⟨y, hy, hyC, hSy⟩ := hprod S hS
  exact ⟨reducedOmegaCost C y, reducedOmegaCost_lt_of_mem_rightPrefixes hy hyC, hSy.le⟩

/-- In a minimal common-margin failure, one factor is pure and the opposite prefix costs cofinal. -/
theorem pure_factor_or_of_common_margin_failure (a b d : Surreal.{u}) (hd : 0 < d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    (hfail : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b <
      reducedOmegaCost (a + b + d) (a + b)) :
    (∃ p, reducedOmegaCost (b + d) b = ω^ p ∧
      Order.IsSuccLimit (reducedOmegaCost (a + d) a).val ∧
      ∀ S < reducedOmegaCost (a + d) a, ∃ w ∈ rightPrefixes a,
        w ≤ a + d ∧ S < reducedOmegaCost (a + d) w) ∨
    (∃ p, reducedOmegaCost (a + d) a = ω^ p ∧
      Order.IsSuccLimit (reducedOmegaCost (b + d) b).val ∧
      ∀ S < reducedOmegaCost (b + d) b, ∃ w ∈ rightPrefixes b,
        w ≤ b + d ∧ S < reducedOmegaCost (b + d) w) := by
  obtain ⟨c, hc, hlim, _, hcof, hcost, _⟩ :=
    exists_limit_prefix_of_common_margin_failure a b d hd ih hfail
  let z := birthdayTruncation (a + b) c
  have hzb : z.birthday = c := birthday_birthdayTruncation (a + b) hc.le
  have hz : birthdayTruncation (a + b) z.birthday = z := by rw [hzb]
  have hzpos : 0 < z.birthday := by
    rw [hzb]
    exact NatOrdinal.val.lt_iff_lt.mp (by
      simpa only [NatOrdinal.val_zero] using
        (pos_iff_ne_zero.mpr (Ordinal.isSuccLimit_iff.mp hlim).1))
  have hcut : min (a + d + b) (a + (b + d)) = a + b + d := by
    rw [add_right_comm a d b, ← add_assoc, min_self]
  have hc' : ∀ e < z.birthday, ∃ v ∈ rightPrefixes z,
      e < v.birthday ∧ v ≤ min (a + d + b) (a + (b + d)) := by
    simpa only [hcut, hzb] using hcof
  have hH : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b ≤
      reducedOmegaCost (min (a + d + b) (a + (b + d))) z := by
    rw [hcut]
    exact hcost.ge
  have hX : 0 < reducedOmegaCost (a + d) a :=
    zero_lt_one.trans_le (one_le_reducedOmegaCost _ _)
  have hY : 0 < reducedOmegaCost (b + d) b :=
    zero_lt_one.trans_le (one_le_reducedOmegaCost _ _)
  rcases retained_rightPrefix_products_cofinal_or_of_eq
    (le_add_of_nonneg_right hd.le) (le_add_of_nonneg_right hd.le)
    ih hz hzpos hc' hH with hA | hB
  · obtain ⟨p, hp⟩ := exists_eq_wpow_of_retained_rightPrefix_products_cofinal hY.ne' hA
    have hcofA := retained_rightPrefix_costs_cofinal_of_products (a + d) a hY hA
    exact Or.inl ⟨p, hp, isSuccLimit_reducedOmegaCost_of_costs_cofinal _ _ hcofA, hcofA⟩
  · have hB' : ∀ S < reducedOmegaCost (b + d) b * reducedOmegaCost (a + d) a,
        ∃ w ∈ rightPrefixes b, w ≤ b + d ∧
          S < reducedOmegaCost (b + d) w * reducedOmegaCost (a + d) a := by
      simpa only [mul_comm] using hB
    obtain ⟨p, hp⟩ := exists_eq_wpow_of_retained_rightPrefix_products_cofinal hX.ne' hB'
    have hcofB := retained_rightPrefix_costs_cofinal_of_products (b + d) b hX hB'
    exact Or.inr ⟨p, hp, isSuccLimit_reducedOmegaCost_of_costs_cofinal _ _ hcofB, hcofB⟩

end Surreal
