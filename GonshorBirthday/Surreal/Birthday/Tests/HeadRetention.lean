/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadRetention

/-!
# Native retained positions and actual boundary capacity

The zero head retains every original sign. A nonzero dyadic boundary consumes a
full actual birthday block before the new headed monomial, including negative
coefficients and arbitrary higher heads.
-/

universe u
public section
open Surreal Set
namespace Tests

/-- With no previous terms every original exponent position is retained. -/
theorem zero_head_retains_all (s : Surreal.{u}) :
    ∃ C : Surreal, s ≤ C ∧ reducedOmegaPositions C s = univ := by
  obtain ⟨C, hCs, _, hC⟩ := exists_reducedOmegaPositions_eq_head_condition 0 s
  refine ⟨C, hCs, ?_⟩
  rw [hC]
  ext i
  simp only [mem_ofPred_eq, support_zero, empty_subset, coeff_zero, Pi.zero_apply,
    Real.toSurreal_zero, birthday_zero, mem_univ, iff_true]
  exact Or.inr ⟨trivial, by exact_mod_cast Ordinal.omega0_pos⟩

/-- A retained dyadic boundary block fits strictly inside the actual source birthday. -/
theorem retained_boundary_birthday_capacity {H s w : Surreal.{u}}
    (hH : H.support ⊆ Ici w) (hw : w ∈ rightPrefixes s) (hc : H.coeff w ≠ 0)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    NatOrdinal.of (H.birthday.val + (ω^ (plusCount w)).val) < (H + ω^ s).birthday := by
  obtain ⟨p, hp, hb⟩ := exists_head_rightPrefix_birthday_add_wpow_plusCount hH hw hc hf
  rw [← hb]
  exact birthday_lt_of_mem_rightPrefixes hp

end Tests
