/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Coefficient
public import GonshorBirthday.Surreal.Birthday.Dyadic

/-!
# A mixed-sign exponent client for monomial coefficient blocks

The exponent -1/2 has canonical signs minus-plus. Its omega-map has omega many
plus signs, and each extra positive integer coefficient appends an omega block.
-/

universe u

public noncomputable section
namespace Tests
open Surreal Set

private theorem rightPrefixes_neg_one : rightPrefixes (-1 : Surreal.{u}) = {0} := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, he, _⟩ := mem_rightPrefixes.mp hz
    have ha' : a < 1 := by simpa only [birthday_neg, birthday_one] using ha
    have ha0 : a = 0 := NatOrdinal.lt_one_iff.mp ha'
    rw [ha0, birthdayTruncation_zero] at he
    exact mem_singleton_iff.mpr he.symm
  · intro hz
    have hz' : z = 0 := mem_singleton_iff.mp hz
    subst z
    exact mem_rightPrefixes_iff.mpr ⟨by simp, neg_lt_zero.mpr zero_lt_one⟩

/-- Appending a plus to minus-one gives the actual dyadic minus-one-half. -/
theorem appendPlus_neg_one : appendPlus (-1 : Surreal.{u}) =
    (((-1 : Dyadic) >>> 1) : Surreal.{u}) := by
  let q : Surreal.{u} := (((-1 : Dyadic) >>> 1) : Surreal.{u})
  have hq : q.birthday = 2 := by rw [birthday_dyadic]; rfl
  have hL : ∀ z ∈ ({-1} : Set Surreal.{u}), z < q := by
    intro z hz
    have hz' : z = -1 := mem_singleton_iff.mp hz
    subst z
    change (-1 : Surreal.{u}) < (((-1 : Dyadic) >>> 1) : Surreal.{u})
    exact_mod_cast (show (-1 : Dyadic) < ((-1 : Dyadic) >>> 1) from by decide)
  have hR : ∀ z ∈ rightPrefixes (-1 : Surreal.{u}), q < z := by
    intro z hz
    rw [rightPrefixes_neg_one] at hz
    have hz' : z = 0 := mem_singleton_iff.mp hz
    subst z
    change (((-1 : Dyadic) >>> 1) : Surreal.{u}) < 0
    exact_mod_cast (show ((-1 : Dyadic) >>> 1) < 0 from by decide)
  by_contra h
  rw [appendPlus_eq_ofSets] at h
  have ht : (appendPlus (-1 : Surreal.{u})).birthday < q.birthday := by
    rw [appendPlus_eq_ofSets]
    exact birthday_ofSets_lt_of_btwn hL hR h
  simp [birthday_appendPlus, hq] at ht

/-- The mixed-sign exponent minus-one-half has one plus sign. -/
theorem plusCount_neg_half : plusCount (((-1 : Dyadic) >>> 1) : Surreal.{u}) = 1 := by
  have hn : plusCount (-1 : Surreal.{u}) = 0 := by
    simpa only [NatOrdinal.toSurreal_one] using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  rw [← appendPlus_neg_one, plusCount_appendPlus, hn, zero_add]

/-- A negative mixed-sign exponent can give omega many pluses under the omega-map. -/
theorem plusCount_wpow_neg_half :
    plusCount (ω^ (((-1 : Dyadic) >>> 1) : Surreal.{u})) = NatOrdinal.of Ordinal.omega0 := by
  rw [plusCount_wpow, plusCount_neg_half, NatOrdinal.wpow_one]

/-- Every additional natural coefficient at this mixed-sign exponent costs an omega block. -/
theorem coefficient_neg_half (n : ℕ) :
    ((n + 1 : ℕ) : Surreal.{u}) * ω^ (((-1 : Dyadic) >>> 1) : Surreal.{u}) =
      appendPluses (ω^ (((-1 : Dyadic) >>> 1) : Surreal.{u}))
        (Ordinal.omega0 * (n : Ordinal)) := by
  rw [natCast_mul_wpow_eq_appendPluses, plusCount_neg_half, NatOrdinal.wpow_one,
    NatOrdinal.val_of]

end Tests
