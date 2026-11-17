/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadRetention
public import GonshorBirthday.Surreal.Birthday.OmegaLength

/-!
# Reduced monomial costs determined by a normal-form head

The original position set retains all plus signs and exactly the minuses whose
right prefix lies below all head exponents and has a dyadic boundary coefficient.
It is one of the existing actual-cutoff reduced position sets. Its expansion
length is invariant under any change preserving support and boundary dyadicness.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- Original exponent signs retained by a normal-form head, including every plus. -/
def headOmegaPositions (H s : Surreal.{u}) : Set s.birthday.val.ToType :=
  {i | birthdayTruncation s (NatOrdinal.of i.toOrd.1) < s ∨
    (H.support ⊆ Ici (birthdayTruncation s (NatOrdinal.of i.toOrd.1)) ∧
      (H.coeff (birthdayTruncation s (NatOrdinal.of i.toOrd.1)) : Surreal.{u}).birthday <
        NatOrdinal.of Ordinal.omega0)}

/-- A minus is retained precisely at a dyadic boundary above no earlier support point. -/
theorem mem_headOmegaPositions (H s : Surreal.{u}) (i : s.birthday.val.ToType) :
    i ∈ headOmegaPositions H s ↔
      birthdayTruncation s (NatOrdinal.of i.toOrd.1) < s ∨
        (H.support ⊆ Ici (birthdayTruncation s (NatOrdinal.of i.toOrd.1)) ∧
          (H.coeff (birthdayTruncation s (NatOrdinal.of i.toOrd.1)) : Surreal.{u}).birthday <
            NatOrdinal.of Ordinal.omega0) := by
  rw [headOmegaPositions]
  rfl

/-- The expanded ordinal length of the original exponent signs retained by a head. -/
def headOmegaCost (H s : Surreal.{u}) : NatOrdinal.{u} :=
  omegaExpansionLength s (headOmegaPositions H s)

/-- The head cost is the expansion length of its retained original positions. -/
theorem headOmegaCost_eq_positions (H s : Surreal.{u}) :
    headOmegaCost H s = omegaExpansionLength s (headOmegaPositions H s) := by
  rw [headOmegaCost]

/-- Any cutoff representing native right-prefix retention selects exactly the head positions. -/
theorem headOmegaPositions_eq_reducedOmegaPositions (H s C : Surreal.{u})
    (hC : ∀ w ∈ rightPrefixes s,
      (H.support ⊆ Ici w ∧
        (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) ↔ w ≤ C) :
    headOmegaPositions H s = reducedOmegaPositions C s := by
  ext i
  rw [mem_headOmegaPositions, mem_reducedOmegaPositions]
  by_cases hl : birthdayTruncation s (NatOrdinal.of i.toOrd.1) < s
  · simp only [hl, true_or]
  · have hb : NatOrdinal.of i.toOrd.1 < s.birthday := by
      apply NatOrdinal.val.lt_iff_lt.mp
      simpa only [NatOrdinal.val_of, Set.mem_Iio] using i.toOrd.2
    have hne : birthdayTruncation s (NatOrdinal.of i.toOrd.1) ≠ s := by
      intro he
      have hh := birthday_birthdayTruncation_le s (NatOrdinal.of i.toOrd.1)
      rw [he] at hh
      exact hb.not_ge hh
    have hr : birthdayTruncation s (NatOrdinal.of i.toOrd.1) ∈ rightPrefixes s :=
      mem_rightPrefixes.mpr ⟨_, hb, rfl, lt_of_le_of_ne (le_of_not_gt hl) hne.symm⟩
    simpa only [hl, false_or] using hC _ hr

/-- Any cutoff representing native right-prefix retention gives the same expanded cost. -/
theorem headOmegaCost_eq_reducedOmegaCost (H s C : Surreal.{u})
    (hC : ∀ w ∈ rightPrefixes s,
      (H.support ⊆ Ici w ∧
        (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) ↔ w ≤ C) :
    headOmegaCost H s = reducedOmegaCost C s := by
  rw [headOmegaCost_eq_positions, headOmegaPositions_eq_reducedOmegaPositions H s C hC,
    reducedOmegaCost_eq_positions]

/-- A head cost is an actual reduced cost at the exponent or one of its right prefixes. -/
theorem exists_headOmegaCost_eq_reducedOmegaCost (H s : Surreal.{u}) :
    ∃ C : Surreal, s ≤ C ∧ (C = s ∨ C ∈ rightPrefixes s) ∧
      headOmegaPositions H s = reducedOmegaPositions C s ∧
      headOmegaCost H s = reducedOmegaCost C s := by
  obtain ⟨C, hCs, hC, he⟩ := exists_reducedOmegaPositions_eq_head_condition H s
  have hp : headOmegaPositions H s = reducedOmegaPositions C s := by
    simpa only [headOmegaPositions] using he.symm
  exact ⟨C, hCs, hC, hp, by rw [headOmegaCost_eq_positions, hp,
    reducedOmegaCost_eq_positions]⟩

/-- Support and boundary dyadicness determine the retained original positions. -/
theorem headOmegaPositions_congr {H K : Surreal.{u}} (hs : H.support = K.support)
    (hc : ∀ w : Surreal.{u},
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ↔
        (K.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (s : Surreal.{u}) : headOmegaPositions H s = headOmegaPositions K s := by
  ext i
  simp only [mem_headOmegaPositions, hs, hc]

/-- Support and boundary dyadicness determine the expanded head cost. -/
theorem headOmegaCost_congr {H K : Surreal.{u}} (hs : H.support = K.support)
    (hc : ∀ w : Surreal.{u},
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ↔
        (K.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (s : Surreal.{u}) : headOmegaCost H s = headOmegaCost K s := by
  rw [headOmegaCost_eq_positions, headOmegaCost_eq_positions, headOmegaPositions_congr hs hc]

/-- Negating the head preserves every retained exponent position. -/
theorem headOmegaPositions_neg (H s : Surreal.{u}) :
    headOmegaPositions (-H) s = headOmegaPositions H s := by
  apply headOmegaPositions_congr
  · rw [← support_coeff, ← support_coeff, coeff_neg, Function.support_neg]
  · intro w
    simp only [coeff_neg, Pi.neg_apply, Real.toSurreal_neg, birthday_neg]

/-- Negating the head preserves the expanded monomial cost. -/
theorem headOmegaCost_neg (H s : Surreal.{u}) : headOmegaCost (-H) s = headOmegaCost H s := by
  rw [headOmegaCost_eq_positions, headOmegaPositions_neg, headOmegaCost_eq_positions]

/-- An empty head retains every original exponent position. -/
theorem headOmegaPositions_zero (s : Surreal.{u}) : headOmegaPositions 0 s = Set.univ := by
  ext i
  simp only [mem_headOmegaPositions, support_zero, empty_subset, coeff_zero, Pi.zero_apply,
    Real.toSurreal_zero, birthday_zero, Set.mem_univ, iff_true]
  exact Or.inr ⟨trivial, by exact_mod_cast Ordinal.omega0_pos⟩

/-- The cost after an empty head is the full monomial birthday. -/
theorem headOmegaCost_zero (s : Surreal.{u}) : headOmegaCost 0 s = (ω^ s).birthday := by
  rw [headOmegaCost_eq_positions, headOmegaPositions_zero, birthday_wpow_eq_omegaExpansionLength]

/-- The initial monomial sign gives every head cost at least one. -/
theorem one_le_headOmegaCost (H s : Surreal.{u}) : 1 ≤ headOmegaCost H s := by
  rw [headOmegaCost_eq_positions]
  exact one_le_omegaExpansionLength _ _

/-- Deleting exponent minuses cannot exceed the unheaded monomial birthday. -/
theorem headOmegaCost_le_birthday_wpow (H s : Surreal.{u}) :
    headOmegaCost H s ≤ (ω^ s).birthday := by
  rw [headOmegaCost_eq_positions, birthday_wpow_eq_omegaExpansionLength]
  exact omegaExpansionLength_mono s (Set.subset_univ _)

/-- If all exponent minuses are deleted, only the plus-count baseline remains. -/
theorem headOmegaCost_eq_wpow_of_no_retained_rightPrefix (H s : Surreal.{u})
    (hdel : ∀ w ∈ rightPrefixes s, ¬ (H.support ⊆ Ici w ∧
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)) :
    headOmegaCost H s = ω^ plusCount s := by
  rw [headOmegaCost_eq_reducedOmegaCost H s s, reducedOmegaCost_self_eq_wpow]
  intro w hw
  exact iff_of_false (hdel w hw) (mem_rightPrefixes_iff.mp hw).2.not_ge

/-- A supported exponent in the head deletes every proper exponent minus. -/
theorem headOmegaCost_eq_wpow_of_mem_support {H s : Surreal.{u}}
    (hs : s ∈ H.support) : headOmegaCost H s = ω^ plusCount s := by
  apply headOmegaCost_eq_wpow_of_no_retained_rightPrefix
  intro w hw hret
  exact (mem_rightPrefixes_iff.mp hw).2.not_ge (mem_Ici.mp (hret.1 hs))

end Surreal
