/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.OmegaLength
public import GonshorBirthday.Surreal.Birthday.ExpansionPosition

/-!
# Complete intrinsic sign expansion of the omega-map

Every noninitial omega-map position belongs to an original exponent block and
carries exactly that exponent sign, measured by actual birthday truncations.
-/

universe u
public noncomputable section
namespace Surreal
open Set Order

/-- Every omega-map sign is initial or lies in an exact block carrying an original exponent sign. -/
theorem wpow_position (x : Surreal.{u}) {j : Ordinal.{u}}
    (hj : j < (ω^ x).birthday.val) :
    j = 0 ∨ ∃ a : NatOrdinal.{u}, a < x.birthday ∧ ∃ t : Ordinal.{u},
      t < (ω^ (plusCount (birthdayTruncation x a) + 1)).val ∧
      j = (omegaExpansionLength (birthdayTruncation x a) Set.univ).val + t ∧
      (birthdayTruncation (ω^ x) (NatOrdinal.of j) < ω^ x ↔ birthdayTruncation x a < x) ∧
      (ω^ x < birthdayTruncation (ω^ x) (NatOrdinal.of j) ↔ x < birthdayTruncation x a) := by
  rw [birthday_wpow_eq_omegaExpansionLength] at hj
  obtain hj0 | ⟨a, ha, t, ht, hpos⟩ := omegaExpansionLength_univ_position x hj
  · exact Or.inl hj0
  right
  refine ⟨a, ha, t, ht, hpos, ?_⟩
  have ha1 : a + 1 ≤ x.birthday := Order.add_one_le_of_lt ha
  have ht' : t < (ω^ plusCount (birthdayTruncation x a)).val * Ordinal.omega0 := by
    simpa only [NatOrdinal.val_wpow, NatOrdinal.val_add_one, Ordinal.opow_add,
      Ordinal.opow_one] using ht
  have hne : birthdayTruncation x a ≠ x := by
    intro he
    have hb := birthday_birthdayTruncation x ha.le
    rw [he] at hb
    exact ha.ne hb.symm
  obtain hl | hr := lt_or_gt_of_ne hne
  · have hsign := birthdayTruncation_wpow_plus_block_lt x ha1 hl ht'
    rw [← hpos] at hsign
    exact ⟨iff_of_true hsign hl, iff_of_false hsign.not_gt hl.not_gt⟩
  · have hsign := lt_birthdayTruncation_wpow_minus_block x ha1 hr ht'
    rw [← hpos] at hsign
    exact ⟨iff_of_false hsign.not_gt hr.not_gt, iff_of_true hsign hr⟩

end Surreal
