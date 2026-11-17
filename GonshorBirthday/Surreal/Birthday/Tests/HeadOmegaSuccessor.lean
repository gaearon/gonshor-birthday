/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadOmegaSuccessor

/-!
# Headed omega successor clients

Even at exponent plus rank zero both successor signs append an entire omega block.
The head may be nonempty and have arbitrary real coefficients.
-/

universe u
public section
open Surreal Set
namespace Tests

/-- An exponent minus at zero appends omega many minuses after an arbitrary higher head. -/
theorem headed_reciprocal_omega_minus_word {H : Surreal.{u}}
    (hH : H.support ⊆ Ioi (0 : Surreal)) :
    appendMinuses (H + 1) Ordinal.omega0 = H + ω^ (-1 : Surreal) := by
  have he : (-1 : Surreal.{u}) = appendMinus (0 : Surreal) := by
    apply eq_appendMinus_of_birthdayTruncation_eq
    · simp only [birthday_zero, birthdayTruncation_zero]
    · simp only [birthday_neg, birthday_one, birthday_zero, zero_add]
    · exact neg_lt_zero.mpr (zero_lt_one : (0 : Surreal.{u}) < 1)
  have h := appendMinuses_head_wpow_appendMinus hH
  simpa only [plusCount_zero, NatOrdinal.wpow_zero, NatOrdinal.val_one, one_mul,
    wpow_zero, ← he] using h

/-- A nonempty higher head retains the whole exponent plus block at zero. -/
theorem omega_square_head_plus_word :
    appendPluses (ω^ (2 : Surreal.{u}) + 1) Ordinal.omega0 =
      ω^ (2 : Surreal.{u}) + ω^ (1 : Surreal) := by
  have he : (1 : Surreal.{u}) = appendPlus (0 : Surreal) := by
    apply eq_appendPlus_of_birthdayTruncation_eq
    · simp only [birthday_zero, birthdayTruncation_zero]
    · simp only [birthday_one, birthday_zero, zero_add]
    · exact zero_lt_one
  have hH : (ω^ (2 : Surreal.{u})).support ⊆ Ioi (appendPlus (0 : Surreal)) := by
    rw [← he]
    simp only [support_wpow, singleton_subset_iff, mem_Ioi]
    norm_num
  have h := appendPluses_head_wpow_appendPlus hH
  simpa only [plusCount_zero, NatOrdinal.wpow_zero, NatOrdinal.val_one, one_mul,
    wpow_zero, ← he] using h

end Tests
