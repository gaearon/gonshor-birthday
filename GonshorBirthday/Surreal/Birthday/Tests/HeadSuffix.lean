/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.HeadSuffix
import GonshorBirthday.Surreal.Birthday.OmegaBlock

/-!
# Negative-unit original minus suffix clients

All exponents and higher heads are allowed. At exponent minus one there is at most
one minus position although the full birthday is omega, distinguishing the count from length.
-/

universe u
open Surreal Set Ordinal

example (s : Surreal.{u}) :
    ∃ c < (ω^ (s + 1) - ω^ s).birthday,
      typeLT {i : (ω^ (s + 1) - ω^ s).birthday.val.ToType |
        c ≤ NatOrdinal.of i.toOrd.1 ∧
          ω^ (s + 1) - ω^ s < birthdayTruncation (ω^ (s + 1) - ω^ s)
            (NatOrdinal.of i.toOrd.1)} ≤ (ω^ (plusCount s)).val := by
  apply exists_minus_suffix_le_head_sub_wpow (ω^ (s + 1)) s
  rw [support_wpow]
  intro i hi
  rw [mem_singleton_iff] at hi
  subst i
  exact lt_add_one s

example : typeLT {i : (-ω^ (-1 : Surreal.{u})).birthday.val.ToType |
    -ω^ (-1 : Surreal) < birthdayTruncation (-ω^ (-1 : Surreal))
      (NatOrdinal.of i.toOrd.1)} ≤ 1 := by
  have hpc : plusCount (-1 : Surreal.{u}) = 0 := by
    simpa using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  have ht := minus_suffix_type_head_sub_wpow 0 (-1 : Surreal.{u}) (by simp)
  rw [_root_.zero_sub, birthday_zero] at ht
  have he : {i : (-ω^ (-1 : Surreal.{u})).birthday.val.ToType |
      (0 : NatOrdinal.{u}) ≤ NatOrdinal.of i.toOrd.1 ∧
        -ω^ (-1 : Surreal) < birthdayTruncation (-ω^ (-1 : Surreal))
          (NatOrdinal.of i.toOrd.1)} =
      {i : (-ω^ (-1 : Surreal.{u})).birthday.val.ToType |
        -ω^ (-1 : Surreal) < birthdayTruncation (-ω^ (-1 : Surreal))
          (NatOrdinal.of i.toOrd.1)} := by
    ext i
    simp only [mem_ofPred_eq, and_iff_right_iff_imp]
    exact fun _ ↦ bot_le
  rw [he] at ht
  simpa only [hpc, NatOrdinal.wpow_zero, NatOrdinal.val_one] using ht

example : (-ω^ (-1 : Surreal.{u})).birthday = NatOrdinal.of Ordinal.omega0 := by
  have hs : (-1 : Surreal.{u}) = appendMinus (0 : Surreal) := by
    apply eq_appendMinus_of_birthdayTruncation_eq
    · simp
    · simp
    · norm_num
  rw [birthday_neg, hs, birthday_wpow_appendMinus]
  simp
