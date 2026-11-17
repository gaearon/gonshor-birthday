/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.OmegaLength

/-!
# Public exact omega birthday clients
-/

universe u
open Surreal

example (x : Surreal.{u}) : (ω^ x).birthday = omegaExpansionLength x Set.univ :=
  birthday_wpow_eq_omegaExpansionLength x

example : (ω^ (0 : Surreal.{u})).birthday = 1 := by simp

example : (ω^ appendMinus (1 : Surreal.{u})).birthday =
    NatOrdinal.of (Ordinal.omega0 + Ordinal.omega0 * Ordinal.omega0) := by
  have hp : plusCount (1 : Surreal.{u}) = 1 := by
    simpa using plusCount_toSurreal (1 : NatOrdinal.{u})
  have hb : (ω^ (1 : Surreal.{u})).birthday = NatOrdinal.of Ordinal.omega0 := by
    simpa using birthday_wpow_toSurreal (1 : NatOrdinal.{u})
  rw [birthday_wpow_appendMinus, hp, hb]
  simp

example (x : Surreal.{u}) {a : NatOrdinal.{u}} (ha : a + 1 ≤ x.birthday)
    (hr : x < birthdayTruncation x a) {t : Ordinal.{u}}
    (ht : t < (ω^ plusCount (birthdayTruncation x a)).val * Ordinal.omega0) :
    ω^ x < birthdayTruncation (ω^ x)
      (NatOrdinal.of ((omegaExpansionLength (birthdayTruncation x a) Set.univ).val + t)) :=
  lt_birthdayTruncation_wpow_minus_block x ha hr ht

example : birthdayTruncation (ω^ appendMinus (1 : Surreal.{u}))
    (NatOrdinal.of Ordinal.omega0) = ω^ (1 : Surreal) := by
  have h1 : birthdayTruncation (appendMinus (1 : Surreal.{u})) 1 = 1 := by
    simpa only [birthday_one] using birthdayTruncation_appendMinus (1 : Surreal.{u})
  have hE : omegaExpansionLength (1 : Surreal.{u}) Set.univ =
      NatOrdinal.of Ordinal.omega0 := by
    rw [← birthday_wpow_eq_omegaExpansionLength]
    simpa using birthday_wpow_toSurreal (1 : NatOrdinal.{u})
  have ht := birthdayTruncation_wpow_minus_block (appendMinus (1 : Surreal.{u}))
    (a := 1) (by simp [birthday_appendMinus])
    (by rw [h1]; exact appendMinus_lt 1) (t := 0) (by simp)
  rw [h1] at ht
  rw [hE] at ht
  simpa only [NatOrdinal.val_of, add_zero, appendMinuses_zero] using ht
