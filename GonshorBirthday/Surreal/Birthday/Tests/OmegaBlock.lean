/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.OmegaBlock

/-!
# Public omega sign-block clients
-/

universe u
open Surreal

example (x : Surreal.{u}) :
    ω^ appendPlus x = appendPluses (ω^ x) ((ω^ plusCount x).val * Ordinal.omega0) :=
  wpow_appendPlus x

example (x : Surreal.{u}) :
    ω^ appendMinus x = appendMinuses (ω^ x) ((ω^ plusCount x).val * Ordinal.omega0) :=
  wpow_appendMinus x

example : ω^ appendMinus (0 : Surreal.{u}) = appendMinuses 1 Ordinal.omega0 := by
  rw [wpow_appendMinus]
  simp

example : ω^ appendMinus (appendPlus (-1 : Surreal.{u})) =
    appendMinuses (ω^ appendPlus (-1 : Surreal)) (Ordinal.omega0 * Ordinal.omega0) := by
  rw [wpow_appendMinus, plusCount_appendPlus]
  have he : plusCount (-(1 : Surreal.{u})) = 0 := by
    simpa using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  simp [he]

example (o : NatOrdinal.{u}) :
    (ω^ (NatOrdinal.of Ordinal.omega0).toSurreal).birthday ≤ o ↔
      ∀ a < NatOrdinal.of Ordinal.omega0,
        (ω^ birthdayTruncation (NatOrdinal.of Ordinal.omega0).toSurreal a).birthday ≤ o := by
  simpa only [birthday_toSurreal] using
    birthday_wpow_le_iff_of_isSuccLimit (NatOrdinal.of Ordinal.omega0).toSurreal
      (by simpa only [birthday_toSurreal, NatOrdinal.val_of] using
        Ordinal.isSuccLimit_omega0) o
