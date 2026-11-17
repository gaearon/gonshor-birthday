/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ExpansionLength
public import GonshorBirthday.Surreal.Birthday.Append

import Mathlib.SetTheory.Ordinal.Principal

/-!
# Complete expansion successor and limit clients

The mixed word obtained by appending a minus to one has expanded length omega squared.
At the first infinite ordinal, the prefix-bound criterion reduces exactly to all finite
ordinal prefixes.
-/

public noncomputable section

namespace Tests

open Surreal Ordinal

/-- The mixed two-sign exponent has a final omega-squared block. -/
theorem mixed_exponent_full_length :
    omegaExpansionLength (appendMinus (1 : Surreal.{0})) Set.univ = ω^ (2 : NatOrdinal.{0}) := by
  have h := omegaExpansionLength_univ_birthdayTruncation_add_one (appendMinus (1 : Surreal.{0}))
    (a := 1) (by rw [birthday_appendMinus, birthday_one])
  have ht1 : birthdayTruncation (appendMinus (1 : Surreal.{0})) 1 = 1 := by
    simpa only [birthday_one] using birthdayTruncation_appendMinus (1 : Surreal.{0})
  have ht2 : birthdayTruncation (appendMinus (1 : Surreal.{0})) (1 + 1) = appendMinus 1 := by
    convert birthdayTruncation_birthday (appendMinus (1 : Surreal.{0})) using 1
    rw [birthday_appendMinus, birthday_one]
  have he1 : omegaExpansionLength (1 : Surreal.{0}) Set.univ = NatOrdinal.of Ordinal.omega0 := by
    rw [← reducedOmegaCost_eq_omegaExpansionLength_univ
      (C := 1) (by simp), reducedOmegaCost_one]
  have hp1 : plusCount (1 : Surreal.{0}) = 1 := by
    simpa using plusCount_toSurreal (1 : NatOrdinal.{0})
  rw [ht1, ht2, he1, hp1, one_add_one_eq_two, NatOrdinal.val_of] at h
  have hs : Ordinal.omega0 < (ω^ (2 : NatOrdinal.{0})).val := by
    simpa only [NatOrdinal.wpow_one, NatOrdinal.val_of] using
      NatOrdinal.val.strictMono (NatOrdinal.wpow_lt_wpow.mpr
        (one_lt_two : (1 : NatOrdinal.{0}) < 2))
  have he : Ordinal.omega0 + (ω^ (2 : NatOrdinal.{0})).val =
      (ω^ (2 : NatOrdinal.{0})).val := by
    rw [NatOrdinal.val_wpow] at hs ⊢
    exact Ordinal.add_omega0_opow hs
  rw [he] at h
  exact NatOrdinal.val.injective h

/-- At omega, bounding every finite ordinal prefix bounds the complete expansion. -/
theorem omega_full_length_le_iff (M : NatOrdinal.{0}) :
    omegaExpansionLength (NatOrdinal.of Ordinal.omega0 : NatOrdinal.{0}).toSurreal Set.univ ≤ M ↔
      ∀ n : ℕ, omegaExpansionLength (n : NatOrdinal.{0}).toSurreal Set.univ ≤ M := by
  let a : NatOrdinal.{0} := NatOrdinal.of Ordinal.omega0
  let E (x : Surreal.{0}) := omegaExpansionLength x Set.univ
  have ht : birthdayTruncation a.toSurreal a = a.toSurreal := birthdayTruncation_toSurreal le_rfl
  have he := omegaExpansionLength_univ_birthdayTruncation_limit a.toSurreal
    (a := a) (by simp) (by simpa only [a, NatOrdinal.val_of] using Ordinal.isSuccLimit_omega0) M
  change E (birthdayTruncation a.toSurreal a) ≤ M ↔
    ∀ b < a, E (birthdayTruncation a.toSurreal b) ≤ M at he
  rw [ht] at he
  constructor
  · intro h n
    have hn : (n : NatOrdinal.{0}) < a := by
      simpa only [NatOrdinal.of_natCast] using NatOrdinal.of.strictMono
        (Ordinal.natCast_lt_omega0 n)
    have h' := he.mp h (n : NatOrdinal.{0}) hn
    rw [birthdayTruncation_toSurreal hn.le] at h'
    exact h'
  · intro h
    apply he.mpr
    intro b hb
    have hb' : b.val < Ordinal.omega0 := hb
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hb'
    have hbn : b = (n : NatOrdinal.{0}) := by
      simpa only [NatOrdinal.of_val, NatOrdinal.of_natCast] using congrArg NatOrdinal.of hn
    subst b
    rw [birthdayTruncation_toSurreal hb.le]
    exact h n

end Tests
