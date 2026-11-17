/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadRetainedBlock

/-!
# Actual retained boundary block clients

A coefficient with no plus signs in the exponent still allocates omega many
original positions. At a positive plus rank the block has strictly larger length.
-/

universe u
public section
open Surreal Set
namespace Tests

/-- Plus rank zero gives an actual omega-length boundary suffix, not a one-sign suffix. -/
theorem retained_zero_plus_rank_capacity {H s w : Surreal.{u}}
    (hH : H.support ⊆ Ici w) (hw : w ∈ rightPrefixes s) (hc : H.coeff w ≠ 0)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hp : plusCount w = 0) :
    H.birthday.val + Ordinal.omega0 ≤ (H + ω^ s).birthday.val := by
  have h := birthday_add_wpow_mul_omega0_le_of_retained_boundary hH hw hc hf
  simpa only [hp, NatOrdinal.wpow_zero, NatOrdinal.val_one, one_mul] using h

/-- Every finite stage is strictly younger than the source, rather than merely bounded. -/
theorem retained_stage_strict {H s w : Surreal.{u}}
    (hH : H.support ⊆ Ici w) (hw : w ∈ rightPrefixes s) (hc : H.coeff w ≠ 0)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) (n : ℕ) :
    NatOrdinal.of (H.birthday.val + (ω^ (plusCount w)).val * (n + 1)) <
      (H + ω^ s).birthday := by
  obtain ⟨p, hp, hb⟩ := exists_head_rightPrefix_birthday_add_wpow_mul_nat hH hw hc hf n
  rw [← hb]
  exact birthday_lt_of_mem_rightPrefixes hp

end Tests
