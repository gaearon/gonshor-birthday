/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ExpansionPosition
public import GonshorBirthday.NatOrdinal.OrderedSumPosition

import Mathlib.Tactic.NormNum
import Mathlib.Order.Interval.Finset.Fin

/-!
# Ordered-block position clients

Inside the second of two omega blocks, local position seven has global position omega plus
seven. The surreal expansion client crosses the first infinite block boundary of the
ordinal exponent two.
-/

public noncomputable section

namespace Tests

open Ordinal Surreal

/-- The rank inside the second omega block includes the whole first block. -/
theorem second_omega_block_position :
    Ordinal.typein ((· < ·) : (Σₗ _i : Fin 2, (Ordinal.omega0 : Ordinal.{0}).ToType) → _ → Prop)
      (toLex ⟨1, Ordinal.enum ((· < ·) : (Ordinal.omega0 : Ordinal.{0}).ToType → _ → Prop)
        ⟨7, by
          change (7 : Ordinal.{0}) < typeLT (Ordinal.omega0 : Ordinal.{0}).ToType
          rw [Ordinal.type_toType]
          exact Ordinal.natCast_lt_omega0 7⟩⟩) =
      Ordinal.omega0 + 7 := by
  rw [Ordinal.typein_sigma, Ordinal.typein_enum, Ordinal.type_sigma_const,
    Ordinal.type_toType, Ordinal.type_fintype]
  norm_num

/-- A genuine infinite expansion position lies in an original finite exponent block. -/
theorem omega_position_in_two_expansion :
    ∃ a : NatOrdinal.{0}, a < 2 ∧ ∃ t : Ordinal.{0},
      t < (ω^ (plusCount (birthdayTruncation (2 : NatOrdinal.{0}).toSurreal a) + 1)).val ∧
      Ordinal.omega0 =
        (omegaExpansionLength (birthdayTruncation (2 : NatOrdinal.{0}).toSurreal a)
          Set.univ).val + t := by
  have he : omegaExpansionLength (2 : NatOrdinal.{0}).toSurreal Set.univ =
      ω^ (2 : NatOrdinal.{0}) := by
    rw [← reducedOmegaCost_eq_omegaExpansionLength_univ
      (C := (2 : NatOrdinal.{0}).toSurreal) (by simp), reducedOmegaCost_self_eq_wpow,
      plusCount_toSurreal]
  have hj : Ordinal.omega0 <
      (omegaExpansionLength (2 : NatOrdinal.{0}).toSurreal Set.univ).val := by
    rw [he]
    simpa only [NatOrdinal.wpow_one, NatOrdinal.val_of] using
      NatOrdinal.val.strictMono (NatOrdinal.wpow_lt_wpow.mpr
        (one_lt_two : (1 : NatOrdinal.{0}) < 2))
  simpa only [birthday_toSurreal] using
    (omegaExpansionLength_univ_position (2 : NatOrdinal.{0}).toSurreal hj).resolve_left
      Ordinal.omega0_ne_zero

end Tests
