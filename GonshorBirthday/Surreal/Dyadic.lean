/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Dyadic

import Mathlib.Algebra.Order.Ring.Rat

/-!
# Canonical neighbours of noninteger dyadic games

The canonical game of a noninteger dyadic fits both neighbouring canonical games.
-/

public section

open IGame

namespace Dyadic

/-- A noninteger dyadic lies below the upper neighbour of its lower neighbour. -/
theorem lt_upper_lower_of_den_ne_one {x : Dyadic} (hx : x.den ≠ 1) : x < x.lower.upper := by
  rw [← Dyadic.coe_lt_coe, coe_upper, coe_lower]
  have hd : ((x.den : ℚ)⁻¹) < ((x.lower.den : ℚ)⁻¹) := by
    apply (inv_lt_inv₀ (by exact_mod_cast x.den_pos) (by exact_mod_cast x.lower.den_pos)).mpr
    exact_mod_cast den_lower_lt hx
  calc
    (x : ℚ) = (x - (x.den : ℚ)⁻¹) + (x.den : ℚ)⁻¹ := (sub_add_cancel _ _).symm
    _ < _ := add_lt_add_right hd _

/-- A noninteger dyadic lies above the lower neighbour of its upper neighbour. -/
theorem lower_upper_lt_of_den_ne_one {x : Dyadic} (hx : x.den ≠ 1) : x.upper.lower < x := by
  have hn : (-x).den ≠ 1 := by simpa using hx
  simpa using lt_upper_lower_of_den_ne_one hn

/-- A noninteger dyadic fits the canonical game of its lower neighbour. -/
theorem fits_lower {x : Dyadic} (hx : x.den ≠ 1) :
    Fits (x : IGame) (x.lower : IGame) := by
  constructor
  · intro z hz
    rw [eq_lower_of_mem_moves_left_toIGame hz]
    exact (toIGame_lt_toIGame.mpr ((lower_lt x.lower).trans (lower_lt x))).not_ge
  · intro z hz
    rw [eq_upper_of_mem_moves_right_toIGame hz]
    exact (toIGame_lt_toIGame.mpr (lt_upper_lower_of_den_ne_one hx)).not_ge

/-- A noninteger dyadic fits the canonical game of its upper neighbour. -/
theorem fits_upper {x : Dyadic} (hx : x.den ≠ 1) :
    Fits (x : IGame) (x.upper : IGame) := by
  constructor
  · intro z hz
    rw [eq_lower_of_mem_moves_left_toIGame hz]
    exact (toIGame_lt_toIGame.mpr (lower_upper_lt_of_den_ne_one hx)).not_ge
  · intro z hz
    rw [eq_upper_of_mem_moves_right_toIGame hz]
    exact (toIGame_lt_toIGame.mpr ((lt_upper x).trans (lt_upper x.upper))).not_ge

end Dyadic
