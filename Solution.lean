/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Copyright (c) 2025 Aaron Liu. All rights reserved.
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Aaron Liu, Apurva Nakade, Fox Thomson, František Silváši,
Isabel Longbottom, Junyan Xu, Kim Morrison, Mario Carneiro, Reid Barton, Theodore Hwa,
Violeta Hernández Palacios, Yuyang Zhao
-/
/-
Adapted and modified from the Apache-2.0-licensed CombinatorialGames construction:
https://github.com/vihdzp/combinatorial-games
-/
module

public import GonshorBirthday.Inline.Multiplication

/-! # Proof of the Mathlib-only multiplication birthday statement -/

universe u
public noncomputable section
namespace GonshorBirthday.Palomar

/-- The birthday of a product is bounded by the natural product of its birthdays. -/
theorem birthday_mul_le (x y : Inline.Surreal.{u}) :
    Inline.Game.birthday (Inline.Game.mul x.game y.game) ≤
      Inline.naturalMul (Inline.Game.birthday x.game) (Inline.Game.birthday y.game) :=
  Inline.birthday_mul_le x y

end GonshorBirthday.Palomar
