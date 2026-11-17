/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Violeta Hernández Palacios
-/
module

public import GonshorBirthday.Inline.Ordinal
public import CombinatorialGames.NatOrdinal.Basic

/-!
# Agreement of natural ordinal operations

The visible Mathlib-only recursive definitions agree with the dependency's
natural ordinal addition and multiplication for every pair of ordinals.
-/

public noncomputable section

namespace GonshorBirthday.Inline

universe v

/-- The visible natural sum is the natural sum of the dependency. -/
theorem naturalAdd_eq_native (a b : Ordinal.{v}) :
    naturalAdd a b = (NatOrdinal.of a + NatOrdinal.of b).val := by
  induction a, b using ordinalPairRec with
  | _ a b ih =>
    rw [naturalAdd_eq, NatOrdinal.add_def]
    change max (⨆ x : Set.Iio a, Order.succ (naturalAdd x.1 b))
        (⨆ y : Set.Iio b, Order.succ (naturalAdd a y.1)) =
      max (⨆ x : Set.Iio a, Order.succ ((NatOrdinal.of x.1 + NatOrdinal.of b).val))
        (⨆ y : Set.Iio b, Order.succ ((NatOrdinal.of a + NatOrdinal.of y.1).val))
    congr 1
    · congr 1
      funext x
      rw [ih x.1 b (Prod.Lex.left b b x.2)]
    · congr 1
      funext y
      rw [ih a y.1 (Prod.Lex.right a y.2)]

/-- The visible natural product is the natural product of the dependency. -/
theorem naturalMul_eq_native (a b : Ordinal.{v}) :
    naturalMul a b = (NatOrdinal.of a * NatOrdinal.of b).val := by
  induction a, b using ordinalPairRec with
  | _ a b ih =>
    rw [naturalMul_eq, NatOrdinal.mul_def]
    apply congrArg sInf
    ext c
    change (∀ a' < a, ∀ b' < b,
      naturalAdd (naturalMul a' b) (naturalMul a b') <
        naturalAdd c (naturalMul a' b')) ↔ _
    simp only [naturalAdd_eq_native]
    apply forall_congr'
    intro a'
    apply forall_congr'
    intro ha
    apply forall_congr'
    intro b'
    apply forall_congr'
    intro hb
    rw [ih a' b (Prod.Lex.left b b ha), ih a b' (Prod.Lex.right a hb),
      ih a' b' (Prod.Lex.left b' b ha)]
    rfl

end GonshorBirthday.Inline
