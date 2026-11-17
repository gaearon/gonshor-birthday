/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Family

/-!+# Natural ordinal operations from Conway recursion

These are the recursive definitions of natural addition and multiplication from
CombinatorialGames, stated on Mathlib ordinals without its arithmetic type synonym.+-/

universe u
public noncomputable section

namespace GonshorBirthday.Inline

/-- Lexicographic comparison of ordinal pairs is well founded. -/
theorem ordinal_pair_wf :
    WellFounded (Prod.Lex ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)
      ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)) :=
  Ordinal.lt_wf.prod_lex Ordinal.lt_wf

/-- Well-founded recursion on an ordered pair of ordinals. -/
def ordinalPairRec {C : Ordinal.{u} → Ordinal.{u} → Sort*}
    (step : ∀ a b,
      (∀ a' b', Prod.Lex (· < ·) (· < ·) (a', b') (a, b) → C a' b') → C a b)
    (a b : Ordinal.{u}) : C a b :=
  @WellFounded.fix (Ordinal.{u} × Ordinal.{u}) (fun p ↦ C p.1 p.2) _
    ordinal_pair_wf
    (fun p rec ↦ step p.1 p.2 (fun a' b' h ↦ rec (a', b') h)) (a, b)

/-- The characteristic equation for pair recursion. -/
theorem ordinalPairRec_eq {C : Ordinal.{u} → Ordinal.{u} → Sort*}
    (step : ∀ a b,
      (∀ a' b', Prod.Lex (· < ·) (· < ·) (a', b') (a, b) → C a' b') → C a b)
    (a b : Ordinal.{u}) :
    ordinalPairRec step a b = step a b (fun a' b' _ ↦ ordinalPairRec step a' b') :=
  WellFounded.fix_eq ..

/-- The natural sum is the least ordinal above every sum obtained by lowering one argument. -/
@[expose] def naturalAdd : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} :=
  ordinalPairRec fun a b rec ↦
    max (⨆ x : Set.Iio a, Order.succ (rec x.1 b (Prod.Lex.left b b x.2)))
      (⨆ y : Set.Iio b, Order.succ (rec a y.1 (Prod.Lex.right a y.2)))

/-- The defining recursion for natural addition. -/
theorem naturalAdd_eq (a b : Ordinal.{u}) :
    naturalAdd a b =
      max (⨆ x : Set.Iio a, Order.succ (naturalAdd x.1 b))
        (⨆ y : Set.Iio b, Order.succ (naturalAdd a y.1)) := by
  rw [naturalAdd, ordinalPairRec_eq]

/-- Conway's recursive definition of the natural (Hessenberg) product. -/
@[expose] def naturalMul : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} :=
  ordinalPairRec fun a b rec ↦
    sInf {c | ∀ a' (ha : a' < a), ∀ b' (hb : b' < b),
      naturalAdd (rec a' b (Prod.Lex.left b b ha)) (rec a b' (Prod.Lex.right a hb)) <
        naturalAdd c (rec a' b' (Prod.Lex.left b' b ha))}

/-- The defining recursion for natural multiplication. -/
theorem naturalMul_eq (a b : Ordinal.{u}) :
    naturalMul a b = sInf {c | ∀ a' < a, ∀ b' < b,
      naturalAdd (naturalMul a' b) (naturalMul a b') <
        naturalAdd c (naturalMul a' b')} := by
  rw [naturalMul, ordinalPairRec_eq]

end GonshorBirthday.Inline
