/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.ProductCut
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Public canonical product-cut clients

A product of negative integers forces the right-right multiplication family.
-/

universe u
open Surreal

example (x : Surreal.{u}) : leftPrefixes (x * 0) = ∅ := by simp

example : ∃ a ∈ rightPrefixes (-2 : Surreal.{u}),
    ∃ b ∈ rightPrefixes (-3 : Surreal), (5 : Surreal) ≤ a * -3 + -2 * b - a * b := by
  have h5 : NatOrdinal.toSurreal (5 : NatOrdinal.{u}) = (5 : Surreal.{u}) :=
    NatOrdinal.toSurreal_natCast 5
  have h6 : NatOrdinal.toSurreal (6 : NatOrdinal.{u}) = (6 : Surreal.{u}) :=
    NatOrdinal.toSurreal_natCast 6
  have ht := birthdayTruncation_toSurreal (show (5 : NatOrdinal.{u}) ≤ 6 by norm_num)
  rw [h5, h6] at ht
  have hz0 : (5 : Surreal.{u}) ∈ leftPrefixes 6 := by
    apply mem_leftPrefixes_iff.mpr
    refine ⟨?_, by norm_num⟩
    simpa using ht
  have he : (-2 : Surreal.{u}) * (-3) = 6 := by ring
  have hz : (5 : Surreal.{u}) ∈ leftPrefixes ((-2 : Surreal) * (-3)) := by
    rw [he]
    exact hz0
  obtain ⟨a, ha, b, hb, hz⟩ | h := exists_leftPrefixes_mul_ge hz
  · have h2 : NatOrdinal.toSurreal (2 : NatOrdinal.{u}) = (2 : Surreal.{u}) :=
      NatOrdinal.toSurreal_natCast 2
    have hL := leftPrefixes_neg_toSurreal (2 : NatOrdinal.{u})
    rw [h2] at hL
    simp only [hL, Set.mem_empty_iff_false] at ha
  · exact h
