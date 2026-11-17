/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.HeadMidpoint
import GonshorBirthday.Surreal.Birthday.LastMinusFamily

/-!
# Shifted dyadic boundary clients

A negative preceding coefficient and a nonempty higher head occur in the family.
Zero preceding coefficient recovers the strict higher-head boundary.
-/

universe u
open Surreal Set

example (K w : Surreal.{u}) (hK : K.support ⊆ Ioi w) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K + (2 : Surreal)⁻¹ ^ n * ω^ w ∈
        rightPrefixes (K + ω^ (appendMinus w)) := by
  obtain ⟨N, hN, _, _⟩ := exists_head_shifted_reciprocal_wpow_halving_family K w hK
    (a := (0 : ℝ)) (by simp)
  exact ⟨N, by simpa using hN⟩

example (w : Surreal.{u}) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ω^ (w + 1) + (-ω^ w + (2 : Surreal)⁻¹ ^ n * ω^ w) ∈
        rightPrefixes (ω^ (w + 1) + (-ω^ w + ω^ (appendMinus w))) := by
  have hK : (ω^ (w + 1)).support ⊆ Ioi w := by
    rw [support_wpow]
    intro i hi
    rw [mem_singleton_iff] at hi
    subst i
    exact lt_add_one w
  obtain ⟨N, hN, _, _⟩ := exists_head_shifted_reciprocal_wpow_halving_family
    (ω^ (w + 1)) w hK (a := (-1 : ℝ)) (by simp)
  exact ⟨N, by simpa using hN⟩

example (w : Surreal.{u}) :
    ∃ N : ℕ, ∀ p ∈ rightPrefixes (ω^ (appendPlus (appendMinus w))),
      ∃ n : ℕ, N ≤ n ∧ (2 : Surreal)⁻¹ ^ n * ω^ w ≤ p := by
  have hw : w ∈ rightPrefixes (appendPlus (appendMinus w)) := by
    rw [rightPrefixes_appendPlus]
    exact mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus w, appendMinus_lt w⟩
  have hm : ∀ v ∈ rightPrefixes (appendPlus (appendMinus w)), w ≤ v := by
    intro v hv
    rw [rightPrefixes_appendPlus] at hv
    exact le_of_mem_rightPrefixes_appendMinus hv
  obtain ⟨N, _, hN, _⟩ :=
    exists_head_shifted_reciprocal_wpow_halving_family_of_min_rightPrefix 0 w (by simp)
      (a := (0 : ℝ)) (by simp) hw hm
  exact ⟨N, by simpa using hN⟩

example (w : Surreal.{u}) {s : Surreal.{u}} (hw : w ∈ rightPrefixes s) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ω^ (w + 1) + (-ω^ w + (2 : Surreal)⁻¹ ^ n * ω^ w) ∈
        rightPrefixes (ω^ (w + 1) + (-ω^ w + ((1 / 3 : ℝ) : Surreal) * ω^ s)) := by
  have hK : (ω^ (w + 1)).support ⊆ Ioi w := by
    rw [support_wpow]
    intro i hi
    rw [mem_singleton_iff] at hi
    subst i
    exact lt_add_one w
  have ht := exists_head_shifted_reciprocal_wpow_rightPrefixes_of_pos
    (ω^ (w + 1)) w hK (a := (-1 : ℝ)) (by simp) (t := (1 / 3 : ℝ)) (by norm_num) hw
  simpa using ht

example (w : Surreal.{u}) {s : Surreal.{u}} (hw : w ∈ rightPrefixes s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ, (1 / 3 : ℝ) < q ∧ q < 1 / 3 + ε ∧
      ω^ (w + 1) + (q : Surreal) * ω^ w ∈
        rightPrefixes (ω^ (w + 1) +
          (((1 / 3 : ℝ) : Surreal) * ω^ w + ((1 / 3 : ℝ) : Surreal) * ω^ s)) := by
  apply exists_head_real_mul_wpow_rightPrefix_lt_add (ω^ (w + 1)) w _ (1 / 3 : ℝ)
    (by norm_num) hw hε
  rw [support_wpow]
  intro i hi
  rw [mem_singleton_iff] at hi
  subst i
  exact lt_add_one w
