/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadOmega

/-!
# Varying right-exponent boundary clients

An arbitrary head is allowed. The concrete family above exponent minus omega
has no last right exponent and a nonempty unit head.
-/

universe u
open Surreal Set

private theorem ordinal_mem_left {a b : NatOrdinal.{u}} (hab : a < b) :
    a.toSurreal ∈ leftPrefixes b.toSurreal := by
  apply mem_leftPrefixes_iff.mpr
  exact ⟨by rw [birthday_toSurreal, birthdayTruncation_toSurreal hab.le],
    NatOrdinal.toSurreal.strictMono hab⟩

private theorem omega_neg_no_min :
    ∀ v ∈ rightPrefixes (-(NatOrdinal.of Ordinal.omega0).toSurreal : Surreal.{u}),
      ∃ z ∈ rightPrefixes (-(NatOrdinal.of Ordinal.omega0).toSurreal : Surreal.{u}), z < v := by
  intro v hv
  have hvl : -v ∈ leftPrefixes ((NatOrdinal.of Ordinal.omega0).toSurreal : Surreal.{u}) := by
    simpa only [neg_neg] using neg_mem_leftPrefixes_iff.mpr hv
  obtain ⟨a, ha, he, _⟩ := mem_leftPrefixes.mp hvl
  have ha' : a < NatOrdinal.of Ordinal.omega0 := by simpa using ha
  rw [birthdayTruncation_toSurreal ha'.le] at he
  obtain ⟨n, hn⟩ := NatOrdinal.lt_omega0.mp ha'
  subst a
  refine ⟨-(((n + 1 : ℕ) : NatOrdinal.{u}).toSurreal),
    neg_mem_rightPrefixes_iff.mpr (ordinal_mem_left (NatOrdinal.natCast_lt_omega0 (n + 1))), ?_⟩
  calc
    -(((n + 1 : ℕ) : NatOrdinal.{u}).toSurreal) < -((n : NatOrdinal.{u}).toSurreal) := by
      apply neg_lt_neg
      exact NatOrdinal.toSurreal.strictMono (by exact_mod_cast Nat.lt_succ_self n)
    _ = v := by rw [he, neg_neg]

/-- The unit head above exponent minus omega has a canonical half-gap right prefix. -/
public theorem Tests.negative_omega_head_half_gap {p : Surreal.{u}}
    (hp : p ∈ rightPrefixes (1 + ω^ (-(NatOrdinal.of Ordinal.omega0).toSurreal))) :
    ∃ z ∈ rightPrefixes (-(NatOrdinal.of Ordinal.omega0).toSurreal : Surreal.{u}),
      (1 : Surreal).support ⊆ Ioi z ∧
      1 + ω^ z ∈ rightPrefixes (1 + ω^ (-(NatOrdinal.of Ordinal.omega0).toSurreal)) ∧
      2 * ((1 + ω^ z) - (1 + ω^ (-(NatOrdinal.of Ordinal.omega0).toSurreal))) <
        p - (1 + ω^ (-(NatOrdinal.of Ordinal.omega0).toSurreal)) := by
  apply exists_head_wpow_rightPrefix_half_gap_of_no_min 1
    (-(NatOrdinal.of Ordinal.omega0).toSurreal) _ omega_neg_no_min hp
  have h1 : (1 : NatOrdinal.{u}) < NatOrdinal.of Ordinal.omega0 := by simp
  refine ⟨-((1 : NatOrdinal.{u}).toSurreal),
    neg_mem_rightPrefixes_iff.mpr (ordinal_mem_left h1), ?_⟩
  have hs : (1 : Surreal.{u}).support = {0} := by simpa using support_wpow (0 : Surreal.{u})
  rw [hs]
  intro i hi
  rw [mem_singleton_iff] at hi
  subst i
  simp

example {p : Surreal.{u}}
    (hp : p ∈ rightPrefixes (ω^ (1 : Surreal) + ω^ (appendMinus (0 : Surreal)))) :
    ∃ q ∈ rightPrefixes (ω^ (1 : Surreal) + ω^ (appendMinus (0 : Surreal))),
      2 * (q - (ω^ (1 : Surreal) + ω^ (appendMinus (0 : Surreal)))) <
        p - (ω^ (1 : Surreal) + ω^ (appendMinus (0 : Surreal))) := by
  apply exists_rightPrefix_half_gap_of_head_boundary (ω^ (1 : Surreal)) (appendMinus 0) _ hp
  refine ⟨0, mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus 0, appendMinus_lt 0⟩,
    ?_⟩
  rw [support_wpow]
  intro i hi
  rw [mem_singleton_iff] at hi
  subst i
  norm_num

example (K w : Surreal.{u}) (hK : K.support ⊆ Ioi w) {a : ℝ}
    (ha : (a : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {s : Surreal.{u}} (hw : w ∈ rightPrefixes s) {p : Surreal.{u}}
    (hp : p ∈ rightPrefixes (K + ((a : Surreal) * ω^ w + ω^ s))) :
    ∃ q ∈ rightPrefixes (K + ((a : Surreal) * ω^ w + ω^ s)),
      2 * (q - (K + ((a : Surreal) * ω^ w + ω^ s))) <
        p - (K + ((a : Surreal) * ω^ w + ω^ s)) :=
  exists_rightPrefix_half_gap_of_dyadic_coefficient_boundary K w hK ha hw hp
