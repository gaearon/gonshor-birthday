/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.SupportGap
public import GonshorBirthday.Surreal.Birthday.ReducedCostHead

/-!
# Right-prefix gap clients with actual infinite normal forms

The series indexed by the negative ordinals below a limit has genuinely infinite
support. Its length and support are checked before using the limit-support theorem.
The limit and its cofinality are arbitrary.
-/

universe u
public noncomputable section
namespace Tests
open Surreal Set

private def decreasingOrdinalTerms (Λ : Ordinal.{u}) : SurrealHahnSeries.TermSeq.{u} where
  length := Λ
  exp i := -(NatOrdinal.of i.val : Surreal.{u})
  coeff _ := 1
  exp_strictAnti := by
    intro i j hij
    apply neg_lt_neg
    apply NatOrdinal.toSurreal.strictMono
    exact hij
  coeff_ne_zero _ := one_ne_zero

/-- The surreal normal form with coefficient one at every negative ordinal below `Λ`. -/
def decreasingOrdinalSeries (Λ : Ordinal.{u}) : Surreal.{u} :=
  (decreasingOrdinalTerms Λ : SurrealHahnSeries).toSurreal

/-- The constructed series has exactly the prescribed support. -/
theorem support_decreasingOrdinalSeries (Λ : Ordinal.{u}) :
    (decreasingOrdinalSeries Λ).support =
      range (fun i : Iio Λ ↦ -(NatOrdinal.of i.val : Surreal.{u})) := by
  simp only [decreasingOrdinalSeries, SurrealHahnSeries.support_toSurreal,
    SurrealHahnSeries.TermSeq.support_coe, decreasingOrdinalTerms]

/-- The normal-form length is the entire ordinal index, including arbitrary limits. -/
theorem length_decreasingOrdinalSeries (Λ : Ordinal.{u}) :
    (decreasingOrdinalSeries Λ).length = Λ := by
  simp only [decreasingOrdinalSeries, SurrealHahnSeries.length_toSurreal,
    SurrealHahnSeries.TermSeq.length_coe, decreasingOrdinalTerms]

/-- A nonzero limit index gives a support without a least exponent. -/
theorem decreasingOrdinalSeries_no_min {Λ : Ordinal.{u}} (hΛ : Order.IsSuccLimit Λ) :
    ∀ s ∈ (decreasingOrdinalSeries Λ).support,
      ∃ t ∈ (decreasingOrdinalSeries Λ).support, t < s := by
  intro s hs
  rw [support_decreasingOrdinalSeries] at hs
  obtain ⟨i, rfl⟩ := hs
  let j : Iio Λ := ⟨i.val + 1, hΛ.add_one_lt i.2⟩
  refine ⟨-(NatOrdinal.of j.val : Surreal.{u}), ?_, ?_⟩
  · rw [support_decreasingOrdinalSeries]
    exact mem_range_self j
  · apply neg_lt_neg
    apply NatOrdinal.toSurreal.strictMono
    change i.val < i.val + 1
    exact lt_add_one _

/-- The genuine limit-support example has smaller right gaps at every supported scale. -/
theorem decreasingOrdinalSeries_small_gaps {Λ : Ordinal.{u}} (hΛ : Order.IsSuccLimit Λ)
    {s : Surreal.{u}} (hs : s ∈ (decreasingOrdinalSeries Λ).support) :
    ∃ p ∈ rightPrefixes (decreasingOrdinalSeries Λ),
      (p - decreasingOrdinalSeries Λ).wlog < s :=
  exists_rightPrefix_small_gap_of_no_min_support (decreasingOrdinalSeries_no_min hΛ) hs

/-- Every right-prefix gap of the genuine limit-support example can be strictly halved. -/
theorem decreasingOrdinalSeries_half_gaps {Λ : Ordinal.{u}} (hΛ : Order.IsSuccLimit Λ)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes (decreasingOrdinalSeries Λ)) :
    ∃ p ∈ rightPrefixes (decreasingOrdinalSeries Λ),
      2 * (p - decreasingOrdinalSeries Λ) < w - decreasingOrdinalSeries Λ :=
  exists_rightPrefix_half_gap_of_no_min_support (decreasingOrdinalSeries_no_min hΛ) hw

/-- The countable example has actual right prefixes, so the half-gap conclusion is nonvacuous. -/
theorem omegaSeries_rightPrefixes_nonempty :
    (rightPrefixes (decreasingOrdinalSeries Ordinal.omega0 : Surreal.{u})).Nonempty := by
  have hs : (0 : Surreal.{u}) ∈ (decreasingOrdinalSeries Ordinal.omega0).support := by
    rw [support_decreasingOrdinalSeries]
    refine ⟨⟨0, Ordinal.omega0_pos⟩, ?_⟩
    simp
  obtain ⟨p, hp, _⟩ := decreasingOrdinalSeries_small_gaps Ordinal.isSuccLimit_omega0 hs
  exact ⟨p, hp⟩

/-- A negative last coefficient after a nonempty higher head uses the same gap theorem. -/
theorem negative_last_term_small_gaps (u : Surreal.{u}) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ rightPrefixes (ω^ (u + 1) - ω^ (appendMinus u)),
      p - (ω^ (u + 1) - ω^ (appendMinus u)) < (ε : Surreal) * ω^ u := by
  have hs : appendMinus u ∈ (ω^ (u + 1) - ω^ (appendMinus u)).support := by
    rw [mem_support_iff, sub_eq_add_neg, coeff_add, coeff_neg]
    simp only [Pi.add_apply, Pi.neg_apply, coeff_wpow]
    have hne : appendMinus u ≠ u + 1 := ((appendMinus_lt u).trans (lt_add_one u)).ne
    simp [Pi.single_eq_of_ne hne]
  exact exists_rightPrefix_sub_lt_real_mul_wpow_of_support hs
    (mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus u, appendMinus_lt u⟩) hε

example (s : Surreal.{u}) : birthdayTruncation 0
    ((0 : Surreal).normalFormTrunc s + ((0 : Surreal).coeff s : Surreal) * ω^ s).birthday =
      (0 : Surreal).normalFormTrunc s + ((0 : Surreal).coeff s : Surreal) * ω^ s :=
  birthdayTruncation_trunc_add_coeff_wpow 0 s

end Tests
