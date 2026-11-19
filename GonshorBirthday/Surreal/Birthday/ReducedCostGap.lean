/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostBaseline
public import GonshorBirthday.Surreal.Birthday.CoefficientCancellation

import GonshorBirthday.Surreal.Birthday.PrefixSums

/-!
# Input and output right gaps at a plus prefix

A dyadic-ended prefix of a sum can be written as a sum of two prefixes on its grid.
If retained minuses are cofinal in one input and a right option is within a real
fraction of the grid's monomial, this gives a strict bound on the output plus count.
-/

universe u
public noncomputable section
namespace Surreal

/-- A dyadic prefix has plus count below every final cost exponent if retained minuses
are cofinal and some input right gap is smaller than a real fraction of its scale. -/
private theorem plusCount_dyadic_prefix_lt {a C H s : Surreal.{u}} (q : Dyadic)
    (hH : H.support ⊆ Set.Ioi s)
    (hz : birthdayTruncation a (H + (q : Surreal) * ω^ s).birthday = H + (q : Surreal) * ω^ s)
    (hcof : ∀ j < a.birthday, ∃ v ∈ rightPrefixes a, j < v.birthday ∧ v ≤ C)
    {α : NatOrdinal.{u}} (hα : α ∈ NatOrdinal.cantorSupport (reducedOmegaCost C a))
    {c : ℝ} (hc : c < 1) {w : Surreal.{u}} (hw : w ∈ rightPrefixes a)
    (hsmall : w ≤ a + (c : Surreal) * ω^ s) : plusCount (H + (q : Surreal) * ω^ s) < α := by
  let z := H + (q : Surreal) * ω^ s
  change birthdayTruncation a z.birthday = z at hz
  have hb : z.birthday ≤ a.birthday := by
    simpa only [hz] using birthday_birthdayTruncation_le_birthday a z.birthday
  rcases hb.lt_or_eq with h | h
  · simpa only [hz] using plusCount_prefix_lt_cantorSupport_of_retained_cofinal hcof h hα
  · have ha : a = z := by simpa only [h, birthdayTruncation_birthday] using hz
    rw [← show a = H + (q : Surreal) * ω^ s from ha]
    apply (plusCount_le_cantorSupport_reducedOmegaCost C a α hα).lt_of_ne
    intro he
    have hL := leftPrefixes_cofinal_of_plusCount_mem_support (he ▸ hα) hcof
    have hR (j) (hj : j < a.birthday) : ∃ v ∈ rightPrefixes a, j < v.birthday := by
      obtain ⟨v, hv, hjv, _⟩ := hcof j hj
      exact ⟨v, hv, hjv⟩
    exact hsmall.not_gt (fraction_wpow_lt_right_gap_of_dyadic_head q hH ha hL hR hc hw)

/-- A dyadic prefix of a sum splits into two rounded input prefixes. At a nearby right
option the prefix in the cofinal input direction leaves a strict inequality. -/
theorem plusCount_dyadic_sum_prefix_lt_of_right_gap {a b C K s : Surreal.{u}} (q : Dyadic)
    (hK : K.support ⊆ Set.Ioi s)
    (hz : birthdayTruncation (a + b) (K + (q : Surreal) * ω^ s).birthday =
      K + (q : Surreal) * ω^ s)
    (hcof : ∀ j < a.birthday, ∃ v ∈ rightPrefixes a, j < v.birthday ∧ v ≤ C)
    {α : NatOrdinal.{u}} (hα : α ∈ NatOrdinal.cantorSupport (reducedOmegaCost C a))
    {c : ℝ} (hc : c < 1) {w : Surreal.{u}} (hw : w ∈ rightPrefixes a)
    (hsmall : w ≤ a + (c : Surreal) * ω^ s) :
    plusCount (K + (q : Surreal) * ω^ s) < α + plusCount b := by
  obtain ⟨x, y, hx, hy, he⟩ := exists_prefixes_add_eq hz
  obtain ⟨u, v, _, _, _, hxu, hyv, hsum⟩ := exists_rounded_prefixes_of_dyadic_sum x y K s q hK he
  have hA := birthdayTruncation_eq_trans hx hxu
  have hB := birthdayTruncation_eq_trans hy hyv
  have hH : (x.normalFormTrunc s).support ⊆ Set.Ioi s := by
    rw [support_trunc]
    exact Set.inter_subset_right
  have hlt := plusCount_dyadic_prefix_lt u hH hA hcof hα hc hw hsmall
  have hb := birthday_birthdayTruncation_le_birthday b
    (y.normalFormTrunc s + (v : Surreal) * ω^ s).birthday
  rw [hB] at hb
  have hle := plusCount_birthdayTruncation_le b hb
  rw [hB] at hle
  rw [← he, ← hsum]
  exact (plusCount_add_le _ _).trans_lt (add_lt_add_of_lt_of_le hlt hle)

end Surreal
