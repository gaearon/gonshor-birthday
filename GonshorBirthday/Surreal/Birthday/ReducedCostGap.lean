/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostBaseline
public import GonshorBirthday.Surreal.Birthday.GapWindow

import GonshorBirthday.Surreal.Birthday.CoefficientCancellation
import GonshorBirthday.Surreal.Birthday.PrefixSums

/-!
# Input and output right gaps at a plus prefix

A dyadic-ended prefix of a sum can be written as a sum of two prefixes on its grid.
If retained minuses are cofinal in one input and a right option is within a real
fraction of the grid's monomial, this gives a strict bound on the output plus count.
The remaining results compare cofinal families of right gaps at a fixed scale.
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

private theorem not_cofinal_below_fraction {a A s : Surreal.{u}} {δ c : ℝ}
    (hδ : 0 < δ) (hc : c < 1)
    (hbase : plusCount a ∈ NatOrdinal.cantorSupport (reducedOmegaCost A a))
    (hgap : ∀ u ∈ rightPrefixes a, u ≤ A → a + (δ : Surreal) * ω^ s < u)
    (hcost : ∀ S < reducedOmegaCost A a, ∃ u ∈ rightPrefixes a,
      u ≤ A ∧ u ≤ a + (c : Surreal) * ω^ s ∧ S < reducedOmegaCost A u) : False := by
  obtain ⟨u, hu, huA, huSmall, _⟩ :=
    hcost 0 (zero_lt_one.trans_le (one_le_reducedOmegaCost A a))
  have hcof := retained_rightPrefixes_cofinal_of_costs_cofinal A a (fun S hS ↦ by
    obtain ⟨v, hv, hvA, _, hSv⟩ := hcost S hS
    exact ⟨v, hv, hvA, hSv⟩)
  apply huSmall.not_gt (fraction_wpow_lt_right_gap_of_both_cofinal hδ hc _
    (leftPrefixes_cofinal_of_plusCount_mem_support hbase hcof) _ hu)
  · intro v hv
    rcases le_total v A with hvA | hAv
    · exact hgap v hv hvA
    · exact (hgap u hu huA).trans_le (huA.trans hAv)
  · intro j hj
    obtain ⟨v, hv, hjv, _⟩ := hcof j hj
    exact ⟨v, hv, hjv⟩

/-- A cofinal input direction cannot supply the right gaps at a fractional monomial
boundary if its last Cantor exponent is its plus count. -/
theorem not_cofinal_at_fractional_right_gap {a b A B z s V : Surreal.{u}}
    (hb : b ≤ B)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
        reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
    (hz : birthdayTruncation (a + b) z.birthday = z)
    (hcof : ∀ j < z.birthday, ∃ v ∈ rightPrefixes z,
      j < v.birthday ∧ v ≤ min (A + b) (a + B))
    (hH : reducedOmegaCost A a * reducedOmegaCost B b ≤
      reducedOmegaCost (min (A + b) (a + B)) z)
    (hA : plusCount a ∈ NatOrdinal.cantorSupport (reducedOmegaCost A a))
    {δ c : ℝ} (hδ : 0 < δ) (hc : c < 1)
    (hgap : ∀ w ∈ rightPrefixes z, a + b + (δ : Surreal) * ω^ s < w)
    (hVc : V ≤ a + b + (c : Surreal) * ω^ s)
    (hcost : ∀ S < reducedOmegaCost A a * reducedOmegaCost B b, ∃ u ∈ rightPrefixes a,
      u ≤ A ∧ u + b ≤ V ∧ S < reducedOmegaCost A u * reducedOmegaCost B b) : False := by
  apply not_cofinal_below_fraction hδ hc hA
  · intro u hu huA
    obtain ⟨w, hw, _, hwu⟩ := exists_retained_rightPrefix_lt_add_of_eq hb ih hz hcof hH hu huA
    linarith only [hgap w hw, hwu]
  · intro S hS
    have hY := zero_lt_one.trans_le (one_le_reducedOmegaCost B b)
    obtain ⟨u, hu, huA, huV, hSu⟩ := hcost _ (mul_lt_mul_of_pos_right hS hY)
    exact ⟨u, hu, huA, by linarith only [huV, hVc],
      lt_of_not_ge (fun h ↦ hSu.not_ge (mul_le_mul' h le_rfl))⟩

/-- Suppose the last Cantor exponent in each input cost equals its plus count, and minuses occur
cofinally in the prefix `z`. If every right gap of `z` measured from the sum exceeds
`δ * ω^s`, and one is at most `c * ω^s` with `c < 1`, the prefix costs strictly less
than the product at the original cutoffs. -/
theorem reducedOmegaCost_lt_of_fractional_right_gap {a b A B z s V : Surreal.{u}}
    (ha : a ≤ A) (hb : b ≤ B)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
        reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
    (hz : birthdayTruncation (a + b) z.birthday = z)
    (hcof : ∀ j < z.birthday, ∃ v ∈ rightPrefixes z,
      j < v.birthday ∧ v ≤ min (A + b) (a + B))
    (hA : plusCount a ∈ NatOrdinal.cantorSupport (reducedOmegaCost A a))
    (hB : plusCount b ∈ NatOrdinal.cantorSupport (reducedOmegaCost B b))
    {δ c : ℝ} (hδ : 0 < δ) (hc : c < 1)
    (hgap : ∀ w ∈ rightPrefixes z, a + b + (δ : Surreal) * ω^ s < w)
    (hV : V ∈ rightPrefixes z) (hVc : V ≤ a + b + (c : Surreal) * ω^ s) :
    reducedOmegaCost (min (A + b) (a + B)) z < reducedOmegaCost A a * reducedOmegaCost B b := by
  by_contra! hH
  rcases rightPrefix_products_cofinal_at_all_gaps ih hz hcof hH with h | h
  · exact not_cofinal_at_fractional_right_gap hb ih hz hcof hH hA hδ hc hgap hVc (h V hV)
  · exact not_cofinal_at_fractional_right_gap (a := b) (b := a) ha
      (by simpa only [add_comm] using ih) (by simpa only [add_comm] using hz)
      (by simpa only [add_comm, min_comm] using hcof)
      (by simpa only [add_comm, min_comm, mul_comm] using hH) hB hδ hc
      (by simpa only [add_comm] using hgap) (by simpa only [add_comm] using hVc)
      (by simpa only [add_comm, mul_comm] using h V hV)

end Surreal
