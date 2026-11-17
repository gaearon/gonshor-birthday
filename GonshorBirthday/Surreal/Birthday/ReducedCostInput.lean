/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostBaseline
public import GonshorBirthday.Surreal.Birthday.ReducedCostPaired
public import GonshorBirthday.Surreal.Birthday.CoefficientCancellation

import GonshorBirthday.Surreal.Birthday.CoefficientBlock
import GonshorBirthday.Surreal.Birthday.SupportGap
import GonshorBirthday.Surreal.HahnSeries.BirthdayAdd
import GonshorBirthday.Surreal.Birthday.HeadRun

/-!
# The input with cofinally retained minuses

Under sharp plus-count addition, a dyadic final output coefficient forces the
retained input coefficient to be dyadic by one-sided canonical approximation. Baseline cost
and cofinally retained minuses give both cofinal signs. Coefficient classification
then leaves only the negative unit, since a small margin deletes every right prefix
of a strictly higher head or a positive unit. Paired prefix gaps contradict retention.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- A baseline input with cofinal retention and a dyadic last coefficient is a negative unit. -/
theorem exists_head_sub_wpow_of_retained_baseline (a d s : Surreal.{u})
    (hsupp : a.support ⊆ Ici s)
    (hfin : (a.coeff s : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hbase : reducedOmegaCost (a + d) a = ω^ plusCount a)
    (hcof : ∀ j < a.birthday,
      ∃ w ∈ rightPrefixes a, j < w.birthday ∧ w ≤ a + d)
    (hret : ∃ w ∈ rightPrefixes a, w ≤ a + d) (hd : d ≤ ω^ s) :
    ∃ H : Surreal.{u}, H.support ⊆ Ioi s ∧ a = H - ω^ s := by
  have hK : (a.normalFormTrunc s).support ⊆ Ioi s := by
    simp only [support_trunc]
    exact Set.inter_subset_right
  have ha := eq_trunc_add_coeff_wpow_of_support_ge hsupp
  have hr : a.coeff s ≠ 0 := by
    intro hr
    have he : a = a.normalFormTrunc s := by
      simpa only [hr, Real.toSurreal_zero, zero_mul, add_zero] using ha
    have hdel := rightPrefixes_gt_shifted_cutoff_of_support_gt hK hd
    rw [← he] at hdel
    obtain ⟨w, hw, hwC⟩ := hret
    exact (hdel w hw).not_ge hwC
  have hL := leftPrefixes_cofinal_of_baseline_cost hbase hcof
  have hR : ∀ j < a.birthday, ∃ w ∈ rightPrefixes a, j < w.birthday := by
    intro j hj
    obtain ⟨w, hw, hjw, _⟩ := hcof j hj
    exact ⟨w, hw, hjw⟩
  obtain hrpos | hrneg := head_real_coefficient_eq_one_or_neg_one_of_both_cofinal
    (a.normalFormTrunc s) s hK hr hfin (by simpa only [← ha] using hL)
      (by simpa only [← ha] using hR)
  · have he : a = a.normalFormTrunc s + ω^ s := by
      simpa only [hrpos, Real.toSurreal_one, one_mul] using ha
    have hdel := rightPrefixes_gt_shifted_cutoff_head_add_wpow hK hd
    rw [← he] at hdel
    obtain ⟨w, hw, hwC⟩ := hret
    exact ((hdel w hw).not_ge hwC).elim
  · refine ⟨a.normalFormTrunc s, hK, ?_⟩
    simpa only [hrneg, Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul,
      sub_eq_add_neg] using ha

/-- Sharp addition and a dyadic output cannot support the final retained-baseline input. -/
theorem not_retained_baseline_of_last_minus_output
    (a b d K s : Surreal.{u}) {r t : ℝ} (q : Dyadic)
    (hK : K.support ⊆ Ioi s)
    (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    (he : a + b = K + ((q.toRat : ℝ) : Surreal) * ω^ s)
    (hsharp : plusCount (a + b) = plusCount a + plusCount b)
    (hbase : reducedOmegaCost (a + d) a = ω^ plusCount a)
    (hcof : ∀ j < a.birthday,
      ∃ w ∈ rightPrefixes a, j < w.birthday ∧ w ≤ a + d)
    (hret : ∃ w ∈ rightPrefixes a, w ≤ a + d)
    (hdel : ∀ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      K + (r : Surreal) * ω^ s + d < w) : False := by
  have hd := shifted_cutoff_lt_wpow_of_last_minus_head K s hK hsrc hdel
  have hsum : (a + b).support ⊆ Ici s := by
    rw [he]
    exact support_head_real_mul_wpow_subset K s hK _
  obtain ⟨ha, hb⟩ := support_subset_Ici_of_plusCount_add_eq a b s hsum hsharp
  have hKa : (a.normalFormTrunc s).support ⊆ Ioi s := by
    simp only [support_trunc]; exact inter_subset_right
  have hKb : (b.normalFormTrunc s).support ⊆ Ioi s := by
    simp only [support_trunc]; exact inter_subset_right
  have hae := eq_trunc_add_coeff_wpow_of_support_ge ha
  have hbe := eq_trunc_add_coeff_wpow_of_support_ge hb
  have hKs : K.coeff s = 0 := notMem_support_iff.mp (fun hs ↦ (lt_irrefl s) (hK hs))
  have hm : (((q.toRat : ℝ) : Surreal.{u}) * ω^ s).toHahnSeries =
      SurrealHahnSeries.single s (q.toRat : ℝ) :=
    toHahnSeries_eq (SurrealHahnSeries.toSurreal_single s (q.toRat : ℝ))
  have hmc : (((q.toRat : ℝ) : Surreal.{u}) * ω^ s).coeff s = (q.toRat : ℝ) := by
    rw [← coeff_toHahnSeries, hm, SurrealHahnSeries.coeff_single]
    simp
  have hcs : a.coeff s + b.coeff s = (q.toRat : ℝ) := by
    have hc := congrArg (fun x : Surreal.{u} ↦ x.coeff s) he
    simpa only [coeff_add, Pi.add_apply, hKs, hmc, zero_add] using hc
  have hfin := birthday_real_coefficient_lt_omega0_of_sharp_add
    (a.normalFormTrunc s) (b.normalFormTrunc s) s hKa hKb (a.coeff s) (b.coeff s) q hcs
      (by simpa only [← hae, ← hbe] using hsharp)
  obtain ⟨H, hH, hax⟩ :=
    exists_head_sub_wpow_of_retained_baseline a d s ha hfin hbase hcof hret hd.le
  have hdelete := rightPrefixes_gt_shifted_cutoff_of_last_minus_head K H s hK hH hsrc hdel
  rw [← hax] at hdelete
  obtain ⟨w, hw, hwC⟩ := hret
  exact (hdelete w hw).not_ge hwC

end Surreal
