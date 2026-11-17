/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostLower
public import GonshorBirthday.Surreal.Birthday.Head

import GonshorBirthday.Surreal.Birthday.SupportGap

/-!
# Last terms forced by reduced-cost endpoints

Normal forms without a last term and normal forms with a nondyadic last coefficient
have canonical right-prefix gaps that can be halved. The lowered-cutoff gap window
therefore forces a last term with a nonzero dyadic coefficient.
-/

universe u

public noncomputable section

namespace Surreal

/-- A nondyadic last coefficient cannot satisfy the lowered-cutoff gap window. -/
theorem not_gap_window_of_nondyadic_last_coefficient
    (K u : Surreal.{u}) (r : ℝ) (hK : K.support ⊆ Set.Ioi u)
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0)
    {e d : Surreal.{u}}
    (hz : birthdayTruncation e (K + (r : Surreal) * ω^ u).birthday =
      K + (r : Surreal) * ω^ u)
    (hdel : ∀ w ∈ rightPrefixes (K + (r : Surreal) * ω^ u),
      K + (r : Surreal) * ω^ u + d < w)
    (hne : ∃ w ∈ rightPrefixes (K + (r : Surreal) * ω^ u), w ≤ e + d) : False := by
  apply not_coinitial_halving_rightPrefixes_of_gap_window hz hdel hne
    (rightPrefixes (K + (r : Surreal) * ω^ u)) (Set.Subset.refl _) ?_ ?_
  · intro w hw
    exact ⟨w, hw, le_rfl⟩
  · intro w hw
    obtain ⟨s, hs, hgap⟩ := exists_head_real_mul_wpow_rightPrefix_half_gap K u hK hr hw
    exact ⟨K + (s : Surreal) * ω^ u, hs, hgap⟩

/-- A pure output-cost equality under smaller-pair induction excludes a nondyadic last term. -/
theorem not_pure_endpoint_of_nondyadic_last_coefficient
    (a b d K u : Surreal.{u}) (r : ℝ) (hd : 0 ≤ d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    (hK : K.support ⊆ Set.Ioi u)
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0)
    (hz : K + (r : Surreal) * ω^ u ∈ leftPrefixes (a + b)) {p : NatOrdinal.{u}}
    (hp : plusCount (K + (r : Surreal) * ω^ u) < p)
    (hH : reducedOmegaCost (a + b + d) (K + (r : Surreal) * ω^ u) = ω^ p)
    (hM : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b = ω^ p)
    (hne : ∃ w ∈ rightPrefixes (K + (r : Surreal) * ω^ u), w ≤ a + b + d) : False := by
  exact not_gap_window_of_nondyadic_last_coefficient K u r hK hr
    (mem_leftPrefixes_iff.mp hz).1
    (rightPrefixes_gt_shifted_cutoff_of_pure_eq hd ih hz hp hH hM) hne

/-- Gaps smaller in scale than every supported monomial give arbitrarily halved right gaps. -/
theorem exists_rightPrefix_half_gap_of_support_gaps {z : Surreal.{u}}
    (hsmall : ∀ s ∈ z.support, ∃ v ∈ rightPrefixes z, (v - z).wlog < s)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes z) :
    ∃ v ∈ rightPrefixes z, 2 * (v - z) < w - z := by
  obtain ⟨s, hs, hsw⟩ := exists_support_le_wlog_sub_of_birthday_lt
    (birthday_lt_of_mem_rightPrefixes hw)
  obtain ⟨v, hv, hvs⟩ := hsmall s hs
  have hvpos : 0 < v - z := sub_pos.mpr (mem_rightPrefixes_iff.mp hv).2
  have hwpos : 0 < w - z := sub_pos.mpr (mem_rightPrefixes_iff.mp hw).2
  have hvl : v - z <ᵥ w - z := by
    rw [← wlog_lt_wlog_iff hvpos.ne' hwpos.ne']
    exact hvs.trans_le hsw
  have hh := (ArchimedeanClass.mk_lt_mk.mp (vlt_def.mp hvl)) 2
  refine ⟨v, hv, ?_⟩
  simpa only [nsmul_eq_mul, Nat.cast_ofNat, abs_of_pos hvpos, abs_of_pos hwpos] using hh

/-- Right gaps small at every support scale are incompatible with the lowered-cutoff window. -/
theorem not_gap_window_of_support_gaps {z e d : Surreal.{u}}
    (hsmall : ∀ s ∈ z.support, ∃ v ∈ rightPrefixes z, (v - z).wlog < s)
    (hz : birthdayTruncation e z.birthday = z)
    (hdel : ∀ w ∈ rightPrefixes z, z + d < w)
    (hne : ∃ w ∈ rightPrefixes z, w ≤ e + d) : False := by
  apply not_coinitial_halving_rightPrefixes_of_gap_window hz hdel hne
    (rightPrefixes z) (Set.Subset.refl _) ?_ ?_
  · intro w hw
    exact ⟨w, hw, le_rfl⟩
  · exact fun w hw ↦ exists_rightPrefix_half_gap_of_support_gaps hsmall hw

/-- A lowered-cutoff window forces one actual support scale to bound all right gaps below. -/
theorem exists_support_le_all_rightPrefix_gap_scales {z e d : Surreal.{u}}
    (hz : birthdayTruncation e z.birthday = z)
    (hdel : ∀ w ∈ rightPrefixes z, z + d < w)
    (hne : ∃ w ∈ rightPrefixes z, w ≤ e + d) :
    ∃ s ∈ z.support, ∀ w ∈ rightPrefixes z, s ≤ (w - z).wlog := by
  by_contra hn
  push Not at hn
  exact not_gap_window_of_support_gaps hn hz hdel hne

/-- A support without a least exponent admits a strict half-gap at every right prefix. -/
theorem exists_rightPrefix_half_gap_of_no_min_support {z : Surreal.{u}}
    (hs : ∀ s ∈ z.support, ∃ t ∈ z.support, t < s)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes z) :
    ∃ p ∈ rightPrefixes z, 2 * (p - z) < w - z :=
  exists_rightPrefix_half_gap_of_support_gaps
    (fun _ ht ↦ exists_rightPrefix_small_gap_of_no_min_support hs ht) hw

/-- A normal form with no last term cannot satisfy the lowered-cutoff gap window. -/
theorem not_gap_window_of_no_min_support {z e d : Surreal.{u}}
    (hs : ∀ s ∈ z.support, ∃ t ∈ z.support, t < s)
    (hz : birthdayTruncation e z.birthday = z)
    (hdel : ∀ w ∈ rightPrefixes z, z + d < w)
    (hne : ∃ w ∈ rightPrefixes z, w ≤ e + d) : False :=
  not_gap_window_of_support_gaps
    (fun _ ht ↦ exists_rightPrefix_small_gap_of_no_min_support hs ht) hz hdel hne

/-- The lowered-cutoff gap window forces a least supported exponent. -/
theorem exists_least_support_of_gap_window {z e d : Surreal.{u}}
    (hz : birthdayTruncation e z.birthday = z)
    (hdel : ∀ w ∈ rightPrefixes z, z + d < w)
    (hne : ∃ w ∈ rightPrefixes z, w ≤ e + d) :
    ∃ s ∈ z.support, ∀ t ∈ z.support, s ≤ t := by
  by_contra hn
  push Not at hn
  exact not_gap_window_of_no_min_support hn hz hdel hne

/-- The lowered-cutoff gap window forces a nonzero dyadic last coefficient. -/
theorem exists_dyadic_last_term_of_gap_window {z e d : Surreal.{u}}
    (hz : birthdayTruncation e z.birthday = z)
    (hdel : ∀ w ∈ rightPrefixes z, z + d < w)
    (hne : ∃ w ∈ rightPrefixes z, w ≤ e + d) :
    ∃ K s : Surreal.{u}, ∃ r : ℝ,
      K.support ⊆ Set.Ioi s ∧ r ≠ 0 ∧
      (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ∧
      z = K + (r : Surreal) * ω^ s := by
  obtain ⟨s, hs, hmin⟩ := exists_least_support_of_gap_window hz hdel hne
  have hK : (z.normalFormTrunc s).support ⊆ Set.Ioi s := by
    simp only [support_trunc]; exact Set.inter_subset_right
  have heq := eq_trunc_add_coeff_wpow_of_support_ge hmin
  refine ⟨z.normalFormTrunc s, s, z.coeff s, hK, mem_support_iff.mp hs, ?_, heq⟩
  apply (birthday_real_le_omega0 _).lt_of_ne
  intro hr
  apply not_gap_window_of_nondyadic_last_coefficient (z.normalFormTrunc s) s (z.coeff s) hK hr
  · simpa only [← heq] using hz
  · simpa only [← heq] using hdel
  · simpa only [← heq] using hne

/-- A pure output-cost endpoint under smaller-pair induction has a dyadic last term. -/
theorem exists_dyadic_last_term_of_pure_endpoint
    (a b d z : Surreal.{u}) (hd : 0 ≤ d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    (hz : z ∈ leftPrefixes (a + b)) {p : NatOrdinal.{u}}
    (hp : plusCount z < p)
    (hH : reducedOmegaCost (a + b + d) z = ω^ p)
    (hM : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b = ω^ p)
    (hne : ∃ w ∈ rightPrefixes z, w ≤ a + b + d) :
    ∃ K s : Surreal.{u}, ∃ r : ℝ,
      K.support ⊆ Set.Ioi s ∧ r ≠ 0 ∧
      (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ∧
      z = K + (r : Surreal) * ω^ s :=
  exists_dyadic_last_term_of_gap_window (mem_leftPrefixes_iff.mp hz).1
    (rightPrefixes_gt_shifted_cutoff_of_pure_eq hd ih hz hp hH hM) hne

end Surreal
