/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientRight
import GonshorBirthday.Surreal.Birthday.CoefficientBlock
import GonshorBirthday.Surreal.Birthday.CoefficientRun
import GonshorBirthday.Surreal.Birthday.LastMinusFamily
import GonshorBirthday.Surreal.Birthday.Perturbation
import GonshorBirthday.Surreal.Birthday.SupportGap
import GonshorBirthday.Surreal.Birthday.Head
import GonshorBirthday.Surreal.HahnSeries.NormalFormAdd
import Mathlib.Order.Minimal

/-!
# Right prefixes at a fixed scale

Let `r` be the coefficient of `z` on the scale of the gap. Varying this coefficient
slightly upwards gives a point in the cut for `z`. Thus `r` is a proper sign prefix of
another real and is dyadic. A nearby right option and cofinally late minuses imply that
the normal form of `z` ends at this coefficient.
-/

universe u

public noncomputable section

namespace Surreal
open Set

/-- A real coefficient strictly between those of `z` and `z+g`, after their common
higher terms, gives a point inside the canonical cut of `z`. -/
private theorem leftPrefix_of_coeff_between {z g : Surreal.{u}} (hg : 0 < g)
    (hgap : ∀ v ∈ rightPrefixes z, z + g ≤ v) {q : ℝ}
    (hlo : z.coeff g.wlog < q) (hhi : q < z.coeff g.wlog + g.leadingCoeff) :
    z ∈ leftPrefixes (z.normalFormTrunc g.wlog + (q : Surreal) * ω^ g.wlog) ∧
      (z.coeff g.wlog : Surreal.{u}) ∈ leftPrefixes (q : Surreal) := by
  let M : Surreal.{u} := ω^ g.wlog
  let K := z.normalFormTrunc g.wlog
  let x := (z - K) / M
  let y := g / M
  have hM : 0 < M := wpow_pos _
  have hx : 0 ≤ ArchimedeanClass.mk x := by
    simpa only [ArchimedeanClass.mk_one] using (vle_def.mp
      ((ValuativeRel.div_vle_one_iff hM.ne').mpr (sub_trunc_vle_wpow z _)))
  have hy : ArchimedeanClass.mk y = 0 := mk_div_wpow_wlog_of_ne_zero hg.ne'
  have hrq := Real.toSurreal_lt_iff.{u}.mpr hlo
  rw [coeff_eq_stdPart] at hlo hhi
  have low : x < (q : Surreal.{u}) := ArchimedeanClass.lt_of_stdPart_lt Real.toSurrealRingHom hx hlo
  have hhi' : q < ArchimedeanClass.stdPart (x + y) := by
    rw [ArchimedeanClass.stdPart_add hx hy.ge]
    exact hhi
  have high : (q : Surreal.{u}) < x + y := ArchimedeanClass.lt_of_lt_stdPart Real.toSurrealRingHom
    ((le_min hx hy.ge).trans (ArchimedeanClass.min_le_mk_add x y)) hhi'
  have ex : x * M = z - K := div_mul_cancel₀ _ hM.ne'
  have ey : y * M = g := div_mul_cancel₀ _ hM.ne'
  have l : z < K + (q : Surreal) * M := by linarith only [ex, mul_lt_mul_of_pos_right low hM]
  have h := mul_lt_mul_of_pos_right high hM
  rw [add_mul, ex, ey] at h
  have ht := birthdayTruncation_eq_of_btwn (H := leftPrefixes_lt_rightPrefixes z)
    (fun a ha ↦ (mem_leftPrefixes_iff.mp ha).2.trans l)
    (fun v hv ↦ lt_of_lt_of_le
      (show K + (q : Surreal) * M < z + g by linarith only [h]) (hgap v hv))
  rw [ofSets_leftPrefixes_rightPrefixes] at ht
  have hK : K.support ⊆ Ioi g.wlog := by rw [support_trunc]; exact inter_subset_right
  exact ⟨mem_leftPrefixes_iff.mpr ⟨ht, l⟩, mem_leftPrefixes_iff.mpr
    ⟨(birthdayTruncation_head_real_mul_wpow_iff K g.wlog hK q _).mp
      (birthdayTruncation_eq_trans ht (birthdayTruncation_trunc_add_coeff_wpow z _)), hrq⟩⟩

/-- A positive lower bound on all canonical right gaps makes the coefficient on its
Archimedean scale dyadic, even if lower terms follow it. -/
theorem dyadic_coeff_of_right_gaps {z g : Surreal.{u}} (hg : 0 < g)
    (hgap : ∀ v ∈ rightPrefixes z, z + g ≤ v) :
    ∃ q : Dyadic, (q.toRat : ℝ) = z.coeff g.wlog := by
  obtain ⟨q, hl, hr⟩ := exists_between
    (lt_add_of_pos_right (z.coeff g.wlog) (leadingCoeff_pos_iff.mpr hg))
  have h := (leftPrefix_of_coeff_between hg hgap hl hr).2
  exact (birthday_real_lt_omega0_iff _).mp ((birthday_lt_of_mem_leftPrefixes h).trans_le
    (birthday_real_le_omega0 q))

/-- If `r` is the greatest left coefficient prefix of `q`, every left option at `q`
already occurs at the coefficient obtained by appending a plus to `r`. -/
private theorem leftPrefixes_subset_at_coefficient_plus (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s)
    {r q c : ℝ} (hr : (r : Surreal.{u}) ∈ leftPrefixes (q : Surreal))
    (hmax : ∀ b : ℝ, (b : Surreal.{u}) ∈ leftPrefixes (q : Surreal) → b ≤ r)
    (hc : (c : Surreal.{u}) = appendPlus (r : Surreal)) :
    leftPrefixes (K + (q : Surreal) * ω^ s) ⊆ leftPrefixes (K + (c : Surreal) * ω^ s) := by
  intro z hz
  have hKn : (-K).support ⊆ Ioi s := by simpa only [support_neg] using hK
  have hn : ((-r : ℝ) : Surreal.{u}) ∈ rightPrefixes ((-q : ℝ) : Surreal) := by
    simpa only [Real.toSurreal_neg] using neg_mem_rightPrefixes_iff.mpr hr
  have hmin (b : ℝ) (hb : (b : Surreal.{u}) ∈ rightPrefixes ((-q : ℝ) : Surreal)) : -r ≤ b := by
    have h : ((-b : ℝ) : Surreal.{u}) ∈ leftPrefixes (q : Surreal) := by
      simpa only [Real.toSurreal_neg, neg_neg] using neg_mem_leftPrefixes_iff.mpr hb
    linarith only [hmax _ h]
  have hw : -z ∈ rightPrefixes (-K + ((-q : ℝ) : Surreal) * ω^ s) := by
    simpa only [Real.toSurreal_neg, neg_mul, ← neg_add] using neg_mem_rightPrefixes_iff.mpr hz
  obtain ⟨u, hu, h⟩ := exists_head_real_mul_wpow_sub_leftPrefix_le (-K) s hKn hn hmin hw
  rw [Real.toSurreal_neg, neg_mul] at h
  have hzu : z ≤ K + ((r : Surreal) * ω^ s + u) := by linarith only [h]
  have huq : K + ((r : Surreal) * ω^ s + u) < K + (q : Surreal) * ω^ s := by
    have h := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr
      (Real.toSurreal_lt_iff.mp (mem_leftPrefixes_iff.mp hr).2)) hu
    rw [Real.toSurreal_sub, sub_mul] at h
    linarith only [h]
  have ht := birthdayTruncation_eq_of_left_between (birthday_lt_of_mem_leftPrefixes hz).le
    (by simpa only [(mem_leftPrefixes_iff.mp hz).1] using hzu) huq.le
  rw [(mem_leftPrefixes_iff.mp hz).1] at ht
  have huc := head_real_mul_wpow_add_leftPrefix_mem_leftPrefixes K s hK hc hu
  exact mem_leftPrefixes_iff.mpr
    ⟨birthdayTruncation_eq_trans (mem_leftPrefixes_iff.mp huc).1 ht,
      hzu.trans_lt (mem_leftPrefixes_iff.mp huc).2⟩

/-- With all right gaps at least `g` and one at most a real multiple of `g`, cofinal minuses
end at a dyadic coefficient on the Archimedean scale of `g`. -/
theorem last_minus_at_scale_of_right_gaps {z w g : Surreal.{u}} (hg : 0 < g)
    (hw : w ∈ rightPrefixes z) (hgap : ∀ v ∈ rightPrefixes z, z + g ≤ v)
    {k : ℝ} (hk : 0 < k) (hwk : w ≤ z + (k : Surreal) * g)
    (hcof : ∀ a < z.birthday, ∃ v ∈ rightPrefixes z, a < v.birthday) :
    ∃ p t : ℝ, p ≠ 0 ∧ (p : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ∧
      (p : Surreal.{u}) = appendMinus (t : Surreal.{u}) ∧
      z = z.normalFormTrunc g.wlog + (p : Surreal) * ω^ g.wlog := by
  let s := g.wlog
  let K := z.normalFormTrunc s
  let r := z.coeff s
  let F (b : ℝ) := K + (b : Surreal) * ω^ s
  have hK : K.support ⊆ Ioi s := by rw [support_trunc]; exact inter_subset_right
  have hr : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 :=
    (birthday_real_lt_omega0_iff _).mpr (dyadic_coeff_of_right_gaps hg hgap)
  obtain ⟨c, hc⟩ := exists_real_appendPlus_of_birthday_lt_omega0 hr
  -- Choose the simplest coefficient in the interval. Its greatest left prefix is r.
  let I := Ioo r (r + g.leadingCoeff)
  obtain ⟨q, hq, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun b : ℝ ↦ b ∈ I) (fun b ↦ (b : Surreal.{u}).birthday)
    (Set.nonempty_Ioo.mpr (lt_add_of_pos_right _ (leadingCoeff_pos_iff.mpr hg)))
  obtain ⟨hz, hrq⟩ := leftPrefix_of_coeff_between hg hgap hq.1 hq.2
  change z ∈ leftPrefixes (F q) at hz
  have hmax (b : ℝ) (hb : (b : Surreal.{u}) ∈ leftPrefixes (q : Surreal)) : b ≤ r := by
    by_contra! h
    have hbq := Real.toSurreal_lt_iff.mp (mem_leftPrefixes_iff.mp hb).2
    exact (birthday_lt_of_mem_leftPrefixes hb).not_ge
      (hmin (show b ∈ I from ⟨h, hbq.trans hq.2⟩) (birthday_lt_of_mem_leftPrefixes hb).le)
  have hzc := leftPrefixes_subset_at_coefficient_plus K s hK hrq hmax hc hz
  have noPlus : birthdayTruncation (K + ω^ s) z.birthday ≠ z := by
    intro h
    have hy := rightPrefixes_subset_of_birthdayTruncation_eq h hw
    have hkM : (k : Surreal) * g ≤ᵥ ω^ s := by
      rw [vle_def, ArchimedeanClass.mk_mul, mk_realCast hk.ne', zero_add]
      exact (vle_def.mp (wpow_wlog_veq hg.ne').symm.1)
    have hv := ValuativeRel.vle_add (sub_trunc_vle_wpow z s) hkM
    obtain ⟨n, hn⟩ := ArchimedeanClass.mk_le_mk.mp (vle_def.mp hv)
    rw [abs_of_pos (wpow_pos s), nsmul_eq_mul] at hn
    have hu := real_mul_wpow_lt_rightPrefix_gap_head_add_wpow K s hK (n : ℝ) hy
    rw [Real.toSurreal_natCast] at hu
    linarith only [(le_abs_self _).trans hn, hwk, hu, wpow_pos s]
  have hr0 : r ≠ 0 := by
    intro he
    have hc1 : c = 1 := by
      apply Real.toSurreal_inj.{u}.mp
      rw [hc, he, Real.toSurreal_zero, Real.toSurreal_one]
      symm
      apply eq_appendPlus_of_birthdayTruncation_eq <;> simp
    apply noPlus
    simpa [F, hc1] using (mem_leftPrefixes_iff.mp hzc).1
  have hzr : z = F r := by
    have hb : z.birthday ≤ (F r).birthday := by
      by_contra! h
      obtain ⟨v, hv, hvb⟩ := hcof _ h
      have hv' := rightPrefixes_subset_of_birthdayTruncation_eq (mem_leftPrefixes_iff.mp hzc).1 hv
      change v ∈ rightPrefixes (K + (c : Surreal) * ω^ s) at hv'
      rw [← appendPluses_head_real_mul_wpow_of_appendPlus K s hK hr0 hc,
        rightPrefixes_appendPluses] at hv'
      exact hvb.not_gt (birthday_lt_of_mem_rightPrefixes hv')
    exact (birthdayTruncation_eq_self_of_birthday_le z hb).symm.trans
      (birthdayTruncation_trunc_add_coeff_wpow z s)
  obtain hr1 | ⟨t, ht⟩ := real_coefficient_eq_one_or_minus_successor_of_head_rightPrefixes_cofinal
    K s hK hr0 hr (by simpa only [hzr, F] using hcof)
  · have he : z = K + ω^ s := by simpa [F, hr1] using hzr
    exact (noPlus (he ▸ birthdayTruncation_birthday _)).elim
  · exact ⟨r, t, hr0, hr, ht, hzr⟩

/-- If one right gap is less than twice every right gap, cofinally many minus signs
end at a dyadic coefficient on the scale of that gap. -/
theorem exists_last_minus_of_right_gap {z w : Surreal.{u}} (hw : w ∈ rightPrefixes z)
    (hgap : ∀ v ∈ rightPrefixes z, w - z < 2 * (v - z))
    (hcof : ∀ a < z.birthday, ∃ v ∈ rightPrefixes z, a < v.birthday) :
    ∃ K s : Surreal.{u}, ∃ r t : ℝ,
      K.support ⊆ Ioi s ∧ r ≠ 0 ∧
      (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ∧
      (r : Surreal.{u}) = appendMinus (t : Surreal.{u}) ∧ z = K + (r : Surreal) * ω^ s := by
  let g := (w - z) / 2
  have hg : 0 < g := half_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hw).2)
  obtain ⟨p, t, hp, hf, ht, hz⟩ := last_minus_at_scale_of_right_gaps hg hw
    (fun v hv ↦ by dsimp only [g]; linarith only [hgap v hv]) (k := 2) (by norm_num)
    (by rw [show ((2 : ℝ) : Surreal.{u}) = 2 from Real.toSurreal_natCast 2]; dsimp [g]; linarith)
    hcof
  exact ⟨_, _, p, t, by rw [support_trunc]; exact inter_subset_right, hp, hf, ht, hz⟩

/-- A right prefix of `K - ω^s` differs from it by more than any real fraction
`c * ω^s` with `c < 1`. -/
theorem fraction_wpow_lt_right_gap_head_sub_wpow {K s w : Surreal.{u}}
    (hK : K.support ⊆ Ioi s) {c : ℝ} (hc : c < 1) (hw : w ∈ rightPrefixes (K - ω^ s)) :
    K - ω^ s + (c : Surreal) * ω^ s < w := by
  have hm : ((-1 : ℝ) : Surreal.{u}) = appendMinus (0 : Surreal.{u}) := by
    apply eq_appendMinus_of_birthdayTruncation_eq <;> simp
  have h := (right_gaps_at_coefficient_minus K s hK (r := -1) (t := 0) (by simpa using hm) (-1)).1 c
    (by simpa using hc)
  simpa only [Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul, ← sub_eq_add_neg] using
    h w (by simpa only [Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul, ← sub_eq_add_neg]
      using hw)

/-- If both signs occur cofinally, a positive lower bound on the right gaps at scale
`ω^s` puts every right gap above every real fraction of that monomial smaller than one. -/
theorem fraction_wpow_lt_right_gap_of_both_cofinal {a s : Surreal.{u}} {δ c : ℝ}
    (hδ : 0 < δ) (hc : c < 1)
    (hgap : ∀ v ∈ rightPrefixes a, a + (δ : Surreal) * ω^ s < v)
    (hL : ∀ j < a.birthday, ∃ v ∈ leftPrefixes a, j < v.birthday)
    (hR : ∀ j < a.birthday, ∃ v ∈ rightPrefixes a, j < v.birthday)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes a) : a + (c : Surreal) * ω^ s < w := by
  by_contra! h
  let g := (δ : Surreal.{u}) * ω^ s
  have hg : 0 < g := mul_pos (Real.toSurreal_pos_iff.mpr hδ) (wpow_pos s)
  have hgs : g.wlog = s := by
    rw [show g = _ from rfl, wlog_mul (Real.toSurreal_pos_iff.mpr hδ).ne' (wpow_ne_zero s),
      wlog_realCast, wlog_wpow, zero_add]
  have hcM : (c : Surreal.{u}) * ω^ s < ω^ s := by
    simpa only [Real.toSurreal_one, one_mul] using
      mul_lt_mul_of_pos_right (Real.toSurreal_lt_iff.mpr hc) (wpow_pos s)
  have hupper : w ≤ a + ((δ⁻¹ : ℝ) : Surreal.{u}) * g := by
    rw [Real.toSurreal_inv, show (δ : Surreal)⁻¹ * g = ω^ s from
      inv_mul_cancel_left₀ (Real.toSurreal_pos_iff.mpr hδ).ne' _]
    exact h.trans (add_le_add le_rfl hcM.le)
  obtain ⟨r, t, _, _, hminus, ha⟩ :=
    last_minus_at_scale_of_right_gaps hg hw (fun v hv ↦ (hgap v hv).le) (inv_pos.mpr hδ) hupper hR
  rw [hgs] at ha
  let K := a.normalFormTrunc s
  have hK : K.support ⊆ Ioi s := by rw [support_trunc]; exact inter_subset_right
  change a = K + (r : Surreal) * ω^ s at ha
  have ht : t = 0 := by
    by_contra hn
    exact not_both_prefixes_cofinal_of_head_real_coefficient_successor K s hK hn
      (Or.inr hminus) (ha ▸ hL) (ha ▸ hR)
  subst t
  have hr : r = -1 := by
    apply Real.toSurreal_inj.mp
    rw [hminus, Real.toSurreal_zero, Real.toSurreal_neg, Real.toSurreal_one]
    symm
    apply eq_appendMinus_of_birthdayTruncation_eq <;> simp
  rw [hr, Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul, ← sub_eq_add_neg] at ha
  exact h.not_gt (ha ▸ fraction_wpow_lt_right_gap_head_sub_wpow hK hc (ha ▸ hw))

end Surreal
