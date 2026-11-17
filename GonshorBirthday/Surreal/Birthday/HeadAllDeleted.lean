/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.Birthday.HeadDeletion
public import GonshorBirthday.Surreal.Birthday.HeadRun
import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient

/-!
# Exact lower monomial word when all exponent minuses are deleted

If every original exponent right prefix is removed by the native head condition,
the new lower monomial preserves the old canonical right cut and appends exactly
one pure plus block of length omega^(plusCount s). Both history deletion mechanisms
are admitted, with arbitrary infinite heads and arbitrary coefficient signs.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- If every omega right option is dominated by a translated old right option, the
new lower monomial preserves the whole canonical head right-prefix set. -/
theorem rightPrefixes_head_add_wpow_of_right_domination
    {H s : Surreal.{u}} (hH : H.support ⊆ Ioi s)
    (hdom : ∀ w ∈ rightPrefixes s, ∀ ε : ℝ, 0 < ε →
      ∃ q ∈ rightPrefixes H, q + ω^ s < H + (ε : Surreal) * ω^ w) :
    rightPrefixes (H + ω^ s) = rightPrefixes H := by
  have hpre : birthdayTruncation (H + ω^ s) H.birthday = H := by
    apply birthdayTruncation_add_of_support_lt
    simpa only [wlog_wpow] using hH
  apply subset_antisymm
  · intro p hp
    have hq : ∃ q ∈ rightPrefixes H, q ≤ p := by
      rcases exists_rightPrefixes_add_le hp with ⟨q, hq, hqp⟩ | ⟨a, ha, hap⟩
      · exact ⟨q, hq, (le_add_of_nonneg_right (wpow_nonneg s)).trans hqp⟩
      · obtain ⟨w, hw, n, hwa⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes ha
        let ε : ℝ := (2 : ℝ)⁻¹ ^ n
        have hε : 0 < ε := pow_pos (by norm_num) _
        obtain ⟨q, hq, hsmall⟩ := hdom w hw ε hε
        have hcast : (ε : Surreal.{u}) = (2 : Surreal)⁻¹ ^ n := by
          dsimp only [ε]
          clear hwa hε hsmall ε
          induction n with
          | zero => simp only [pow_zero, Real.toSurreal_one]
          | succ n ih =>
            rw [pow_succ, Real.toSurreal_mul, ih, Real.toSurreal_inv]
            norm_num only [Real.toSurreal_ofNat]
            rw [pow_succ]
        rw [hcast] at hsmall
        refine ⟨q, hq, ?_⟩
        exact (le_add_of_nonneg_right (wpow_nonneg s)).trans
          (hsmall.le.trans ((add_le_add_right hwa H).trans hap))
    obtain ⟨q, hq, hqp⟩ := hq
    have hq' := rightPrefixes_subset_of_birthdayTruncation_eq hpre hq
    have hb := birthday_le_of_left_between (neg_mem_leftPrefixes_iff.mpr hp)
      (neg_le_neg hqp) (neg_le_neg (mem_rightPrefixes_iff.mp hq').2.le)
    rw [birthday_neg, birthday_neg] at hb
    exact mem_rightPrefixes_of_birthdayTruncation_eq_of_birthday_le hpre hp
      (hb.trans (birthday_lt_of_mem_rightPrefixes hq).le)
      ((lt_add_of_pos_right H (wpow_pos s)).trans (mem_rightPrefixes_iff.mp hp).2)
  · exact rightPrefixes_subset_of_birthdayTruncation_eq hpre

/-- If every original exponent minus is removed by one of the two native head
conditions, no new canonical right prefix is created by the lower monomial. -/
theorem rightPrefixes_head_add_wpow_of_no_retained_rightPrefix
    {H s : Surreal.{u}} (hH : H.support ⊆ Ioi s)
    (hdel : ∀ w ∈ rightPrefixes s, ¬ (H.support ⊆ Ici w ∧
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)) :
    rightPrefixes (H + ω^ s) = rightPrefixes H := by
  apply rightPrefixes_head_add_wpow_of_right_domination hH
  intro w hw ε hε
  by_cases hge : H.support ⊆ Ici w
  · have hnot : ¬ (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 :=
      fun hc ↦ hdel w hw ⟨hge, hc⟩
    have hc := le_antisymm (birthday_real_le_omega0 (H.coeff w)) (le_of_not_gt hnot)
    exact exists_head_rightPrefix_add_wpow_lt_of_coeff_birthday_omega0 hge
      (mem_rightPrefixes_iff.mp hw).2 hc hε
  · obtain ⟨v, hv, hvw⟩ := Set.not_subset.mp hge
    exact exists_head_rightPrefix_add_wpow_lt_of_support_lt hH hv (lt_of_not_ge hvw) hw hε

/-- If all raw omega right options are dominated by old head options, the actual
new term is a pure plus block of its original omega plus rank. -/
theorem appendPluses_head_add_wpow_of_right_domination
    {H s : Surreal.{u}} (hH : H.support ⊆ Ioi s)
    (hdom : ∀ w ∈ rightPrefixes s, ∀ ε : ℝ, 0 < ε →
      ∃ q ∈ rightPrefixes H, q + ω^ s < H + (ε : Surreal) * ω^ w) :
    appendPluses H (ω^ (plusCount s)).val = H + ω^ s := by
  have hcof : ∀ b ∈ rightPrefixes (ω^ s), ∃ p ∈ rightPrefixes H, p ≤ H + b := by
    intro b hb
    obtain ⟨w, hw, n, hwb⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hb
    have hcast : ∀ n : ℕ, (((2 : ℝ)⁻¹ ^ n : ℝ) : Surreal.{u}) =
        (2 : Surreal)⁻¹ ^ n := by
      intro n
      induction n with
      | zero => simp only [pow_zero, Real.toSurreal_one]
      | succ n ih =>
        rw [pow_succ, Real.toSurreal_mul, ih, Real.toSurreal_inv]
        norm_num only [Real.toSurreal_ofNat]
        rw [pow_succ]
    obtain ⟨q, hq, hsmall⟩ := hdom w hw ((2 : ℝ)⁻¹ ^ n) (pow_pos (by norm_num) _)
    rw [hcast] at hsmall
    exact ⟨q, hq, (le_add_of_nonneg_right (wpow_nonneg s)).trans
      (hsmall.le.trans (add_le_add_right hwb H))⟩
  have hR : ∀ z ∈ leftPrefixes (appendPlus (ω^ s)),
      rightPrefixes (H + z) = rightPrefixes H := by
    intro z hz
    rw [leftPrefixes_appendPlus] at hz
    rcases hz with rfl | hz
    · exact rightPrefixes_head_add_wpow_of_right_domination hH hdom
    · exact rightPrefixes_add_leftPrefix_of_cofinal_rightPrefixes (wpow_pos s) hz
        (birthdayTruncation_head_add_leftPrefix_wpow
          (show H.support ⊆ Ici s from fun v hv ↦ mem_Ici.mpr (mem_Ioi.mp (hH hv)).le)
          hz) hcof
  have hP : ∀ z ∈ leftPrefixes (appendPlus (ω^ s)),
      birthdayTruncation (H + ω^ s) (H + z).birthday = H + z := by
    intro z hz
    rw [leftPrefixes_appendPlus] at hz
    rcases hz with rfl | hz
    · exact birthdayTruncation_birthday _
    · apply birthdayTruncation_head_add_of_abs_sub_le_real_mul_wpow hH
        (mem_leftPrefixes_iff.mp hz).1 1
      have hz0 := nonneg_of_mem_leftPrefixes (wpow_pos s) hz
      rw [Real.toSurreal_one, one_mul,
        abs_of_nonneg (sub_nonneg.mpr (mem_leftPrefixes_iff.mp hz).2.le)]
      linarith
  have hB : ∀ z ∈ leftPrefixes (appendPlus (ω^ s)), H + z ≤ H + ω^ s := by
    intro z hz
    rw [leftPrefixes_appendPlus] at hz
    rcases hz with rfl | hz
    · exact le_rfl
    · exact add_le_add_right (mem_leftPrefixes_iff.mp hz).2.le H
  have hG : ∀ z ∈ leftPrefixes (appendPlus (ω^ s)), ∀ p ∈ leftPrefixes H, p + z ≤ H := by
    intro z hz p hp
    have hzle : z ≤ ω^ s := by
      rw [leftPrefixes_appendPlus] at hz
      exact hz.elim (fun h ↦ h.le) (fun h ↦ (mem_leftPrefixes_iff.mp h).2.le)
    have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hH
      (birthday_lt_of_mem_leftPrefixes hp) 1
    rw [Real.toSurreal_one, one_mul,
      abs_of_neg (sub_neg.mpr (mem_leftPrefixes_iff.mp hp).2), neg_sub] at hg
    linarith
  have hmem : ω^ s ∈ leftPrefixes (appendPlus (ω^ s)) := by
    rw [leftPrefixes_appendPlus]
    exact Or.inl rfl
  have hb := birthday_add_left_prefix_eq_of_stage_rightPrefixes
    ((wpow_pos s).trans (lt_appendPlus _)) hR hP hB hG hmem
  rw [plusCount_wpow] at hb
  exact (appendPluses_eq_iff _ _ _).mpr ⟨hb, hR _ hmem⟩

/-- Deleting every original exponent minus appends exactly the omega plus-rank block
at the actual normal-form head. -/
theorem appendPluses_head_add_wpow_of_no_retained_rightPrefix
    {H s : Surreal.{u}} (hH : H.support ⊆ Ioi s)
    (hdel : ∀ w ∈ rightPrefixes s, ¬ (H.support ⊆ Ici w ∧
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)) :
    appendPluses H (ω^ (plusCount s)).val = H + ω^ s := by
  apply appendPluses_head_add_wpow_of_right_domination hH
  intro w hw ε hε
  by_cases hge : H.support ⊆ Ici w
  · have hnot : ¬ (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 :=
      fun hc ↦ hdel w hw ⟨hge, hc⟩
    have hc := le_antisymm (birthday_real_le_omega0 (H.coeff w)) (le_of_not_gt hnot)
    exact exists_head_rightPrefix_add_wpow_lt_of_coeff_birthday_omega0 hge
      (mem_rightPrefixes_iff.mp hw).2 hc hε
  · obtain ⟨v, hv, hvw⟩ := Set.not_subset.mp hge
    exact exists_head_rightPrefix_add_wpow_lt_of_support_lt hH hv (lt_of_not_ge hvw) hw hε

end Surreal
