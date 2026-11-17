/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.Birthday.HeadOmegaSuccessor
import GonshorBirthday.Surreal.Birthday.HeadMidpoint
import GonshorBirthday.Surreal.Birthday.HeadDeletion
import GonshorBirthday.Surreal.Birthday.OmegaBlock
import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient

/-!
# Cofinal headed omega prefixes

A head higher than the relevant exponents preserves their actual canonical omega
prefixes. Birthday bounds are continuous along any nonempty birthday-cofinal
family of such prefixes, including a cofinal ordinal-indexed tail after the first
retained boundary. Shared native right families cover both history deletion
mechanisms, so no unproved cofinality of retained signs is needed.
-/

universe u v
public noncomputable section
namespace Surreal
open Set

/-- A head higher than both exponents preserves an actual omega prefix. -/
theorem birthdayTruncation_head_wpow_of_prefix {H a b : Surreal.{u}}
    (hHa : H.support ⊆ Ioi a) (hHb : H.support ⊆ Ioi b)
    (hp : birthdayTruncation a b.birthday = b) :
    birthdayTruncation (H + ω^ a) (H + ω^ b).birthday = H + ω^ b := by
  have homega := birthdayTruncation_wpow_birthdayTruncation a b.birthday
  rw [hp] at homega
  have hmax : H.support ⊆ Ioi (max a b) := fun j hj ↦
    mem_Ioi.mpr (max_lt (mem_Ioi.mp (hHa hj)) (mem_Ioi.mp (hHb hj)))
  apply birthdayTruncation_head_add_of_abs_sub_le_real_mul_wpow hmax homega 1
  rw [Real.toSurreal_one, one_mul, abs_sub_le_iff]
  have ha := wpow_le_wpow.mpr (le_max_left a b)
  have hb := wpow_le_wpow.mpr (le_max_right a b)
  have ha0 := wpow_nonneg a
  have hb0 := wpow_nonneg b
  constructor <;> linarith

private theorem realCast_inv_two_pow (n : ℕ) :
    (((2 : ℝ)⁻¹ ^ n : ℝ) : Surreal.{u}) = (2 : Surreal)⁻¹ ^ n := by
  induction n with
  | zero => simp only [pow_zero, Real.toSurreal_one]
  | succ n ih =>
    rw [pow_succ, Real.toSurreal_mul, ih, Real.toSurreal_inv]
    norm_num only [Real.toSurreal_ofNat]
    rw [pow_succ]

/-- A shared exponent right prefix supplies shared actual headed right options below
any prescribed reciprocal-power coefficient. -/
theorem exists_common_head_rightPrefix_le_mul_wpow
    {H a b w : Surreal.{u}} (hHa : H.support ⊆ Ioi a) (hHb : H.support ⊆ Ioi b)
    (hwa : w ∈ rightPrefixes a) (hwb : w ∈ rightPrefixes b) (n : ℕ) :
    ∃ q, q ∈ rightPrefixes (H + ω^ a) ∧ q ∈ rightPrefixes (H + ω^ b) ∧
      q ≤ H + (2 : Surreal)⁻¹ ^ n * ω^ w := by
  by_cases hret : H.support ⊆ Ici w ∧
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0
  · have hK : (H.normalFormTrunc w).support ⊆ Ioi w := by
      simp only [support_trunc]
      exact inter_subset_right
    obtain ⟨Na, hNa⟩ := exists_head_shifted_reciprocal_wpow_rightPrefixes_of_pos
      (H.normalFormTrunc w) w hK hret.2 zero_lt_one hwa
    obtain ⟨Nb, hNb⟩ := exists_head_shifted_reciprocal_wpow_rightPrefixes_of_pos
      (H.normalFormTrunc w) w hK hret.2 zero_lt_one hwb
    let m := max n (max Na Nb)
    have hdecomp := eq_trunc_add_coeff_wpow_of_support_ge hret.1
    have hqa : H + (2 : Surreal)⁻¹ ^ m * ω^ w ∈ rightPrefixes (H + ω^ a) := by
      simpa only [Real.toSurreal_one, one_mul, ← add_assoc, ← hdecomp] using
        hNa m ((le_max_left Na Nb).trans (le_max_right n (max Na Nb)))
    have hqb : H + (2 : Surreal)⁻¹ ^ m * ω^ w ∈ rightPrefixes (H + ω^ b) := by
      simpa only [Real.toSurreal_one, one_mul, ← add_assoc, ← hdecomp] using
        hNb m ((le_max_right Na Nb).trans (le_max_right n (max Na Nb)))
    refine ⟨_, hqa, hqb, ?_⟩
    have hpow : (2 : Surreal.{u})⁻¹ ^ m ≤ (2 : Surreal)⁻¹ ^ n :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) (le_max_left _ _)
    exact add_le_add_right (mul_le_mul_of_nonneg_right hpow (wpow_nonneg w)) H
  · have hsmall : ∃ q ∈ rightPrefixes H,
        q + ω^ a < H + (((2 : ℝ)⁻¹ ^ n : ℝ) : Surreal) * ω^ w := by
      by_cases hge : H.support ⊆ Ici w
      · have hn : ¬ (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 :=
          fun hc ↦ hret ⟨hge, hc⟩
        have hc := le_antisymm (birthday_real_le_omega0 (H.coeff w)) (le_of_not_gt hn)
        exact exists_head_rightPrefix_add_wpow_lt_of_coeff_birthday_omega0 hge
          (mem_rightPrefixes_iff.mp hwa).2 hc (pow_pos (by norm_num) _)
      · obtain ⟨v, hv, hvw⟩ := Set.not_subset.mp hge
        exact exists_head_rightPrefix_add_wpow_lt_of_support_lt hHa hv
          (lt_of_not_ge hvw) hwa (pow_pos (by norm_num) _)
    obtain ⟨q, hq, hqp⟩ := hsmall
    rw [realCast_inv_two_pow] at hqp
    have hpre (x : Surreal.{u}) (hHx : H.support ⊆ Ioi x) :
        birthdayTruncation (H + ω^ x) H.birthday = H := by
      apply birthdayTruncation_add_of_support_lt
      simpa only [wlog_wpow] using hHx
    exact ⟨q, rightPrefixes_subset_of_birthdayTruncation_eq (hpre a hHa) hq,
      rightPrefixes_subset_of_birthdayTruncation_eq (hpre b hHb) hq,
      (le_add_of_nonneg_right (wpow_nonneg a)).trans hqp.le⟩

/-- Headed omega birthdays are continuous along any nonempty birthday-cofinal
family of canonical exponent prefixes above which the head stays higher. -/
theorem birthday_head_wpow_le_iff_of_cofinal_prefixes
    {I : Type v} [Nonempty I] {H s : Surreal.{u}} (t : I → Surreal.{u})
    (hH : H.support ⊆ Ioi s) (htH : ∀ i, H.support ⊆ Ioi (t i))
    (ht : ∀ i, birthdayTruncation s (t i).birthday = t i)
    (hcof : ∀ a < s.birthday, ∃ i, a < (t i).birthday) (M : NatOrdinal.{u}) :
    (H + ω^ s).birthday ≤ M ↔ ∀ i, (H + ω^ t i).birthday ≤ M := by
  have hhead (x : Surreal.{u}) (hHx : H.support ⊆ Ioi x) :
      H ∈ leftPrefixes (H + ω^ x) := by
    apply mem_leftPrefixes_iff.mpr
    refine ⟨?_, lt_add_of_pos_right H (wpow_pos x)⟩
    apply birthdayTruncation_add_of_support_lt
    simpa only [wlog_wpow] using hHx
  have hheadR (x : Surreal.{u}) (hHx : H.support ⊆ Ioi x) :
      rightPrefixes H ⊆ rightPrefixes (H + ω^ x) := by
    exact rightPrefixes_subset_of_birthdayTruncation_eq (mem_leftPrefixes_iff.mp (hhead x hHx)).1
  have hnat (x : Surreal.{u}) (hHx : H.support ⊆ Ioi x)
      {v : Surreal.{u}} (hv : v ∈ leftPrefixes x) (n : ℕ) :
      H + (n : Surreal) * ω^ v ∈ leftPrefixes (H + ω^ x) := by
    have hn := natCast_mul_wpow_mem_leftPrefixes hv n
    apply mem_leftPrefixes_iff.mpr
    refine ⟨?_, add_lt_add_right (mem_leftPrefixes_iff.mp hn).2 H⟩
    apply birthdayTruncation_head_add_of_abs_sub_le_real_mul_wpow hHx
      (mem_leftPrefixes_iff.mp hn).1 1
    rw [Real.toSurreal_one, one_mul,
      abs_of_nonneg (sub_nonneg.mpr (mem_leftPrefixes_iff.mp hn).2.le)]
    have hn0 := mul_nonneg (Nat.cast_nonneg n : (0 : Surreal.{u}) ≤ n) (wpow_nonneg v)
    linarith
  have hbi (i : I) : (t i).birthday ≤ s.birthday := by
    have hh := birthday_birthdayTruncation_le_birthday s (t i).birthday
    rwa [ht i] at hh
  constructor
  · intro hm i
    have hp := birthdayTruncation_head_wpow_of_prefix hH (htH i) (ht i)
    have hb := birthday_birthdayTruncation_le_birthday (H + ω^ s) (H + ω^ t i).birthday
    rw [hp] at hb
    exact hb.trans hm
  · intro hm
    apply (birthday_le_iff_forall_prefixes _ _).mpr
    constructor
    · intro p hp
      rcases exists_leftPrefixes_add_ge hp with ⟨q, hq, hpq⟩ | ⟨r, hr, hpr⟩
      · have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hH
          (birthday_lt_of_mem_leftPrefixes hq) 1
        rw [Real.toSurreal_one, one_mul,
          abs_of_neg (sub_neg.mpr (mem_leftPrefixes_iff.mp hq).2), neg_sub] at hg
        have hpH : p ≤ H := hpq.trans (by linarith)
        have hb := birthday_le_of_left_between hp hpH (mem_leftPrefixes_iff.mp (hhead s hH)).2.le
        let i : I := Classical.choice inferInstance
        exact hb.trans_lt ((birthday_lt_of_mem_leftPrefixes (hhead (t i) (htH i))).trans_le (hm i))
      · rcases exists_natCast_mul_wpow_ge_of_mem_leftPrefixes hr with rfl | ⟨v, hv, n, hrv⟩
        · have hpH : p ≤ H := by simpa only [add_zero] using hpr
          have hb := birthday_le_of_left_between hp hpH (mem_leftPrefixes_iff.mp (hhead s hH)).2.le
          let i : I := Classical.choice inferInstance
          exact hb.trans_lt
            ((birthday_lt_of_mem_leftPrefixes (hhead (t i) (htH i))).trans_le (hm i))
        · obtain ⟨i, hvi⟩ := hcof v.birthday (birthday_lt_of_mem_leftPrefixes hv)
          have hvti : v ∈ leftPrefixes (t i) := by
            apply mem_leftPrefixes_of_birthdayTruncation_eq_of_birthday_le (ht i) hv hvi.le
            have hh := (lt_birthdayTruncation_iff (hbi i) hvi).mpr (mem_leftPrefixes_iff.mp hv).2
            simpa only [ht i] using hh
          have hbound := birthday_le_of_left_between hp
            (hpr.trans (add_le_add_right hrv H)) (mem_leftPrefixes_iff.mp (hnat s hH hv n)).2.le
          exact hbound.trans_lt ((birthday_lt_of_mem_leftPrefixes
            (hnat (t i) (htH i) hvti n)).trans_le (hm i))
    · intro p hp
      rcases exists_rightPrefixes_add_le hp with ⟨q, hq, hqp⟩ | ⟨r, hr, hrp⟩
      · have hqp' : q ≤ p := (le_add_of_nonneg_right (wpow_nonneg s)).trans hqp
        have hb := birthday_le_of_left_between (neg_mem_leftPrefixes_iff.mpr hp)
          (neg_le_neg hqp') (neg_le_neg (mem_rightPrefixes_iff.mp (hheadR s hH hq)).2.le)
        rw [birthday_neg, birthday_neg] at hb
        let i : I := Classical.choice inferInstance
        exact hb.trans_lt
          ((birthday_lt_of_mem_rightPrefixes (hheadR (t i) (htH i) hq)).trans_le (hm i))
      · obtain ⟨v, hv, n, hvr⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hr
        obtain ⟨i, hvi⟩ := hcof v.birthday (birthday_lt_of_mem_rightPrefixes hv)
        have hvti : v ∈ rightPrefixes (t i) := by
          apply mem_rightPrefixes_of_birthdayTruncation_eq_of_birthday_le (ht i) hv hvi.le
          have hh := (birthdayTruncation_lt_iff (hbi i) hvi).mpr (mem_rightPrefixes_iff.mp hv).2
          simpa only [ht i] using hh
        obtain ⟨q, hqs, hqi, hqv⟩ := exists_common_head_rightPrefix_le_mul_wpow hH (htH i) hv hvti n
        have hqp : q ≤ p := hqv.trans ((add_le_add_right hvr H).trans hrp)
        have hb := birthday_le_of_left_between (neg_mem_leftPrefixes_iff.mpr hp)
          (neg_le_neg hqp) (neg_le_neg (mem_rightPrefixes_iff.mp hqs).2.le)
        rw [birthday_neg, birthday_neg] at hb
        exact hb.trans_lt ((birthday_lt_of_mem_rightPrefixes hqi).trans_le (hm i))

/-- At an exponent birthday limit, a cofinal tail of actual higher-head prefixes
has exactly the same upper birthday bounds as the limit stage. -/
theorem birthday_head_wpow_birthdayTruncation_limit
    {H x : Surreal.{u}} {a b₀ : NatOrdinal.{u}} (ha : a ≤ x.birthday) (hb₀ : b₀ < a)
    (hlim : Order.IsSuccLimit a.val)
    (hH : ∀ b : NatOrdinal.{u}, b₀ ≤ b → b ≤ a →
      H.support ⊆ Ioi (birthdayTruncation x b)) (M : NatOrdinal.{u}) :
    (H + ω^ birthdayTruncation x a).birthday ≤ M ↔
      ∀ b : NatOrdinal.{u}, b₀ ≤ b → b < a →
        (H + ω^ birthdayTruncation x b).birthday ≤ M := by
  let I := {b : NatOrdinal.{u} // b₀ ≤ b ∧ b < a}
  let t : I → Surreal.{u} := fun b ↦ birthdayTruncation x b.1
  have : Nonempty I := ⟨⟨b₀, le_rfl, hb₀⟩⟩
  have ht : ∀ b : I, birthdayTruncation (birthdayTruncation x a) (t b).birthday = t b := by
    intro b
    have hba : b.1 ≤ a := b.2.2.le
    have hb := birthday_birthdayTruncation x (hba.trans ha)
    dsimp only [t]
    rw [hb]
    exact birthdayTruncation_birthdayTruncation x hba ha
  have hcof : ∀ c < (birthdayTruncation x a).birthday, ∃ b : I, c < (t b).birthday := by
    intro c hc
    rw [birthday_birthdayTruncation x ha] at hc
    have hmax : max b₀.val c.val < a.val :=
      max_lt (NatOrdinal.val.strictMono hb₀) (NatOrdinal.val.strictMono hc)
    obtain ⟨d, hmd, hda⟩ := hlim.lt_iff_nonempty_Ioo.mp hmax
    have hb0d : b₀ ≤ NatOrdinal.of d := by
      apply NatOrdinal.val.le_iff_le.mp
      simpa only [NatOrdinal.val_of] using (le_max_left _ _).trans hmd.le
    have hcd : c < NatOrdinal.of d := by
      apply NatOrdinal.val.lt_iff_lt.mp
      simpa only [NatOrdinal.val_of] using (le_max_right _ _).trans_lt hmd
    have hdal : NatOrdinal.of d < a := by
      apply NatOrdinal.val.lt_iff_lt.mp
      simpa only [NatOrdinal.val_of] using hda
    refine ⟨⟨NatOrdinal.of d, hb0d, hdal⟩, ?_⟩
    dsimp only [t]
    rwa [birthday_birthdayTruncation x (hdal.le.trans ha)]
  have hh := birthday_head_wpow_le_iff_of_cofinal_prefixes t (hH a hb₀.le le_rfl)
    (fun b ↦ hH b.1 b.2.1 b.2.2.le) ht hcof M
  constructor
  · intro hm b hb0 hba
    exact hh.mp hm ⟨b, hb0, hba⟩
  · intro hm
    exact hh.mpr (fun b ↦ hm b.1 b.2.1 b.2.2)

end Surreal
