/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.Birthday.HeadOmegaSuccessor
public import GonshorBirthday.Surreal.Birthday.HeadRetainedBlock
import GonshorBirthday.Surreal.Birthday.HeadAllDeleted
import GonshorBirthday.Surreal.Birthday.CoefficientRun
import GonshorBirthday.Surreal.Birthday.HeadCoefficientWord
import GonshorBirthday.Surreal.Birthday.OmegaBlock
import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient
import GonshorBirthday.Surreal.Birthday.HeadMidpoint

/-!
# The exact initial retained boundary transition

A nonzero dyadic boundary coefficient gives the complete initial plus/minus word
after an arbitrary normal-form head. Canonical left cuts coincide with its plus
successor; finite dyadic right families and actual retained block capacity identify
the exact birthday. A zero boundary coefficient is included at the first retained
right exponent by the checked full-deletion word at that exponent.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem leftPrefixes_subset_of_cofinal_common {x y : Surreal.{u}}
    (h : ∀ p ∈ leftPrefixes x, ∃ q, q ∈ leftPrefixes x ∧ q ∈ leftPrefixes y ∧ p ≤ q) :
    leftPrefixes x ⊆ leftPrefixes y := by
  intro p hp
  obtain ⟨q, hqx, hqy, hpq⟩ := h p hp
  have ht := birthdayTruncation_eq_of_left_between
    (birthday_lt_of_mem_leftPrefixes hp).le
    (by simpa only [(mem_leftPrefixes_iff.mp hp).1] using hpq)
    (mem_leftPrefixes_iff.mp hqx).2.le
  rw [(mem_leftPrefixes_iff.mp hp).1] at ht
  exact mem_leftPrefixes_iff.mpr
    ⟨birthdayTruncation_eq_trans (mem_leftPrefixes_iff.mp hqy).1 ht,
      hpq.trans_lt (mem_leftPrefixes_iff.mp hqy).2⟩

/-- The first retained minus transition has the same actual left cut as the
boundary coefficient's plus successor, even for a zero predecessor. -/
theorem leftPrefixes_head_boundary_appendMinus
    {H w : Surreal.{u}} (hH : H.support ⊆ Ici w) {r : ℝ}
    (hr : (r : Surreal.{u}) = appendPlus (H.coeff w : Surreal.{u})) :
    leftPrefixes (H + ω^ appendMinus w) =
      leftPrefixes (H.normalFormTrunc w + (r : Surreal) * ω^ w) := by
  let P := H.normalFormTrunc w + (r : Surreal) * ω^ w
  have hK : (H.normalFormTrunc w).support ⊆ Ioi w := by
    simp only [support_trunc]
    exact inter_subset_right
  have hdecomp := eq_trunc_add_coeff_wpow_of_support_ge hH
  have hHx : H.support ⊆ Ioi (appendMinus w) := fun v hv ↦
    mem_Ioi.mpr ((appendMinus_lt w).trans_le (mem_Ici.mp (hH hv)))
  have hHP : H ∈ leftPrefixes P := by
    apply mem_leftPrefixes_iff.mpr
    refine ⟨?_, ?_⟩
    · have ht := birthdayTruncation_head_real_mul_wpow_of_prefix (H.normalFormTrunc w) w hK
        (show birthdayTruncation (r : Surreal) (H.coeff w : Surreal).birthday =
          (H.coeff w : Surreal) by rw [hr]; exact birthdayTruncation_appendPlus _)
      simpa only [← hdecomp] using ht
    · have hlt : (H.coeff w : Surreal.{u}) < (r : Surreal) := by rw [hr]; exact lt_appendPlus _
      dsimp only [P]
      linarith only [mul_lt_mul_of_pos_right hlt (wpow_pos w), hdecomp]
  have hHX : H ∈ leftPrefixes (H + ω^ appendMinus w) := by
    apply mem_leftPrefixes_iff.mpr
    refine ⟨?_, lt_add_of_pos_right _ (wpow_pos _)⟩
    apply birthdayTruncation_add_of_support_lt
    simpa only [wlog_wpow] using hHx
  have hfamily : ∀ v ∈ leftPrefixes w, ∀ n : ℕ,
      H + (n : Surreal) * ω^ v ∈ leftPrefixes (H + ω^ appendMinus w) ∧
      H + (n : Surreal) * ω^ v ∈ leftPrefixes P := by
    intro v hv n
    have hvx : v ∈ leftPrefixes (appendMinus w) := by rwa [leftPrefixes_appendMinus]
    have hn := natCast_mul_wpow_mem_leftPrefixes hvx n
    constructor
    · apply mem_leftPrefixes_iff.mpr
      refine ⟨?_, add_lt_add_right (mem_leftPrefixes_iff.mp hn).2 H⟩
      apply birthdayTruncation_head_add_of_abs_sub_le_real_mul_wpow hHx
        (mem_leftPrefixes_iff.mp hn).1 1
      rw [Real.toSurreal_one, one_mul,
        abs_of_nonneg (sub_nonneg.mpr (mem_leftPrefixes_iff.mp hn).2.le)]
      have hn0 : 0 ≤ (n : Surreal.{u}) * ω^ v :=
        mul_nonneg (Nat.cast_nonneg _) (wpow_nonneg v)
      linarith
    · have ht := head_real_mul_wpow_add_leftPrefix_mem_leftPrefixes
        (H.normalFormTrunc w) w hK hr (natCast_mul_wpow_mem_leftPrefixes hv n)
      simpa only [← add_assoc, ← hdecomp] using ht
  have hcofX : ∀ p ∈ leftPrefixes (H + ω^ appendMinus w),
      p ≤ H ∨ ∃ v ∈ leftPrefixes w, ∃ n : ℕ, p ≤ H + (n : Surreal) * ω^ v := by
    intro p hp
    rcases exists_leftPrefixes_add_ge hp with ⟨q, hq, hpq⟩ | ⟨a, ha, hpa⟩
    · have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hHx
        (birthday_lt_of_mem_leftPrefixes hq) 1
      rw [Real.toSurreal_one, one_mul,
        abs_of_neg (sub_neg.mpr (mem_leftPrefixes_iff.mp hq).2), neg_sub] at hg
      exact Or.inl (hpq.trans (by linarith))
    · rcases exists_natCast_mul_wpow_ge_of_mem_leftPrefixes ha with rfl | ⟨v, hv, n, hav⟩
      · exact Or.inl (by simpa only [add_zero] using hpa)
      · rw [leftPrefixes_appendMinus] at hv
        exact Or.inr ⟨v, hv, n, hpa.trans (add_le_add_right hav H)⟩
  have hcofP : ∀ p ∈ leftPrefixes P,
      p ≤ H ∨ ∃ v ∈ leftPrefixes w, ∃ n : ℕ, p ≤ H + (n : Surreal) * ω^ v := by
    intro p hp
    have ht := exists_head_real_mul_wpow_add_natCast_mul_wpow_ge (H.normalFormTrunc w) w hK hr hp
    simpa only [← add_assoc, ← hdecomp] using ht
  apply subset_antisymm
  · apply leftPrefixes_subset_of_cofinal_common
    intro p hp
    rcases hcofX p hp with h | ⟨v, hv, n, hn⟩
    · exact ⟨H, hHX, hHP, h⟩
    · exact ⟨_, (hfamily v hv n).1, (hfamily v hv n).2, hn⟩
  · apply leftPrefixes_subset_of_cofinal_common
    intro p hp
    rcases hcofP p hp with h | ⟨v, hv, n, hn⟩
    · exact ⟨H, hHP, hHX, h⟩
    · exact ⟨_, (hfamily v hv n).2, (hfamily v hv n).1, hn⟩

private theorem birthday_head_positive_finite_lt_limit
    {K w : Surreal.{u}} (hK : K.support ⊆ Ioi w) {a q : ℝ} (ha : 0 < a) (hq : 0 < q)
    (hqf : (q : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    (K + (q : Surreal) * ω^ w).birthday.val <
      (K + (a : Surreal) * ω^ w).birthday.val +
        (ω^ (plusCount w)).val * Ordinal.omega0 := by
  have hbq := birthday_head_real_mul_wpow K w hK hq
  have hba := birthday_head_real_mul_wpow K w hK ha
  have hbase : (K + ω^ w).birthday.val ≤ (K + (a : Surreal) * ω^ w).birthday.val := by
    rw [hba, NatOrdinal.val_of]
    exact le_self_add
  have htail : (q : Surreal.{u}).birthday.val - 1 < Ordinal.omega0 :=
    (Ordinal.sub_le_self _ _).trans_lt (NatOrdinal.val.lt_iff_lt.mpr hqf)
  have hQ : 0 < (ω^ (plusCount w)).val := by
    simpa only [NatOrdinal.val_zero] using NatOrdinal.val.strictMono (NatOrdinal.wpow_pos _)
  rw [hbq, NatOrdinal.val_of]
  apply lt_of_lt_of_le ((Ordinal.isNormal_add_right _).strictMono
    ((Ordinal.isNormal_mul_right hQ).strictMono htail))
  gcongr

private theorem birthday_head_negative_finite_lt_limit
    {K w : Surreal.{u}} (hK : K.support ⊆ Ioi w) {a q : ℝ} (ha : a < 0) (hq : q < 0)
    (hqf : (q : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    (K + (q : Surreal) * ω^ w).birthday.val <
      (K + (a : Surreal) * ω^ w).birthday.val +
        (ω^ (plusCount w)).val * Ordinal.omega0 := by
  have hKn : (-K).support ⊆ Ioi w := by simpa only [support_neg] using hK
  have hqn : ((-q : ℝ) : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
    simpa only [Real.toSurreal_neg, birthday_neg] using hqf
  have hh := birthday_head_positive_finite_lt_limit hKn (neg_pos.mpr ha) (neg_pos.mpr hq) hqn
  have hval (r : ℝ) : -K + ((-r : ℝ) : Surreal.{u}) * ω^ w =
      -(K + (r : Surreal) * ω^ w) := by rw [Real.toSurreal_neg]; ring
  simpa only [hval, birthday_neg] using hh

private theorem realCast_inv_two_pow (n : ℕ) :
    (((2 : ℝ)⁻¹ ^ n : ℝ) : Surreal.{u}) = (2 : Surreal)⁻¹ ^ n := by
  induction n with
  | zero => simp only [pow_zero, Real.toSurreal_one]
  | succ n ih =>
    rw [pow_succ, Real.toSurreal_mul, ih, Real.toSurreal_inv]
    norm_num only [Real.toSurreal_ofNat]
    rw [pow_succ]

private theorem birthday_real_inv_two_pow_lt_omega0 (n : ℕ) :
    ((((2 : ℝ)⁻¹ ^ n : ℝ) : Surreal.{u})).birthday < NatOrdinal.of Ordinal.omega0 := by
  rw [realCast_inv_two_pow]
  have hb := birthday_inv_two_pow_mul_wpow n (0 : Surreal.{u})
  simp only [wpow_zero, mul_one, birthday_one, plusCount_zero, NatOrdinal.wpow_zero,
    NatOrdinal.val_one, one_mul] at hb
  rw [hb]
  have he : 1 + (n : Ordinal.{u}) = ((n + 1 : ℕ) : Ordinal) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact_mod_cast Nat.add_comm 1 n
  rw [he, NatOrdinal.of_natCast]
  exact_mod_cast NatOrdinal.natCast_lt_omega0 (n + 1)

private theorem birthday_real_add_lt_omega0 {a q : ℝ}
    (ha : (a : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hq : (q : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ((a + q : ℝ) : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
  rw [Real.toSurreal_add]
  apply (birthday_add_le _ _).trans_lt
  obtain ⟨m, hm⟩ := NatOrdinal.lt_omega0.mp ha
  obtain ⟨n, hn⟩ := NatOrdinal.lt_omega0.mp hq
  rw [hm, hn, ← Nat.cast_add]
  exact_mod_cast NatOrdinal.natCast_lt_omega0 (m + n)

/-- A nonzero dyadic boundary coefficient gives the exact initial retained plus/minus
word, with no hypothesis on the signs or birthdays of earlier head terms. -/
theorem head_boundary_appendMinus_word {H w : Surreal.{u}}
    (hH : H.support ⊆ Ici w) (hc : H.coeff w ≠ 0)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    appendMinuses (appendPluses H (ω^ (plusCount w)).val)
      ((ω^ (plusCount w)).val * Ordinal.omega0) = H + ω^ appendMinus w := by
  have hK : (H.normalFormTrunc w).support ⊆ Ioi w := by
    simp only [support_trunc]
    exact inter_subset_right
  have hdecomp := eq_trunc_add_coeff_wpow_of_support_ge hH
  obtain ⟨q, _, hq, hblock⟩ := exists_dyadic_head_coefficient_plus_block
    (H.normalFormTrunc w) w hK hc hf
  have hr : ((q.toRat : ℝ) : Surreal.{u}) = appendPlus (H.coeff w : Surreal.{u}) := by
    simpa only [Real.toSurreal_ratCast] using hq
  rw [← hdecomp] at hblock
  have hL := leftPrefixes_head_boundary_appendMinus hH hr
  have hL' : leftPrefixes (H + ω^ appendMinus w) =
      leftPrefixes (appendPluses H (ω^ (plusCount w)).val) := by
    simpa only [Real.toSurreal_ratCast, ← hblock] using hL
  have hw : w ∈ rightPrefixes (appendMinus w) := by
    rw [rightPrefixes_appendMinus]
    exact Or.inl rfl
  obtain ⟨N, hN, hcof, _⟩ := exists_head_shifted_reciprocal_wpow_halving_family
    (H.normalFormTrunc w) w hK hf
  let P : ℕ → Surreal.{u} := fun n ↦ H + (2 : Surreal)⁻¹ ^ n * ω^ w
  have hP (n : ℕ) : P n = H.normalFormTrunc w +
      (((H.coeff w + (2 : ℝ)⁻¹ ^ n : ℝ) : Surreal.{u}) * ω^ w) := by
    rw [Real.toSurreal_add, realCast_inv_two_pow, add_mul, ← add_assoc, ← hdecomp]
  have hmember : ∀ n : ℕ, N ≤ n → P n ∈ rightPrefixes (H + ω^ appendMinus w) := by
    intro n hn
    simpa only [P, ← add_assoc, ← hdecomp] using hN n hn
  have hcofinal : ∀ p ∈ rightPrefixes (H + ω^ appendMinus w),
      ∃ n : ℕ, N ≤ n ∧ P n ≤ p := by
    simpa only [P, ← add_assoc, ← hdecomp] using hcof
  have hbound : ∃ M : ℕ, ∀ n : ℕ, M ≤ n →
      (P n).birthday.val < H.birthday.val + (ω^ (plusCount w)).val * Ordinal.omega0 := by
    rcases lt_or_gt_of_ne hc with ha | ha
    · obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (neg_pos.mpr ha)
        (show (2 : ℝ)⁻¹ < 1 by norm_num)
      refine ⟨M, ?_⟩
      intro n hn
      have hpow : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ M :=
        pow_le_pow_of_le_one (by positivity) (by norm_num) hn
      have hneg : H.coeff w + (2 : ℝ)⁻¹ ^ n < 0 := by linarith
      have hh := birthday_head_negative_finite_lt_limit hK ha hneg
        (birthday_real_add_lt_omega0 hf (birthday_real_inv_two_pow_lt_omega0 n))
      simpa only [← hdecomp, ← hP] using hh
    · refine ⟨0, ?_⟩
      intro n _
      have hpos : 0 < H.coeff w + (2 : ℝ)⁻¹ ^ n := by positivity
      have hh := birthday_head_positive_finite_lt_limit hK ha hpos
        (birthday_real_add_lt_omega0 hf (birthday_real_inv_two_pow_lt_omega0 n))
      simpa only [← hdecomp, ← hP] using hh
  obtain ⟨M, hM⟩ := hbound
  have hQ : 0 < (ω^ (plusCount w)).val := by
    simpa only [NatOrdinal.val_zero] using NatOrdinal.val.strictMono (NatOrdinal.wpow_pos _)
  have hupper : (H + ω^ appendMinus w).birthday ≤
      NatOrdinal.of (H.birthday.val + (ω^ (plusCount w)).val * Ordinal.omega0) := by
    apply (birthday_le_iff_forall_prefixes _ _).mpr
    constructor
    · intro p hp
      rw [hL'] at hp
      apply (birthday_lt_of_mem_leftPrefixes hp).trans_le
      rw [birthday_appendPluses]
      apply NatOrdinal.of.monotone
      apply (Ordinal.isNormal_add_right _).monotone
      simpa only [mul_one] using
        (Ordinal.isNormal_mul_right hQ).monotone
          (show (1 : Ordinal.{u}) ≤ Ordinal.omega0 by
            simpa only [Nat.cast_one] using (Ordinal.natCast_lt_omega0 1).le)
    · intro p hp
      obtain ⟨n, hn, hnp⟩ := hcofinal p hp
      let m := max n M
      have hmN : N ≤ m := hn.trans (le_max_left _ _)
      have hpow : (2 : Surreal.{u})⁻¹ ^ m ≤ (2 : Surreal)⁻¹ ^ n :=
        pow_le_pow_of_le_one (by positivity) (by norm_num) (le_max_left _ _)
      have hmp : P m ≤ p :=
        (add_le_add_right (mul_le_mul_of_nonneg_right hpow (wpow_nonneg w)) H).trans hnp
      have hbp := birthday_le_of_left_between (neg_mem_leftPrefixes_iff.mpr hp)
        (neg_le_neg hmp) (neg_le_neg (mem_rightPrefixes_iff.mp (hmember m hmN)).2.le)
      rw [birthday_neg, birthday_neg] at hbp
      exact hbp.trans_lt (NatOrdinal.val.lt_iff_lt.mp (hM m (le_max_right _ _)))
  have hlow := birthday_add_wpow_mul_omega0_le_of_retained_boundary hH hw hc hf
  have hb : (H + ω^ appendMinus w).birthday =
      NatOrdinal.of (H.birthday.val + (ω^ (plusCount w)).val * Ordinal.omega0) :=
    le_antisymm hupper (NatOrdinal.val.le_iff_le.mp
      (by simpa only [NatOrdinal.val_of] using hlow))
  apply neg_injective
  apply eq_of_birthday_eq_of_rightPrefixes_eq
  · rw [birthday_neg, birthday_neg, birthday_appendMinuses, birthday_appendPluses,
      NatOrdinal.val_of, hb]
    congr 1
    rw [add_assoc]
    congr 1
    calc
      (ω^ (plusCount w)).val + (ω^ (plusCount w)).val * Ordinal.omega0 =
          (ω^ (plusCount w)).val * (1 + Ordinal.omega0) := by rw [mul_add, mul_one]
      _ = _ := by rw [Ordinal.one_add_omega0]
  · rw [rightPrefixes_neg, rightPrefixes_neg, leftPrefixes_appendMinuses, hL']

/-- The exact first retained transition includes a zero boundary coefficient. -/
theorem head_first_retained_appendMinus_word {H w : Surreal.{u}}
    (hH : H.support ⊆ Ici w)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hfirst : ∀ v ∈ rightPrefixes w, ¬ (H.support ⊆ Ici v ∧
      (H.coeff v : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)) :
    appendMinuses (appendPluses H (ω^ (plusCount w)).val)
      ((ω^ (plusCount w)).val * Ordinal.omega0) = H + ω^ appendMinus w := by
  by_cases hc : H.coeff w = 0
  · have hstrict : H.support ⊆ Ioi w := by
      intro v hv
      apply mem_Ioi.mpr
      apply lt_of_le_of_ne (mem_Ici.mp (hH hv))
      intro he
      exact mem_support_iff.mp hv (he ▸ hc)
    rw [appendPluses_head_add_wpow_of_no_retained_rightPrefix hstrict hfirst]
    exact appendMinuses_head_wpow_appendMinus hstrict
  · exact head_boundary_appendMinus_word hH hc hf

end Surreal
