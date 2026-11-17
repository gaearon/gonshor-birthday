/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.Birthday.HeadRun
import GonshorBirthday.Surreal.Birthday.HeadDeletion
import GonshorBirthday.Surreal.Birthday.HeadMidpoint
import GonshorBirthday.Surreal.Birthday.HeadCoefficientWord
import GonshorBirthday.Surreal.Birthday.OmegaBlock
import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient

/-!
# Exact omega successor blocks after a higher head

Above both relevant exponents, an arbitrary normal-form head preserves the complete
original exponent successor block. Plus and minus successors append their full
omega^(plusCount v)*_o omega constant blocks. Native shared canonical option families
identify the headed cuts; actual integer and reciprocal coefficient stages give
both birthday bounds. These laws require no history-dependent length formula.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem realCast_inv_two_pow (n : ℕ) :
    (((2 : ℝ)⁻¹ ^ n : ℝ) : Surreal.{u}) = (2 : Surreal)⁻¹ ^ n := by
  induction n with
  | zero => simp only [pow_zero, Real.toSurreal_one]
  | succ n ih =>
    rw [pow_succ, Real.toSurreal_mul, ih, Real.toSurreal_inv]
    norm_num only [Real.toSurreal_ofNat]
    rw [pow_succ]

private theorem exists_common_head_rightPrefix_le
    {H a b : Surreal.{u}} (hHa : H.support ⊆ Ioi a) (hHb : H.support ⊆ Ioi b)
    (he : rightPrefixes a = rightPrefixes b) {p : Surreal.{u}}
    (hp : p ∈ rightPrefixes (H + ω^ a)) :
    ∃ q, q ∈ rightPrefixes (H + ω^ a) ∧ q ∈ rightPrefixes (H + ω^ b) ∧ q ≤ p := by
  have hprea : birthdayTruncation (H + ω^ a) H.birthday = H := by
    apply birthdayTruncation_add_of_support_lt
    simpa only [wlog_wpow] using hHa
  have hpreb : birthdayTruncation (H + ω^ b) H.birthday = H := by
    apply birthdayTruncation_add_of_support_lt
    simpa only [wlog_wpow] using hHb
  have hold : ∀ q ∈ rightPrefixes H, q ≤ p →
      ∃ q, q ∈ rightPrefixes (H + ω^ a) ∧ q ∈ rightPrefixes (H + ω^ b) ∧ q ≤ p := by
    intro q hq hqp
    exact ⟨q, rightPrefixes_subset_of_birthdayTruncation_eq hprea hq,
      rightPrefixes_subset_of_birthdayTruncation_eq hpreb hq, hqp⟩
  rcases exists_rightPrefixes_add_le hp with ⟨q, hq, hqp⟩ | ⟨r, hr, hrp⟩
  · exact hold q hq ((le_add_of_nonneg_right (wpow_nonneg a)).trans hqp)
  · obtain ⟨w, hw, n, hwr⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hr
    have hwb : w ∈ rightPrefixes b := he ▸ hw
    by_cases hret : H.support ⊆ Ici w ∧
        (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0
    · have hK : (H.normalFormTrunc w).support ⊆ Ioi w := by
        simp only [support_trunc]
        exact inter_subset_right
      obtain ⟨Na, hNa⟩ := exists_head_shifted_reciprocal_wpow_rightPrefixes_of_pos
        (H.normalFormTrunc w) w hK hret.2 zero_lt_one hw
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
      exact (add_le_add_right (mul_le_mul_of_nonneg_right hpow (wpow_nonneg w)) H).trans
        ((add_le_add_right hwr H).trans hrp)
    · have hsmall : ∃ q ∈ rightPrefixes H,
          q + ω^ a < H + (((2 : ℝ)⁻¹ ^ n : ℝ) : Surreal) * ω^ w := by
        by_cases hge : H.support ⊆ Ici w
        · have hn : ¬ (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 :=
            fun hc ↦ hret ⟨hge, hc⟩
          have hc := le_antisymm (birthday_real_le_omega0 (H.coeff w)) (le_of_not_gt hn)
          exact exists_head_rightPrefix_add_wpow_lt_of_coeff_birthday_omega0 hge
            (mem_rightPrefixes_iff.mp hw).2 hc (pow_pos (by norm_num) _)
        · obtain ⟨v, hv, hvw⟩ := Set.not_subset.mp hge
          exact exists_head_rightPrefix_add_wpow_lt_of_support_lt hHa hv
            (lt_of_not_ge hvw) hw (pow_pos (by norm_num) _)
      obtain ⟨q, hq, hqp⟩ := hsmall
      rw [realCast_inv_two_pow] at hqp
      exact hold q hq ((le_add_of_nonneg_right (wpow_nonneg a)).trans
        (hqp.le.trans ((add_le_add_right hwr H).trans hrp)))

/-- Equal original exponent right-prefix sets give equal actual headed omega right cuts. -/
theorem rightPrefixes_head_add_wpow_eq_of_rightPrefixes_eq
    {H a b : Surreal.{u}} (hHa : H.support ⊆ Ioi a) (hHb : H.support ⊆ Ioi b)
    (he : rightPrefixes a = rightPrefixes b) :
    rightPrefixes (H + ω^ a) = rightPrefixes (H + ω^ b) := by
  have hsub : ∀ {a b : Surreal.{u}}, H.support ⊆ Ioi a → H.support ⊆ Ioi b →
      rightPrefixes a = rightPrefixes b →
      rightPrefixes (H + ω^ a) ⊆ rightPrefixes (H + ω^ b) := by
    intro a b hHa hHb he p hp
    obtain ⟨q, hqa, hqb, hqp⟩ := exists_common_head_rightPrefix_le hHa hHb he hp
    have ht := birthdayTruncation_eq_of_right_between
      (birthday_lt_of_mem_rightPrefixes hp).le (mem_rightPrefixes_iff.mp hqa).2.le
      (by simpa only [(mem_rightPrefixes_iff.mp hp).1] using hqp)
    rw [(mem_rightPrefixes_iff.mp hp).1] at ht
    exact mem_rightPrefixes_iff.mpr
      ⟨birthdayTruncation_eq_trans (mem_rightPrefixes_iff.mp hqb).1 ht,
        (mem_rightPrefixes_iff.mp hqb).2.trans_le hqp⟩
  exact subset_antisymm (hsub hHa hHb he) (hsub hHb hHa he.symm)

private theorem birthday_head_natCast_succ_mul_wpow
    {H v : Surreal.{u}} (hH : H.support ⊆ Ioi v) (n : ℕ) :
    (H + ((n + 1 : ℕ) : Surreal) * ω^ v).birthday =
      NatOrdinal.of ((H + ω^ v).birthday.val + (ω^ (plusCount v)).val * n) := by
  have hh := birthday_head_real_mul_wpow_of_birthday_nat H v hH
    (r := ((n + 1 : ℕ) : ℝ)) (by positivity)
    (by rw [Real.toSurreal_natCast, birthday_natCast])
  simpa only [Real.toSurreal_natCast] using hh

private theorem head_natCast_mul_wpow_mem_leftPrefixes
    {H x v : Surreal.{u}} (hH : H.support ⊆ Ioi x) (hv : v ∈ leftPrefixes x) (n : ℕ) :
    H + (n : Surreal) * ω^ v ∈ leftPrefixes (H + ω^ x) := by
  have hn := natCast_mul_wpow_mem_leftPrefixes hv n
  apply mem_leftPrefixes_iff.mpr
  refine ⟨?_, add_lt_add_right (mem_leftPrefixes_iff.mp hn).2 H⟩
  apply birthdayTruncation_head_add_of_abs_sub_le_real_mul_wpow hH
    (mem_leftPrefixes_iff.mp hn).1 1
  rw [Real.toSurreal_one, one_mul,
    abs_of_nonneg (sub_nonneg.mpr (mem_leftPrefixes_iff.mp hn).2.le)]
  have hn0 : 0 ≤ (n : Surreal.{u}) * ω^ v := mul_nonneg (Nat.cast_nonneg _) (wpow_nonneg v)
  linarith

private theorem exists_head_natCast_mul_wpow_ge_of_leftPrefix_appendPlus
    {H v p : Surreal.{u}} (hH : H.support ⊆ Ioi (appendPlus v))
    (hp : p ∈ leftPrefixes (H + ω^ appendPlus v)) :
    ∃ n : ℕ, p ≤ H + ((n + 1 : ℕ) : Surreal) * ω^ v := by
  rcases exists_leftPrefixes_add_ge hp with ⟨q, hq, hpq⟩ | ⟨r, hr, hpr⟩
  · have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hH
      (birthday_lt_of_mem_leftPrefixes hq) 1
    rw [Real.toSurreal_one, one_mul,
      abs_of_neg (sub_neg.mpr (mem_leftPrefixes_iff.mp hq).2), neg_sub] at hg
    refine ⟨0, hpq.trans ?_⟩
    have hv0 := wpow_nonneg v
    norm_num only [Nat.cast_add, Nat.cast_zero, zero_add, Nat.cast_one, one_mul]
    linarith
  · rcases exists_natCast_mul_wpow_ge_of_mem_leftPrefixes hr with rfl | ⟨u, hu, n, hru⟩
    · refine ⟨0, hpr.trans ?_⟩
      norm_num only [add_zero, Nat.cast_add, Nat.cast_zero, zero_add, Nat.cast_one, one_mul]
      exact le_add_of_nonneg_right (wpow_nonneg v)
    · rw [leftPrefixes_appendPlus] at hu
      rcases hu with rfl | hu
      · refine ⟨n, hpr.trans ((add_le_add_right hru H).trans ?_)⟩
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_right _ (wpow_nonneg u)
        exact_mod_cast Nat.le_succ n
      · have hsmall := mul_wpow_lt_wpow (n : ℝ) (mem_leftPrefixes_iff.mp hu).2
        rw [Real.toSurreal_natCast] at hsmall
        refine ⟨0, hpr.trans ((add_le_add_right (hru.trans hsmall.le) H).trans ?_)⟩
        simp only [Nat.cast_one, zero_add, one_mul, le_refl]

/-- An exponent plus successor appends its full undeleted plus block after a higher head. -/
theorem appendPluses_head_wpow_appendPlus {H v : Surreal.{u}}
    (hH : H.support ⊆ Ioi (appendPlus v)) :
    appendPluses (H + ω^ v) ((ω^ (plusCount v)).val * Ordinal.omega0) =
      H + ω^ appendPlus v := by
  have hvH : H.support ⊆ Ioi v := fun j hj ↦
    mem_Ioi.mpr ((lt_appendPlus v).trans (mem_Ioi.mp (hH hj)))
  have hv : v ∈ leftPrefixes (appendPlus v) := by
    rw [leftPrefixes_appendPlus]
    exact Or.inl rfl
  have hR : rightPrefixes (H + ω^ appendPlus v) = rightPrefixes (H + ω^ v) :=
    rightPrefixes_head_add_wpow_eq_of_rightPrefixes_eq hH hvH (rightPrefixes_appendPlus v)
  have hstage : ∀ n : ℕ, H + ((n + 1 : ℕ) : Surreal) * ω^ v ∈
      leftPrefixes (H + ω^ appendPlus v) := fun n ↦
    head_natCast_mul_wpow_mem_leftPrefixes hH hv (n + 1)
  have hfinite : ∀ n : ℕ, (H + ω^ v).birthday.val + (ω^ (plusCount v)).val * n <
      (H + ω^ appendPlus v).birthday.val := by
    intro n
    have hh := birthday_lt_of_mem_leftPrefixes (hstage n)
    rw [birthday_head_natCast_succ_mul_wpow hvH n] at hh
    exact NatOrdinal.val.lt_iff_lt.mpr hh
  have hQ : 0 < (ω^ (plusCount v)).val := by
    simpa only [NatOrdinal.val_zero] using NatOrdinal.val.strictMono (NatOrdinal.wpow_pos _)
  have hupper : (H + ω^ appendPlus v).birthday ≤ NatOrdinal.of
      ((H + ω^ v).birthday.val + (ω^ (plusCount v)).val * Ordinal.omega0) := by
    apply (birthday_le_iff_forall_prefixes _ _).mpr
    constructor
    · intro p hp
      obtain ⟨n, hn⟩ := exists_head_natCast_mul_wpow_ge_of_leftPrefix_appendPlus hH hp
      have hbp := birthday_le_of_left_between hp hn (mem_leftPrefixes_iff.mp (hstage n)).2.le
      rw [birthday_head_natCast_succ_mul_wpow hvH n] at hbp
      apply hbp.trans_lt
      apply NatOrdinal.of.strictMono
      exact (Ordinal.isNormal_add_right _).strictMono
        ((Ordinal.isNormal_mul_right hQ).strictMono (Ordinal.natCast_lt_omega0 n))
    · intro p hp
      rw [hR] at hp
      exact (birthday_lt_of_mem_rightPrefixes hp).trans_le
        (NatOrdinal.val.le_iff_le.mp (by
          rw [NatOrdinal.val_of]
          exact le_self_add))
  have hlower : (H + ω^ v).birthday.val + (ω^ (plusCount v)).val * Ordinal.omega0 ≤
      (H + ω^ appendPlus v).birthday.val := by
    have hWY : (H + ω^ v).birthday.val ≤ (H + ω^ appendPlus v).birthday.val := by
      simpa only [Nat.cast_zero, mul_zero, add_zero] using (hfinite 0).le
    apply (Ordinal.le_sub_of_le hWY).mp
    apply (Ordinal.mul_le_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mpr
    intro a ha
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ha
    exact (Ordinal.le_sub_of_le hWY).mpr (hfinite n).le
  apply (appendPluses_eq_iff _ _ _).mpr
  refine ⟨le_antisymm hupper ?_, hR⟩
  exact NatOrdinal.val.le_iff_le.mp (by simpa only [NatOrdinal.val_of] using hlower)

/-- Equal original exponent left-prefix sets give equal actual headed omega left cuts. -/
theorem leftPrefixes_head_add_wpow_eq_of_leftPrefixes_eq
    {H a b : Surreal.{u}} (hHa : H.support ⊆ Ioi a) (hHb : H.support ⊆ Ioi b)
    (he : leftPrefixes a = leftPrefixes b) :
    leftPrefixes (H + ω^ a) = leftPrefixes (H + ω^ b) := by
  have hcommon : ∀ {a b : Surreal.{u}}, H.support ⊆ Ioi a → H.support ⊆ Ioi b →
      leftPrefixes a = leftPrefixes b → ∀ p ∈ leftPrefixes (H + ω^ a),
      ∃ q, q ∈ leftPrefixes (H + ω^ a) ∧ q ∈ leftPrefixes (H + ω^ b) ∧ p ≤ q := by
    intro a b hHa hHb he p hp
    have hhead : ∀ x : Surreal.{u}, H.support ⊆ Ioi x → H ∈ leftPrefixes (H + ω^ x) := by
      intro x hHx
      apply mem_leftPrefixes_iff.mpr
      refine ⟨?_, lt_add_of_pos_right H (wpow_pos x)⟩
      apply birthdayTruncation_add_of_support_lt
      simpa only [wlog_wpow] using hHx
    have hold : p ≤ H →
        ∃ q, q ∈ leftPrefixes (H + ω^ a) ∧ q ∈ leftPrefixes (H + ω^ b) ∧ p ≤ q :=
      fun hpH ↦ ⟨H, hhead a hHa, hhead b hHb, hpH⟩
    rcases exists_leftPrefixes_add_ge hp with ⟨q, hq, hpq⟩ | ⟨r, hr, hpr⟩
    · have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hHa
        (birthday_lt_of_mem_leftPrefixes hq) 1
      rw [Real.toSurreal_one, one_mul,
        abs_of_neg (sub_neg.mpr (mem_leftPrefixes_iff.mp hq).2), neg_sub] at hg
      exact hold (hpq.trans (by linarith))
    · rcases exists_natCast_mul_wpow_ge_of_mem_leftPrefixes hr with rfl | ⟨v, hv, n, hrv⟩
      · exact hold (by simpa only [add_zero] using hpr)
      · exact ⟨_, head_natCast_mul_wpow_mem_leftPrefixes hHa hv n,
          head_natCast_mul_wpow_mem_leftPrefixes hHb (he ▸ hv) n,
          hpr.trans (add_le_add_right hrv H)⟩
  have hsub : ∀ {a b : Surreal.{u}}, H.support ⊆ Ioi a → H.support ⊆ Ioi b →
      leftPrefixes a = leftPrefixes b →
      leftPrefixes (H + ω^ a) ⊆ leftPrefixes (H + ω^ b) := by
    intro a b hHa hHb he p hp
    obtain ⟨q, hqa, hqb, hpq⟩ := hcommon hHa hHb he p hp
    have ht := birthdayTruncation_eq_of_left_between
      (birthday_lt_of_mem_leftPrefixes hp).le
      (by simpa only [(mem_leftPrefixes_iff.mp hp).1] using hpq)
      (mem_leftPrefixes_iff.mp hqa).2.le
    rw [(mem_leftPrefixes_iff.mp hp).1] at ht
    exact mem_leftPrefixes_iff.mpr
      ⟨birthdayTruncation_eq_trans (mem_leftPrefixes_iff.mp hqb).1 ht,
        hpq.trans_lt (mem_leftPrefixes_iff.mp hqb).2⟩
  exact subset_antisymm (hsub hHa hHb he) (hsub hHb hHa he.symm)

private theorem birthday_head_inv_two_pow_mul_wpow
    {H v : Surreal.{u}} (hH : H.support ⊆ Ioi v) (n : ℕ) :
    (H + (2 : Surreal)⁻¹ ^ n * ω^ v).birthday =
      NatOrdinal.of ((H + ω^ v).birthday.val + (ω^ (plusCount v)).val * n) := by
  have hbr : ((((2 : ℝ)⁻¹ ^ n : ℝ) : Surreal.{u})).birthday =
      ((n + 1 : ℕ) : NatOrdinal.{u}) := by
    rw [realCast_inv_two_pow]
    have hb := birthday_inv_two_pow_mul_wpow n (0 : Surreal.{u})
    simp only [wpow_zero, mul_one, birthday_one, plusCount_zero, NatOrdinal.wpow_zero,
      NatOrdinal.val_one, one_mul] at hb
    rw [hb, ← NatOrdinal.of_natCast]
    congr 1
    rw [Nat.cast_add, Nat.cast_one]
    exact_mod_cast Nat.add_comm 1 n
  have hh := birthday_head_real_mul_wpow_of_birthday_nat H v hH
    (r := (2 : ℝ)⁻¹ ^ n) (pow_pos (by norm_num) _) hbr
  simpa only [realCast_inv_two_pow] using hh

private theorem head_inv_two_pow_mul_wpow_mem_rightPrefixes
    {H x v : Surreal.{u}} (hH : H.support ⊆ Ioi v) (hv : v ∈ rightPrefixes x) (n : ℕ) :
    H + (2 : Surreal)⁻¹ ^ n * ω^ v ∈ rightPrefixes (H + ω^ x) := by
  have hn := inv_two_pow_mul_wpow_mem_rightPrefixes hv n
  apply mem_rightPrefixes_iff.mpr
  refine ⟨?_, add_lt_add_right (mem_rightPrefixes_iff.mp hn).2 H⟩
  apply birthdayTruncation_head_add_of_abs_sub_le_real_mul_wpow hH
    (mem_rightPrefixes_iff.mp hn).1 1
  rw [Real.toSurreal_one, one_mul,
    abs_of_nonpos (sub_nonpos.mpr (mem_rightPrefixes_iff.mp hn).2.le), neg_sub]
  have hcoeff : (2 : Surreal.{u})⁻¹ ^ n ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hcoeff (wpow_nonneg v)
  rw [one_mul] at hh
  have hx0 := wpow_nonneg x
  linarith

private theorem exists_head_inv_two_pow_mul_wpow_le_of_rightPrefix_appendMinus
    {H v p : Surreal.{u}} (hH : H.support ⊆ Ioi v)
    (hp : p ∈ rightPrefixes (H + ω^ appendMinus v)) :
    ∃ n : ℕ, H + (2 : Surreal)⁻¹ ^ n * ω^ v ≤ p := by
  rcases exists_rightPrefixes_add_le hp with ⟨q, hq, hqp⟩ | ⟨r, hr, hrp⟩
  · have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hH
      (birthday_lt_of_mem_rightPrefixes hq) 1
    rw [Real.toSurreal_one, one_mul,
      abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hq).2)] at hg
    refine ⟨0, le_trans ?_ hqp⟩
    simp only [pow_zero, one_mul]
    have hv0 := wpow_nonneg (appendMinus v)
    linarith
  · obtain ⟨w, hw, n, hwr⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hr
    rw [rightPrefixes_appendMinus] at hw
    rcases hw with rfl | hw
    · exact ⟨n, (add_le_add_right hwr H).trans hrp⟩
    · have hsmall := wpow_lt_mul_wpow (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) n)
        (mem_rightPrefixes_iff.mp hw).2
      rw [realCast_inv_two_pow] at hsmall
      refine ⟨0, le_trans ?_ hrp⟩
      simp only [pow_zero, one_mul]
      exact add_le_add_right (hsmall.le.trans hwr) H

/-- An exponent minus successor appends its full undeleted minus block after a higher head. -/
theorem appendMinuses_head_wpow_appendMinus {H v : Surreal.{u}}
    (hH : H.support ⊆ Ioi v) :
    appendMinuses (H + ω^ v) ((ω^ (plusCount v)).val * Ordinal.omega0) =
      H + ω^ appendMinus v := by
  have hxH : H.support ⊆ Ioi (appendMinus v) := fun j hj ↦
    mem_Ioi.mpr ((appendMinus_lt v).trans (mem_Ioi.mp (hH hj)))
  have hv : v ∈ rightPrefixes (appendMinus v) := by
    rw [rightPrefixes_appendMinus]
    exact Or.inl rfl
  have hL : leftPrefixes (H + ω^ appendMinus v) = leftPrefixes (H + ω^ v) :=
    leftPrefixes_head_add_wpow_eq_of_leftPrefixes_eq hxH hH (leftPrefixes_appendMinus v)
  have hstage : ∀ n : ℕ, H + (2 : Surreal)⁻¹ ^ n * ω^ v ∈
      rightPrefixes (H + ω^ appendMinus v) := fun n ↦
    head_inv_two_pow_mul_wpow_mem_rightPrefixes hH hv n
  have hfinite : ∀ n : ℕ, (H + ω^ v).birthday.val + (ω^ (plusCount v)).val * n <
      (H + ω^ appendMinus v).birthday.val := by
    intro n
    have hh := birthday_lt_of_mem_rightPrefixes (hstage n)
    rw [birthday_head_inv_two_pow_mul_wpow hH n] at hh
    exact NatOrdinal.val.lt_iff_lt.mpr hh
  have hQ : 0 < (ω^ (plusCount v)).val := by
    simpa only [NatOrdinal.val_zero] using NatOrdinal.val.strictMono (NatOrdinal.wpow_pos _)
  have hupper : (H + ω^ appendMinus v).birthday ≤ NatOrdinal.of
      ((H + ω^ v).birthday.val + (ω^ (plusCount v)).val * Ordinal.omega0) := by
    apply (birthday_le_iff_forall_prefixes _ _).mpr
    constructor
    · intro p hp
      rw [hL] at hp
      exact (birthday_lt_of_mem_leftPrefixes hp).trans_le
        (NatOrdinal.val.le_iff_le.mp (by
          rw [NatOrdinal.val_of]
          exact le_self_add))
    · intro p hp
      obtain ⟨n, hn⟩ := exists_head_inv_two_pow_mul_wpow_le_of_rightPrefix_appendMinus hH hp
      have hbp := birthday_le_of_left_between (neg_mem_leftPrefixes_iff.mpr hp)
        (neg_le_neg hn) (neg_le_neg (mem_rightPrefixes_iff.mp (hstage n)).2.le)
      rw [birthday_neg, birthday_neg, birthday_head_inv_two_pow_mul_wpow hH n] at hbp
      apply hbp.trans_lt
      apply NatOrdinal.of.strictMono
      exact (Ordinal.isNormal_add_right _).strictMono
        ((Ordinal.isNormal_mul_right hQ).strictMono (Ordinal.natCast_lt_omega0 n))
  have hlower : (H + ω^ v).birthday.val + (ω^ (plusCount v)).val * Ordinal.omega0 ≤
      (H + ω^ appendMinus v).birthday.val := by
    have hWY : (H + ω^ v).birthday.val ≤ (H + ω^ appendMinus v).birthday.val := by
      simpa only [Nat.cast_zero, mul_zero, add_zero] using (hfinite 0).le
    apply (Ordinal.le_sub_of_le hWY).mp
    apply (Ordinal.mul_le_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mpr
    intro a ha
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ha
    exact (Ordinal.le_sub_of_le hWY).mpr (hfinite n).le
  have hb : (H + ω^ appendMinus v).birthday = NatOrdinal.of
      ((H + ω^ v).birthday.val + (ω^ (plusCount v)).val * Ordinal.omega0) := by
    exact le_antisymm hupper
      (NatOrdinal.val.le_iff_le.mp (by simpa only [NatOrdinal.val_of] using hlower))
  apply neg_injective
  apply eq_of_birthday_eq_of_rightPrefixes_eq
  · rw [birthday_neg, birthday_neg, birthday_appendMinuses, hb]
  · rw [rightPrefixes_neg, rightPrefixes_neg, leftPrefixes_appendMinuses, hL]

end Surreal
