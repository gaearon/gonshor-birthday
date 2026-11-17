/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Head
public import GonshorBirthday.Surreal.Birthday.CoefficientShift

import GonshorBirthday.Surreal.Birthday.OmegaBlock

/-!
# Headed lower-monomial right-prefix families

Canonical coefficient right prefixes, of either sign and including zero, give
actual lower-monomial right-prefix families after an arbitrary higher normal-form head.
For a negative unit last coefficient, the family is coinitial in value and cofinal
in birthday whenever all right-prefix birthdays are cofinal. Exact block lengths
are not asserted.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- A real monomial bound on the change permits prefix transport past a higher head. -/
theorem birthdayTruncation_head_add_of_abs_sub_le_real_mul_wpow
    {K a b s : Surreal.{u}} (hK : K.support ⊆ Ioi s)
    (hp : birthdayTruncation a b.birthday = b) (r : ℝ)
    (hab : |a - b| ≤ (r : Surreal) * ω^ s) :
    birthdayTruncation (K + a) (K + b).birthday = K + b := by
  apply birthdayTruncation_add_of_prefix_of_head_gaps hp
  · intro p hpk
    have hg := hab.trans_lt (real_mul_wpow_lt_abs_sub_of_birthday_lt hK
      (birthday_lt_of_mem_leftPrefixes hpk) r)
    rw [abs_of_neg (sub_neg.mpr (mem_leftPrefixes_iff.mp hpk).2), neg_sub] at hg
    have hb := neg_abs_le (a - b)
    linarith only [hb, hg]
  · intro p hpk
    have hg := hab.trans_lt (real_mul_wpow_lt_abs_sub_of_birthday_lt hK
      (birthday_lt_of_mem_rightPrefixes hpk) r)
    rw [abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hpk).2)] at hg
    have hb := (le_abs_self (a - b)).trans_lt hg
    linarith only [hb]

/-- A coefficient right prefix admits all lower canonical monomial-prefix subtractions. -/
theorem birthdayTruncation_real_mul_wpow_sub_leftPrefix_of_rightPrefix {r s : ℝ}
    (hsr : s < r)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = r)
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    birthdayTruncation ((s : Surreal) * ω^ x) ((r : Surreal) * ω^ x - a).birthday =
      (r : Surreal) * ω^ x - a := by
  by_cases hs : 0 < s
  · exact birthdayTruncation_real_mul_wpow_sub_leftPrefix hs hsr hp ha
  have hr : r ≤ 0 := by
    by_contra hn
    have hr0 : (0 : Surreal.{u}) < (r : Surreal) :=
      Real.toSurreal_pos_iff.mpr (lt_of_not_ge hn)
    have hz := leftPrefixes_subset_of_birthdayTruncation_eq hp (zero_mem_leftPrefixes hr0)
    exact hs (Real.toSurreal_pos_iff.mp (mem_leftPrefixes_iff.mp hz).2)
  obtain hr | rfl := hr.lt_or_eq
  · have hpneg : birthdayTruncation ((-s : ℝ) : Surreal.{u})
        (((-r : ℝ) : Surreal.{u})).birthday = ((-r : ℝ) : Surreal.{u}) := by
      simpa only [Real.toSurreal_neg, birthday_neg] using birthdayTruncation_neg_of_eq hp
    have ht := birthdayTruncation_real_mul_wpow_add_leftPrefix (neg_pos.mpr hr)
      (neg_lt_neg_iff.mpr hsr) hpneg ha
    have htn := birthdayTruncation_neg_of_eq ht
    rw [← birthday_neg (((-r : ℝ) : Surreal.{u}) * ω^ x + a)] at htn
    simpa only [Real.toSurreal_neg, neg_mul, neg_add_rev, neg_neg, sub_eq_add_neg,
      add_comm] using htn
  · have hpre := birthdayTruncation_real_mul_wpow (-s) (by linarith) x
    have ha' := birthdayTruncation_eq_trans hpre (mem_leftPrefixes_iff.mp ha).1
    have ht := birthdayTruncation_neg_of_eq ha'
    simpa only [Real.toSurreal_neg, neg_mul, birthday_neg, neg_neg,
      Real.toSurreal_zero, zero_mul, zero_sub] using ht

/-- Higher heads preserve the reflected lower-prefix family at any coefficient right prefix. -/
theorem birthdayTruncation_head_real_mul_wpow_sub_leftPrefix_of_rightPrefix
    (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x) {r s : ℝ}
    (hsr : s < r)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = r)
    {a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    birthdayTruncation (K + (s : Surreal) * ω^ x)
      (K + ((r : Surreal) * ω^ x - a)).birthday =
        K + ((r : Surreal) * ω^ x - a) := by
  apply birthdayTruncation_head_add_of_abs_sub_le_real_mul_wpow hK
    (birthdayTruncation_real_mul_wpow_sub_leftPrefix_of_rightPrefix hsr hp ha) (r - s)
  have hsmall := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hsr) ha
  have ha0 := nonneg_of_mem_leftPrefixes (wpow_pos x) ha
  rw [Real.toSurreal_sub, sub_mul] at hsmall ⊢
  rw [abs_of_neg (by linarith only [hsmall])]
  linarith only [ha0]

/-- Reflected lower monomial prefixes are right prefixes after an arbitrary higher head. -/
theorem head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes
    (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x) {r s : ℝ}
    (hsr : s < r)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = r)
    {a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    K + ((r : Surreal) * ω^ x - a) ∈ rightPrefixes (K + (s : Surreal) * ω^ x) := by
  apply mem_rightPrefixes_iff.mpr
  refine ⟨birthdayTruncation_head_real_mul_wpow_sub_leftPrefix_of_rightPrefix K x hK hsr hp ha,
    ?_⟩
  have ht := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hsr) ha
  rw [Real.toSurreal_sub, sub_mul] at ht
  linarith only [ht]

/-- A negative unit last coefficient admits every finite lower-monomial right prefix. -/
theorem head_sub_natCast_mul_wpow_mem_rightPrefixes (K s : Surreal.{u})
    (hK : K.support ⊆ Ioi s) {v : Surreal.{u}} (hv : v ∈ leftPrefixes s) (n : ℕ) :
    K - (n : Surreal) * ω^ v ∈ rightPrefixes (K - ω^ s) := by
  have ht := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK
    (r := (0 : ℝ)) (s := (-1 : ℝ)) (by norm_num) (by simp)
    (natCast_mul_wpow_mem_leftPrefixes hv n)
  simpa only [Real.toSurreal_zero, zero_mul, zero_sub, Real.toSurreal_neg,
    Real.toSurreal_one, neg_one_mul, sub_eq_add_neg, zero_add] using ht

/-- Headed finite lower monomials are coinitial among negative-unit right prefixes. -/
theorem exists_head_sub_natCast_mul_wpow_le_of_mem_rightPrefixes (K s : Surreal.{u})
    (hK : K.support ⊆ Ioi s) {w : Surreal.{u}}
    (hw : w ∈ rightPrefixes (K - ω^ s)) :
    K ≤ w ∨ ∃ v ∈ leftPrefixes s, ∃ n : ℕ, K - (n : Surreal) * ω^ v ≤ w := by
  rw [sub_eq_add_neg] at hw
  rcases exists_rightPrefixes_add_le hw with ⟨p, hp, hpw⟩ | ⟨p, hp, hpw⟩
  · left
    have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hK
      (birthday_lt_of_mem_rightPrefixes hp) (1 : ℝ)
    rw [Real.toSurreal_one, one_mul,
      abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hp).2)] at hg
    linarith only [hg, hpw]
  · rw [rightPrefixes_neg] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    rcases exists_natCast_mul_wpow_ge_of_mem_leftPrefixes ha with rfl | ⟨v, hv, n, han⟩
    · left
      simpa using hpw
    · exact Or.inr ⟨v, hv, n, (sub_le_sub_left han K).trans
        (by simpa only [sub_eq_add_neg] using hpw)⟩

/-- The higher head is a right prefix of a negative unit last monomial. -/
theorem head_mem_rightPrefixes_sub_wpow (K s : Surreal.{u})
    (hK : K.support ⊆ Ioi s) : K ∈ rightPrefixes (K - ω^ s) := by
  have ht := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK
    (r := (0 : ℝ)) (s := (-1 : ℝ)) (by norm_num) (by simp)
    (zero_mem_leftPrefixes (wpow_pos s))
  simpa [sub_eq_add_neg] using ht

/-- Cofinal right-prefix birthdays are witnessed by the headed negative-unit family. -/
theorem head_sub_natCast_mul_wpow_cofinal (K s : Surreal.{u})
    (hK : K.support ⊆ Ioi s)
    (hcof : ∀ a < (K - ω^ s).birthday,
      ∃ w ∈ rightPrefixes (K - ω^ s), a < w.birthday) :
    ∀ a < (K - ω^ s).birthday, ∃ p ∈ rightPrefixes (K - ω^ s), a < p.birthday ∧
      (p = K ∨ ∃ v ∈ leftPrefixes s, ∃ n : ℕ, p = K - (n : Surreal) * ω^ v) := by
  intro a ha
  obtain ⟨w, hw, haw⟩ := hcof a ha
  have hb {p : Surreal.{u}} (hp : p ∈ rightPrefixes (K - ω^ s)) (hpw : p ≤ w) :
      w.birthday ≤ p.birthday := by
    have ht := birthday_le_of_left_between (neg_mem_leftPrefixes_iff.mpr hw)
      (neg_le_neg hpw) (neg_le_neg (mem_rightPrefixes_iff.mp hp).2.le)
    simpa only [birthday_neg] using ht
  rcases exists_head_sub_natCast_mul_wpow_le_of_mem_rightPrefixes K s hK hw with
    hKw | ⟨v, hv, n, hn⟩
  · have hKp := head_mem_rightPrefixes_sub_wpow K s hK
    exact ⟨K, hKp, haw.trans_le (hb hKp hKw), Or.inl rfl⟩
  · have hp := head_sub_natCast_mul_wpow_mem_rightPrefixes K s hK hv n
    exact ⟨_, hp, haw.trans_le (hb hp hn), Or.inr ⟨v, hv, n, rfl⟩⟩

/-- Cofinal negative-unit right prefixes have a cofinal positive-multiplier monomial family. -/
theorem head_sub_natCast_mul_wpow_pos_cofinal (K s : Surreal.{u})
    (hK : K.support ⊆ Ioi s)
    (hcof : ∀ a < (K - ω^ s).birthday,
      ∃ w ∈ rightPrefixes (K - ω^ s), a < w.birthday) :
    ∀ a < (K - ω^ s).birthday, ∃ v ∈ leftPrefixes s, ∃ n : ℕ, 0 < n ∧
      a < (K - (n : Surreal) * ω^ v).birthday := by
  have hKp := head_mem_rightPrefixes_sub_wpow K s hK
  have hf := head_sub_natCast_mul_wpow_cofinal K s hK hcof
  obtain ⟨p, _, hbp, hpf⟩ := hf K.birthday (birthday_lt_of_mem_rightPrefixes hKp)
  have hv0 : ∃ v ∈ leftPrefixes s, True := by
    rcases hpf with rfl | ⟨v, hv, n, _⟩
    · exact (lt_irrefl _ hbp).elim
    · exact ⟨v, hv, trivial⟩
  obtain ⟨v0, hv0, _⟩ := hv0
  have hbK : K.birthday ≤ (K - ((1 : ℕ) : Surreal) * ω^ v0).birthday := by
    have hp0 := head_sub_natCast_mul_wpow_mem_rightPrefixes K s hK hv0 1
    have ht := birthday_le_of_left_between (neg_mem_leftPrefixes_iff.mpr hKp)
      (neg_le_neg (show K - ((1 : ℕ) : Surreal) * ω^ v0 ≤ K by simp [wpow_nonneg]))
      (neg_le_neg (mem_rightPrefixes_iff.mp hp0).2.le)
    simpa only [birthday_neg] using ht
  intro a ha
  obtain ⟨p, _, hap, hpf⟩ := hf a ha
  rcases hpf with rfl | ⟨v, hv, n, rfl⟩
  · exact ⟨v0, hv0, 1, by omega, hap.trans_le hbK⟩
  · cases n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, sub_zero] at hap
      exact ⟨v0, hv0, 1, by omega, hap.trans_le hbK⟩
    | succ n => exact ⟨v, hv, n + 1, by omega, hap⟩

end Surreal
