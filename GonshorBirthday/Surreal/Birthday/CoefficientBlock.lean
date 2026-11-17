/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadRun

import GonshorBirthday.Surreal.Birthday.CoefficientCofinality
import GonshorBirthday.Surreal.Birthday.LastMinusFamily
import GonshorBirthday.Surreal.Birthday.OmegaBlock

/-!
# Final real coefficient constant blocks after higher heads

If a real coefficient is a canonical sign successor of a nonzero real predecessor,
cofinal canonical prefix birthdays identify its entire final headed constant block.
The length is omega to the original exponent plus count. Both signs are included;
zero predecessors are excluded explicitly because unit coefficients have different words.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem length_lower_monomial_lt {s v : Surreal.{u}}
    (hv : v ∈ leftPrefixes s) (n : ℕ) :
    (ω^ (plusCount v)).val * (n : Ordinal) < (ω^ (plusCount s)).val := by
  have hn : NatOrdinal.of ((ω^ (plusCount v)).val * (n : Ordinal)) < ω^ (plusCount s) := by
    rw [NatOrdinal.val_wpow, NatOrdinal.of_omega0_opow_mul_natCast, NatOrdinal.of_val]
    exact NatOrdinal.wpow_mul_natCast_lt (plusCount_lt_of_mem_leftPrefixes hv) n
  simpa only [NatOrdinal.val_of] using NatOrdinal.val.strictMono hn

/-- A final coefficient minus gives its exact headed minus block under cofinal right prefixes. -/
theorem appendMinuses_head_real_mul_wpow_of_cofinal_rightPrefixes
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ} (ht : t ≠ 0)
    (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    (hcof : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ rightPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday) :
    appendMinuses (K + (t : Surreal) * ω^ s) (ω^ (plusCount s)).val =
      K + (r : Surreal) * ω^ s := by
  let W := K + (t : Surreal) * ω^ s
  let Z := K + (r : Surreal) * ω^ s
  have hrt : r < t := Real.toSurreal_lt_iff.mp (by rw [hsrc]; exact appendMinus_lt _)
  have hpcoef : birthdayTruncation (r : Surreal.{u}) (t : Surreal).birthday = t := by
    rw [hsrc]
    exact birthdayTruncation_appendMinus _
  have hW : W ∈ rightPrefixes Z := by
    have h := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK hrt hpcoef
      (zero_mem_leftPrefixes (wpow_pos s))
    simpa only [sub_zero] using h
  have hStage (v : Surreal.{u}) (hv : v ∈ leftPrefixes s) (n : ℕ) :
      W - (n : Surreal) * ω^ v ∈ rightPrefixes Z ∧
      (W - (n : Surreal) * ω^ v).birthday =
        NatOrdinal.of (W.birthday.val + (ω^ (plusCount v)).val * (n : Ordinal)) ∧
      leftPrefixes (W - (n : Surreal) * ω^ v) = leftPrefixes W := by
    have hRun := appendMinuses_head_real_mul_wpow K s hK ht hv n
    change appendMinuses W _ = _ at hRun
    refine ⟨?_, ?_, ?_⟩
    · have h := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK hrt hpcoef
        (natCast_mul_wpow_mem_leftPrefixes hv n)
      simpa only [W, add_sub_assoc] using h
    · rw [← hRun, birthday_appendMinuses]
    · rw [← hRun, leftPrefixes_appendMinuses]
  have hf : ∀ a < Z.birthday, ∃ v ∈ leftPrefixes s, ∃ n : ℕ,
      a < (W - (n : Surreal) * ω^ v).birthday := by
    intro a ha
    obtain ⟨v, hv, n, _, _, hb⟩ :=
      head_real_mul_wpow_sub_natCast_mul_wpow_pos_cofinal K s hK hsrc hcof a ha
    exact ⟨v, hv, n, by simpa only [W, add_sub_assoc] using hb⟩
  have hUpper : Z.birthday ≤ NatOrdinal.of (W.birthday.val + (ω^ (plusCount s)).val) := by
    by_contra hn
    obtain ⟨v, hv, n, hbn⟩ := hf _ (lt_of_not_ge hn)
    rw [(hStage v hv n).2.1] at hbn
    have hc := (Ordinal.isNormal_add_right W.birthday.val).strictMono
      (length_lower_monomial_lt hv n)
    have hc' := NatOrdinal.of.strictMono hc
    exact (lt_asymm hbn hc').elim
  have hb : Z.birthday = NatOrdinal.of (W.birthday.val + (ω^ (plusCount s)).val) := by
    apply le_antisymm hUpper (oadd_wpow_plusCount_le_of_leftPrefixes s W.birthday Z.birthday ?_)
    intro a ha
    have hm : W - a ∈ rightPrefixes Z := by
      simpa only [W, Z, add_sub_assoc] using
        head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK hrt hpcoef ha
    have hrun : appendMinuses W (plusCount a).val = W - a := appendMinuses_eq_sub_leftPrefix_wpow
      (support_head_real_mul_wpow_subset K s hK t) (mem_support_head_real_mul_wpow K s hK ht) ha
    rw [← hrun] at hm
    simpa only [birthday_appendMinuses] using birthday_lt_of_mem_rightPrefixes hm
  have hL : leftPrefixes Z = leftPrefixes W := by
    apply Set.Subset.antisymm
    · intro p hp
      obtain ⟨v, hv, n, hpn⟩ := hf p.birthday (birthday_lt_of_mem_leftPrefixes hp)
      have h := mem_leftPrefixes_of_birthdayTruncation_eq_of_birthday_le
        (mem_rightPrefixes_iff.mp (hStage v hv n).1).1 hp hpn.le
        ((mem_leftPrefixes_iff.mp hp).2.trans (mem_rightPrefixes_iff.mp (hStage v hv n).1).2)
      rwa [(hStage v hv n).2.2] at h
    · exact leftPrefixes_subset_of_birthdayTruncation_eq (mem_rightPrefixes_iff.mp hW).1
  change appendMinuses W (ω^ (plusCount s)).val = Z
  apply neg_injective
  apply eq_of_birthday_eq_of_rightPrefixes_eq
  · rw [birthday_neg, birthday_neg, birthday_appendMinuses]
    exact hb.symm
  · rw [rightPrefixes_neg, rightPrefixes_neg, leftPrefixes_appendMinuses, hL]

/-- A final coefficient plus gives its exact headed plus block under cofinal left prefixes. -/
theorem appendPluses_head_real_mul_wpow_of_cofinal_leftPrefixes
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ} (ht : t ≠ 0)
    (hsrc : (r : Surreal.{u}) = appendPlus (t : Surreal.{u}))
    (hcof : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ leftPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday) :
    appendPluses (K + (t : Surreal) * ω^ s) (ω^ (plusCount s)).val =
      K + (r : Surreal) * ω^ s := by
  have hKn : (-K).support ⊆ Ioi s := by simpa only [support_neg] using hK
  have hsrcn : ((-r : ℝ) : Surreal.{u}) = appendMinus ((-t : ℝ) : Surreal.{u}) := by
    rw [Real.toSurreal_neg, Real.toSurreal_neg, hsrc]
    rw [← appendMinuses_one, appendMinuses_eq_neg, neg_neg, appendPluses_one]
  have hZn : -K + ((-r : ℝ) : Surreal.{u}) * ω^ s = -(K + (r : Surreal) * ω^ s) := by
    rw [Real.toSurreal_neg]
    ring
  have hWn : -K + ((-t : ℝ) : Surreal.{u}) * ω^ s = -(K + (t : Surreal) * ω^ s) := by
    rw [Real.toSurreal_neg]
    ring
  have hcofn : ∀ a < (-K + ((-r : ℝ) : Surreal.{u}) * ω^ s).birthday,
      ∃ p ∈ rightPrefixes (-K + ((-r : ℝ) : Surreal.{u}) * ω^ s), a < p.birthday := by
    rw [hZn, birthday_neg]
    intro a ha
    obtain ⟨p, hp, hbp⟩ := hcof a ha
    exact ⟨-p, neg_mem_rightPrefixes_iff.mpr hp, by simpa only [birthday_neg] using hbp⟩
  have h := appendMinuses_head_real_mul_wpow_of_cofinal_rightPrefixes (-K) s hKn
    (neg_ne_zero.mpr ht) hsrcn hcofn
  rw [hZn, hWn, appendMinuses_eq_neg, neg_neg] at h
  exact neg_injective h

/-- A coefficient sign successor with nonzero predecessor cannot have both prefix sides cofinal. -/
theorem not_both_prefixes_cofinal_of_head_real_coefficient_successor
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ} (ht : t ≠ 0)
    (hsrc : (r : Surreal.{u}) = appendPlus (t : Surreal.{u}) ∨
      (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    (hL : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ leftPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday)
    (hR : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ rightPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday) : False := by
  have hQ : 0 < (ω^ (plusCount s)).val := by
    simpa only [NatOrdinal.val_zero] using NatOrdinal.val.strictMono
      (NatOrdinal.wpow_pos (plusCount s))
  rcases hsrc with hsrc | hsrc
  · have he := appendPluses_head_real_mul_wpow_of_cofinal_leftPrefixes K s hK ht hsrc hL
    have hb : (K + (t : Surreal) * ω^ s).birthday < (K + (r : Surreal) * ω^ s).birthday := by
      rw [← he, birthday_appendPluses]
      exact NatOrdinal.of.strictMono (lt_add_of_pos_right _ hQ)
    obtain ⟨p, hp, hbp⟩ := hR _ hb
    rw [← he, rightPrefixes_appendPluses] at hp
    exact hbp.not_gt (birthday_lt_of_mem_rightPrefixes hp)
  · have he := appendMinuses_head_real_mul_wpow_of_cofinal_rightPrefixes K s hK ht hsrc hR
    have hb : (K + (t : Surreal) * ω^ s).birthday < (K + (r : Surreal) * ω^ s).birthday := by
      rw [← he, birthday_appendMinuses]
      exact NatOrdinal.of.strictMono (lt_add_of_pos_right _ hQ)
    obtain ⟨p, hp, hbp⟩ := hL _ hb
    rw [← he, leftPrefixes_appendMinuses] at hp
    exact hbp.not_gt (birthday_lt_of_mem_leftPrefixes hp)

/-- Every nonunit nonzero dyadic real has a nonzero real canonical last-sign predecessor. -/
theorem exists_nonzero_real_predecessor_of_finite_birthday {r : ℝ}
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrn1 : r ≠ -1)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ∃ t : ℝ, t ≠ 0 ∧ ((r : Surreal.{u}) = appendPlus (t : Surreal.{u}) ∨
      (r : Surreal.{u}) = appendMinus (t : Surreal.{u})) := by
  have hb : 1 < (r : Surreal.{u}).birthday := by
    by_contra hn
    rcases birthday_le_one.mp (le_of_not_gt hn) with h0 | h1 | hn1
    · exact hr0 (Real.toSurreal_inj.{u}.mp (by simpa using h0))
    · exact hr1 (Real.toSurreal_inj.{u}.mp (by simpa using h1))
    · exact hrn1 (Real.toSurreal_inj.{u}.mp (by simpa using hn1))
  obtain ⟨n, hn⟩ := NatOrdinal.lt_omega0.mp hf
  have hn2 : 2 ≤ n := by
    have hh : (1 : NatOrdinal.{u}) < (n : NatOrdinal.{u}) := by simpa only [hn] using hb
    exact_mod_cast hh
  cases n with
  | zero => omega
  | succ n =>
    have hlast : (n : NatOrdinal.{u}) + 1 = (r : Surreal.{u}).birthday := by
      simpa only [Nat.cast_add, Nat.cast_one] using hn.symm
    have hlt : (n : NatOrdinal.{u}) < (r : Surreal.{u}).birthday := by
      rw [← hlast]
      exact lt_add_one _
    obtain ⟨t, ht⟩ := birthdayTruncation_real_mem_range_real r (n : NatOrdinal.{u})
    have hbt : (t : Surreal.{u}).birthday = (n : NatOrdinal.{u}) := by
      rw [ht, birthday_birthdayTruncation _ hlt.le]
    have ht0 : t ≠ 0 := by
      intro he
      have hn0 : (n : NatOrdinal.{u}) = 0 := by simpa only [he, Real.toSurreal_zero,
        birthday_zero] using hbt.symm
      have : n = 0 := by exact_mod_cast hn0
      omega
    refine ⟨t, ht0, ?_⟩
    rcases lt_trichotomy (t : Surreal.{u}) (r : Surreal.{u}) with htr | he | hrt
    · left
      have hh := birthdayTruncation_add_one_eq_appendPlus (r : Surreal.{u}) hlast.le
        (by simpa only [← ht] using htr)
      rw [hlast, birthdayTruncation_birthday, ← ht] at hh
      exact hh
    · have hh := congrArg birthday he
      rw [hbt] at hh
      exact (hlt.ne hh).elim
    · right
      have hh := birthdayTruncation_add_one_eq_appendMinus (r : Surreal.{u}) hlast.le
        (by simpa only [← ht] using hrt)
      rw [hlast, birthdayTruncation_birthday, ← ht] at hh
      exact hh


/-- Two cofinal prefix sides force a nonzero dyadic last coefficient to be a signed unit. -/
theorem head_real_coefficient_eq_one_or_neg_one_of_both_cofinal
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : r ≠ 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hL : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ leftPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday)
    (hR : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ rightPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday) :
    r = 1 ∨ r = -1 := by
  by_cases hr1 : r = 1
  · exact Or.inl hr1
  · right
    by_contra hrn1
    obtain ⟨t, ht, hsrc⟩ := exists_nonzero_real_predecessor_of_finite_birthday hr hr1 hrn1 hf
    exact not_both_prefixes_cofinal_of_head_real_coefficient_successor K s hK ht hsrc hL hR

end Surreal
