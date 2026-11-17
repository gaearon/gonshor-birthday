/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientRight

import GonshorBirthday.Surreal.Birthday.CoefficientCofinality
import GonshorBirthday.Surreal.Birthday.LastMinusFamily
import GonshorBirthday.Surreal.Birthday.OmegaBlock

/-!
# Exact headed real coefficient successor blocks

For real r=appendPlus(t) with t nonzero, the headed monomial K+r*omega^s is obtained
from K+t*omega^s by appending exactly omega^(plusCount s) plus signs. There is no
cofinality hypothesis. The corresponding minus formula follows by negation.
Canonical addition/product cofinality and the exact lower perturbation runs supply
a birthday bound on every option of the coefficient successor. Real finite-birthday
coefficients have actual nonzero dyadic plus successors, giving a dyadic endpoint.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem real_neg_plus (r t : ℝ)
    (h : (r : Surreal.{u}) = appendPlus (t : Surreal.{u})) :
    ((-r : ℝ) : Surreal.{u}) = appendMinus ((-t : ℝ) : Surreal.{u}) := by
  rw [Real.toSurreal_neg, Real.toSurreal_neg, h]
  rw [← appendMinuses_one, appendMinuses_eq_neg, neg_neg, appendPluses_one]

/-- Lower monomial prefixes translate to headed left prefixes at a coefficient plus successor. -/
theorem head_real_mul_wpow_add_leftPrefix_mem_leftPrefixes
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ}
    (hsrc : (r : Surreal.{u}) = appendPlus (t : Surreal.{u}))
    {a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ s)) :
    K + ((t : Surreal) * ω^ s + a) ∈ leftPrefixes (K + (r : Surreal) * ω^ s) := by
  have hKn : (-K).support ⊆ Ioi s := by simpa only [support_neg] using hK
  have hsrcn := real_neg_plus r t hsrc
  have hnegtr : -r < -t := Real.toSurreal_lt_iff.mp (by rw [hsrcn]; exact appendMinus_lt _)
  have hpcoef : birthdayTruncation ((-r : ℝ) : Surreal.{u})
      (((-t : ℝ) : Surreal.{u})).birthday = ((-t : ℝ) : Surreal.{u}) := by
    rw [hsrcn]
    exact birthdayTruncation_appendMinus _
  have h := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes (-K) s hKn hnegtr hpcoef ha
  have hZ : -K + ((-r : ℝ) : Surreal.{u}) * ω^ s = -(K + (r : Surreal) * ω^ s) := by
    rw [Real.toSurreal_neg]
    ring
  have hP : -K + (((-t : ℝ) : Surreal.{u}) * ω^ s - a) =
      -(K + ((t : Surreal) * ω^ s + a)) := by
    rw [Real.toSurreal_neg]
    ring
  rw [hZ, hP] at h
  exact neg_mem_rightPrefixes_iff.mp h

/-- Finite lower monomials bound all headed left prefixes at a coefficient plus successor. -/
theorem exists_head_real_mul_wpow_add_natCast_mul_wpow_ge
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ}
    (hsrc : (r : Surreal.{u}) = appendPlus (t : Surreal.{u}))
    {p : Surreal.{u}} (hp : p ∈ leftPrefixes (K + (r : Surreal) * ω^ s)) :
    p ≤ K + (t : Surreal) * ω^ s ∨
      ∃ v ∈ leftPrefixes s, ∃ n : ℕ,
        p ≤ K + ((t : Surreal) * ω^ s + (n : Surreal) * ω^ v) := by
  have hKn : (-K).support ⊆ Ioi s := by simpa only [support_neg] using hK
  have hsrcn := real_neg_plus r t hsrc
  have hZ : -K + ((-r : ℝ) : Surreal.{u}) * ω^ s = -(K + (r : Surreal) * ω^ s) := by
    rw [Real.toSurreal_neg]
    ring
  have hW : -K + ((-t : ℝ) : Surreal.{u}) * ω^ s = -(K + (t : Surreal) * ω^ s) := by
    rw [Real.toSurreal_neg]
    ring
  have hpn : -p ∈ rightPrefixes (-K + ((-r : ℝ) : Surreal.{u}) * ω^ s) := by
    rw [hZ]
    exact neg_mem_rightPrefixes_iff.mpr hp
  rcases exists_head_real_mul_wpow_sub_natCast_mul_wpow_le (-K) s hKn hsrcn hpn with
    h | ⟨v, hv, n, hn⟩
  · left
    rw [hW] at h
    exact neg_le_neg_iff.mp h
  · right
    refine ⟨v, hv, n, ?_⟩
    rw [Real.toSurreal_neg, neg_mul] at hn
    linarith only [hn]

private theorem length_lower_monomial_lt {s v : Surreal.{u}}
    (hv : v ∈ leftPrefixes s) (n : ℕ) :
    (ω^ (plusCount v)).val * (n : Ordinal) < (ω^ (plusCount s)).val := by
  have hn : NatOrdinal.of ((ω^ (plusCount v)).val * (n : Ordinal)) < ω^ (plusCount s) := by
    rw [NatOrdinal.val_wpow, NatOrdinal.of_omega0_opow_mul_natCast, NatOrdinal.of_val]
    exact NatOrdinal.wpow_mul_natCast_lt (plusCount_lt_of_mem_leftPrefixes hv) n
  simpa only [NatOrdinal.val_of] using NatOrdinal.val.strictMono hn

/-- A real coefficient plus successor gives its exact headed pure plus block. -/
theorem appendPluses_head_real_mul_wpow_of_appendPlus
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ} (ht : t ≠ 0)
    (hsrc : (r : Surreal.{u}) = appendPlus (t : Surreal.{u})) :
    appendPluses (K + (t : Surreal) * ω^ s) (ω^ (plusCount s)).val =
      K + (r : Surreal) * ω^ s := by
  let W := K + (t : Surreal) * ω^ s
  let Z := K + (r : Surreal) * ω^ s
  have hW : W ∈ leftPrefixes Z := by
    have hh := head_real_mul_wpow_add_leftPrefix_mem_leftPrefixes K s hK hsrc
      (zero_mem_leftPrefixes (wpow_pos s))
    simpa only [add_zero] using hh
  have hR : rightPrefixes Z = rightPrefixes W :=
    rightPrefixes_head_real_mul_wpow_appendPlus K s hK ht hsrc
  have hStage (v : Surreal.{u}) (hv : v ∈ leftPrefixes s) (n : ℕ) :
      W + (n : Surreal) * ω^ v ∈ leftPrefixes Z ∧
      (W + (n : Surreal) * ω^ v).birthday =
        NatOrdinal.of (W.birthday.val + (ω^ (plusCount v)).val * (n : Ordinal)) := by
    have hRun := appendPluses_head_real_mul_wpow K s hK ht hv n
    change appendPluses W _ = _ at hRun
    constructor
    · have hh := head_real_mul_wpow_add_leftPrefix_mem_leftPrefixes K s hK hsrc
        (natCast_mul_wpow_mem_leftPrefixes hv n)
      simpa only [W, add_assoc] using hh
    · rw [← hRun, birthday_appendPluses]
  have hQ : 0 < (ω^ (plusCount s)).val := by
    simpa only [NatOrdinal.val_zero] using NatOrdinal.val.strictMono
      (NatOrdinal.wpow_pos (plusCount s))
  have hB : W.birthday < NatOrdinal.of (W.birthday.val + (ω^ (plusCount s)).val) :=
    NatOrdinal.of.strictMono (lt_add_of_pos_right _ hQ)
  have hUpper : Z.birthday ≤ NatOrdinal.of (W.birthday.val + (ω^ (plusCount s)).val) := by
    apply (birthday_le_iff_forall_prefixes _ _).mpr
    constructor
    · intro p hp
      rcases exists_head_real_mul_wpow_add_natCast_mul_wpow_ge K s hK hsrc hp with
        hpW | ⟨v, hv, n, hpn⟩
      · exact (birthday_le_of_left_between hp hpW (mem_leftPrefixes_iff.mp hW).2.le).trans_lt hB
      · have hb := birthday_le_of_left_between hp (by simpa only [W, add_assoc] using hpn)
          (mem_leftPrefixes_iff.mp (hStage v hv n).1).2.le
        rw [(hStage v hv n).2] at hb
        exact hb.trans_lt (NatOrdinal.of.strictMono
          ((Ordinal.isNormal_add_right W.birthday.val).strictMono (length_lower_monomial_lt hv n)))
    · intro p hp
      rw [hR] at hp
      exact (birthday_lt_of_mem_rightPrefixes hp).trans hB
  have hLower : NatOrdinal.of (W.birthday.val + (ω^ (plusCount s)).val) ≤ Z.birthday := by
    apply oadd_wpow_plusCount_le_of_leftPrefixes
    intro a ha
    have hm : W + a ∈ leftPrefixes Z := by
      simpa only [W, Z, add_assoc] using head_real_mul_wpow_add_leftPrefix_mem_leftPrefixes K s hK
        hsrc ha
    have hrun : appendPluses W (plusCount a).val = W + a := appendPluses_eq_add_leftPrefix_wpow
      (support_head_real_mul_wpow_subset K s hK t) (mem_support_head_real_mul_wpow K s hK ht) ha
    rw [← hrun] at hm
    simpa only [birthday_appendPluses] using birthday_lt_of_mem_leftPrefixes hm
  change appendPluses W (ω^ (plusCount s)).val = Z
  exact (appendPluses_eq_iff _ _ _).mpr ⟨le_antisymm hUpper hLower, hR⟩

/-- A real coefficient minus successor gives its exact headed pure minus block. -/
theorem appendMinuses_head_real_mul_wpow_of_appendMinus
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ} (ht : t ≠ 0)
    (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u})) :
    appendMinuses (K + (t : Surreal) * ω^ s) (ω^ (plusCount s)).val =
      K + (r : Surreal) * ω^ s := by
  have hKn : (-K).support ⊆ Ioi s := by simpa only [support_neg] using hK
  have hsrcn : ((-r : ℝ) : Surreal.{u}) = appendPlus ((-t : ℝ) : Surreal.{u}) := by
    rw [Real.toSurreal_neg, Real.toSurreal_neg, hsrc]
    rw [← appendMinuses_one, appendMinuses_eq_neg, neg_neg, appendPluses_one]
  have hZ : -K + ((-r : ℝ) : Surreal.{u}) * ω^ s = -(K + (r : Surreal) * ω^ s) := by
    rw [Real.toSurreal_neg]
    ring
  have hW : -K + ((-t : ℝ) : Surreal.{u}) * ω^ s = -(K + (t : Surreal) * ω^ s) := by
    rw [Real.toSurreal_neg]
    ring
  have hh := appendPluses_head_real_mul_wpow_of_appendPlus (-K) s hKn
    (neg_ne_zero.mpr ht) hsrcn
  rw [hZ, hW] at hh
  rw [appendMinuses_eq_neg, hh, neg_neg]

/-- A nonzero dyadic last coefficient has a nonzero dyadic plus-block endpoint. -/
theorem exists_dyadic_head_coefficient_plus_block
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : r ≠ 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ∃ q : Dyadic, q ≠ 0 ∧ (q : Surreal.{u}) = appendPlus (r : Surreal.{u}) ∧
      appendPluses (K + (r : Surreal) * ω^ s) (ω^ (plusCount s)).val =
        K + (q : Surreal) * ω^ s := by
  have hfnext : (appendPlus (r : Surreal.{u})).birthday < NatOrdinal.of Ordinal.omega0 := by
    rw [birthday_appendPlus]
    obtain ⟨n, hn⟩ := NatOrdinal.lt_omega0.mp hf
    rw [hn]
    exact_mod_cast NatOrdinal.natCast_lt_omega0 (n + 1)
  obtain ⟨q, hq⟩ := birthday_lt_omega0_iff.mp hfnext
  have hq0 : q ≠ 0 := by
    intro he
    have hh : (appendPlus (r : Surreal.{u})).birthday = 0 := by rw [← hq, he]; simp
    simp only [birthday_appendPlus, NatOrdinal.add_eq_zero_iff, one_ne_zero, and_false] at hh
  have hsrc : ((q.toRat : ℝ) : Surreal.{u}) = appendPlus (r : Surreal.{u}) := by
    simpa only [Real.toSurreal_ratCast] using hq
  refine ⟨q, hq0, hq, ?_⟩
  have hh := appendPluses_head_real_mul_wpow_of_appendPlus K s hK hr hsrc
  simpa only [Real.toSurreal_ratCast] using hh

end Surreal
