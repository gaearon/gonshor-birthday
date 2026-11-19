/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientRun
public import GonshorBirthday.Surreal.Birthday.ReducedCostSuffix

import GonshorBirthday.Surreal.Birthday.ReducedCostCofinality
import GonshorBirthday.Surreal.Birthday.CoefficientCofinality
import GonshorBirthday.Surreal.Birthday.LastMinusFamily
import GonshorBirthday.Surreal.Birthday.OmegaBlock
import GonshorBirthday.Surreal.Birthday.CoefficientBlock
import GonshorBirthday.Surreal.Birthday.HeadSuffix

/-!
# Full final intervals at headed coefficient minuses

Passing a right prefix takes at least a full coefficient block of pluses. A final
coefficient minus has a suffix containing at most that many minuses. For a negative
unit, count minus positions in the monomial itself.

-/

universe u
public noncomputable section

namespace Ordinal

private theorem typeLT_subtype_toType_le_of_suffix (a b c : Ordinal.{u}) (hab : a ≤ b + c)
    (S : Set a.ToType) (hS : ∀ i ∈ S, b ≤ i.toOrd.1) : typeLT S ≤ c := by
  let f : S → c.ToType := fun i ↦
    ToType.mk ⟨i.1.toOrd.1 - b,
      (sub_lt_of_le (hS i.1 i.2)).mpr (i.1.toOrd.2.trans_le hab)⟩
  have hf : StrictMono f := by
    intro i j hij
    apply ToType.mk.strictMono
    change i.1.toOrd.1 - b < j.1.toOrd.1 - b
    apply (isNormal_add_right b).strictMono.lt_iff_lt.mp
    rw [Ordinal.add_sub_cancel_of_le (hS i.1 i.2),
      Ordinal.add_sub_cancel_of_le (hS j.1 j.2)]
    exact ToType.mk.symm.strictMono hij
  simpa only [type_toType] using (RelEmbedding.ofMonotone f hf).ordinal_type_le

end Ordinal

namespace Surreal
open Set

/-- Suppose the last coefficient of `z` ends in a minus. For an extension `e` of `z`,
its next coefficient plus is a prefix of `e` exactly when a translate of `e` reaches
an old right option while the same translate of `z` lies below them all. -/
theorem coefficient_plus_prefix_iff_exists_margin
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t q : ℝ} (hr : r ≠ 0)
    (hminus : (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    (hplus : (q : Surreal.{u}) = appendPlus (r : Surreal.{u})) {e : Surreal.{u}}
    (hpre : birthdayTruncation e (K + (r : Surreal) * ω^ s).birthday = K + (r : Surreal) * ω^ s) :
    let z := K + (r : Surreal) * ω^ s
    let y := K + (q : Surreal) * ω^ s
    birthdayTruncation e y.birthday = y ↔ ∃ d : Surreal, 0 < d ∧
      (∀ w ∈ rightPrefixes z, z + d < w) ∧ ∃ w ∈ rightPrefixes z, w ≤ e + d := by
  let z := K + (r : Surreal) * ω^ s
  let W := K + (t : Surreal) * ω^ s
  let y := K + (q : Surreal) * ω^ s
  obtain ⟨hright, hcoin⟩ := rightPrefixes_at_coefficient_minus K s hK hminus
  have hW : W ∈ rightPrefixes z := by
    simpa only [sub_zero] using hright 0 (zero_mem_leftPrefixes (wpow_pos s))
  have heR (w : Surreal.{u}) (hw : w ∈ rightPrefixes z) : e < w :=
    (mem_rightPrefixes_iff.mp (rightPrefixes_subset_of_birthdayTruncation_eq hpre hw)).2
  constructor
  · intro hy
    refine ⟨W - e, sub_pos.mpr (heR W hW), ?_, W, hW, by simp⟩
    intro w hw
    obtain ⟨u, hu, huw⟩ := hcoin w hw
    have hl := head_real_mul_wpow_add_leftPrefix_mem_leftPrefixes K s hK hplus hu
    have he := (mem_leftPrefixes_iff.mp (leftPrefixes_subset_of_birthdayTruncation_eq hy hl)).2
    change z + (W - e) < w
    change K + ((r : Surreal) * ω^ s + u) < e at he
    dsimp only [z]
    linarith only [he, huw]
  · rintro ⟨d, _, hdel, w, hw, hwe⟩
    obtain ⟨v, hv, hvw⟩ := hcoin w hw
    have hleft {u : Surreal.{u}} (hu : u ∈ leftPrefixes (ω^ s)) : z + u < e := by
      obtain ⟨c, hc, hsum⟩ := exists_leftPrefix_wpow_ge_add hu hv
      have hd : z + d < W - c := hdel _ (hright c hc)
      linarith only [hd, hsum, hvw, hwe]
    have hl (p : Surreal.{u}) (hp : p ∈ leftPrefixes y) : p < e := by
      rcases exists_head_real_mul_wpow_add_natCast_mul_wpow_ge K s hK hplus hp with
        h | ⟨v, hv, n, h⟩
      · apply h.trans_lt
        simpa only [add_zero] using hleft (zero_mem_leftPrefixes (wpow_pos s))
      · apply h.trans_lt
        simpa only [z, add_assoc] using hleft (natCast_mul_wpow_mem_leftPrefixes hv n)
    have hr' (p : Surreal.{u}) (hp : p ∈ rightPrefixes y) : e < p :=
      heR p (rightPrefixes_head_real_mul_wpow_appendPlus K s hK hr hplus ▸ hp)
    simpa only [ofSets_leftPrefixes_rightPrefixes] using
      (birthdayTruncation_eq_of_btwn (H := leftPrefixes_lt_rightPrefixes y) hl hr')

open Ordinal in
/-- The original minus positions in an appended minus suffix have at most its length. -/
theorem minus_suffix_le_of_eq_appendMinuses {x y : Surreal.{u}} {ρ : Ordinal.{u}}
    (h : x = appendMinuses y ρ) :
    typeLT {i : x.birthday.val.ToType | y.birthday ≤ NatOrdinal.of i.toOrd.1 ∧
      x < birthdayTruncation x (NatOrdinal.of i.toOrd.1)} ≤ ρ := by
  apply Ordinal.typeLT_subtype_toType_le_of_suffix _ y.birthday.val
  · rw [h, birthday_appendMinuses, NatOrdinal.val_of]
  · intro i hi
    exact NatOrdinal.val.monotone hi.1

open Ordinal in
/-- Beyond a prefix of a final coefficient minus, at most one coefficient block of
minus positions remains. This includes a negative unit, whose predecessor is zero. -/
theorem exists_minus_suffix_le_of_coefficient_minus (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s)
    {r t : ℝ} (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    (hcof : ∀ j < (K + (r : Surreal) * ω^ s).birthday,
      ∃ y ∈ rightPrefixes (K + (r : Surreal) * ω^ s), j < y.birthday) :
    ∃ c < (K + (r : Surreal) * ω^ s).birthday,
      typeLT {i : (K + (r : Surreal) * ω^ s).birthday.val.ToType |
        c ≤ NatOrdinal.of i.toOrd.1 ∧ K + (r : Surreal) * ω^ s <
          birthdayTruncation (K + (r : Surreal) * ω^ s) (NatOrdinal.of i.toOrd.1)} ≤
            (ω^ (plusCount s)).val := by
  by_cases ht : t = 0
  · subst t
    have hm : ((-1 : ℝ) : Surreal.{u}) = appendMinus (0 : Surreal.{u}) := by
      apply eq_appendMinus_of_birthdayTruncation_eq
      · simp
      · simp
      · norm_num
    have hz : K + (r : Surreal) * ω^ s = K - ω^ s := by
      rw [hsrc, Real.toSurreal_zero, ← hm]
      simp only [Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul, sub_eq_add_neg]
    obtain ⟨c, hc, hminus⟩ := exists_minus_suffix_le_head_sub_wpow K s hK
    rw [← hz] at hc hminus
    exact ⟨c, hc, hminus⟩
  · have hblock := appendMinuses_head_real_mul_wpow_of_cofinal_rightPrefixes K s hK ht hsrc
      hcof
    have hc : (K + (t : Surreal) * ω^ s).birthday <
        (K + (r : Surreal) * ω^ s).birthday := by
      rw [← hblock, birthday_appendMinuses]
      apply NatOrdinal.val.lt_iff_lt.mp
      simp only [NatOrdinal.val_of]
      simpa only [add_zero, NatOrdinal.val_zero] using
        (Ordinal.isNormal_add_right (K + (t : Surreal) * ω^ s).birthday.val).strictMono
          (NatOrdinal.val.strictMono (NatOrdinal.wpow_pos (plusCount s)))
    exact ⟨_, hc, minus_suffix_le_of_eq_appendMinuses hblock.symm⟩

/-- If the retained minuses at a last coefficient minus exhaust a power, its exponent
is at most the plus count at the next coefficient plus. -/
theorem pure_cost_exponent_le_next_coefficient (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s)
    {r t : ℝ} (hminus : (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    {C : Surreal.{u}} {γ : NatOrdinal.{u}}
    (hcost : reducedOmegaCost C (K + (r : Surreal) * ω^ s) = ω^ γ)
    (hcof : ∀ j < (K + (r : Surreal) * ω^ s).birthday,
      ∃ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s), j < w.birthday ∧ w ≤ C) :
    let y := appendPluses (K + (r : Surreal) * ω^ s) (ω^ (plusCount s)).val
    γ ≤ plusCount y := by
  obtain ⟨i, hi, hcount⟩ := exists_minus_suffix_le_of_coefficient_minus K s hK hminus (by
    intro j hj
    obtain ⟨w, hw, hjw, _⟩ := hcof j hj
    exact ⟨w, hw, hjw⟩)
  have hbound := pure_reducedOmegaCost_exponent_le_of_minus_suffix hcost hi hcof hcount
  have h : 1 + (plusCount s).val ≤ Ordinal.omega0 ^ (plusCount s).val := by
    by_cases hz : (plusCount s).val = 0
    · simp [hz]
    · have hω := Ordinal.left_le_opow Ordinal.omega0 (pos_iff_ne_zero.mpr hz)
      exact ((Ordinal.isNormal_add_right 1).monotone
        (Ordinal.right_le_opow (plusCount s).val Ordinal.one_lt_omega0)).trans_eq
        (Ordinal.one_add_of_omega0_le hω)
  simp only [plusCount_appendPluses]
  apply hbound.trans
  apply NatOrdinal.of.monotone
  rw [add_assoc]
  exact (Ordinal.isNormal_add_right _).monotone h

end Surreal
