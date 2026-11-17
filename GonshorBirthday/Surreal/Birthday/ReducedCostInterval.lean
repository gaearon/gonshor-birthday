/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadRun
public import GonshorBirthday.Surreal.Birthday.ReducedCostEquality

import GonshorBirthday.Surreal.Birthday.LastMinusFamily
import GonshorBirthday.Surreal.Birthday.OmegaBlock
import GonshorBirthday.Surreal.Birthday.CoefficientBlock
import GonshorBirthday.Surreal.Birthday.HeadSuffix

/-!
# Full final intervals at headed coefficient minuses

A lowered-cutoff gap window forces the final plus interval to have length at least
omega to the last exponent's plus count. A final coefficient minus supplies a
suffix with at most that many minus positions. The two bounds force equality
of the interval length and the plus-only input costs. A zero coefficient
predecessor uses the minus-position count in the monomial itself.
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

/-- Finite multiples of left-exponent block lengths are cofinal in the full plus-count power. -/
theorem exists_leftPrefix_monomial_length_gt {s : Surreal.{u}}
    (hq : plusCount s ≠ 0) {ρ : Ordinal.{u}} (hρ : ρ < (ω^ (plusCount s)).val) :
    ∃ v ∈ leftPrefixes s, ∃ n : ℕ, ρ < (ω^ (plusCount v)).val * (n : Ordinal) := by
  have hρ' : NatOrdinal.of ρ < ω^ (plusCount s) := hρ
  obtain ⟨α, hα, n, hn⟩ := (NatOrdinal.lt_wpow_iff hq).mp hρ'
  obtain ⟨v, hv, hαv⟩ := exists_leftPrefixes_plusCount_ge hα
  have hbound : NatOrdinal.of ρ < ω^ (plusCount v) * n :=
    hn.trans_le (mul_le_mul_of_nonneg_right (NatOrdinal.wpow_le_wpow.mpr hαv) bot_le)
  refine ⟨v, hv, n, ?_⟩
  simpa only [NatOrdinal.wpow_mul_natCast, NatOrdinal.val_of, NatOrdinal.val_wpow] using
    NatOrdinal.val.strictMono hbound

/-- A final plus interval crossing a lowered-cutoff gap window spans a full coefficient block. -/
theorem wpow_plusCount_le_plus_interval_of_gap_window
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ} (hr : r ≠ 0)
    (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    {ρ : Ordinal.{u}} (hρpos : 0 < ρ) {d : Surreal.{u}}
    (hdel : ∀ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      K + (r : Surreal) * ω^ s + d < w)
    (hne : ∃ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      w ≤ appendPluses (K + (r : Surreal) * ω^ s) ρ + d) :
    (ω^ (plusCount s)).val ≤ ρ := by
  by_cases hq : plusCount s = 0
  · simp only [hq, NatOrdinal.wpow_zero, NatOrdinal.val_one]
    simpa only [zero_add] using Order.add_one_le_iff.mpr hρpos
  by_contra hn
  obtain ⟨u, hu, n, hρn⟩ := exists_leftPrefix_monomial_length_gt hq (lt_of_not_ge hn)
  have hrun : appendPluses (K + (r : Surreal) * ω^ s) ρ ≤
      K + (r : Surreal) * ω^ s + (n : Surreal) * ω^ u := by
    rw [← appendPluses_head_real_mul_wpow K s hK hr hu n]
    exact (strictMono_appendPluses _).monotone hρn.le
  obtain ⟨w, hw, hwC⟩ := hne
  have hrs : r < t := Real.toSurreal_lt_iff.mp (by rw [hsrc]; exact appendMinus_lt _)
  have hp : birthdayTruncation (r : Surreal.{u}) (t : Surreal).birthday = t := by
    rw [hsrc]; exact birthdayTruncation_appendMinus _
  rcases exists_head_real_mul_wpow_sub_natCast_mul_wpow_le K s hK hsrc hw with
      hbase | ⟨v, hv, m, hm⟩
  · have hnew := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK hrs hp
      (natCast_mul_wpow_mem_leftPrefixes hu n)
    have hd := hdel _ hnew
    linarith only [hd, hbase, hwC, hrun]
  · let v' := max u v
    have hv' : v' ∈ leftPrefixes s := by
      rcases le_total u v with huv | hvu
      · simpa only [v', max_eq_right huv] using hv
      · simpa only [v', max_eq_left hvu] using hu
    have hun : (n : Surreal) * ω^ u ≤ (n : Surreal) * ω^ v' :=
      mul_le_mul_of_nonneg_left (wpow_le_wpow.mpr (le_max_left u v)) (Nat.cast_nonneg n)
    have hvm : (m : Surreal) * ω^ v ≤ (m : Surreal) * ω^ v' :=
      mul_le_mul_of_nonneg_left (wpow_le_wpow.mpr (le_max_right u v)) (Nat.cast_nonneg m)
    have hsum : (n : Surreal) * ω^ u + (m : Surreal) * ω^ v ≤
        ((n + m : ℕ) : Surreal) * ω^ v' := by
      simpa only [Nat.cast_add, add_mul] using add_le_add hun hvm
    have hnew := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK hrs hp
      (natCast_mul_wpow_mem_leftPrefixes hv' (n + m))
    have hd := hdel _ hnew
    linarith only [hd, hm, hwC, hrun, hsum]

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
/-- A bounded minus suffix forces a full block and plus-only input costs. -/
theorem full_block_and_baseline_of_head_minus_suffix
    (a b d K s : Surreal.{u}) {r t : ℝ} (hK : K.support ⊆ Ioi s) (hr : r ≠ 0)
    (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    {α β c : NatOrdinal.{u}} {ρ : Ordinal.{u}} (hρpos : 0 < ρ)
    (hA : reducedOmegaCost (a + d) a = ω^ α)
    (hB : reducedOmegaCost (b + d) b = ω^ β)
    (hH : reducedOmegaCost (a + b + d) (K + (r : Surreal) * ω^ s) = ω^ (α + β))
    (he : a + b = appendPluses (K + (r : Surreal) * ω^ s) ρ)
    (hc : c < (K + (r : Surreal) * ω^ s).birthday)
    (hcof : ∀ j < (K + (r : Surreal) * ω^ s).birthday,
      ∃ y ∈ rightPrefixes (K + (r : Surreal) * ω^ s), j < y.birthday ∧ y ≤ a + b + d)
    (hdel : ∀ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      K + (r : Surreal) * ω^ s + d < w)
    (hminus : typeLT {i : (K + (r : Surreal) * ω^ s).birthday.val.ToType |
      c ≤ NatOrdinal.of i.toOrd.1 ∧ K + (r : Surreal) * ω^ s <
        birthdayTruncation (K + (r : Surreal) * ω^ s) (NatOrdinal.of i.toOrd.1)} ≤
          (ω^ (plusCount s)).val) :
    ρ = (ω^ (plusCount s)).val ∧
      plusCount (a + b) = α + β ∧ α = plusCount a ∧ β = plusCount b ∧
      reducedOmegaCost (a + d) a = ω^ plusCount a ∧
      reducedOmegaCost (b + d) b = ω^ plusCount b := by
  have hne : ∃ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      w ≤ appendPluses (K + (r : Surreal) * ω^ s) ρ + d := by
    obtain ⟨w, hw, _, hwC⟩ := hcof c hc
    exact ⟨w, hw, by simpa only [← he] using hwC⟩
  exact full_block_and_baseline_of_pure_suffix a b d (K + (r : Surreal) * ω^ s)
    hA hB hH he (wpow_plusCount_le_plus_interval_of_gap_window K s hK hr hsrc
      hρpos hdel hne) hc hcof hminus

/-- A nonzero coefficient predecessor supplies both coefficient-block length bounds. -/
theorem full_block_and_baseline_of_head_nonzero_predecessor
    (a b d K s : Surreal.{u}) {r t : ℝ} (hK : K.support ⊆ Ioi s) (hr : r ≠ 0)
    (ht : t ≠ 0) (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    {α β : NatOrdinal.{u}} {ρ : Ordinal.{u}} (hρpos : 0 < ρ)
    (hA : reducedOmegaCost (a + d) a = ω^ α)
    (hB : reducedOmegaCost (b + d) b = ω^ β)
    (hH : reducedOmegaCost (a + b + d) (K + (r : Surreal) * ω^ s) = ω^ (α + β))
    (he : a + b = appendPluses (K + (r : Surreal) * ω^ s) ρ)
    (hcof : ∀ j < (K + (r : Surreal) * ω^ s).birthday,
      ∃ y ∈ rightPrefixes (K + (r : Surreal) * ω^ s), j < y.birthday ∧ y ≤ a + b + d)
    (hdel : ∀ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      K + (r : Surreal) * ω^ s + d < w) :
    ρ = (ω^ (plusCount s)).val ∧
      plusCount (a + b) = α + β ∧ α = plusCount a ∧ β = plusCount b ∧
      reducedOmegaCost (a + d) a = ω^ plusCount a ∧
      reducedOmegaCost (b + d) b = ω^ plusCount b := by
  have hblock := appendMinuses_head_real_mul_wpow_of_cofinal_rightPrefixes K s hK ht hsrc
    (fun j hj ↦ by obtain ⟨y, hy, hjy, _⟩ := hcof j hj; exact ⟨y, hy, hjy⟩)
  have hc : (K + (t : Surreal) * ω^ s).birthday <
      (K + (r : Surreal) * ω^ s).birthday := by
    rw [← hblock, birthday_appendMinuses]
    apply NatOrdinal.val.lt_iff_lt.mp
    simp only [NatOrdinal.val_of]
    simpa only [add_zero, NatOrdinal.val_zero] using
      (Ordinal.isNormal_add_right (K + (t : Surreal) * ω^ s).birthday.val).strictMono
        (NatOrdinal.val.strictMono (NatOrdinal.wpow_pos (plusCount s)))
  exact full_block_and_baseline_of_head_minus_suffix a b d K s hK hr hsrc hρpos
    hA hB hH he hc hcof hdel (minus_suffix_le_of_eq_appendMinuses hblock.symm)

/-- Every final coefficient minus forces a full final plus block and plus-only input costs. -/
theorem full_block_and_baseline_of_head_coefficient_minus
    (a b d K s : Surreal.{u}) {r t : ℝ} (hK : K.support ⊆ Ioi s) (hr : r ≠ 0)
    (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    {α β : NatOrdinal.{u}} {ρ : Ordinal.{u}} (hρpos : 0 < ρ)
    (hA : reducedOmegaCost (a + d) a = ω^ α)
    (hB : reducedOmegaCost (b + d) b = ω^ β)
    (hH : reducedOmegaCost (a + b + d) (K + (r : Surreal) * ω^ s) = ω^ (α + β))
    (he : a + b = appendPluses (K + (r : Surreal) * ω^ s) ρ)
    (hcof : ∀ j < (K + (r : Surreal) * ω^ s).birthday,
      ∃ y ∈ rightPrefixes (K + (r : Surreal) * ω^ s), j < y.birthday ∧ y ≤ a + b + d)
    (hdel : ∀ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      K + (r : Surreal) * ω^ s + d < w) :
    ρ = (ω^ (plusCount s)).val ∧
      plusCount (a + b) = α + β ∧ α = plusCount a ∧ β = plusCount b ∧
      reducedOmegaCost (a + d) a = ω^ plusCount a ∧
      reducedOmegaCost (b + d) b = ω^ plusCount b := by
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
    exact full_block_and_baseline_of_head_minus_suffix a b d K s hK hr hsrc hρpos
      hA hB hH he hc hcof hdel hminus
  · exact full_block_and_baseline_of_head_nonzero_predecessor a b d K s hK hr ht hsrc hρpos
      hA hB hH he hcof hdel

end Surreal
