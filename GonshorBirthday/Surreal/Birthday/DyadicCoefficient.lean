/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Coefficient
public import GonshorBirthday.Surreal.Birthday.Minus
public import GonshorBirthday.Surreal.Birthday.Dyadic

/-!
# Dyadic monomial coefficients and canonical prefixes
-/

universe u
public noncomputable section

namespace IGame

/-- Every positive dyadic multiple fits the defining cut of its monomial. -/
theorem Fits.dyadic_mul_wpow (r : Dyadic) (hr : 0 < r) (x : IGame.{u}) [Numeric x] :
    Fits (r * ω^ x) (ω^ x) := by
  constructor
  · rw [forall_mem_moves_left_wpow]
    constructor
    · exact (Numeric.mul_pos (by exact_mod_cast hr) (Numeric.wpow_pos x)).not_ge
    · intro s hs y hy
      numeric
      exact (Numeric.mul_wpow_lt_mul_wpow_of_pos' s hr (Numeric.left_lt hy)).not_ge
  · rw [forall_moves_right_wpow]
    intro s hs y hy
    numeric
    exact (Numeric.mul_wpow_lt_mul_wpow_of_pos' r hs (Numeric.lt_right hy)).not_ge

end IGame

namespace Surreal
open Set IGame

/-- Every positive dyadic monomial coefficient extends its coefficient-one monomial. -/
theorem birthdayTruncation_dyadic_mul_wpow (r : Dyadic) (hr : 0 < r)
    (x : Surreal.{u}) :
    birthdayTruncation ((r : Surreal) * ω^ x) (ω^ x).birthday = ω^ x := by
  have ht := (IGame.Fits.dyadic_mul_wpow r hr x.out).birthdayTruncation_eq
  simpa only [mk_mul, mk_dyadic, mk_wpow, out_eq] using ht

/-- The coefficient-one monomial is a canonical prefix of its half. -/
theorem birthdayTruncation_half_mul_wpow (x : Surreal.{u}) :
    birthdayTruncation ((2 : Surreal)⁻¹ * ω^ x) (ω^ x).birthday = ω^ x := by
  have ht := birthdayTruncation_dyadic_mul_wpow Dyadic.half (by decide) x
  have he : (Dyadic.half : Surreal.{u}) = (2 : Surreal)⁻¹ := by
    rw [← mk_dyadic]
    simpa only [Dyadic.toIGame_half] using (IGame.mk_half.{u})
  rwa [he] at ht


/-- Canonical left prefixes of a half monomial are bounded by lower monomials. -/
theorem exists_natCast_mul_wpow_ge_of_mem_leftPrefixes_half {x z : Surreal.{u}}
    (hz : z ∈ leftPrefixes ((2 : Surreal)⁻¹ * ω^ x)) : z = 0 ∨
      ∃ v ∈ leftPrefixes x, ∃ n : ℕ, z ≤ (n : Surreal) * ω^ v := by
  have he := ofSets_eq_mk (s := leftPrefixes x) (t := rightPrefixes x)
    (H := leftPrefixes_lt_rightPrefixes x)
  generalize_proofs at he
  rw [ofSets_leftPrefixes_rightPrefixes] at he
  let g : IGame.{u} := !{out '' leftPrefixes x | out '' rightPrefixes x}
  have : IGame.Numeric g := by assumption
  change x = mk g at he
  have hh : mk (½ * ω^ g) = (2 : Surreal)⁻¹ * ω^ x := by
    rw [mk_mul, IGame.mk_half, mk_wpow, ← he]
  have hpos : (0 : Surreal.{u}) < (2 : Surreal)⁻¹ * ω^ x :=
    mul_pos (inv_pos.mpr (by norm_num)) (wpow_pos x)
  have hzb := birthday_lt_of_mem_leftPrefixes hz
  have hzx := (mem_leftPrefixes_iff.mp hz).2
  have hn : ¬ IGame.Fits z.out (½ * ω^ g) := by
    intro h
    have hb := h.surrealBirthday_le
    exact hzb.not_ge (by simpa only [hh, out_eq] using hb)
  rw [IGame.not_fits_iff] at hn
  rcases hn with ⟨v, hv, hzv⟩ | ⟨v, hv, hvz⟩
  · have hm : ∃ v ∈ (½ * ω^ g)ᴸ, z.out ≤ v := ⟨v, hv, hzv⟩
    rw [IGame.exists_moves_mul] at hm
    rcases hm with ⟨p, a, ha, b, hb, hzv⟩
    cases p
    · simp only [IGame.moves_left_half, Set.mem_singleton_iff] at ha
      subst a
      simp only [Player.mul_left] at hb
      rw [IGame.moves_left_wpow] at hb
      rcases hb with hb | ⟨r, hr, w, hw, rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp hb
        have hle := mk_le_mk.mpr hzv
        have hz0 : z ≤ 0 := by simpa [IGame.mulOption, mk_add, mk_sub, mk_mul] using hle
        exact Or.inl (hz0.antisymm (nonneg_of_mem_leftPrefixes hpos hz))
      · rw [IGame.moves_left_ofSets] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        have hle := mk_le_mk.mpr hzv
        have hzv' : z ≤ ((2 : Surreal)⁻¹ * (r : Surreal)) * ω^ v := by
          simpa [IGame.mulOption, mk_add, mk_sub, mk_mul, mk_wpow, mk_dyadic,
            IGame.mk_half, out_eq, mul_assoc] using hle
        obtain ⟨n, hn⟩ := exists_nat_gt r
        have hrn : (r : Surreal.{u}) ≤ (n : Surreal) := by exact_mod_cast hn.le
        have hh1 : (2 : Surreal.{u})⁻¹ ≤ 1 := by norm_num
        have hle' : (2 : Surreal.{u})⁻¹ * (r : Surreal) ≤ (n : Surreal) :=
          (mul_le_of_le_one_left
            (by exact_mod_cast (show (0 : Dyadic) < r from hr).le) hh1).trans hrn
        exact Or.inr ⟨v, hv, n,
          hzv'.trans (mul_le_mul_of_nonneg_right hle' (wpow_nonneg v))⟩
    · simp only [IGame.moves_right_half, Set.mem_singleton_iff] at ha
      subst a
      simp only [Player.mul_left] at hb
      rw [IGame.moves_right_wpow] at hb
      obtain ⟨r, hr, w, hw, rfl⟩ := hb
      rw [IGame.moves_right_ofSets] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      have hxv := (mem_rightPrefixes_iff.mp hv).2
      have hscale : ω^ x < (2 : Surreal)⁻¹ * ((r : Surreal) * ω^ v) := by
        have hrreal : (0 : ℝ) < r.toRat := by
          exact_mod_cast (show (0 : Dyadic) < r from hr)
        have hrpos : (0 : ℝ) < r.toRat / 2 := by positivity
        have ht := wpow_lt_mul_wpow hrpos hxv
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, Real.toSurreal_mul,
          Real.toSurreal_inv, Real.toSurreal_ratCast] using ht
      have hle := mk_le_mk.mpr hzv
      have hzneg : z < 0 := by
        have ht : mk (IGame.mulOption ½ (ω^ g) 1 (r * ω^ v.out)) < 0 := by
          simp only [IGame.mulOption, mk_add, mk_sub, mk_mul, mk_wpow,
            IGame.mk_half, mk_dyadic, out_eq, mk_one, ← he]
          nlinarith only [hscale]
        exact lt_of_le_of_lt (by simpa only [out_eq] using hle) ht
      exact False.elim ((nonneg_of_mem_leftPrefixes hpos hz).not_gt hzneg)
  · have ht := mk_lt_mk.mpr ((IGame.Numeric.lt_right hv).trans_le hvz)
    have ht' : (2 : Surreal)⁻¹ * ω^ x < z := by simpa only [hh, out_eq] using ht
    exact False.elim (hzx.not_gt ht')


/-- Halving a monomial preserves exactly its canonical left prefixes. -/
theorem leftPrefixes_half_mul_wpow (x : Surreal.{u}) :
    leftPrefixes ((2 : Surreal)⁻¹ * ω^ x) = leftPrefixes (ω^ x) := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain rfl | ⟨v, hv, n, hzn⟩ :=
      exists_natCast_mul_wpow_ge_of_mem_leftPrefixes_half hz
    · exact zero_mem_leftPrefixes (wpow_pos x)
    have hvx := (mem_leftPrefixes_iff.mp hv).2
    have hpre : birthdayTruncation (ω^ x) ((n : Surreal) * ω^ v).birthday =
        (n : Surreal) * ω^ v := by
      obtain ⟨a, ha, rfl, hl⟩ := mem_leftPrefixes.mp hv
      exact birthdayTruncation_natCast_mul_wpow_birthdayTruncation x a hl n
    have hn : (n : Surreal.{u}) * ω^ v < (2 : Surreal)⁻¹ * ω^ x := by
      have hh : (0 : ℝ) < (2 : ℝ)⁻¹ := by positivity
      have ht := mul_wpow_lt_mul_wpow_of_pos (n : ℝ) hh hvx
      simpa using ht
    have hzpre := (mem_leftPrefixes_iff.mp hz).1
    have ht := birthdayTruncation_eq_of_left_between
      (birthday_lt_of_mem_leftPrefixes hz).le (by rwa [hzpre]) hn.le
    rw [hzpre] at ht
    apply mem_leftPrefixes_iff.mpr
    refine ⟨birthdayTruncation_eq_trans hpre ht, ?_⟩
    have hh : (2 : Surreal.{u})⁻¹ * ω^ x < ω^ x := by
      exact mul_lt_of_lt_one_left (wpow_pos x) (by norm_num)
    exact (mem_leftPrefixes_iff.mp hz).2.trans hh
  · exact leftPrefixes_subset_of_birthdayTruncation_eq (birthdayTruncation_half_mul_wpow x)

/-- Halving a monomial preserves its full ordinal plus count. -/
theorem plusCount_half_mul_wpow (x : Surreal.{u}) :
    plusCount ((2 : Surreal)⁻¹ * ω^ x) = ω^ plusCount x := by
  rw [plusCount_eq_of_leftPrefixes_eq (leftPrefixes_half_mul_wpow x), plusCount_wpow]


/-- Every canonical left prefix of a monomial lies strictly below its half. -/
theorem lt_half_mul_wpow_of_mem_leftPrefixes_wpow {x a : Surreal.{u}}
    (ha : a ∈ leftPrefixes (ω^ x)) : a < (2 : Surreal)⁻¹ * ω^ x := by
  obtain rfl | ⟨v, hv, n, han⟩ := exists_natCast_mul_wpow_ge_of_mem_leftPrefixes ha
  · exact mul_pos (inv_pos.mpr (by norm_num)) (wpow_pos x)
  apply han.trans_lt
  have hh : (0 : ℝ) < (2 : ℝ)⁻¹ := by positivity
  have ht := mul_wpow_lt_mul_wpow_of_pos (n : ℝ) hh (mem_leftPrefixes_iff.mp hv).2
  simpa using ht

/-- Subtracting any canonical left prefix of a monomial gives a prefix of its half. -/
theorem birthdayTruncation_half_mul_wpow_sub_leftPrefix {x a : Surreal.{u}}
    (ha : a ∈ leftPrefixes (ω^ x)) :
    birthdayTruncation ((2 : Surreal)⁻¹ * ω^ x) (ω^ x - a).birthday = ω^ x - a := by
  have ha0 := nonneg_of_mem_leftPrefixes (wpow_pos x) ha
  have haA := (mem_leftPrefixes_iff.mp ha).2
  have hhalf : 0 < (2 : Surreal.{u})⁻¹ * ω^ x :=
    mul_pos (inv_pos.mpr (by norm_num)) (wpow_pos x)
  have hhalfA : (2 : Surreal.{u})⁻¹ * ω^ x < ω^ x :=
    mul_lt_of_lt_one_left (wpow_pos x) (by norm_num)
  have hAhalf : ω^ x - (2 : Surreal)⁻¹ * ω^ x = (2 : Surreal)⁻¹ * ω^ x := by ring
  have hL : ∀ z ∈ (· + -a) '' leftPrefixes (ω^ x) ∪
      (ω^ x + ·) '' leftPrefixes (-a), z < (2 : Surreal)⁻¹ * ω^ x := by
    rintro z (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact (add_le_of_nonpos_right (neg_nonpos.mpr ha0)).trans_lt
        (lt_half_mul_wpow_of_mem_leftPrefixes_wpow hp)
    · rw [leftPrefixes_neg] at hp
      obtain ⟨r, hr, rfl⟩ := hp
      have hrA := rightPrefixes_subset_of_birthdayTruncation_eq
        (mem_leftPrefixes_iff.mp ha).1 hr
      have hAr := (mem_rightPrefixes_iff.mp hrA).2
      simpa only [sub_eq_add_neg] using (sub_neg.mpr hAr).trans hhalf
  have hR : ∀ z ∈ (· + -a) '' rightPrefixes (ω^ x) ∪
      (ω^ x + ·) '' rightPrefixes (-a), (2 : Surreal)⁻¹ * ω^ x < z := by
    rintro z (⟨r, hr, rfl⟩ | ⟨p, hp, rfl⟩)
    · have h2 := natCast_mul_wpow_lt_of_mem_rightPrefixes hr 2
      norm_num only [Nat.cast_ofNat] at h2
      have ht : ω^ x < r - a := by nlinarith only [h2, haA]
      simpa only [sub_eq_add_neg] using hhalfA.trans ht
    · rw [rightPrefixes_neg] at hp
      obtain ⟨p, hp, rfl⟩ := hp
      have hpA := leftPrefixes_subset_of_birthdayTruncation_eq
        (mem_leftPrefixes_iff.mp ha).1 hp
      have ht := lt_half_mul_wpow_of_mem_leftPrefixes_wpow hpA
      rw [← hAhalf]
      simpa only [sub_eq_add_neg] using sub_lt_sub_left ht (ω^ x)
  have ht := birthdayTruncation_eq_of_btwn
    (H := fun z hz w hw ↦ (hL z hz).trans (hR w hw)) hL hR
  have he := add_eq_ofSets_leftPrefixes (ω^ x) (-a)
  rw [← he] at ht
  simpa only [sub_eq_add_neg] using ht


/-- Subtracting a canonical left prefix has exact relative birthday above a monomial head. -/
theorem birthday_wpow_sub_leftPrefix {x a : Surreal.{u}}
    (ha : a ∈ leftPrefixes (ω^ x)) :
    (ω^ x - a).birthday =
      NatOrdinal.of ((ω^ x).birthday.val + (plusCount a).val) := by
  have hR : rightPrefixes (-((2 : Surreal)⁻¹ * ω^ x)) = rightPrefixes (-(ω^ x)) := by
    rw [rightPrefixes_neg, rightPrefixes_neg, leftPrefixes_half_mul_wpow]
  have hP : ∀ y ∈ leftPrefixes (ω^ x),
      birthdayTruncation (-((2 : Surreal)⁻¹ * ω^ x)) (-(ω^ x) + y).birthday =
        -(ω^ x) + y := by
    intro y hy
    have ht := birthdayTruncation_neg_of_eq
      (birthdayTruncation_half_mul_wpow_sub_leftPrefix hy)
    have he : -(ω^ x - y) = -(ω^ x) + y := by ring
    rw [← birthday_neg (ω^ x - y), he] at ht
    exact ht
  have hB : ∀ y ∈ leftPrefixes (ω^ x), -(ω^ x) + y ≤ -((2 : Surreal)⁻¹ * ω^ x) := by
    intro y hy
    have ht := lt_half_mul_wpow_of_mem_leftPrefixes_wpow hy
    have he : ω^ x - (2 : Surreal)⁻¹ * ω^ x = (2 : Surreal)⁻¹ * ω^ x := by ring
    rw [← he] at ht
    exact le_of_lt (by linarith only [ht])
  have hG : ∀ y ∈ leftPrefixes (ω^ x), ∀ p ∈ leftPrefixes (-(ω^ x)),
      p + y ≤ -(ω^ x) := by
    intro y hy p hp
    rw [leftPrefixes_neg] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    have h2 := natCast_mul_wpow_lt_of_mem_rightPrefixes hr 2
    norm_num only [Nat.cast_ofNat] at h2
    have hyA := (mem_leftPrefixes_iff.mp hy).2
    linarith only [h2, hyA]
  have ht := birthday_add_left_prefix_eq_of_prefix_family (wpow_pos x) hR hP hB hG ha
  have he : -(ω^ x) + a = -(ω^ x - a) := by ring
  rw [he, birthday_neg, birthday_neg] at ht
  exact ht


/-- Every canonical right prefix of a half monomial bounds a reflected left prefix. -/
theorem exists_wpow_sub_leftPrefix_le_of_mem_rightPrefixes_half {x z : Surreal.{u}}
    (hz : z ∈ rightPrefixes ((2 : Surreal)⁻¹ * ω^ x)) :
    ∃ a ∈ leftPrefixes (ω^ x), ω^ x - a ≤ z := by
  have he := ofSets_eq_mk (s := leftPrefixes x) (t := rightPrefixes x)
    (H := leftPrefixes_lt_rightPrefixes x)
  generalize_proofs at he
  rw [ofSets_leftPrefixes_rightPrefixes] at he
  let g : IGame.{u} := !{out '' leftPrefixes x | out '' rightPrefixes x}
  have : IGame.Numeric g := by assumption
  change x = mk g at he
  have hh : mk (½ * ω^ g) = (2 : Surreal)⁻¹ * ω^ x := by
    rw [mk_mul, IGame.mk_half, mk_wpow, ← he]
  have hzb := birthday_lt_of_mem_rightPrefixes hz
  have hzx := (mem_rightPrefixes_iff.mp hz).2
  have hn : ¬ IGame.Fits z.out (½ * ω^ g) := by
    intro h
    have hb := h.surrealBirthday_le
    exact hzb.not_ge (by simpa only [hh, out_eq] using hb)
  rw [IGame.not_fits_iff] at hn
  rcases hn with ⟨v, hv, hzv⟩ | ⟨v, hv, hvz⟩
  · numeric
    have ht := mk_lt_mk.mpr (hzv.trans_lt (IGame.Numeric.left_lt hv))
    have ht' : z < (2 : Surreal)⁻¹ * ω^ x := by simpa only [hh, out_eq] using ht
    exact False.elim (hzx.not_gt ht')
  · have hm : ∃ v ∈ (½ * ω^ g)ᴿ, v ≤ z.out := ⟨v, hv, hvz⟩
    rw [IGame.exists_moves_mul] at hm
    rcases hm with ⟨p, a, ha, b, hb, hvz⟩
    cases p
    · simp only [IGame.moves_left_half, Set.mem_singleton_iff] at ha
      subst a
      simp only [Player.mul_right, Player.neg_left] at hb
      rw [IGame.moves_right_wpow] at hb
      obtain ⟨r, hr, w, hw, rfl⟩ := hb
      rw [IGame.moves_right_ofSets] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      have hxv := (mem_rightPrefixes_iff.mp hv).2
      have hrreal : (0 : ℝ) < r.toRat := by exact_mod_cast (show (0 : Dyadic) < r from hr)
      have hrpos : (0 : ℝ) < r.toRat / 2 := by positivity
      have ht := wpow_lt_mul_wpow hrpos hxv
      have hscale : ω^ x < (2 : Surreal)⁻¹ * ((r : Surreal) * ω^ v) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, Real.toSurreal_mul,
          Real.toSurreal_inv, Real.toSurreal_ratCast] using ht
      have hle := mk_le_mk.mpr hvz
      have hle' : (2 : Surreal)⁻¹ * ((r : Surreal) * ω^ v) ≤ z := by
        simpa [IGame.mulOption, mk_add, mk_sub, mk_mul, mk_wpow, mk_dyadic,
          IGame.mk_half, out_eq] using hle
      exact ⟨0, zero_mem_leftPrefixes (wpow_pos x), by simpa using hscale.le.trans hle'⟩
    · simp only [IGame.moves_right_half, Set.mem_singleton_iff] at ha
      subst a
      simp only [Player.mul_right, Player.neg_right] at hb
      rw [IGame.moves_left_wpow] at hb
      rcases hb with hb | ⟨r, hr, w, hw, rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp hb
        have hle := mk_le_mk.mpr hvz
        refine ⟨0, zero_mem_leftPrefixes (wpow_pos x), ?_⟩
        simpa [IGame.mulOption, mk_add, mk_sub, mk_mul, mk_wpow, IGame.mk_half,
          out_eq, ← he] using hle
      · rw [IGame.moves_left_ofSets] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        obtain ⟨n, hn⟩ := exists_nat_gt r
        have hrn : (r : Surreal.{u}) ≤ (n : Surreal) := by exact_mod_cast hn.le
        have hh1 : (2 : Surreal.{u})⁻¹ ≤ 1 := by norm_num
        have hr0 : (0 : Surreal.{u}) ≤ (r : Surreal) := by
          exact_mod_cast (show (0 : Dyadic) < r from hr).le
        have hcoeff := (mul_le_of_le_one_left hr0 hh1).trans hrn
        have hle := mk_le_mk.mpr hvz
        have hle' : ω^ x - ((2 : Surreal)⁻¹ * (r : Surreal)) * ω^ v ≤ z := by
          have heq : mk (IGame.mulOption ½ (ω^ g) 1 (r * ω^ v.out)) =
              ω^ x - ((2 : Surreal)⁻¹ * (r : Surreal)) * ω^ v := by
            simp only [IGame.mulOption, mk_add, mk_sub, mk_mul, mk_wpow,
              mk_dyadic, IGame.mk_half, out_eq, mk_one, ← he]
            ring
          simpa only [heq, out_eq] using hle
        have hpre : birthdayTruncation (ω^ x) ((n : Surreal) * ω^ v).birthday =
            (n : Surreal) * ω^ v := by
          obtain ⟨a, ha, rfl, hl⟩ := mem_leftPrefixes.mp hv
          exact birthdayTruncation_natCast_mul_wpow_birthdayTruncation x a hl n
        have hlt : (n : Surreal) * ω^ v < ω^ x := by
          have ht := mul_wpow_lt_wpow (n : ℝ) (mem_leftPrefixes_iff.mp hv).2
          simpa only [Real.toSurreal_natCast] using ht
        refine ⟨(n : Surreal) * ω^ v, mem_leftPrefixes_iff.mpr ⟨hpre, hlt⟩, ?_⟩
        exact (sub_le_sub_left (mul_le_mul_of_nonneg_right hcoeff (wpow_nonneg v)) _).trans hle'


/-- Halving a monomial adds one full pure-power block to its birthday. -/
theorem birthday_half_mul_wpow (x : Surreal.{u}) :
    ((2 : Surreal)⁻¹ * ω^ x).birthday =
      NatOrdinal.of ((ω^ x).birthday.val + (ω^ plusCount x).val) := by
  have hcp : 0 < plusCount (ω^ x) := by
    simpa only [plusCount_zero] using
      plusCount_lt_of_mem_leftPrefixes (zero_mem_leftPrefixes (wpow_pos x))
  have hcp' : (0 : Ordinal.{u}) < (plusCount (ω^ x)).val := by
    simpa only [NatOrdinal.val_zero] using NatOrdinal.val.strictMono hcp
  have hhalf (a : Surreal.{u}) (ha : a ∈ leftPrefixes (ω^ x)) :
      (2 : Surreal)⁻¹ * ω^ x < ω^ x - a := by
    have ht := lt_half_mul_wpow_of_mem_leftPrefixes_wpow ha
    have he : ω^ x - (2 : Surreal)⁻¹ * ω^ x = (2 : Surreal)⁻¹ * ω^ x := by ring
    rw [← he] at ht
    linarith only [ht]
  rw [← plusCount_wpow]
  apply le_antisymm
  · apply (birthday_le_iff_forall_prefixes _ _).mpr
    constructor
    · intro p hp
      rw [leftPrefixes_half_mul_wpow] at hp
      apply (birthday_lt_of_mem_leftPrefixes hp).trans_le
      exact NatOrdinal.of.monotone le_self_add
    · intro p hp
      obtain ⟨a, ha, hap⟩ := exists_wpow_sub_leftPrefix_le_of_mem_rightPrefixes_half hp
      have hneg : -p ∈ leftPrefixes (-((2 : Surreal)⁻¹ * ω^ x)) :=
        neg_mem_leftPrefixes_iff.mpr hp
      have hpb := birthday_le_of_left_between hneg (neg_le_neg hap)
        (neg_le_neg (hhalf a ha).le)
      rw [birthday_neg, birthday_neg, birthday_wpow_sub_leftPrefix ha] at hpb
      apply hpb.trans_lt
      exact NatOrdinal.of.strictMono (add_lt_add_right
        (NatOrdinal.val.strictMono (plusCount_lt_of_mem_leftPrefixes ha)) _)
  · apply NatOrdinal.val.le_iff_le.mp
    rw [NatOrdinal.val_of]
    apply (Ordinal.add_le_iff hcp'.ne').mpr
    intro d hd
    have hd' : NatOrdinal.of d < plusCount (ω^ x) := NatOrdinal.of.lt_iff_lt.mpr hd
    obtain ⟨a, ha, hda⟩ := exists_leftPrefixes_plusCount_ge hd'
    have hp : ω^ x - a ∈ rightPrefixes ((2 : Surreal)⁻¹ * ω^ x) :=
      mem_rightPrefixes_iff.mpr
        ⟨birthdayTruncation_half_mul_wpow_sub_leftPrefix ha, hhalf a ha⟩
    have hlt := birthday_lt_of_mem_rightPrefixes hp
    rw [birthday_wpow_sub_leftPrefix ha] at hlt
    have hda' : d ≤ (plusCount a).val := by
      simpa only [NatOrdinal.val_of] using NatOrdinal.val.monotone hda
    exact (add_le_add_right hda' _).trans_lt (by
      simpa only [NatOrdinal.val_of] using NatOrdinal.val.strictMono hlt)

/-- Halving a monomial appends exactly its plus-rank pure-power block of minus signs. -/
theorem half_mul_wpow_eq_appendMinuses (x : Surreal.{u}) :
    (2 : Surreal)⁻¹ * ω^ x = appendMinuses (ω^ x) (ω^ plusCount x).val := by
  have he : appendPluses (-(ω^ x)) (ω^ plusCount x).val =
      -((2 : Surreal)⁻¹ * ω^ x) := by
    apply (appendPluses_eq_iff _ _ _).mpr
    constructor
    · rw [birthday_neg, birthday_neg, birthday_half_mul_wpow]
    · rw [rightPrefixes_neg, rightPrefixes_neg, leftPrefixes_half_mul_wpow]
  rw [appendMinuses_eq_neg, he, neg_neg]


end Surreal
