/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.DyadicCoefficient

/-!
# Reciprocal-power monomial coefficients

The coefficient cuts use the native dyadic embedding into actual numeric games.
-/

universe u
public noncomputable section

namespace Dyadic

/-- A dyadic with numerator one is the reciprocal of its denominator. -/
theorem toRat_eq_one_div_den_of_num_eq_one {r : Dyadic} (hr : r.num = 1) :
    r.toRat = 1 / (r.den : ℚ) := by
  rw [← Rat.num_div_den r.toRat]
  simp only [show r.toRat.num = 1 from hr, Int.cast_one]

/-- Dyadics with numerator one are positive. -/
theorem pos_of_num_eq_one {r : Dyadic} (hr : r.num = 1) : 0 < r := by
  rw [← coe_lt_coe, coe_zero, toRat_eq_one_div_den_of_num_eq_one hr]
  positivity

/-- Dyadics with numerator one are at most one. -/
theorem le_one_of_num_eq_one {r : Dyadic} (hr : r.num = 1) : r ≤ 1 := by
  rw [← coe_le_coe, coe_one, toRat_eq_one_div_den_of_num_eq_one hr]
  exact (div_le_one (by exact_mod_cast r.den_pos)).mpr (by exact_mod_cast r.one_le_den)

/-- Doubling a noninteger dyadic with numerator one preserves that numerator. -/
theorem num_add_self_eq_one_of_num_eq_one {r : Dyadic} (hr : r.num = 1)
    (hd : r.den ≠ 1) : (r + r).num = 1 := by
  obtain ⟨n, hn⟩ := r.den_mem_powers
  change 2 ^ n = r.den at hn
  cases n with
  | zero => exact False.elim (hd hn.symm)
  | succ n =>
    have he : (r + r).toRat = (1 : ℚ) / (2 ^ n : ℕ) := by
      rw [toRat_add, toRat_eq_one_div_den_of_num_eq_one hr, ← hn]
      push_cast
      rw [pow_succ]
      field_simp
      ring
    change (r + r).toRat.num = 1
    rw [he]
    simp

/-- Doubling a numerator-one dyadic removes one power of two from its denominator. -/
theorem den_add_self_eq_of_den_eq_two_pow_succ {r : Dyadic} (hr : r.num = 1)
    {n : ℕ} (hd : r.den = 2 ^ (n + 1)) : (r + r).den = 2 ^ n := by
  have he : (r + r).toRat = (1 : ℚ) / (2 ^ n : ℕ) := by
    rw [toRat_add, toRat_eq_one_div_den_of_num_eq_one hr, hd]
    push_cast
    rw [pow_succ]
    field_simp
    ring
  change (r + r).toRat.den = 2 ^ n
  rw [he]
  simp

/-- A dyadic with numerator one has zero as its lower neighbour. -/
theorem lower_eq_zero_of_num_eq_one {r : Dyadic} (hr : r.num = 1) : r.lower = 0 := by
  rw [← coe_inj, lower, coe_mkRat]
  simp [hr]

/-- A dyadic with numerator one has twice itself as its upper neighbour. -/
theorem upper_eq_add_self_of_num_eq_one {r : Dyadic} (hr : r.num = 1) :
    r.upper = r + r := by
  rw [← coe_inj, upper, coe_mkRat, coe_add]
  have he : r.toRat = 1 / (r.den : ℚ) := by
    rw [← Rat.num_div_den r.toRat]
    simp only [show r.toRat.num = 1 from hr, Int.cast_one]
  rw [Rat.mkRat_eq_div]
  rw [show r.num + 1 = 2 by omega, he]
  ring

/-- A noninteger dyadic with numerator one has exactly the cut zero versus twice itself. -/
theorem toIGame_eq_zero_add_self_of_num_eq_one {r : Dyadic}
    (hr : r.num = 1) (hd : r.den ≠ 1) :
    (r : IGame.{u}) = !{{0} | {((r + r : Dyadic) : IGame)}} := by
  rw [toIGame_of_den_ne_one hd, lower_eq_zero_of_num_eq_one hr,
    upper_eq_add_self_of_num_eq_one hr, toIGame_zero]

end Dyadic

namespace IGame

/-- Reciprocal-power monomials at fitting larger exponents are canonical prefixes. -/
theorem Fits.reciprocal_mul_wpow {x y : IGame.{u}} [Numeric x] [Numeric y]
    (h : Fits x y) (hxy : x < y) {r : Dyadic} (hr : r.num = 1) (hd : r.den ≠ 1) :
    Fits (ω^ x) ((r : IGame) * ω^ y) := by
  have hrpos := Dyadic.pos_of_num_eq_one hr
  have hqpos : 0 < r + r := add_pos hrpos hrpos
  have hdouble : ((r + r : Dyadic) : Surreal.{u}) = (r : Surreal) + (r : Surreal) := by
    push_cast
    rfl
  have hfitL {w : IGame.{u}} (hw : w ∈ yᴸ) : w < x := by
    numeric
    rw [← Surreal.mk_lt_mk, lt_iff_not_ge, Surreal.mk_le_mk]
    exact h.1 w hw
  have hfitR {w : IGame.{u}} (hw : w ∈ yᴿ) : x < w := by
    numeric
    rw [← Surreal.mk_lt_mk, lt_iff_not_ge, Surreal.mk_le_mk]
    exact h.2 w hw
  constructor
  · rw [forall_moves_mul]
    rintro (_ | _) a ha b hb
    · rw [Dyadic.toIGame_eq_zero_add_self_of_num_eq_one hr hd, moves_left_ofSets] at ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      simp only [Player.mul_left] at hb
      rw [moves_left_wpow] at hb
      rcases hb with hb | ⟨s, hs, w, hw, rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp hb
        rw [← Surreal.mk_le_mk]
        simp [mulOption]
      · numeric
        have ht := Numeric.mul_wpow_lt_wpow' (r * s) (hfitL hw)
        rw [← Surreal.mk_le_mk]
        apply not_le_of_gt
        simpa [← Surreal.mk_lt_mk, mulOption, Surreal.mk_add, Surreal.mk_sub,
          Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow, mul_assoc] using ht
    · rw [Dyadic.toIGame_eq_zero_add_self_of_num_eq_one hr hd, moves_right_ofSets] at ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      simp only [Player.mul_left] at hb
      rw [moves_right_wpow] at hb
      obtain ⟨s, hs, w, hw, rfl⟩ := hb
      numeric
      have hscale := Numeric.mul_wpow_lt_mul_wpow_of_pos' (r + r)
        (mul_pos hrpos (show 0 < s from hs)) (Numeric.lt_right hw)
      have hs' := Surreal.mk_lt_mk.mpr hscale
      simp only [Surreal.mk_mul, Surreal.mk_wpow, Surreal.mk_dyadic] at hs'
      have hpos := Surreal.mk_lt_mk.mpr (Numeric.wpow_pos x)
      simp only [Surreal.mk_zero, Surreal.mk_wpow] at hpos
      rw [← Surreal.mk_le_mk]
      apply not_le_of_gt
      simp only [mulOption, Surreal.mk_add, Surreal.mk_sub, Surreal.mk_mul,
        Surreal.mk_dyadic, Surreal.mk_wpow]
      push_cast at hs'
      rw [hdouble]
      nlinarith only [hs', hpos]
  · rw [forall_moves_mul]
    rintro (_ | _) a ha b hb
    · rw [Dyadic.toIGame_eq_zero_add_self_of_num_eq_one hr hd, moves_left_ofSets] at ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      simp only [Player.mul_right, Player.neg_left] at hb
      rw [moves_right_wpow] at hb
      obtain ⟨s, hs, w, hw, rfl⟩ := hb
      numeric
      have ht := Numeric.wpow_lt_mul_wpow' (mul_pos hrpos (show 0 < s from hs)) (hfitR hw)
      rw [← Surreal.mk_le_mk]
      apply not_le_of_gt
      simpa [← Surreal.mk_lt_mk, mulOption, Surreal.mk_add, Surreal.mk_sub,
        Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow, mul_assoc] using ht
    · rw [Dyadic.toIGame_eq_zero_add_self_of_num_eq_one hr hd, moves_right_ofSets] at ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      simp only [Player.mul_right, Player.neg_right] at hb
      rw [moves_left_wpow] at hb
      rcases hb with hb | ⟨s, hs, w, hw, rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp hb
        have ht := Numeric.wpow_lt_mul_wpow' hqpos hxy
        rw [← Surreal.mk_le_mk]
        apply not_le_of_gt
        simpa [← Surreal.mk_lt_mk, mulOption, Surreal.mk_add, Surreal.mk_sub,
          Surreal.mk_mul, Surreal.mk_dyadic, Surreal.mk_wpow] using ht
      · numeric
        have ht := Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow' 1 (r * s) hqpos
          hxy (Numeric.left_lt hw)
        have ht' := Surreal.mk_lt_mk.mpr ht
        simp only [Surreal.mk_add, Surreal.mk_mul, Surreal.mk_wpow, Surreal.mk_dyadic] at ht'
        rw [← Surreal.mk_le_mk]
        apply not_le_of_gt
        simp only [mulOption, Surreal.mk_add, Surreal.mk_sub, Surreal.mk_mul,
          Surreal.mk_dyadic, Surreal.mk_wpow]
        push_cast at ht'
        rw [hdouble]
        nlinarith only [ht']

end IGame

namespace Surreal
open Set IGame

private theorem realCast_inv_two_pow (n : ℕ) :
    Real.toSurreal ((2 : ℝ)⁻¹ ^ n) = (2 : Surreal.{u})⁻¹ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.toSurreal_mul, ih, Real.toSurreal_inv]
    norm_num only [Real.toSurreal_ofNat]
    rw [pow_succ]

/-- Canonical left prefixes of a reciprocal-power monomial are bounded by lower monomials. -/
theorem exists_natCast_mul_wpow_ge_of_mem_leftPrefixes_reciprocal
    {r : Dyadic} (hnum : r.num = 1) (hd : r.den ≠ 1) {x z : Surreal.{u}}
    (hz : z ∈ leftPrefixes ((r : Surreal) * ω^ x)) : z = 0 ∨
      ∃ v ∈ leftPrefixes x, ∃ n : ℕ, z ≤ (n : Surreal) * ω^ v := by
  have he := ofSets_eq_mk (s := leftPrefixes x) (t := rightPrefixes x)
    (H := leftPrefixes_lt_rightPrefixes x)
  generalize_proofs at he
  rw [ofSets_leftPrefixes_rightPrefixes] at he
  let g : IGame.{u} := !{out '' leftPrefixes x | out '' rightPrefixes x}
  have : IGame.Numeric g := by assumption
  change x = mk g at he
  have hh : mk ((r : IGame) * ω^ g) = (r : Surreal) * ω^ x := by
    rw [mk_mul, mk_dyadic, mk_wpow, ← he]
  have hpos : (0 : Surreal.{u}) < (r : Surreal) * ω^ x :=
    mul_pos (by exact_mod_cast Dyadic.pos_of_num_eq_one hnum) (wpow_pos x)
  have hzb := birthday_lt_of_mem_leftPrefixes hz
  have hzx := (mem_leftPrefixes_iff.mp hz).2
  have hn : ¬ IGame.Fits z.out ((r : IGame) * ω^ g) := by
    intro h
    have hb := h.surrealBirthday_le
    exact hzb.not_ge (by simpa only [hh, out_eq] using hb)
  rw [IGame.not_fits_iff] at hn
  rcases hn with ⟨v, hv, hzv⟩ | ⟨v, hv, hvz⟩
  · have hm : ∃ v ∈ ((r : IGame) * ω^ g)ᴸ, z.out ≤ v := ⟨v, hv, hzv⟩
    rw [IGame.exists_moves_mul] at hm
    rcases hm with ⟨p, a, ha, b, hb, hzv⟩
    cases p
    · rw [Dyadic.toIGame_eq_zero_add_self_of_num_eq_one hnum hd,
        IGame.moves_left_ofSets] at ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      simp only [Player.mul_left] at hb
      rw [IGame.moves_left_wpow] at hb
      rcases hb with hb | ⟨s, hr, w, hw, rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp hb
        have hle := mk_le_mk.mpr hzv
        have hz0 : z ≤ 0 := by simpa [IGame.mulOption, mk_add, mk_sub, mk_mul] using hle
        exact Or.inl (hz0.antisymm (nonneg_of_mem_leftPrefixes hpos hz))
      · rw [IGame.moves_left_ofSets] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        have hle := mk_le_mk.mpr hzv
        have hzv' : z ≤ ((r : Surreal) * (s : Surreal)) * ω^ v := by
          simpa [IGame.mulOption, mk_add, mk_sub, mk_mul, mk_wpow, mk_dyadic,
            mk_dyadic, out_eq, mul_assoc] using hle
        obtain ⟨n, hn⟩ := exists_nat_gt s
        have hrn : (s : Surreal.{u}) ≤ (n : Surreal) := by exact_mod_cast hn.le
        have hh1 : (r : Surreal.{u}) ≤ 1 := by
          exact_mod_cast Dyadic.le_one_of_num_eq_one hnum
        have hle' : (r : Surreal.{u}) * (s : Surreal) ≤ (n : Surreal) :=
          (mul_le_of_le_one_left
            (by exact_mod_cast (show (0 : Dyadic) < s from hr).le) hh1).trans hrn
        exact Or.inr ⟨v, hv, n,
          hzv'.trans (mul_le_mul_of_nonneg_right hle' (wpow_nonneg v))⟩
    · rw [Dyadic.toIGame_eq_zero_add_self_of_num_eq_one hnum hd,
        IGame.moves_right_ofSets] at ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      simp only [Player.mul_left] at hb
      rw [IGame.moves_right_wpow] at hb
      obtain ⟨s, hr, w, hw, rfl⟩ := hb
      rw [IGame.moves_right_ofSets] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      have hxv := (mem_rightPrefixes_iff.mp hv).2
      have hscale : ((r + r : Dyadic) : Surreal) * ω^ x <
          (r : Surreal) * ((s : Surreal) * ω^ v) := by
        have hrreal : (0 : ℝ) < s.toRat := by
          exact_mod_cast (show (0 : Dyadic) < s from hr)
        have hrreal2 : (0 : ℝ) < r.toRat := by
          exact_mod_cast Dyadic.pos_of_num_eq_one hnum
        have hrpos : (0 : ℝ) < s.toRat * r.toRat := by positivity
        have ht := mul_wpow_lt_mul_wpow_of_pos
          (((r + r : Dyadic) : ℚ) : ℝ) hrpos hxv
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, Real.toSurreal_mul,
          Real.toSurreal_inv, Real.toSurreal_ratCast] using ht
      have hle := mk_le_mk.mpr hzv
      have hzneg : z < 0 := by
        have ht : mk (IGame.mulOption (r : IGame) (ω^ g)
            ((r + r : Dyadic) : IGame) (s * ω^ v.out)) < 0 := by
          simp only [IGame.mulOption, mk_add, mk_sub, mk_mul, mk_wpow,
            mk_dyadic, out_eq, ← he]
          have hdouble : ((r + r : Dyadic) : Surreal.{u}) =
              (r : Surreal) + (r : Surreal) := by push_cast; rfl
          rw [hdouble] at hscale ⊢
          nlinarith only [hscale]
        exact lt_of_le_of_lt (by simpa only [out_eq] using hle) ht
      exact False.elim ((nonneg_of_mem_leftPrefixes hpos hz).not_gt hzneg)
  · have ht := mk_lt_mk.mpr ((IGame.Numeric.lt_right hv).trans_le hvz)
    have ht' : (r : Surreal) * ω^ x < z := by simpa only [hh, out_eq] using ht
    exact False.elim (hzx.not_gt ht')



/-- Every left prefix of a monomial lies below every positive reciprocal-power coefficient. -/
theorem lt_reciprocal_mul_wpow_of_mem_leftPrefixes {r : Dyadic} (hr : r.num = 1)
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) : a < (r : Surreal) * ω^ x := by
  obtain rfl | ⟨v, hv, n, han⟩ := exists_natCast_mul_wpow_ge_of_mem_leftPrefixes ha
  · exact mul_pos (by exact_mod_cast Dyadic.pos_of_num_eq_one hr) (wpow_pos x)
  apply han.trans_lt
  have hrreal : (0 : ℝ) < r.toRat := by exact_mod_cast Dyadic.pos_of_num_eq_one hr
  have ht := mul_wpow_lt_mul_wpow_of_pos (n : ℝ) hrreal (mem_leftPrefixes_iff.mp hv).2
  simpa using ht

/-- Reciprocal powers of two preserve exactly the canonical left prefixes of a monomial. -/
theorem leftPrefixes_reciprocal_mul_wpow {r : Dyadic} (hr : r.num = 1)
    (x : Surreal.{u}) : leftPrefixes ((r : Surreal) * ω^ x) = leftPrefixes (ω^ x) := by
  obtain hd | hd := eq_or_ne r.den 1
  · have he : r = 1 := by
      rw [← Dyadic.intCast_num_eq_self_of_den_eq_one hd, hr]
      simp
    simp [he]
  apply Set.Subset.antisymm
  · intro z hz
    obtain rfl | ⟨v, hv, n, hzn⟩ :=
      exists_natCast_mul_wpow_ge_of_mem_leftPrefixes_reciprocal hr hd hz
    · exact zero_mem_leftPrefixes (wpow_pos x)
    have hvx := (mem_leftPrefixes_iff.mp hv).2
    have hpre : birthdayTruncation (ω^ x) ((n : Surreal) * ω^ v).birthday =
        (n : Surreal) * ω^ v := by
      obtain ⟨a, ha, rfl, hl⟩ := mem_leftPrefixes.mp hv
      exact birthdayTruncation_natCast_mul_wpow_birthdayTruncation x a hl n
    have hn : (n : Surreal.{u}) * ω^ v < (r : Surreal) * ω^ x := by
      have hh : (0 : ℝ) < r.toRat := by exact_mod_cast Dyadic.pos_of_num_eq_one hr
      have ht := mul_wpow_lt_mul_wpow_of_pos (n : ℝ) hh hvx
      simpa using ht
    have hzpre := (mem_leftPrefixes_iff.mp hz).1
    have ht := birthdayTruncation_eq_of_left_between
      (birthday_lt_of_mem_leftPrefixes hz).le (by rwa [hzpre]) hn.le
    rw [hzpre] at ht
    apply mem_leftPrefixes_iff.mpr
    refine ⟨birthdayTruncation_eq_trans hpre ht, ?_⟩
    have hh : (r : Surreal.{u}) * ω^ x ≤ ω^ x :=
      mul_le_of_le_one_left (wpow_nonneg x) (by exact_mod_cast Dyadic.le_one_of_num_eq_one hr)
    exact (mem_leftPrefixes_iff.mp hz).2.trans_le hh
  · exact leftPrefixes_subset_of_birthdayTruncation_eq
      (birthdayTruncation_dyadic_mul_wpow r (Dyadic.pos_of_num_eq_one hr) x)

/-- Reciprocal powers of two preserve the complete monomial plus count. -/
theorem plusCount_reciprocal_mul_wpow {r : Dyadic} (hr : r.num = 1)
    (x : Surreal.{u}) : plusCount ((r : Surreal) * ω^ x) = ω^ plusCount x := by
  rw [plusCount_eq_of_leftPrefixes_eq (leftPrefixes_reciprocal_mul_wpow hr x), plusCount_wpow]


/-- Reflected left prefixes at the doubled coefficient prefix a reciprocal-power monomial. -/
theorem birthdayTruncation_reciprocal_mul_wpow_sub_leftPrefix {r : Dyadic}
    (hr : r.num = 1) (hd : r.den ≠ 1) {x a : Surreal.{u}}
    (ha : a ∈ leftPrefixes (ω^ x)) :
    birthdayTruncation ((r : Surreal) * ω^ x)
      (((r + r : Dyadic) : Surreal) * ω^ x - a).birthday =
        ((r + r : Dyadic) : Surreal) * ω^ x - a := by
  have hq := Dyadic.num_add_self_eq_one_of_num_eq_one hr hd
  have hdouble : ((r + r : Dyadic) : Surreal.{u}) = (r : Surreal) + (r : Surreal) := by
    push_cast
    rfl
  have ha0 := nonneg_of_mem_leftPrefixes (wpow_pos x) ha
  have haA := (mem_leftPrefixes_iff.mp ha).2
  have hpos : 0 < (r : Surreal.{u}) * ω^ x :=
    mul_pos (by exact_mod_cast Dyadic.pos_of_num_eq_one hr) (wpow_pos x)
  have hL : ∀ z ∈ (· + -a) '' leftPrefixes (((r + r : Dyadic) : Surreal) * ω^ x) ∪
      (((r + r : Dyadic) : Surreal) * ω^ x + ·) '' leftPrefixes (-a),
      z < (r : Surreal) * ω^ x := by
    rintro z (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · rw [leftPrefixes_reciprocal_mul_wpow hq] at hp
      exact (add_le_of_nonpos_right (neg_nonpos.mpr ha0)).trans_lt
        (lt_reciprocal_mul_wpow_of_mem_leftPrefixes hr hp)
    · rw [leftPrefixes_neg] at hp
      obtain ⟨b, hb, rfl⟩ := hp
      have hbA := rightPrefixes_subset_of_birthdayTruncation_eq
        (mem_leftPrefixes_iff.mp ha).1 hb
      have hAb := (mem_rightPrefixes_iff.mp hbA).2
      have hqle : ((r + r : Dyadic) : Surreal.{u}) * ω^ x ≤ ω^ x :=
        mul_le_of_le_one_left (wpow_nonneg x)
          (by exact_mod_cast Dyadic.le_one_of_num_eq_one hq)
      have ht : ((r + r : Dyadic) : Surreal.{u}) * ω^ x - b < 0 :=
        sub_neg.mpr (hqle.trans_lt hAb)
      simpa only [sub_eq_add_neg] using ht.trans hpos
  have hR : ∀ z ∈ (· + -a) '' rightPrefixes (((r + r : Dyadic) : Surreal) * ω^ x) ∪
      (((r + r : Dyadic) : Surreal) * ω^ x + ·) '' rightPrefixes (-a),
      (r : Surreal) * ω^ x < z := by
    rintro z (⟨b, hb, rfl⟩ | ⟨p, hp, rfl⟩)
    · have hqb := (mem_rightPrefixes_iff.mp hb).2
      have ht := lt_reciprocal_mul_wpow_of_mem_leftPrefixes hr ha
      rw [hdouble, add_mul] at hqb
      change (r : Surreal) * ω^ x < b + -a
      linarith only [hqb, ht]
    · rw [rightPrefixes_neg] at hp
      obtain ⟨p, hp, rfl⟩ := hp
      have hpA := leftPrefixes_subset_of_birthdayTruncation_eq
        (mem_leftPrefixes_iff.mp ha).1 hp
      have ht := lt_reciprocal_mul_wpow_of_mem_leftPrefixes hr hpA
      rw [hdouble, add_mul]
      change (r : Surreal) * ω^ x < (r : Surreal) * ω^ x +
        (r : Surreal) * ω^ x + -p
      linarith only [ht]
  have ht := birthdayTruncation_eq_of_btwn
    (H := fun z hz w hw ↦ (hL z hz).trans (hR w hw)) hL hR
  have he := add_eq_ofSets_leftPrefixes (((r + r : Dyadic) : Surreal) * ω^ x) (-a)
  rw [← he] at ht
  simpa only [sub_eq_add_neg] using ht

/-- Reflected left prefixes have exact relative birthday at each reciprocal-power step. -/
theorem birthday_reciprocal_mul_wpow_sub_leftPrefix {r : Dyadic}
    (hr : r.num = 1) (hd : r.den ≠ 1) {x a : Surreal.{u}}
    (ha : a ∈ leftPrefixes (ω^ x)) :
    (((r + r : Dyadic) : Surreal) * ω^ x - a).birthday = NatOrdinal.of
      ((((r + r : Dyadic) : Surreal) * ω^ x).birthday.val + (plusCount a).val) := by
  let H : Surreal.{u} := -(((r + r : Dyadic) : Surreal) * ω^ x)
  let t : Surreal.{u} := -((r : Surreal) * ω^ x)
  have hq := Dyadic.num_add_self_eq_one_of_num_eq_one hr hd
  have hR : rightPrefixes t = rightPrefixes H := by
    dsimp only [t, H]
    rw [rightPrefixes_neg, rightPrefixes_neg, leftPrefixes_reciprocal_mul_wpow hr,
      leftPrefixes_reciprocal_mul_wpow hq]
  have hP : ∀ y ∈ leftPrefixes (ω^ x),
      birthdayTruncation t (H + y).birthday = H + y := by
    intro y hy
    have ht := birthdayTruncation_neg_of_eq
      (birthdayTruncation_reciprocal_mul_wpow_sub_leftPrefix hr hd hy)
    have he : -(((r + r : Dyadic) : Surreal) * ω^ x - y) = H + y := by
      dsimp only [H]
      ring
    rw [← birthday_neg (((r + r : Dyadic) : Surreal) * ω^ x - y), he] at ht
    exact ht
  have hB : ∀ y ∈ leftPrefixes (ω^ x), H + y ≤ t := by
    intro y hy
    have ht := lt_reciprocal_mul_wpow_of_mem_leftPrefixes hr hy
    have hdouble : ((r + r : Dyadic) : Surreal.{u}) = (r : Surreal) + (r : Surreal) := by
      push_cast
      rfl
    dsimp only [H, t]
    rw [hdouble, add_mul]
    linarith only [ht]
  have hSupport : H.support ⊆ Ici x := by
    have he : H = (SurrealHahnSeries.single x (-((r + r : Dyadic).toRat : ℝ))).toSurreal := by
      rw [SurrealHahnSeries.toSurreal_single, Real.toSurreal_neg,
        Real.toSurreal_ratCast, neg_mul]
    rw [he, SurrealHahnSeries.support_toSurreal]
    intro z hz
    have hez : z = x := Set.mem_singleton_iff.mp (SurrealHahnSeries.support_single_subset hz)
    rw [hez]
    change x ≤ x
    exact le_rfl
  have hG : ∀ y ∈ leftPrefixes (ω^ x), ∀ p ∈ leftPrefixes H, p + y ≤ H :=
    fun _ hy _ hp ↦ (add_lt_of_mem_leftPrefixes_wpow_of_support hSupport hy hp).le
  have ht := birthday_add_left_prefix_eq_of_prefix_family (wpow_pos x) hR hP hB hG ha
  have he : H + a = -(((r + r : Dyadic) : Surreal) * ω^ x - a) := by
    dsimp only [H]
    ring
  rw [he, birthday_neg] at ht
  simpa only [H, birthday_neg] using ht

/-- Every canonical right prefix of a reciprocal-power monomial bounds a reflected left prefix. -/
theorem exists_reciprocal_mul_wpow_sub_leftPrefix_le_of_mem_rightPrefixes
    {r : Dyadic} (hnum : r.num = 1) (hd : r.den ≠ 1) {x z : Surreal.{u}}
    (hz : z ∈ rightPrefixes ((r : Surreal) * ω^ x)) :
    ∃ a ∈ leftPrefixes (ω^ x), ((r + r : Dyadic) : Surreal) * ω^ x - a ≤ z := by
  have he := ofSets_eq_mk (s := leftPrefixes x) (t := rightPrefixes x)
    (H := leftPrefixes_lt_rightPrefixes x)
  generalize_proofs at he
  rw [ofSets_leftPrefixes_rightPrefixes] at he
  let g : IGame.{u} := !{out '' leftPrefixes x | out '' rightPrefixes x}
  have : IGame.Numeric g := by assumption
  change x = mk g at he
  have hh : mk ((r : IGame) * ω^ g) = (r : Surreal) * ω^ x := by
    rw [mk_mul, mk_dyadic, mk_wpow, ← he]
  have hzb := birthday_lt_of_mem_rightPrefixes hz
  have hzx := (mem_rightPrefixes_iff.mp hz).2
  have hn : ¬ IGame.Fits z.out ((r : IGame) * ω^ g) := by
    intro h
    have hb := h.surrealBirthday_le
    exact hzb.not_ge (by simpa only [hh, out_eq] using hb)
  rw [IGame.not_fits_iff] at hn
  rcases hn with ⟨v, hv, hzv⟩ | ⟨v, hv, hvz⟩
  · numeric
    have ht := mk_lt_mk.mpr (hzv.trans_lt (IGame.Numeric.left_lt hv))
    have ht' : z < (r : Surreal) * ω^ x := by simpa only [hh, out_eq] using ht
    exact False.elim (hzx.not_gt ht')
  · have hm : ∃ v ∈ ((r : IGame) * ω^ g)ᴿ, v ≤ z.out := ⟨v, hv, hvz⟩
    rw [IGame.exists_moves_mul] at hm
    rcases hm with ⟨p, a, ha, b, hb, hvz⟩
    cases p
    · rw [Dyadic.toIGame_eq_zero_add_self_of_num_eq_one hnum hd,
        IGame.moves_left_ofSets] at ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      simp only [Player.mul_right, Player.neg_left] at hb
      rw [IGame.moves_right_wpow] at hb
      obtain ⟨s, hr, w, hw, rfl⟩ := hb
      rw [IGame.moves_right_ofSets] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      have hxv := (mem_rightPrefixes_iff.mp hv).2
      have hrreal : (0 : ℝ) < s.toRat := by exact_mod_cast (show (0 : Dyadic) < s from hr)
      have hrreal2 : (0 : ℝ) < r.toRat := by
        exact_mod_cast Dyadic.pos_of_num_eq_one hnum
      have hrpos : (0 : ℝ) < s.toRat * r.toRat := by positivity
      have ht := mul_wpow_lt_mul_wpow_of_pos
        (((r + r : Dyadic) : ℚ) : ℝ) hrpos hxv
      have hscale : ((r + r : Dyadic) : Surreal) * ω^ x <
          (r : Surreal) * ((s : Surreal) * ω^ v) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, Real.toSurreal_mul,
          Real.toSurreal_inv, Real.toSurreal_ratCast] using ht
      have hle := mk_le_mk.mpr hvz
      have hle' : (r : Surreal) * ((s : Surreal) * ω^ v) ≤ z := by
        simpa [IGame.mulOption, mk_add, mk_sub, mk_mul, mk_wpow, mk_dyadic,
          mk_dyadic, out_eq] using hle
      exact ⟨0, zero_mem_leftPrefixes (wpow_pos x), by simpa using hscale.le.trans hle'⟩
    · rw [Dyadic.toIGame_eq_zero_add_self_of_num_eq_one hnum hd,
        IGame.moves_right_ofSets] at ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      simp only [Player.mul_right, Player.neg_right] at hb
      rw [IGame.moves_left_wpow] at hb
      rcases hb with hb | ⟨s, hr, w, hw, rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp hb
        have hle := mk_le_mk.mpr hvz
        refine ⟨0, zero_mem_leftPrefixes (wpow_pos x), ?_⟩
        simpa [IGame.mulOption, mk_add, mk_sub, mk_mul, mk_wpow, mk_dyadic,
          out_eq, ← he] using hle
      · rw [IGame.moves_left_ofSets] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        obtain ⟨n, hn⟩ := exists_nat_gt s
        have hrn : (s : Surreal.{u}) ≤ (n : Surreal) := by exact_mod_cast hn.le
        have hh1 : (r : Surreal.{u}) ≤ 1 := by
          exact_mod_cast Dyadic.le_one_of_num_eq_one hnum
        have hr0 : (0 : Surreal.{u}) ≤ (s : Surreal) := by
          exact_mod_cast (show (0 : Dyadic) < s from hr).le
        have hcoeff := (mul_le_of_le_one_left hr0 hh1).trans hrn
        have hle := mk_le_mk.mpr hvz
        have hle' : ((r + r : Dyadic) : Surreal) * ω^ x -
            ((r : Surreal) * (s : Surreal)) * ω^ v ≤ z := by
          have heq : mk (IGame.mulOption (r : IGame) (ω^ g)
              ((r + r : Dyadic) : IGame) (s * ω^ v.out)) =
              ((r + r : Dyadic) : Surreal) * ω^ x -
                ((r : Surreal) * (s : Surreal)) * ω^ v := by
            simp only [IGame.mulOption, mk_add, mk_sub, mk_mul, mk_wpow,
              mk_dyadic, mk_dyadic, out_eq, ← he]
            have hdouble : ((r + r : Dyadic) : Surreal.{u}) =
                (r : Surreal) + (r : Surreal) := by push_cast; rfl
            rw [hdouble]
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
theorem birthday_reciprocal_mul_wpow_step {r : Dyadic}
    (hr : r.num = 1) (hd : r.den ≠ 1) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).birthday =
      NatOrdinal.of ((((r + r : Dyadic) : Surreal) * ω^ x).birthday.val +
        (ω^ plusCount x).val) := by
  have hcp : 0 < plusCount (ω^ x) := by
    simpa only [plusCount_zero] using
      plusCount_lt_of_mem_leftPrefixes (zero_mem_leftPrefixes (wpow_pos x))
  have hcp' : (0 : Ordinal.{u}) < (plusCount (ω^ x)).val := by
    simpa only [NatOrdinal.val_zero] using NatOrdinal.val.strictMono hcp
  have hhalf (a : Surreal.{u}) (ha : a ∈ leftPrefixes (ω^ x)) :
      (r : Surreal) * ω^ x < ((r + r : Dyadic) : Surreal) * ω^ x - a := by
    have ht := lt_reciprocal_mul_wpow_of_mem_leftPrefixes hr ha
    have he : ((r + r : Dyadic) : Surreal.{u}) = (r : Surreal) + (r : Surreal) := by
      push_cast
      rfl
    rw [he, add_mul]
    linarith only [ht]
  rw [← plusCount_wpow]
  apply le_antisymm
  · apply (birthday_le_iff_forall_prefixes _ _).mpr
    constructor
    · intro p hp
      rw [leftPrefixes_reciprocal_mul_wpow hr] at hp
      have hpre := birthdayTruncation_dyadic_mul_wpow (r + r)
        (Dyadic.pos_of_num_eq_one (Dyadic.num_add_self_eq_one_of_num_eq_one hr hd)) x
      have hb := birthday_birthdayTruncation_le_birthday
        (((r + r : Dyadic) : Surreal) * ω^ x) (ω^ x).birthday
      rw [hpre] at hb
      apply (birthday_lt_of_mem_leftPrefixes hp).trans_le
      exact hb.trans (NatOrdinal.of.monotone le_self_add)
    · intro p hp
      obtain ⟨a, ha, hap⟩ :=
        exists_reciprocal_mul_wpow_sub_leftPrefix_le_of_mem_rightPrefixes hr hd hp
      have hneg : -p ∈ leftPrefixes (-((r : Surreal) * ω^ x)) :=
        neg_mem_leftPrefixes_iff.mpr hp
      have hpb := birthday_le_of_left_between hneg (neg_le_neg hap)
        (neg_le_neg (hhalf a ha).le)
      rw [birthday_neg, birthday_neg, birthday_reciprocal_mul_wpow_sub_leftPrefix hr hd ha] at hpb
      apply hpb.trans_lt
      exact NatOrdinal.of.strictMono (add_lt_add_right
        (NatOrdinal.val.strictMono (plusCount_lt_of_mem_leftPrefixes ha)) _)
  · apply NatOrdinal.val.le_iff_le.mp
    rw [NatOrdinal.val_of]
    apply (Ordinal.add_le_iff hcp'.ne').mpr
    intro d ho
    have hd' : NatOrdinal.of d < plusCount (ω^ x) := NatOrdinal.of.lt_iff_lt.mpr ho
    obtain ⟨a, ha, hda⟩ := exists_leftPrefixes_plusCount_ge hd'
    have hp : ((r + r : Dyadic) : Surreal) * ω^ x - a ∈ rightPrefixes ((r : Surreal) * ω^ x) :=
      mem_rightPrefixes_iff.mpr
        ⟨birthdayTruncation_reciprocal_mul_wpow_sub_leftPrefix hr hd ha, hhalf a ha⟩
    have hlt := birthday_lt_of_mem_rightPrefixes hp
    rw [birthday_reciprocal_mul_wpow_sub_leftPrefix hr hd ha] at hlt
    have hda' : d ≤ (plusCount a).val := by
      simpa only [NatOrdinal.val_of] using NatOrdinal.val.monotone hda
    exact (add_le_add_right hda' _).trans_lt (by
      simpa only [NatOrdinal.val_of] using NatOrdinal.val.strictMono hlt)

/-- A reciprocal-power step appends one exact pure-power block of minus signs. -/
theorem reciprocal_mul_wpow_eq_appendMinuses_step {r : Dyadic}
    (hr : r.num = 1) (hd : r.den ≠ 1) (x : Surreal.{u}) :
    (r : Surreal) * ω^ x =
      appendMinuses (((r + r : Dyadic) : Surreal) * ω^ x) (ω^ plusCount x).val := by
  have hq := Dyadic.num_add_self_eq_one_of_num_eq_one hr hd
  have he : appendPluses (-(((r + r : Dyadic) : Surreal) * ω^ x))
      (ω^ plusCount x).val = -((r : Surreal) * ω^ x) := by
    apply (appendPluses_eq_iff _ _ _).mpr
    constructor
    · rw [birthday_neg, birthday_neg, birthday_reciprocal_mul_wpow_step hr hd]
    · rw [rightPrefixes_neg, rightPrefixes_neg, leftPrefixes_reciprocal_mul_wpow hr,
        leftPrefixes_reciprocal_mul_wpow hq]
  rw [appendMinuses_eq_neg, he, neg_neg]

/-- Reciprocal powers of two have exact finite-block monomial birthdays. -/
theorem birthday_reciprocal_mul_wpow {r : Dyadic} (hr : r.num = 1) {n : ℕ}
    (hd : r.den = 2 ^ n) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal)) := by
  induction n generalizing r with
  | zero =>
    have hd1 : r.den = 1 := by simpa using hd
    have he : r = 1 := by
      rw [← Dyadic.intCast_num_eq_self_of_den_eq_one hd1, hr]
      simp
    simp [he]
  | succ n ih =>
    have hd1 : r.den ≠ 1 := by
      rw [hd, pow_succ]
      have hp : 0 < 2 ^ n := by positivity
      omega
    rw [birthday_reciprocal_mul_wpow_step hr hd1,
      ih (Dyadic.num_add_self_eq_one_of_num_eq_one hr hd1)
        (Dyadic.den_add_self_eq_of_den_eq_two_pow_succ hr hd), NatOrdinal.val_of]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc]

/-- Every reciprocal power of two appends its exact finite sequence of minus blocks. -/
theorem reciprocal_mul_wpow_eq_appendMinuses {r : Dyadic} (hr : r.num = 1) {n : ℕ}
    (hd : r.den = 2 ^ n) (x : Surreal.{u}) :
    (r : Surreal) * ω^ x = appendMinuses (ω^ x) ((ω^ plusCount x).val * (n : Ordinal)) := by
  have he : appendPluses (-(ω^ x)) ((ω^ plusCount x).val * (n : Ordinal)) =
      -((r : Surreal) * ω^ x) := by
    apply (appendPluses_eq_iff _ _ _).mpr
    constructor
    · rw [birthday_neg, birthday_neg, birthday_reciprocal_mul_wpow hr hd]
    · rw [rightPrefixes_neg, rightPrefixes_neg, leftPrefixes_reciprocal_mul_wpow hr]
  rw [appendMinuses_eq_neg, he, neg_neg]


/-- Inverse powers of two append exactly the corresponding number of minus blocks. -/
theorem inv_two_pow_mul_wpow_eq_appendMinuses (n : ℕ) (x : Surreal.{u}) :
    (2 : Surreal)⁻¹ ^ n * ω^ x =
      appendMinuses (ω^ x) ((ω^ plusCount x).val * (n : Ordinal)) := by
  let r : Dyadic := Dyadic.mkRat 1 (show 2 ^ n ∈ Submonoid.powers 2 from ⟨n, rfl⟩)
  have hr : r.num = 1 := by
    change r.toRat.num = 1
    simp [r, Dyadic.coe_mkRat, Rat.mkRat_eq_div]
  have hd : r.den = 2 ^ n := by
    change r.toRat.den = 2 ^ n
    simp [r, Dyadic.coe_mkRat, Rat.mkRat_eq_div]
  have hval : (r : Surreal.{u}) = (2 : Surreal)⁻¹ ^ n := by
    simp [r, Dyadic.coe_mkRat, Rat.mkRat_eq_div, div_eq_mul_inv, inv_pow]
  rw [← hval]
  exact reciprocal_mul_wpow_eq_appendMinuses hr hd x

/-- The exact birthday of every reciprocal-power-of-two monomial. -/
theorem birthday_inv_two_pow_mul_wpow (n : ℕ) (x : Surreal.{u}) :
    ((2 : Surreal)⁻¹ ^ n * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal)) := by
  rw [inv_two_pow_mul_wpow_eq_appendMinuses, birthday_appendMinuses]

/-- Reciprocal-power coefficients at a fitting larger cut remain canonical prefixes. -/
theorem birthdayTruncation_reciprocal_mul_wpow_eq_of_btwn {s t : Set Surreal.{u}}
    [Small.{u} s] [Small.{u} t] {H : ∀ a ∈ s, ∀ b ∈ t, a < b} {x : Surreal.{u}}
    (hL : ∀ z ∈ s, z < x) (hR : ∀ z ∈ t, x < z) (hx : x < (!{s | t}'H)) {r : Dyadic}
    (hr : r.num = 1) (hd : r.den ≠ 1) :
    birthdayTruncation (ω^ x) ((r : Surreal) * ω^ (!{s | t}'H)).birthday =
      (r : Surreal) * ω^ (!{s | t}'H) := by
  rw [ofSets_eq_mk] at hx ⊢
  generalize_proofs hn at hx ⊢
  have hf : Fits x.out !{out '' s | out '' t} := by
    constructor
    · intro z hz
      rw [moves_left_ofSets] at hz
      obtain ⟨z, hz, rfl⟩ := hz
      rw [← mk_le_mk, out_eq, out_eq]
      exact (hL z hz).not_ge
    · intro z hz
      rw [moves_right_ofSets] at hz
      obtain ⟨z, hz, rfl⟩ := hz
      rw [← mk_le_mk, out_eq, out_eq]
      exact (hR z hz).not_ge
  have hx' : x.out < !{out '' s | out '' t} := by
    rw [← mk_lt_mk, out_eq]
    exact hx
  have ht := (hf.reciprocal_mul_wpow hx' hr hd).birthdayTruncation_eq
  simpa only [mk_mul, mk_dyadic, mk_wpow, out_eq] using ht

/-- Natural multiples at canonical left exponents are canonical omega-map prefixes. -/
theorem birthdayTruncation_reciprocal_mul_wpow_birthdayTruncation (x : Surreal.{u})
    (a : NatOrdinal.{u}) (ha : x < birthdayTruncation x a) {r : Dyadic}
    (hr : r.num = 1) (hd : r.den ≠ 1) :
    birthdayTruncation (ω^ x) ((r : Surreal) * ω^ birthdayTruncation x a).birthday =
      (r : Surreal) * ω^ birthdayTruncation x a := by
  rw [birthdayTruncation_eq_ofSets x a] at ha ⊢
  exact birthdayTruncation_reciprocal_mul_wpow_eq_of_btwn
    (s := {z : Surreal | z.birthday < a ∧ z < x})
    (t := {z : Surreal | z.birthday < a ∧ x < z})
    (H := fun _ hz _ hw ↦ hz.2.trans hw.2)
    (fun _ hz ↦ hz.2) (fun _ hz ↦ hz.2) ha hr hd


/-- Inverse powers of two at canonical right exponent prefixes remain canonical prefixes. -/
theorem birthdayTruncation_inv_two_pow_mul_wpow_birthdayTruncation (x : Surreal.{u})
    (a : NatOrdinal.{u}) (ha : x < birthdayTruncation x a) (n : ℕ) :
    birthdayTruncation (ω^ x)
      ((2 : Surreal)⁻¹ ^ n * ω^ birthdayTruncation x a).birthday =
        (2 : Surreal)⁻¹ ^ n * ω^ birthdayTruncation x a := by
  cases n with
  | zero =>
    simpa only [pow_zero, one_mul] using birthdayTruncation_wpow_birthdayTruncation x a
  | succ n =>
    let r : Dyadic := Dyadic.mkRat 1
      (show 2 ^ (n + 1) ∈ Submonoid.powers 2 from ⟨n + 1, rfl⟩)
    have hr : r.num = 1 := by
      change r.toRat.num = 1
      simp [r, Dyadic.coe_mkRat, Rat.mkRat_eq_div]
    have hd : r.den = 2 ^ (n + 1) := by
      change r.toRat.den = 2 ^ (n + 1)
      simp [r, Dyadic.coe_mkRat, Rat.mkRat_eq_div]
    have hd1 : r.den ≠ 1 := by
      rw [hd, pow_succ]
      have hp : 0 < 2 ^ n := by positivity
      omega
    have hval : (r : Surreal.{u}) = (2 : Surreal)⁻¹ ^ (n + 1) := by
      simp [r, Dyadic.coe_mkRat, Rat.mkRat_eq_div, div_eq_mul_inv, inv_pow]
    rw [← hval]
    exact birthdayTruncation_reciprocal_mul_wpow_birthdayTruncation x a ha hr hd1

/-- The omega cut has canonical reciprocal-power right options at every right exponent prefix. -/
theorem inv_two_pow_mul_wpow_mem_rightPrefixes {x v : Surreal.{u}}
    (hv : v ∈ rightPrefixes x) (n : ℕ) :
    (2 : Surreal)⁻¹ ^ n * ω^ v ∈ rightPrefixes (ω^ x) := by
  obtain ⟨a, ha, rfl, hxv⟩ := mem_rightPrefixes.mp hv
  apply mem_rightPrefixes_iff.mpr
  refine ⟨birthdayTruncation_inv_two_pow_mul_wpow_birthdayTruncation x a hxv n, ?_⟩
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have ht := wpow_lt_mul_wpow hr hxv
  have hm := realCast_inv_two_pow.{u} n
  rw [hm] at ht
  exact ht


/-- Canonical right prefixes of the omega-map bound a reciprocal-power canonical family. -/
theorem exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes {x z : Surreal.{u}}
    (hz : z ∈ rightPrefixes (ω^ x)) :
    ∃ v ∈ rightPrefixes x, ∃ n : ℕ, (2 : Surreal)⁻¹ ^ n * ω^ v ≤ z := by
  have he := ofSets_eq_mk (s := leftPrefixes x) (t := rightPrefixes x)
    (H := leftPrefixes_lt_rightPrefixes x)
  generalize_proofs at he
  rw [ofSets_leftPrefixes_rightPrefixes] at he
  let g : IGame.{u} := !{out '' leftPrefixes x | out '' rightPrefixes x}
  have : IGame.Numeric g := by assumption
  change x = mk g at he
  have hwp : mk (ω^ g) = ω^ x := by rw [mk_wpow, ← he]
  have hzb := birthday_lt_of_mem_rightPrefixes hz
  have hzx := (mem_rightPrefixes_iff.mp hz).2
  have hn : ¬ Fits z.out (ω^ g) := by
    intro h
    have hb := h.surrealBirthday_le
    exact hzb.not_ge (by simpa only [hwp, out_eq] using hb)
  rw [not_fits_iff] at hn
  rcases hn with ⟨v, hv, hzv⟩ | ⟨v, hv, hvz⟩
  · numeric
    have ht := mk_lt_mk.mpr (hzv.trans_lt (Numeric.left_lt hv))
    have ht' : z < ω^ x := by simpa only [hwp, out_eq] using ht
    exact False.elim (hzx.not_gt ht')
  · rw [moves_right_wpow] at hv
    obtain ⟨r, hr, w, hw, rfl⟩ := hv
    rw [moves_right_ofSets] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hrpos : (0 : ℝ) < r.toRat := by exact_mod_cast (show (0 : Dyadic) < r from hr)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hrpos (show (2 : ℝ)⁻¹ < 1 by norm_num)
    have hcoeff : (2 : Surreal.{u})⁻¹ ^ n ≤ (r : Surreal) := by
      have ht := Real.toSurreal_le_iff.mpr hn.le
      simpa only [realCast_inv_two_pow, Real.toSurreal_ratCast] using ht
    have hle : (r : Surreal) * ω^ v ≤ z := by
      simpa only [mk_mul, mk_wpow, mk_dyadic, out_eq] using mk_le_mk.mpr hvz
    exact ⟨v, hv, n, (mul_le_mul_of_nonneg_right hcoeff (wpow_nonneg v)).trans hle⟩


end Surreal
