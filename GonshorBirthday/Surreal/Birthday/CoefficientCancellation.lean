/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Head
public import GonshorBirthday.Surreal.Birthday.Addition

import GonshorBirthday.Surreal.HahnSeries.BirthdayAdd
import GonshorBirthday.Surreal.Birthday.SupportGap
import GonshorBirthday.Surreal.Birthday.CoefficientBlock

/-!
# Rounding two summands at a dyadic coefficient

If a sum ends on a dyadic grid, round one coefficient down and the other up on that
grid. The two prefixes still give the same sum. At equality in the plus-count bound,
both prefixes must therefore be the original summands.
-/

universe u

public noncomputable section

namespace Surreal

/-- A dyadic remains a canonical prefix throughout its open real option interval. -/
theorem birthdayTruncation_real_eq_dyadic_of_lower_upper (r : ℝ) (q : Dyadic)
    (hl : (q.lower.toRat : ℝ) < r) (hu : r < (q.upper.toRat : ℝ)) :
    birthdayTruncation (r : Surreal.{u}) (q : Surreal).birthday = (q : Surreal) := by
  have hf : IGame.Fits (r : IGame.{u}) (q : IGame) := by
    constructor
    · intro z hz
      rw [Dyadic.eq_lower_of_mem_moves_left_toIGame hz, ← mk_le_mk,
        mk_real_toIGame, mk_dyadic]
      have h := Real.toSurreal_lt_iff.mpr hl
      simpa only [Real.toSurreal_ratCast] using h.not_ge
    · intro z hz
      rw [Dyadic.eq_upper_of_mem_moves_right_toIGame hz, ← mk_le_mk,
        mk_real_toIGame, mk_dyadic]
      have h := Real.toSurreal_lt_iff.mpr hu
      simpa only [Real.toSurreal_ratCast] using h.not_ge
  simpa only [mk_real_toIGame, mk_dyadic] using hf.birthdayTruncation_eq

/-- At the mesh of a dyadic sum, rounding the first real down and the second up
gives sign prefixes on that same mesh with exactly the original sum. -/
theorem exists_dyadic_prefixes_add_eq (r t : ℝ) (q : Dyadic) (hs : r + t = q.toRat) :
    ∃ u v : Dyadic, u.den ≤ q.den ∧ v.den ≤ q.den ∧ u + v = q ∧
      birthdayTruncation (r : Surreal.{u}) (u : Surreal).birthday = u ∧
      birthdayTruncation (t : Surreal.{u}) (v : Surreal).birthday = v := by
  let m := ⌊r * q.den⌋
  let u := Dyadic.mkRat m q.den_mem_powers
  let v := q - u
  have hd : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hu : u.den ≤ q.den := by
    change (Dyadic.mkRat m q.den_mem_powers).toRat.den ≤ q.den
    rw [Dyadic.coe_mkRat]
    exact Dyadic.den_mkRat_le _ q.den_ne_zero
  have hv : v.den ≤ q.den := by
    simpa only [v, sub_eq_add_neg, add_comm q] using
      Dyadic.den_add_le_den_right (x := -u) (y := q) (by simpa using hu)
  have hur : (u.toRat : ℝ) = (m : ℝ) / q.den := by
    simp only [u, Dyadic.coe_mkRat, Rat.mkRat_eq_div, Rat.cast_div, Rat.cast_intCast,
      Rat.cast_natCast]
  have hvr : (v.toRat : ℝ) = (q.toRat : ℝ) - (u.toRat : ℝ) := by
    simp only [v, Dyadic.toRat_sub, Rat.cast_sub]
  have hlo : (u.toRat : ℝ) ≤ r := by
    rw [hur, div_le_iff₀ hd]
    exact Int.floor_le _
  have hhi : r < (u.toRat : ℝ) + (q.den : ℝ)⁻¹ := by
    rw [hur, inv_eq_one_div, ← add_div, lt_div_iff₀ hd]
    exact Int.lt_floor_add_one _
  have pref (x : ℝ) (k : Dyadic) (hk : k.den ≤ q.den)
      (hl : (k.toRat : ℝ) - (q.den : ℝ)⁻¹ < x)
      (hh : x < (k.toRat : ℝ) + (q.den : ℝ)⁻¹) :
      birthdayTruncation (x : Surreal.{u}) (k : Surreal).birthday = k := by
    have hkd : 0 < (k.den : ℝ) := by exact_mod_cast k.den_pos
    have hi : (q.den : ℝ)⁻¹ ≤ (k.den : ℝ)⁻¹ := by
      exact inv_anti₀ hkd (by exact_mod_cast hk)
    apply birthdayTruncation_real_eq_dyadic_of_lower_upper
    · rw [Dyadic.coe_lower, Rat.cast_sub, Rat.cast_inv, Rat.cast_natCast]
      linarith only [hi, hl]
    · rw [Dyadic.coe_upper, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      linarith only [hi, hh]
  have hstep := inv_pos.mpr hd
  exact ⟨u, v, hu, hv, by simp [v], pref r u hu (by linarith) hhi,
    pref t v hv (by linarith only [hs, hvr, hhi]) (by linarith only [hs, hvr, hlo, hstep])⟩

private theorem coeff_at_head (K s : Surreal.{u}) (hK : K.support ⊆ Set.Ioi s) (r : ℝ) :
    (K + (r : Surreal) * ω^ s).coeff s = r := by
  have hKs : K.coeff s = 0 := notMem_support_iff.mp (fun hs ↦ (lt_irrefl s) (hK hs))
  have hsingle := toHahnSeries_eq (SurrealHahnSeries.toSurreal_single s r)
  rw [coeff_add, Pi.add_apply, hKs, zero_add, ← coeff_toHahnSeries, hsingle,
    SurrealHahnSeries.coeff_single]
  simp

/-- A dyadic endpoint is the exact sum of two prefixes obtained by rounding at its scale. -/
theorem exists_rounded_prefixes_of_dyadic_sum (a b K s : Surreal.{u}) (q : Dyadic)
    (hK : K.support ⊆ Set.Ioi s) (he : a + b = K + (q : Surreal) * ω^ s) :
    ∃ u v : Dyadic, u.den ≤ q.den ∧ v.den ≤ q.den ∧ u + v = q ∧
      let x := a.normalFormTrunc s + (u : Surreal) * ω^ s
      let y := b.normalFormTrunc s + (v : Surreal) * ω^ s
      birthdayTruncation a x.birthday = x ∧ birthdayTruncation b y.birthday = y ∧
        x + y = a + b := by
  have he' : a + b = K + ((q.toRat : ℝ) : Surreal) * ω^ s := by
    simpa only [Real.toSurreal_ratCast] using he
  have hs : (a + b).support ⊆ Set.Ici s := he' ▸ support_head_real_mul_wpow_subset K s hK _
  have hq : (a + b).coeff s = (q.toRat : ℝ) := he' ▸ coeff_at_head K s hK _
  have hcoeff : a.coeff s + b.coeff s = (q.toRat : ℝ) := by
    simpa only [coeff_add, Pi.add_apply] using hq
  obtain ⟨u, v, hu, hv, huv, hau, hbv⟩ :=
    exists_dyadic_prefixes_add_eq.{u} (a.coeff s) (b.coeff s) q hcoeff
  let F (x : Surreal.{u}) (k : Dyadic) := x.normalFormTrunc s + (k : Surreal) * ω^ s
  have pref (x : Surreal.{u}) (k : Dyadic)
      (hk : birthdayTruncation ((x.coeff s : ℝ) : Surreal.{u}) (k : Surreal).birthday = k) :
      birthdayTruncation x (F x k).birthday = F x k := by
    have hK : (x.normalFormTrunc s).support ⊆ Set.Ioi s := by
      rw [support_trunc]
      exact Set.inter_subset_right
    apply birthdayTruncation_eq_trans (birthdayTruncation_trunc_add_coeff_wpow x s)
    simpa only [F, Real.toSurreal_ratCast] using
      birthdayTruncation_head_real_mul_wpow_of_prefix (x.normalFormTrunc s) s hK
        (r := x.coeff s) (s := (k.toRat : ℝ)) (by simpa only [Real.toSurreal_ratCast] using hk)
  have ha := pref a u hau
  have hb := pref b v hbv
  have sum : F a u + F b v = a + b := by
    conv_rhs => rw [eq_trunc_add_coeff_wpow_of_support_ge hs, trunc_add, hq, Real.toSurreal_ratCast]
    have hq' : (u : Surreal.{u}) + (v : Surreal) = q := by exact_mod_cast huv
    dsimp only [F]
    rw [← hq', add_mul]
    abel
  exact ⟨u, v, hu, hv, huv, ha, hb, sum⟩

/-- When a sum ends on a dyadic grid, sharp plus-count addition puts both summands
on that grid, including the absence of terms on every smaller scale. -/
theorem exists_dyadic_heads_of_sharp_add (a b K s : Surreal.{u}) (q : Dyadic)
    (hK : K.support ⊆ Set.Ioi s) (he : a + b = K + (q : Surreal) * ω^ s)
    (hp : plusCount (a + b) = plusCount a + plusCount b) :
    ∃ u v : Dyadic, u.den ≤ q.den ∧ v.den ≤ q.den ∧ u + v = q ∧
      a = a.normalFormTrunc s + (u : Surreal) * ω^ s ∧
      b = b.normalFormTrunc s + (v : Surreal) * ω^ s := by
  obtain ⟨u, v, hu, hv, huv, ha, hb, sum⟩ := exists_rounded_prefixes_of_dyadic_sum a b K s q hK he
  let F (x : Surreal.{u}) (k : Dyadic) := x.normalFormTrunc s + (k : Surreal) * ω^ s
  have bound (x : Surreal.{u}) (k : Dyadic) (h : birthdayTruncation x (F x k).birthday = F x k) :
      (F x k).birthday ≤ x.birthday := by
    simpa only [h] using birthday_birthdayTruncation_le_birthday x (F x k).birthday
  obtain ⟨h₁, h₂⟩ := birthdayTruncation_eq_of_add_eq_of_plusCount_add_eq a b
    (bound a u ha) (bound b v hb) (by rwa [ha, hb]) hp
  exact ⟨u, v, hu, hv, huv, h₁.symm.trans ha, h₂.symm.trans hb⟩

/-- A dyadic-headed number with both signs cofinal has no right option within
a real fraction of its last monomial. -/
theorem fraction_wpow_lt_right_gap_of_dyadic_head {a H s : Surreal.{u}} (u : Dyadic)
    (hH : H.support ⊆ Set.Ioi s) (ha : a = H + (u : Surreal) * ω^ s)
    (hL : ∀ j < a.birthday, ∃ v ∈ leftPrefixes a, j < v.birthday)
    (hR : ∀ j < a.birthday, ∃ v ∈ rightPrefixes a, j < v.birthday)
    {c : ℝ} (hc : c < 1) {w : Surreal.{u}} (hw : w ∈ rightPrefixes a) :
    a + (c : Surreal) * ω^ s < w := by
  by_cases hpos : 0 < c
  swap
  · have hc' := Real.toSurreal_le_iff.{u}.mpr (le_of_not_gt hpos)
    rw [Real.toSurreal_zero] at hc'
    exact (add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg hc' (wpow_nonneg s))).trans_lt
      (mem_rightPrefixes_iff.mp hw).2
  have ha' : a = H + ((u.toRat : ℝ) : Surreal) * ω^ s := by
    simpa only [Real.toSurreal_ratCast] using ha
  have integer : u.den = 1 := by
    by_cases hz : u = 0
    · simp [hz]
    have hu : (u.toRat : ℝ) ≠ 0 := by exact_mod_cast hz
    have hfinite := (birthday_real_lt_omega0_iff.{u} _).mpr ⟨u, rfl⟩
    rcases head_real_coefficient_eq_one_or_neg_one_of_both_cofinal H s hH hu hfinite
      (by rwa [← ha']) (by rwa [← ha']) with h | h
    · have : u = 1 := by exact_mod_cast h
      simp [this]
    · have : u = -1 := by exact_mod_cast h
      simp [this]
  have hfit := birthdayTruncation_real_eq_dyadic_of_lower_upper.{u} ((u.toRat : ℝ) + c) u
    (by rw [Dyadic.coe_lower, Rat.cast_sub, integer]; norm_num; linarith)
    (by rw [Dyadic.coe_upper, Rat.cast_add, integer]; norm_num; exact hc)
  have hpre := birthdayTruncation_head_real_mul_wpow_of_prefix H s hH
    (r := (u.toRat : ℝ) + c) (s := (u.toRat : ℝ))
    (by simpa only [Real.toSurreal_ratCast] using hfit)
  have h := (mem_rightPrefixes_iff.mp
    (rightPrefixes_subset_of_birthdayTruncation_eq hpre (ha' ▸ hw))).2
  rw [Real.toSurreal_add, add_mul] at h
  rw [ha']
  simpa only [add_assoc] using h

/-- A sharp sum of two headed terms puts the first coefficient on the grid of their sum. -/
theorem exists_coefficient_of_den_le_of_sharp_add (A B s : Surreal.{u})
    (hA : A.support ⊆ Set.Ioi s) (hB : B.support ⊆ Set.Ioi s)
    (r t : ℝ) (q : Dyadic) (hs : r + t = (q.toRat : ℝ))
    (hsharp : plusCount ((A + (r : Surreal) * ω^ s) + (B + (t : Surreal) * ω^ s)) =
      plusCount (A + (r : Surreal) * ω^ s) + plusCount (B + (t : Surreal) * ω^ s)) :
    ∃ u : Dyadic, u.den ≤ q.den ∧ (u.toRat : ℝ) = r := by
  let a := A + (r : Surreal) * ω^ s
  let b := B + (t : Surreal) * ω^ s
  have hAB : (A + B).support ⊆ Set.Ioi s := fun _ hv ↦ (support_add_subset hv).elim
    (fun h ↦ hA h) (fun h ↦ hB h)
  have he : a + b = (A + B) + (q : Surreal) * ω^ s := by
    rw [← Real.toSurreal_ratCast, ← hs, Real.toSurreal_add, add_mul]
    dsimp only [a, b]
    abel
  obtain ⟨u, _, hu, _, _, ha, _⟩ := exists_dyadic_heads_of_sharp_add a b _ s q hAB he hsharp
  have htr : (a.normalFormTrunc s).support ⊆ Set.Ioi s := by
    rw [support_trunc]
    exact Set.inter_subset_right
  have hru := congrArg (fun x : Surreal.{u} ↦ x.coeff s) ha
  rw [← Real.toSurreal_ratCast] at hru
  change (A + (r : Surreal) * ω^ s).coeff s =
    (a.normalFormTrunc s + ((u.toRat : ℝ) : Surreal) * ω^ s).coeff s at hru
  rw [coeff_at_head A s hA r, coeff_at_head _ s htr] at hru
  exact ⟨u, hu, hru.symm⟩

/-- Sharp plus-count addition with a dyadic last coefficient forces the first input coefficient
to have finite birthday. -/
theorem birthday_real_coefficient_lt_omega0_of_sharp_add (A B s : Surreal.{u})
    (hA : A.support ⊆ Set.Ioi s) (hB : B.support ⊆ Set.Ioi s)
    (r t : ℝ) (q : Dyadic) (hs : r + t = (q.toRat : ℝ))
    (hsharp : plusCount ((A + (r : Surreal) * ω^ s) + (B + (t : Surreal) * ω^ s)) =
      plusCount (A + (r : Surreal) * ω^ s) + plusCount (B + (t : Surreal) * ω^ s)) :
    (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
  obtain ⟨u, _, hu⟩ := exists_coefficient_of_den_le_of_sharp_add A B s hA hB r t q hs hsharp
  exact (birthday_real_lt_omega0_iff _).mpr ⟨u, hu⟩

/-- A nondyadic coefficient forces strict plus-count addition when the final sum
coefficient is dyadic. -/
theorem plusCount_add_lt_of_nondyadic_last_coefficient (A B s : Surreal.{u})
    (hA : A.support ⊆ Set.Ioi s) (hB : B.support ⊆ Set.Ioi s)
    (r t : ℝ) (q : Dyadic) (hs : r + t = (q.toRat : ℝ))
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    plusCount ((A + (r : Surreal) * ω^ s) + (B + (t : Surreal) * ω^ s)) <
      plusCount (A + (r : Surreal) * ω^ s) + plusCount (B + (t : Surreal) * ω^ s) := by
  apply (plusCount_add_le _ _).lt_of_ne
  intro he
  exact (birthday_real_coefficient_lt_omega0_of_sharp_add A B s hA hB r t q hs he).ne hr

end Surreal
