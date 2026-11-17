/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Head
public import GonshorBirthday.Surreal.Birthday.Addition

/-!
# Strict plus-count addition for nondyadic last coefficients

A dyadic coefficient has an open real interval on which it remains a canonical
prefix. Replacing a nondyadic input coefficient by one sufficiently close left
prefix preserves the output as a prefix, but strictly lowers the input plus count.
Thus sharp plus-count addition forces both last coefficients to be dyadic.
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

/-- A nondyadic coefficient forces strict plus-count addition when the final sum
coefficient is dyadic, by one sufficiently close canonical left prefix. -/
theorem plusCount_add_lt_of_nondyadic_last_coefficient (A B s : Surreal.{u})
    (hA : A.support ⊆ Set.Ioi s) (hB : B.support ⊆ Set.Ioi s)
    (r t : ℝ) (q : Dyadic) (hs : r + t = (q.toRat : ℝ))
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    plusCount ((A + (r : Surreal) * ω^ s) + (B + (t : Surreal) * ω^ s)) <
      plusCount (A + (r : Surreal) * ω^ s) + plusCount (B + (t : Surreal) * ω^ s) := by
  have hgap : 0 < (q.toRat : ℝ) - q.lower.toRat := by
    rw [Dyadic.coe_lower, Rat.cast_sub, Rat.cast_inv, Rat.cast_natCast]
    exact sub_pos.mpr (sub_lt_self _ (inv_pos.mpr (by exact_mod_cast q.den_pos)))
  have hrneg : ((-r : ℝ) : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 := by
    rwa [Real.toSurreal_neg, birthday_neg]
  obtain ⟨c, hc, hclt⟩ := exists_real_rightPrefix_lt hrneg
    (show -r < -r + ((q.toRat : ℝ) - q.lower.toRat) from lt_add_of_pos_right _ hgap)
  have hrc : -c < r := by
    have hh := Real.toSurreal_lt_iff.mp (mem_rightPrefixes_iff.mp hc).2
    linarith only [hh]
  have hcp : birthdayTruncation (r : Surreal.{u}) ((-c : ℝ) : Surreal).birthday =
      ((-c : ℝ) : Surreal) := by
    have hh := neg_mem_leftPrefixes_iff.mpr hc
    simp only [Real.toSurreal_neg, neg_neg] at hh
    simpa only [Real.toSurreal_neg] using (mem_leftPrefixes_iff.mp hh).1
  have hqp : birthdayTruncation ((-c + t : ℝ) : Surreal.{u}) (q : Surreal).birthday =
      (q : Surreal) := by
    apply birthdayTruncation_real_eq_dyadic_of_lower_upper
    · linarith only [hclt, hs]
    · have hqu : (q.toRat : ℝ) < q.upper.toRat := by
        rw [Dyadic.coe_upper, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
        exact lt_add_of_pos_right _ (inv_pos.mpr (by exact_mod_cast q.den_pos))
      linarith only [hrc, hs, hqu]
  have hAB : (A + B).support ⊆ Set.Ioi s := by
    intro v hv
    exact (support_add_subset hv).elim (fun h ↦ hA h) (fun h ↦ hB h)
  have hout := birthdayTruncation_head_real_mul_wpow_of_prefix (A + B) s hAB
    (show birthdayTruncation ((-c + t : ℝ) : Surreal.{u})
      (((q.toRat : ℝ) : Surreal).birthday) = ((q.toRat : ℝ) : Surreal) by
        simpa only [Real.toSurreal_ratCast] using hqp)
  have hsum : (A + (r : Surreal) * ω^ s) + (B + (t : Surreal) * ω^ s) =
      A + B + ((q.toRat : ℝ) : Surreal) * ω^ s := by
    rw [← hs, Real.toSurreal_add]
    ring
  have hshort : (A + ((-c : ℝ) : Surreal) * ω^ s) + (B + (t : Surreal) * ω^ s) =
      A + B + ((-c + t : ℝ) : Surreal) * ω^ s := by
    rw [Real.toSurreal_add]
    ring
  have hpc : plusCount ((A + (r : Surreal) * ω^ s) + (B + (t : Surreal) * ω^ s)) ≤
      plusCount ((A + ((-c : ℝ) : Surreal) * ω^ s) + (B + (t : Surreal) * ω^ s)) := by
    rw [hsum, hshort]
    have hb := birthday_birthdayTruncation_le_birthday
      (A + B + ((-c + t : ℝ) : Surreal) * ω^ s)
      (A + B + ((q.toRat : ℝ) : Surreal) * ω^ s).birthday
    rw [hout] at hb
    have hh := plusCount_birthdayTruncation_le _ hb
    rwa [hout] at hh
  have hinput := birthdayTruncation_head_real_mul_wpow_of_prefix A s hA hcp
  have hinputlt : A + ((-c : ℝ) : Surreal) * ω^ s < A + (r : Surreal) * ω^ s := by
    exact _root_.add_lt_add_right (mul_lt_mul_of_pos_right (Real.toSurreal_lt_iff.mpr hrc)
      (wpow_pos s)) A
  exact (hpc.trans (plusCount_add_le _ _)).trans_lt
    (add_lt_add_of_lt_of_le (plusCount_lt_of_mem_leftPrefixes
      (mem_leftPrefixes_iff.mpr ⟨hinput, hinputlt⟩)) le_rfl)

/-- Sharp plus-count addition with a dyadic last coefficient forces the first input coefficient
to have finite birthday. -/
theorem birthday_real_coefficient_lt_omega0_of_sharp_add (A B s : Surreal.{u})
    (hA : A.support ⊆ Set.Ioi s) (hB : B.support ⊆ Set.Ioi s)
    (r t : ℝ) (q : Dyadic) (hs : r + t = (q.toRat : ℝ))
    (hsharp : plusCount ((A + (r : Surreal) * ω^ s) + (B + (t : Surreal) * ω^ s)) =
      plusCount (A + (r : Surreal) * ω^ s) + plusCount (B + (t : Surreal) * ω^ s)) :
    (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
  by_contra hn
  have hr := le_antisymm (birthday_real_le_omega0 r) (le_of_not_gt hn)
  exact (plusCount_add_lt_of_nondyadic_last_coefficient A B s hA hB r t q hs hr).ne hsharp

end Surreal
