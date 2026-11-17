/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Constant
public import CombinatorialGames.Surreal.Pow

import GonshorBirthday.Surreal.Birthday.Addition

/-!
# The omega-map and intrinsic prefixes
-/

universe u

public noncomputable section

namespace IGame

/-- Applying the omega-map preserves fitting between numeric games. -/
theorem Fits.wpow {x y : IGame.{u}} [Numeric x] [Numeric y] (h : Fits x y) :
    Fits (ω^ x) (ω^ y) := by
  constructor
  · rw [forall_mem_moves_left_wpow]
    constructor
    · exact (Numeric.wpow_pos x).not_ge
    · intro r hr z hz
      numeric
      have hzx : z < x := by
        rw [← Surreal.mk_lt_mk, lt_iff_not_ge, Surreal.mk_le_mk]
        exact h.1 z hz
      exact (Numeric.mul_wpow_lt_wpow' r hzx).not_ge
  · rw [forall_moves_right_wpow]
    intro r hr z hz
    numeric
    have hxz : x < z := by
      rw [← Surreal.mk_lt_mk, lt_iff_not_ge, Surreal.mk_le_mk]
      exact h.2 z hz
    exact (Numeric.wpow_lt_mul_wpow' hr hxz).not_ge

/-- Natural multiples of an omega-map at a smaller fitting exponent are canonical prefixes. -/
theorem Fits.nsmul_wpow {x y : IGame.{u}} [Numeric x] [Numeric y]
    (h : Fits x y) (hyx : y < x) (n : ℕ) : Fits (ω^ x) (n • ω^ y) := by
  cases n with
  | zero => simp [Fits]
  | succ n =>
    constructor
    · intro z hz
      rw [moves_succ_nsmul] at hz
      obtain ⟨z, hz, rfl⟩ := hz
      rw [moves_left_wpow] at hz
      obtain rfl | ⟨r, hr, w, hw, rfl⟩ := hz
      · rw [← Surreal.mk_le_mk]
        apply not_le_of_gt
        simpa only [Surreal.mk_add, Surreal.mk_nsmul, Surreal.mk_wpow, Surreal.mk_zero,
          add_zero, nsmul_eq_mul, Real.toSurreal_natCast] using
          (Surreal.mul_wpow_lt_wpow (n : ℝ) (Surreal.mk_lt_mk.mpr hyx))
      · numeric
        have hwx : w < x := by
          rw [← Surreal.mk_lt_mk, lt_iff_not_ge, Surreal.mk_le_mk]
          exact h.1 w hw
        have ht := Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow' (n : Dyadic) r
          (t := 1) (by simp) hyx hwx
        rw [← Surreal.mk_lt_mk] at ht
        rw [← Surreal.mk_le_mk]
        apply not_le_of_gt
        simpa [Surreal.mk_add, Surreal.mk_nsmul, Surreal.mk_mul, Surreal.mk_wpow,
          nsmul_eq_mul] using ht
    · intro z hz
      rw [moves_succ_nsmul] at hz
      obtain ⟨z, hz, rfl⟩ := hz
      rw [moves_right_wpow] at hz
      obtain ⟨r, hr, w, hw, rfl⟩ := hz
      numeric
      have hxw : x < w := by
        rw [← Surreal.mk_lt_mk, lt_iff_not_ge, Surreal.mk_le_mk]
        exact h.2 w hw
      have ht : Surreal.mk (ω^ x) < Surreal.mk (n • ω^ y + r * ω^ w) := by
        rw [Surreal.mk_add, Surreal.mk_nsmul]
        apply (Surreal.mk_lt_mk.mpr (Numeric.wpow_lt_mul_wpow' hr hxw)).trans_le
        exact le_add_of_nonneg_left (nsmul_nonneg (by simp) _)
      rw [← Surreal.mk_le_mk]
      exact ht.not_ge

end IGame

namespace Surreal
open Set IGame

/-- Every canonical right prefix of a monomial exceeds all its natural multiples. -/
theorem natCast_mul_wpow_lt_of_mem_rightPrefixes {x z : Surreal.{u}}
    (hz : z ∈ rightPrefixes (ω^ x)) (n : ℕ) : (n : Surreal) * ω^ x < z := by
  have hzb := birthday_lt_of_mem_rightPrefixes hz
  have hzx : ω^ x < z := (mem_rightPrefixes.mp hz).choose_spec.2.2
  have hn : ¬ Fits z.out (ω^ x.out) := by
    intro h
    have hb := h.surrealBirthday_le
    exact hzb.not_ge (by simpa only [mk_wpow, out_eq] using hb)
  rw [not_fits_iff] at hn
  rcases hn with ⟨v, hv, hzv⟩ | ⟨v, hv, hvz⟩
  · numeric
    have ht := mk_lt_mk.mpr (hzv.trans_lt (Numeric.left_lt hv))
    have ht' : z < ω^ x := by simpa only [mk_wpow, out_eq] using ht
    exact False.elim (hzx.not_gt ht')
  · rw [moves_right_wpow] at hv
    obtain ⟨r, hr, w, hw, rfl⟩ := hv
    numeric
    have ht := Numeric.mul_wpow_lt_mul_wpow_of_pos' (n : Dyadic) hr (Numeric.lt_right hw)
    have hs := mk_lt_mk.mpr (ht.trans_le hvz)
    simpa [mk_mul, mk_wpow, out_eq] using hs

/-- Positive natural coefficients introduce no new canonical right prefixes of a monomial. -/
theorem rightPrefixes_natCast_mul_wpow (x : Surreal.{u}) (n : ℕ) :
    rightPrefixes (((n + 1 : ℕ) : Surreal) * ω^ x) = rightPrefixes (ω^ x) := by
  have he := ofSets_eq_mk (s := leftPrefixes (ω^ x)) (t := rightPrefixes (ω^ x))
    (H := leftPrefixes_lt_rightPrefixes (ω^ x))
  generalize_proofs ng at he
  rw [ofSets_leftPrefixes_rightPrefixes] at he
  let g : IGame.{u} := !{out '' leftPrefixes (ω^ x) | out '' rightPrefixes (ω^ x)}
  have : Numeric g := by assumption
  change ω^ x = mk g at he
  have hsum : mk ((n + 1) • g) = ((n + 1 : ℕ) : Surreal) * ω^ x := by
    rw [mk_nsmul, ← he, nsmul_eq_mul]
  ext z
  constructor
  · intro hz
    have hzb := birthday_lt_of_mem_rightPrefixes hz
    have hzx := (mem_rightPrefixes.mp hz).choose_spec.2.2
    have hn : ¬ Fits z.out ((n + 1) • g) := by
      intro h
      have hb := h.surrealBirthday_le
      exact hzb.not_ge (by simpa only [hsum, out_eq] using hb)
    rw [not_fits_iff] at hn
    rcases hn with ⟨v, hv, hzv⟩ | ⟨v, hv, hvz⟩
    · numeric
      have ht := mk_lt_mk.mpr (hzv.trans_lt (Numeric.left_lt hv))
      have ht' : z < ((n + 1 : ℕ) : Surreal) * ω^ x := by
        simpa only [hsum, out_eq] using ht
      exact False.elim (hzx.not_gt ht')
    · rw [moves_succ_nsmul] at hv
      obtain ⟨v, hv, rfl⟩ := hv
      change v ∈ (!{out '' leftPrefixes (ω^ x) | out '' rightPrefixes (ω^ x)} : IGame)ᴿ at hv
      rw [moves_right_ofSets] at hv
      obtain ⟨b, hb, rfl⟩ := hv
      have hle : (n : Surreal) * ω^ x + b ≤ z := by
        have ht := mk_le_mk.mpr hvz
        simpa only [mk_add, mk_nsmul, ← he, out_eq, nsmul_eq_mul] using ht
      have hbz : b ≤ z := (le_add_of_nonneg_left
        (mul_nonneg (Nat.cast_nonneg n) (wpow_nonneg x))).trans hle
      have hgap := natCast_mul_wpow_lt_of_mem_rightPrefixes hb (n + 1)
      have hpz := (mem_rightPrefixes_iff.mp hz).1
      have hpbz : birthdayTruncation b z.birthday = z := by
        have ht := birthdayTruncation_eq_of_right_between hzb.le hgap.le (by rwa [hpz])
        exact ht.trans hpz
      apply mem_rightPrefixes_iff.mpr
      exact ⟨birthdayTruncation_eq_trans (mem_rightPrefixes_iff.mp hb).1 hpbz,
        ((mem_rightPrefixes_iff.mp hb).2).trans_le hbz⟩
  · intro hz
    have hgap := natCast_mul_wpow_lt_of_mem_rightPrefixes hz (n + 1)
    have hlow : ω^ x ≤ ((n + 1 : ℕ) : Surreal) * ω^ x := by
      have ht : ω^ x ≤ (n : Surreal) * ω^ x + ω^ x :=
        le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg n) (wpow_nonneg x))
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ht
    have hpz := (mem_rightPrefixes_iff.mp hz).1
    have ht := birthdayTruncation_eq_of_right_between
      (birthday_lt_of_mem_rightPrefixes hz).le hlow (by rw [hpz]; exact hgap.le)
    exact mem_rightPrefixes_iff.mpr ⟨ht.trans hpz, hgap⟩

/-- A monomial is a canonical prefix of each of its positive natural multiples. -/
theorem birthdayTruncation_natCast_mul_wpow (x : Surreal.{u}) (n : ℕ) :
    birthdayTruncation (((n + 1 : ℕ) : Surreal) * ω^ x) (ω^ x).birthday = ω^ x := by
  have hlow : ω^ x ≤ ((n + 1 : ℕ) : Surreal) * ω^ x := by
    have ht : ω^ x ≤ (n : Surreal) * ω^ x + ω^ x :=
      le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg n) (wpow_nonneg x))
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ht
  have ht := birthdayTruncation_eq_of_btwn
    (H := leftPrefixes_lt_rightPrefixes (ω^ x))
    (fun z hz ↦ ((mem_leftPrefixes.mp hz).choose_spec.2.2).trans_le hlow)
    (fun z hz ↦ natCast_mul_wpow_lt_of_mem_rightPrefixes hz (n + 1))
  simpa only [ofSets_leftPrefixes_rightPrefixes] using ht

/-- A positive natural coefficient cannot decrease a monomial's birthday. -/
theorem birthday_wpow_le_natCast_mul_wpow (x : Surreal.{u}) (n : ℕ) :
    (ω^ x).birthday ≤ (((n + 1 : ℕ) : Surreal) * ω^ x).birthday := by
  have ht := birthday_birthdayTruncation_le_birthday
    (((n + 1 : ℕ) : Surreal) * ω^ x) (ω^ x).birthday
  rwa [birthdayTruncation_natCast_mul_wpow] at ht

/-- A positive natural coefficient appends only plus signs to the monomial. -/
theorem natCast_mul_wpow_eq_appendPluses_sub (x : Surreal.{u}) (n : ℕ) :
    ((n + 1 : ℕ) : Surreal) * ω^ x = appendPluses (ω^ x)
      ((((n + 1 : ℕ) : Surreal) * ω^ x).birthday.val - (ω^ x).birthday.val) := by
  apply Eq.symm
  apply (appendPluses_eq_iff _ _ _).mpr
  constructor
  · rw [Ordinal.add_sub_cancel_of_le
      (NatOrdinal.val.monotone (birthday_wpow_le_natCast_mul_wpow x n)), NatOrdinal.of_val]
  · exact rightPrefixes_natCast_mul_wpow x n

/-- The exact monomial coefficient block is equivalent to its birthday increment formula. -/
theorem natCast_mul_wpow_eq_appendPluses_iff (x : Surreal.{u}) (n : ℕ) :
    (((n + 1 : ℕ) : Surreal) * ω^ x =
      appendPluses (ω^ x) ((ω^ plusCount x).val * (n : Ordinal))) ↔
    (((n + 1 : ℕ) : Surreal) * ω^ x).birthday =
      NatOrdinal.of ((ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal)) := by
  rw [eq_comm, appendPluses_eq_iff, rightPrefixes_natCast_mul_wpow]
  simp only [and_true]

/-- Canonical left prefixes of an omega-map are bounded by natural multiples at left exponents. -/
theorem exists_natCast_mul_wpow_ge_of_mem_leftPrefixes {x z : Surreal.{u}}
    (hz : z ∈ leftPrefixes (ω^ x)) : z = 0 ∨
      ∃ v ∈ leftPrefixes x, ∃ n : ℕ, z ≤ (n : Surreal) * ω^ v := by
  have he := ofSets_eq_mk (s := leftPrefixes x) (t := rightPrefixes x)
    (H := leftPrefixes_lt_rightPrefixes x)
  generalize_proofs at he
  rw [ofSets_leftPrefixes_rightPrefixes] at he
  let g : IGame.{u} := !{out '' leftPrefixes x | out '' rightPrefixes x}
  have : Numeric g := by assumption
  change x = mk g at he
  have hwp : mk (ω^ g) = ω^ x := by rw [mk_wpow, ← he]
  have hzb := birthday_lt_of_mem_leftPrefixes hz
  have hzx := (mem_leftPrefixes.mp hz).choose_spec.2.2
  have hn : ¬ Fits z.out (ω^ g) := by
    intro h
    have hb := h.surrealBirthday_le
    exact hzb.not_ge (by simpa only [hwp, out_eq] using hb)
  rw [not_fits_iff] at hn
  rcases hn with ⟨v, hv, hzv⟩ | ⟨v, hv, hvz⟩
  · rw [moves_left_wpow] at hv
    rcases hv with hv | ⟨r, hr, w, hw, rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hv
      have ht : z ≤ 0 := by simpa only [out_eq, mk_zero] using mk_le_mk.mpr hzv
      exact Or.inl (ht.antisymm (nonneg_of_mem_leftPrefixes (wpow_pos x) hz))
    · change w ∈ (!{out '' leftPrefixes x | out '' rightPrefixes x} : IGame)ᴸ at hw
      rw [moves_left_ofSets] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      obtain ⟨n, hn⟩ := exists_nat_gt r
      have hn' : (r : Surreal.{u}) ≤ (n : Surreal) := by exact_mod_cast hn.le
      have hle : z ≤ (r : Surreal) * ω^ v := by
        simpa only [mk_mul, mk_wpow, mk_dyadic, out_eq] using mk_le_mk.mpr hzv
      exact Or.inr ⟨v, hv, n, hle.trans (mul_le_mul_of_nonneg_right hn' (wpow_nonneg v))⟩
  · numeric
    have ht := mk_lt_mk.mpr ((Numeric.lt_right hv).trans_le hvz)
    have ht' : ω^ x < z := by simpa only [hwp, out_eq] using ht
    exact False.elim (hzx.not_gt ht')

/-- Left prefixes in a natural coefficient interval are bounded by shifted lower monomials. -/
theorem exists_natCast_mul_wpow_add_ge_of_mem_leftPrefixes {x z : Surreal.{u}} (n : ℕ)
    (hz : z ∈ leftPrefixes (((n + 1 : ℕ) : Surreal) * ω^ x)) :
    z ≤ (n : Surreal) * ω^ x ∨ ∃ v ∈ leftPrefixes x, ∃ m : ℕ,
      z ≤ (n : Surreal) * ω^ x + (m : Surreal) * ω^ v := by
  have he := ofSets_eq_mk (s := leftPrefixes x) (t := rightPrefixes x)
    (H := leftPrefixes_lt_rightPrefixes x)
  generalize_proofs at he
  rw [ofSets_leftPrefixes_rightPrefixes] at he
  let g : IGame.{u} := !{out '' leftPrefixes x | out '' rightPrefixes x}
  have : Numeric g := by assumption
  change x = mk g at he
  have hsum : mk ((n + 1) • ω^ g) = ((n + 1 : ℕ) : Surreal) * ω^ x := by
    rw [mk_nsmul, mk_wpow, ← he, nsmul_eq_mul]
  have hzb := birthday_lt_of_mem_leftPrefixes hz
  have hzx := (mem_leftPrefixes.mp hz).choose_spec.2.2
  have hn : ¬ Fits z.out ((n + 1) • ω^ g) := by
    intro h
    have hb := h.surrealBirthday_le
    exact hzb.not_ge (by simpa only [hsum, out_eq] using hb)
  rw [not_fits_iff] at hn
  rcases hn with ⟨v, hv, hzv⟩ | ⟨v, hv, hvz⟩
  · rw [moves_succ_nsmul] at hv
    obtain ⟨v, hv, rfl⟩ := hv
    rw [moves_left_wpow] at hv
    rcases hv with hv | ⟨r, hr, w, hw, rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hv
      have ht := mk_le_mk.mpr hzv
      exact Or.inl (by simpa only [mk_add, mk_nsmul, mk_wpow, ← he,
        mk_zero, add_zero, nsmul_eq_mul, out_eq] using ht)
    · change w ∈ (!{out '' leftPrefixes x | out '' rightPrefixes x} : IGame)ᴸ at hw
      rw [moves_left_ofSets] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      obtain ⟨m, hm⟩ := exists_nat_gt r
      have hm' : (r : Surreal.{u}) ≤ (m : Surreal) := by exact_mod_cast hm.le
      have hle : z ≤ (n : Surreal) * ω^ x + (r : Surreal) * ω^ v := by
        simpa only [mk_add, mk_nsmul, mk_mul, mk_wpow, mk_dyadic, ← he,
          out_eq, nsmul_eq_mul] using mk_le_mk.mpr hzv
      exact Or.inr ⟨v, hv, m, hle.trans
        (add_le_add_right (mul_le_mul_of_nonneg_right hm' (wpow_nonneg v)) _)⟩
  · numeric
    have ht := mk_lt_mk.mpr ((Numeric.lt_right hv).trans_le hvz)
    have ht' : ((n + 1 : ℕ) : Surreal) * ω^ x < z := by
      simpa only [hsum, out_eq] using ht
    exact False.elim (hzx.not_gt ht')

/-- A head with large left-prefix gaps leaves a cofinal shifted omega-prefix family. -/
theorem exists_head_natCast_mul_wpow_add_ge_of_mem_leftPrefixes
    {H x z : Surreal.{u}} (n : ℕ)
    (hH : ∀ a ∈ leftPrefixes H, a + ((n + 1 : ℕ) : Surreal) * ω^ x ≤ H)
    (hz : z ∈ leftPrefixes (H + ((n + 1 : ℕ) : Surreal) * ω^ x)) :
    z ≤ H + (n : Surreal) * ω^ x ∨ ∃ v ∈ leftPrefixes x, ∃ m : ℕ,
      z ≤ H + (n : Surreal) * ω^ x + (m : Surreal) * ω^ v := by
  rcases exists_leftPrefixes_add_ge hz with ⟨a, ha, hza⟩ | ⟨b, hb, hzb⟩
  · exact Or.inl ((hza.trans (hH a ha)).trans
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (wpow_nonneg x))))
  · rcases exists_natCast_mul_wpow_add_ge_of_mem_leftPrefixes n hb with hb | ⟨v, hv, m, hbm⟩
    · exact Or.inl (hzb.trans (add_le_add_right hb H))
    · apply Or.inr
      refine ⟨v, hv, m, ?_⟩
      simpa only [add_assoc] using hzb.trans (add_le_add_right hbm H)

/-- An exponent with no left prefixes gives a monomial with zero as its only left prefix. -/
theorem leftPrefixes_wpow_of_leftPrefixes_eq_empty {x : Surreal.{u}}
    (hx : leftPrefixes x = ∅) : leftPrefixes (ω^ x) = {0} := by
  ext z
  constructor
  · intro hz
    rcases exists_natCast_mul_wpow_ge_of_mem_leftPrefixes hz with hz0 | ⟨v, hv, _, _⟩
    · exact Set.mem_singleton_iff.mpr hz0
    · rw [hx] at hv
      exact False.elim hv
  · intro hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact zero_mem_leftPrefixes (wpow_pos x)

/-- A zero-plus-count exponent gives a monomial whose only left prefix is zero. -/
theorem leftPrefixes_wpow_of_plusCount_eq_zero {x : Surreal.{u}} (hx : plusCount x = 0) :
    leftPrefixes (ω^ x) = {0} :=
  leftPrefixes_wpow_of_leftPrefixes_eq_empty (leftPrefixes_eq_empty_of_plusCount_eq_zero hx)

/-- At plus rank zero, increasing a natural monomial coefficient appends one plus sign. -/
theorem appendPlus_natCast_mul_wpow_of_plusCount_eq_zero {x : Surreal.{u}}
    (hx : plusCount x = 0) (n : ℕ) :
    appendPlus (((n + 1 : ℕ) : Surreal) * ω^ x) =
      ((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x := by
  have hL0 := leftPrefixes_wpow_of_plusCount_eq_zero hx
  have hsum (m : ℕ) : ((m + 1 : ℕ) : Surreal) * ω^ x + ω^ x =
      ((m + 2 : ℕ) : Surreal) * ω^ x := by
    change _ = (((m + 1) + 1 : ℕ) : Surreal) * ω^ x
    rw [Nat.cast_add (m + 1) 1, Nat.cast_one, add_mul, one_mul]
  have step (m : ℕ)
      (hgap : ∀ z ∈ leftPrefixes (((m + 1 : ℕ) : Surreal) * ω^ x),
        z + ω^ x ≤ ((m + 1 : ℕ) : Surreal) * ω^ x) :
      appendPlus (((m + 1 : ℕ) : Surreal) * ω^ x) =
        ((m + 1 : ℕ) : Surreal) * ω^ x + ω^ x := by
    apply appendPlus_eq_of_rightPrefixes_eq
    · exact lt_add_of_pos_right _ (wpow_pos x)
    · rw [hsum, rightPrefixes_natCast_mul_wpow, rightPrefixes_natCast_mul_wpow]
    · intro z hz
      rcases exists_leftPrefixes_add_ge hz with ⟨a, ha, hza⟩ | ⟨b, hb, hzb⟩
      · exact hza.trans (hgap a ha)
      · rw [hL0] at hb
        obtain rfl := Set.mem_singleton_iff.mp hb
        simpa only [add_zero] using hzb
  have gap : ∀ m : ℕ, ∀ z ∈ leftPrefixes (((m + 1 : ℕ) : Surreal) * ω^ x),
      z + ω^ x ≤ ((m + 1 : ℕ) : Surreal) * ω^ x := by
    intro m
    induction m with
    | zero =>
      intro z hz
      simp only [zero_add, Nat.cast_one, one_mul] at hz ⊢
      rw [hL0] at hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      simp
    | succ m ih =>
      have he := (step m ih).trans (hsum m)
      change ∀ z ∈ leftPrefixes (((m + 2 : ℕ) : Surreal) * ω^ x),
        z + ω^ x ≤ ((m + 2 : ℕ) : Surreal) * ω^ x
      rw [← he, leftPrefixes_appendPlus]
      intro z hz
      rcases hz with hz | hz
      · subst z
        rw [step m ih]
      · exact (ih z hz).trans (lt_appendPlus _).le
  exact step n (gap n)

/-- At plus rank zero, the exact natural coefficient birthday increment is finite. -/
theorem birthday_natCast_mul_wpow_of_plusCount_eq_zero {x : Surreal.{u}}
    (hx : plusCount x = 0) (n : ℕ) :
    (((n + 1 : ℕ) : Surreal) * ω^ x).birthday =
      NatOrdinal.of ((ω^ x).birthday.val + (n : Ordinal)) := by
  induction n with
  | zero => simp only [zero_add, Nat.cast_one, one_mul, Nat.cast_zero, add_zero, NatOrdinal.of_val]
  | succ n ih =>
    have he : appendPlus (((n + 1 : ℕ) : Surreal) * ω^ x) =
        ((n + 2 : ℕ) : Surreal) * ω^ x := by
      rw [appendPlus_natCast_mul_wpow_of_plusCount_eq_zero hx n]
      change _ = (((n + 1) + 1 : ℕ) : Surreal) * ω^ x
      rw [Nat.cast_add (n + 1) 1, Nat.cast_one, add_mul, one_mul]
    change (((n + 2 : ℕ) : Surreal) * ω^ x).birthday =
      NatOrdinal.of ((ω^ x).birthday.val + ((n + 1 : ℕ) : Ordinal))
    rw [← he, birthday_appendPlus, ih, ← NatOrdinal.of_add_one,
      Nat.cast_add, Nat.cast_one, add_assoc]

/-- The exact one-term coefficient block holds for every zero-plus-count exponent. -/
theorem natCast_mul_wpow_eq_appendPluses_of_plusCount_eq_zero {x : Surreal.{u}}
    (hx : plusCount x = 0) (n : ℕ) :
    ((n + 1 : ℕ) : Surreal) * ω^ x =
      appendPluses (ω^ x) ((ω^ plusCount x).val * (n : Ordinal)) := by
  apply (natCast_mul_wpow_eq_appendPluses_iff x n).mpr
  rw [hx, NatOrdinal.wpow_zero, NatOrdinal.val_one, one_mul]
  exact birthday_natCast_mul_wpow_of_plusCount_eq_zero hx n

/-- The omega-map of the simplest member of a cut is a prefix of every fitting omega-map. -/
theorem birthdayTruncation_wpow_eq_of_btwn {s t : Set Surreal.{u}}
    [Small.{u} s] [Small.{u} t] {H : ∀ a ∈ s, ∀ b ∈ t, a < b} {x : Surreal.{u}}
    (hL : ∀ z ∈ s, z < x) (hR : ∀ z ∈ t, x < z) :
    birthdayTruncation (ω^ x) (ω^ (!{s | t}'H)).birthday = ω^ (!{s | t}'H) := by
  rw [ofSets_eq_mk]
  generalize_proofs hn
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
  have ht := hf.wpow.birthdayTruncation_eq
  simpa only [mk_wpow, out_eq] using ht

/-- Every natural multiple of the omega-map of a smaller fitting cut is a prefix. -/
theorem birthdayTruncation_natCast_mul_wpow_eq_of_btwn {s t : Set Surreal.{u}}
    [Small.{u} s] [Small.{u} t] {H : ∀ a ∈ s, ∀ b ∈ t, a < b} {x : Surreal.{u}}
    (hL : ∀ z ∈ s, z < x) (hR : ∀ z ∈ t, x < z) (hx : (!{s | t}'H) < x) (n : ℕ) :
    birthdayTruncation (ω^ x) ((n : Surreal) * ω^ (!{s | t}'H)).birthday =
      (n : Surreal) * ω^ (!{s | t}'H) := by
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
  have hx' : !{out '' s | out '' t} < x.out := by
    rw [← mk_lt_mk, out_eq]
    exact hx
  have ht := (hf.nsmul_wpow hx' n).birthdayTruncation_eq
  simpa only [mk_nsmul, mk_wpow, out_eq, nsmul_eq_mul] using ht

/-- Natural multiples at canonical left exponents are canonical omega-map prefixes. -/
theorem birthdayTruncation_natCast_mul_wpow_birthdayTruncation (x : Surreal.{u})
    (a : NatOrdinal.{u}) (ha : birthdayTruncation x a < x) (n : ℕ) :
    birthdayTruncation (ω^ x) ((n : Surreal) * ω^ birthdayTruncation x a).birthday =
      (n : Surreal) * ω^ birthdayTruncation x a := by
  rw [birthdayTruncation_eq_ofSets x a] at ha ⊢
  exact birthdayTruncation_natCast_mul_wpow_eq_of_btwn
    (s := {z : Surreal | z.birthday < a ∧ z < x})
    (t := {z : Surreal | z.birthday < a ∧ x < z})
    (H := fun _ hz _ hw ↦ hz.2.trans hw.2)
    (fun _ hz ↦ hz.2) (fun _ hz ↦ hz.2) ha n

/-- Smaller canonical exponent prefixes remain canonical after a natural monomial head. -/
theorem birthdayTruncation_natCast_mul_wpow_add (x : Surreal.{u}) (a : NatOrdinal.{u})
    (ha : birthdayTruncation x a < x) (k n : ℕ) :
    birthdayTruncation (((k + 1 : ℕ) : Surreal) * ω^ x)
      ((k : Surreal) * ω^ x + (n : Surreal) * ω^ birthdayTruncation x a).birthday =
      (k : Surreal) * ω^ x + (n : Surreal) * ω^ birthdayTruncation x a := by
  have hp := birthdayTruncation_natCast_mul_wpow_birthdayTruncation x a ha n
  have hc : 0 ≤ (n : Surreal) * ω^ birthdayTruncation x a :=
    mul_nonneg (Nat.cast_nonneg n) (wpow_nonneg _)
  have hcb : (n : Surreal) * ω^ birthdayTruncation x a ≤ ω^ x := by
    have ht := (mul_wpow_lt_wpow (n : ℝ) ha).le
    simpa only [Real.toSurreal_natCast] using ht
  have hsum : (k : Surreal) * ω^ x + ω^ x = ((k + 1 : ℕ) : Surreal) * ω^ x := by
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  have hR : ∀ z ∈ rightPrefixes ((k : Surreal) * ω^ x),
      (k : Surreal) * ω^ x + ω^ x < z := by
    intro z hz
    have hz' : z ∈ rightPrefixes (ω^ x) := by
      cases k with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, rightPrefixes_zero, Set.mem_empty_iff_false] at hz
      | succ k =>
        simpa only [Nat.succ_eq_add_one, rightPrefixes_natCast_mul_wpow] using hz
    rw [hsum]
    exact natCast_mul_wpow_lt_of_mem_rightPrefixes hz' (k + 1)
  have ht := birthdayTruncation_add_left_eq hp hc hcb hR
  rwa [hsum] at ht

/-- The omega-map sends every intrinsic canonical prefix to a canonical prefix. -/
theorem birthdayTruncation_wpow_birthdayTruncation (x : Surreal.{u}) (a : NatOrdinal.{u}) :
    birthdayTruncation (ω^ x) (ω^ birthdayTruncation x a).birthday =
      ω^ birthdayTruncation x a := by
  rw [birthdayTruncation_eq_ofSets x a]
  exact birthdayTruncation_wpow_eq_of_btwn (fun _ hz ↦ hz.2) (fun _ hz ↦ hz.2)

/-- The omega-map cannot decrease the birthday order between a source and its prefix. -/
theorem birthday_wpow_birthdayTruncation_le (x : Surreal.{u}) (a : NatOrdinal.{u}) :
    (ω^ birthdayTruncation x a).birthday ≤ (ω^ x).birthday := by
  rw [← birthdayTruncation_wpow_birthdayTruncation x a]
  exact birthday_birthdayTruncation_le_birthday _ _

/-- A proper exponent prefix gives a strictly younger omega-map prefix. -/
theorem birthday_wpow_birthdayTruncation_lt (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a < x.birthday) : (ω^ birthdayTruncation x a).birthday < (ω^ x).birthday := by
  apply lt_of_le_of_ne (birthday_wpow_birthdayTruncation_le x a)
  intro he
  have hp := birthdayTruncation_wpow_birthdayTruncation x a
  rw [he, birthdayTruncation_birthday] at hp
  have hx : birthdayTruncation x a = x := wpow_inj.mp hp.symm
  have hb := congrArg birthday hx
  rw [birthday_birthdayTruncation x ha.le] at hb
  exact ha.ne hb

/-- The omega-map does not decrease intrinsic birthday. -/
theorem birthday_le_birthday_wpow (x : Surreal.{u}) : x.birthday ≤ (ω^ x).birthday := by
  have aux : ∀ b : NatOrdinal.{u}, ∀ x : Surreal.{u}, x.birthday = b →
      x.birthday ≤ (ω^ x).birthday := by
    intro b
    induction b using NatOrdinal.lt_wf.induction with
    | h b ih =>
      intro x hb
      by_contra h
      have hx : (ω^ x).birthday < x.birthday := lt_of_not_ge h
      have hp := birthday_wpow_birthdayTruncation_lt x hx
      have hq := ih (ω^ x).birthday (hx.trans_eq hb)
        (birthdayTruncation x (ω^ x).birthday) (birthday_birthdayTruncation x hx.le)
      rw [birthday_birthdayTruncation x hx.le] at hq
      exact hp.not_ge hq
  exact aux x.birthday x rfl

/-- On ordinal exponents the omega-map has exactly its ordinal birthday. -/
@[simp]
theorem birthday_wpow_toSurreal (a : NatOrdinal.{u}) :
    (ω^ a.toSurreal).birthday = ω^ a := by
  rw [← toSurreal_wpow, birthday_toSurreal]

end Surreal

end
