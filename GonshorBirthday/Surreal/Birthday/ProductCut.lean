/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Canonical
public import CombinatorialGames.Surreal.Division

/-!
# Canonical product option cofinality

The four Conway multiplication families use actual canonical prefixes of the
factors. Every output prefix is bounded by an option on its corresponding side.
-/

universe u
public noncomputable section
namespace Surreal
open Set IGame

/-- Every canonical left product prefix is bounded by a same-side multiplication option. -/
theorem exists_leftPrefixes_mul_ge {x y z : Surreal.{u}}
    (hz : z ∈ leftPrefixes (x * y)) :
    (∃ a ∈ leftPrefixes x, ∃ b ∈ leftPrefixes y, z ≤ a * y + x * b - a * b) ∨
      (∃ a ∈ rightPrefixes x, ∃ b ∈ rightPrefixes y, z ≤ a * y + x * b - a * b) := by
  have hx := ofSets_eq_mk (s := leftPrefixes x) (t := rightPrefixes x)
    (H := leftPrefixes_lt_rightPrefixes x)
  have hy := ofSets_eq_mk (s := leftPrefixes y) (t := rightPrefixes y)
    (H := leftPrefixes_lt_rightPrefixes y)
  generalize_proofs at hx hy
  rw [ofSets_leftPrefixes_rightPrefixes] at hx hy
  let g : IGame.{u} := !{out '' leftPrefixes x | out '' rightPrefixes x}
  let f : IGame.{u} := !{out '' leftPrefixes y | out '' rightPrefixes y}
  have : Numeric g := by assumption
  have : Numeric f := by assumption
  change x = mk g at hx
  change y = mk f at hy
  have hprod : mk (g * f) = x * y := by rw [mk_mul, ← hx, ← hy]
  have hzb := birthday_lt_of_mem_leftPrefixes hz
  have hzx := (mem_leftPrefixes_iff.mp hz).2
  have hn : ¬ Fits z.out (g * f) := by
    intro h
    have hb := h.surrealBirthday_le
    exact hzb.not_ge (by simpa only [hprod, out_eq] using hb)
  rw [not_fits_iff] at hn
  rcases hn with ⟨v, hv, hzv⟩ | ⟨v, hv, hvz⟩
  · have hm : ∃ v ∈ (g * f)ᴸ, z.out ≤ v := ⟨v, hv, hzv⟩
    rw [exists_moves_mul] at hm
    obtain ⟨p, a, ha, b, hb, hab⟩ := hm
    cases p
    · simp only [Player.mul_left] at hb
      rw [moves_left_ofSets] at ha hb
      obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      refine Or.inl ⟨a, ha, b, hb, ?_⟩
      simpa only [mulOption, mk_add, mk_sub, mk_mul, out_eq, ← hx, ← hy] using
        mk_le_mk.mpr hab
    · simp only [Player.mul_left] at hb
      rw [moves_right_ofSets] at ha hb
      obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      refine Or.inr ⟨a, ha, b, hb, ?_⟩
      simpa only [mulOption, mk_add, mk_sub, mk_mul, out_eq, ← hx, ← hy] using
        mk_le_mk.mpr hab
  · numeric
    have ht := mk_lt_mk.mpr ((Numeric.lt_right hv).trans_le hvz)
    have ht' : x * y < z := by simpa only [hprod, out_eq] using ht
    exact False.elim (hzx.not_gt ht')

/-- Every canonical right product prefix bounds an opposite-side multiplication option. -/
theorem exists_rightPrefixes_mul_le {x y z : Surreal.{u}}
    (hz : z ∈ rightPrefixes (x * y)) :
    (∃ a ∈ leftPrefixes x, ∃ b ∈ rightPrefixes y, a * y + x * b - a * b ≤ z) ∨
      (∃ a ∈ rightPrefixes x, ∃ b ∈ leftPrefixes y, a * y + x * b - a * b ≤ z) := by
  have hx := ofSets_eq_mk (s := leftPrefixes x) (t := rightPrefixes x)
    (H := leftPrefixes_lt_rightPrefixes x)
  have hy := ofSets_eq_mk (s := leftPrefixes y) (t := rightPrefixes y)
    (H := leftPrefixes_lt_rightPrefixes y)
  generalize_proofs at hx hy
  rw [ofSets_leftPrefixes_rightPrefixes] at hx hy
  let g : IGame.{u} := !{out '' leftPrefixes x | out '' rightPrefixes x}
  let f : IGame.{u} := !{out '' leftPrefixes y | out '' rightPrefixes y}
  have : Numeric g := by assumption
  have : Numeric f := by assumption
  change x = mk g at hx
  change y = mk f at hy
  have hprod : mk (g * f) = x * y := by rw [mk_mul, ← hx, ← hy]
  have hzb := birthday_lt_of_mem_rightPrefixes hz
  have hzx := (mem_rightPrefixes_iff.mp hz).2
  have hn : ¬ Fits z.out (g * f) := by
    intro h
    have hb := h.surrealBirthday_le
    exact hzb.not_ge (by simpa only [hprod, out_eq] using hb)
  rw [not_fits_iff] at hn
  rcases hn with ⟨v, hv, hzv⟩ | ⟨v, hv, hvz⟩
  · numeric
    have ht := mk_lt_mk.mpr (hzv.trans_lt (Numeric.left_lt hv))
    have ht' : z < x * y := by simpa only [hprod, out_eq] using ht
    exact False.elim (hzx.not_gt ht')
  · have hm : ∃ v ∈ (g * f)ᴿ, v ≤ z.out := ⟨v, hv, hvz⟩
    rw [exists_moves_mul] at hm
    obtain ⟨p, a, ha, b, hb, hab⟩ := hm
    cases p
    · simp only [Player.mul_right, Player.neg_left] at hb
      rw [moves_left_ofSets] at ha
      rw [moves_right_ofSets] at hb
      obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      refine Or.inl ⟨a, ha, b, hb, ?_⟩
      simpa only [mulOption, mk_add, mk_sub, mk_mul, out_eq, ← hx, ← hy] using
        mk_le_mk.mpr hab
    · simp only [Player.mul_right, Player.neg_right] at hb
      rw [moves_right_ofSets] at ha
      rw [moves_left_ofSets] at hb
      obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      refine Or.inr ⟨a, ha, b, hb, ?_⟩
      simpa only [mulOption, mk_add, mk_sub, mk_mul, out_eq, ← hx, ← hy] using
        mk_le_mk.mpr hab

end Surreal
