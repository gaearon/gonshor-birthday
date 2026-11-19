/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.PrefixSums
public import GonshorBirthday.Surreal.Birthday.ReducedCostPrefix
import GonshorBirthday.Surreal.Birthday.ReducedCostEndpoint
import GonshorBirthday.Surreal.Birthday.ReducedCostSuffix
import GonshorBirthday.NatOrdinal.ProductSum
import GonshorBirthday.NatOrdinal.OrderedSumBound
import GonshorBirthday.NatOrdinal.FinalPower

/-!
# Translating exponents by ordinals

Every right prefix of `a + γ`, for `γ` an ordinal, has the form `u + γ` for a unique
right prefix of `a`. A left prefix has the form `a₀ + δ` with `δ ≤ γ`. Reading a right
prefix in both descriptions bounds its block weight using the smaller of the two ordinals.
-/

universe u
public noncomputable section
open Ordinal

namespace Surreal

/-- An order-preserving assignment of the retained minuses bounds their total expanded length.
The pluses, including the initial sign, have total length `ω ^ plusCount z`. -/
private theorem reducedCost_le_of_minus_translation {z a C A t : Surreal.{u}} {δ : NatOrdinal.{u}}
    (h : ∀ w ∈ rightPrefixes z, w ≤ C →
      w - t ∈ rightPrefixes a ∧ w - t ≤ A ∧ plusCount w ≤ plusCount (w - t) + δ) :
    reducedOmegaCost C z ≤ reducedOmegaCost A a * ω^ δ + ω^ plusCount z := by
  let I := reducedOmegaPositions C z
  let atZ (i : I) := birthdayTruncation z (NatOrdinal.of i.1.toOrd.1)
  let M : Set I := {i | z < atZ i}
  let W (v : Surreal.{u}) := ω^ (plusCount v + 1)
  have hm (i : M) : atZ i.1 ∈ rightPrefixes z :=
    mem_rightPrefixes.mpr ⟨_, NatOrdinal.of.strictMono i.1.1.toOrd.2, rfl, i.2⟩
  have hc (i : M) : atZ i.1 ≤ C :=
    (mem_reducedOmegaPositions.mp i.1.2).resolve_left (not_lt_of_gt i.2)
  let u (i : M) := atZ i.1 - t
  have hu (i : M) : u i ∈ rightPrefixes a ∧ u i ≤ A ∧ plusCount (atZ i.1) ≤ plusCount (u i) + δ :=
    h _ (hm i) (hc i)
  let pos (i : M) : reducedOmegaPositions A a :=
    ⟨Ordinal.ToType.mk ⟨(u i).birthday.val,
      NatOrdinal.val.strictMono (birthday_lt_of_mem_rightPrefixes (hu i).1)⟩, by
      apply mem_reducedOmegaPositions.mpr
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val,
        (mem_rightPrefixes_iff.mp (hu i).1).1] using Or.inr (hu i).2.1⟩
  have hpos : StrictMono pos := by
    intro i j hij
    have hidx : NatOrdinal.of i.1.1.toOrd.1 < NatOrdinal.of j.1.1.toOrd.1 :=
      NatOrdinal.of.strictMono (Ordinal.ToType.mk.symm.strictMono hij)
    have hval : atZ j.1 < atZ i.1 := birthdayTruncation_lt
      ((birthday_birthdayTruncation_le z _).trans_lt hidx) i.2
    exact Ordinal.ToType.mk.strictMono (NatOrdinal.val.strictMono
      (birthday_lt_of_rightPrefixes_lt (hu i).1 (hu j).1 (sub_lt_sub_right hval t)))
  let atA (i : reducedOmegaPositions A a) := birthdayTruncation a (NatOrdinal.of i.1.toOrd.1)
  have hp (i : M) : atA (pos i) = u i := by
    simpa only [atA, pos, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val]
      using (mem_rightPrefixes_iff.mp (hu i).1).1
  have hw (i : M) : W (atZ i.1) ≤ W (atA (pos i)) * ω^ δ := by
    rw [hp, ← NatOrdinal.wpow_add]
    apply NatOrdinal.wpow_le_wpow.mpr
    simpa only [add_right_comm (plusCount (u i))] using add_le_add (hu i).2.2 (le_refl 1)
  have hminus : NatOrdinal.of (typeLT (Σₗ i : M, (W (atZ i.1)).val.ToType)) ≤
      reducedOmegaCost A a * ω^ δ := by
    have he := Ordinal.type_sigma_le_of_embedding
      (A := fun i : M ↦ (W (atZ i.1)).val.ToType)
      (B := fun i : reducedOmegaPositions A a ↦ (W (atA i) * ω^ δ).val.ToType)
      (OrderEmbedding.ofStrictMono pos hpos) (fun i ↦ OrderEmbedding.ofStrictMono
        (fun v ↦ Ordinal.ToType.mk ⟨v.toOrd.1, v.toOrd.2.trans_le (NatOrdinal.val.monotone (hw i))⟩)
        (fun _ _ h ↦ Ordinal.ToType.mk.strictMono (Ordinal.ToType.mk.symm.strictMono h)))
    apply (NatOrdinal.of.monotone he).trans
    apply (NatOrdinal.of_type_sigma_mul_const_le (fun i ↦ W (atA i)) (ω^ δ)).trans
    apply mul_le_mul' _ le_rfl
    rw [reducedOmegaCost_eq_positions, omegaExpansionLength_eq]
    exact NatOrdinal.of.monotone le_add_self
  rw [reducedOmegaCost_eq_positions]
  exact (omegaExpansionLength_le_minus_add_wpow z I).trans (add_le_add hminus le_rfl)

private theorem plusCount_le_of_rightPrefixes_le {a u v : Surreal.{u}}
    (hu : u ∈ rightPrefixes a) (hv : v ∈ rightPrefixes a) (h : u ≤ v) :
    plusCount v ≤ plusCount u := by
  rcases h.lt_or_eq with h | rfl
  · have hb := (birthday_lt_of_rightPrefixes_lt hv hu h).le
    have he : birthdayTruncation u v.birthday = v := by
      rw [← (mem_rightPrefixes_iff.mp hu).1,
        birthdayTruncation_birthdayTruncation a hb (birthday_lt_of_mem_rightPrefixes hu).le,
        (mem_rightPrefixes_iff.mp hv).1]
    simpa only [he] using plusCount_birthdayTruncation_le u hb
  · rfl

/-- At the original cutoff every strict left prefix leaves room in the product. -/
theorem reducedOmegaCost_lt_of_leftPrefix_add_toSurreal {a z : Surreal.{u}}
    (A : Surreal.{u}) (γ : NatOrdinal.{u}) (hz : z ∈ leftPrefixes (a + γ.toSurreal)) :
    reducedOmegaCost (A + γ.toSurreal) z < reducedOmegaCost A a * ω^ γ := by
  obtain ⟨x, hx, y, hy, he⟩ := exists_add_eq_of_mem_leftPrefixes hz
  obtain ⟨δ, hδ, rfl⟩ : ∃ δ ≤ γ, δ.toSurreal = y := by
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ⟨γ, le_rfl, rfl⟩
    · obtain ⟨δ, hd, h, _⟩ := mem_leftPrefixes.mp hy
      rw [birthday_toSurreal] at hd
      exact ⟨δ, hd.le, (birthdayTruncation_toSurreal hd.le).symm.trans h⟩
  have hsmall (w : Surreal.{u}) (hw : w ∈ rightPrefixes z) :
      w - δ.toSurreal ∈ rightPrefixes x := by
    exact sub_toSurreal_mem_rightPrefixes δ (by rwa [he])
  have hpc (w : Surreal.{u}) : plusCount w ≤ plusCount (w - δ.toSurreal) + δ := by
    simpa only [sub_add_cancel, plusCount_toSurreal] using
      plusCount_add_le (w - δ.toSurreal) δ.toSurreal
  have hN : ∀ p ∈ NatOrdinal.cantorSupport (reducedOmegaCost A a * ω^ γ),
      plusCount (a + γ.toSurreal) ≤ p := by
    intro p hp
    apply (plusCount_add_le a γ.toSurreal).trans
    rw [plusCount_toSurreal]
    exact NatOrdinal.le_cantorSupport_mul (plusCount_le_cantorSupport_reducedOmegaCost A a)
      (by simp [NatOrdinal.cantorSupport_wpow]) p hp
  have hp := NatOrdinal.wpow_lt_wpow.mpr (plusCount_lt_of_mem_leftPrefixes hz)
  rcases hδ.lt_or_eq with hδ | hd
  · have hx' : birthdayTruncation a x.birthday = x := by
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact birthdayTruncation_birthday _
      · exact (mem_leftPrefixes_iff.mp hx).1
    have h := reducedCost_le_of_minus_translation (z := z) (a := a)
      (C := A + γ.toSurreal) (A := A) (t := γ.toSurreal) (δ := δ) (by
        intro w hw hwC
        have hu := sub_toSurreal_mem_rightPrefixes γ
          (rightPrefixes_subset_of_birthdayTruncation_eq (mem_leftPrefixes_iff.mp hz).1 hw)
        have hv := rightPrefixes_subset_of_birthdayTruncation_eq hx' (hsmall w hw)
        have hle := sub_le_sub_left (NatOrdinal.toSurreal.monotone hδ.le) w
        exact ⟨hu, sub_le_iff_le_add.mpr hwC,
          (hpc w).trans (add_le_add (plusCount_le_of_rightPrefixes_le hu hv hle) le_rfl)⟩)
    exact h.trans_lt (NatOrdinal.add_lt_of_lt_last_power
      (mul_lt_mul_of_pos_left (NatOrdinal.wpow_lt_wpow.mpr hδ)
        (zero_lt_one.trans_le (one_le_reducedOmegaCost A a))) hp hN)
  · subst δ
    have hxa : x ∈ leftPrefixes a := (Set.mem_insert_iff.mp hx).resolve_left
      (fun h ↦ (mem_leftPrefixes_iff.mp hz).2.ne (he.symm.trans (congrArg (· + γ.toSurreal) h)))
    have h := reducedCost_le_of_minus_translation (z := z) (a := x)
      (C := A + γ.toSurreal) (A := A) (t := γ.toSurreal) (δ := γ)
      (fun w hw hwC ↦ ⟨hsmall w hw, sub_le_iff_le_add.mpr hwC, hpc w⟩)
    exact h.trans_lt (NatOrdinal.add_lt_of_lt_last_power
      (mul_lt_mul_of_pos_right (reducedOmegaCost_lt_of_mem_leftPrefixes A hxa)
        (NatOrdinal.wpow_pos γ)) hp hN)

/-- Translating an exponent and its cutoff by an ordinal costs at most the corresponding
power of omega in natural multiplication. -/
theorem reducedOmegaCost_add_toSurreal_le (a A : Surreal.{u}) (γ : NatOrdinal.{u}) :
    reducedOmegaCost (A + γ.toSurreal) (a + γ.toSurreal) ≤ reducedOmegaCost A a * ω^ γ := by
  let g := γ.toSurreal
  have hs : ∀ p ∈ NatOrdinal.cantorSupport (reducedOmegaCost A a * ω^ γ),
      plusCount (a + g) ≤ p := by
    intro p hp
    apply (plusCount_add_le a g).trans
    rw [plusCount_toSurreal]
    exact NatOrdinal.le_cantorSupport_mul (plusCount_le_cantorSupport_reducedOmegaCost A a)
      (by simp [NatOrdinal.cantorSupport_wpow]) p hp
  apply (reducedOmegaCost_le_iff_leftPrefixes_lt _ hs _).mpr
  · exact fun _ hz ↦ reducedOmegaCost_lt_of_leftPrefix_add_toSurreal A γ hz
  · simpa only [one_mul, NatOrdinal.wpow_zero] using mul_le_mul'
      (one_le_reducedOmegaCost A a) (NatOrdinal.wpow_le_wpow.mpr (show 0 ≤ γ from bot_le))
  · intro w hw hwC
    let u := w - g
    have hu : u ∈ rightPrefixes a := sub_toSurreal_mem_rightPrefixes γ hw
    have hbound : reducedOmegaCost (A + g) w ≤ reducedOmegaCost A u * ω^ γ := by
      simpa only [u, g, sub_add_cancel] using reducedOmegaCost_add_toSurreal_le u A γ
    have hweight : ω^ (plusCount w + 1) ≤ ω^ (plusCount u + 1) * ω^ γ := by
      rw [← NatOrdinal.wpow_add, add_right_comm (plusCount u)]
      apply NatOrdinal.wpow_le_wpow.mpr
      have hc : plusCount w ≤ plusCount u + γ := by
        simpa only [u, g, sub_add_cancel, plusCount_toSurreal] using plusCount_add_le u g
      exact add_le_add hc le_rfl
    exact (NatOrdinal.of.monotone (add_le_add (NatOrdinal.val.monotone hbound)
      (NatOrdinal.val.monotone hweight))).trans
      ((NatOrdinal.of_oadd_mul_le _ _ (ω^ γ)).trans (mul_le_mul'
        (reducedOmegaCost_add_block_le_of_mem_rightPrefixes hu (sub_le_iff_le_add.mpr hwC)) le_rfl))
termination_by a.birthday.val
decreasing_by exact NatOrdinal.val.strictMono (birthday_lt_of_mem_rightPrefixes hu)

end Surreal
