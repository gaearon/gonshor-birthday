/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostPrefix
public import GonshorBirthday.Surreal.Birthday.Constant

import GonshorBirthday.NatOrdinal.PowerSum
import GonshorBirthday.NatOrdinal.OrderedSum

/-!
# Plus portions and remaining-plus budgets

A nonempty final retained portion consisting of plus signs contributes exactly the
omega power of the total original plus count. Earlier prefix costs and all retained
block weights remain in their original order.
-/

universe u

public noncomputable section

namespace Surreal

open Ordinal

private theorem plusCount_position_mono (x : Surreal.{u}) {a b : NatOrdinal.{u}}
    (hab : a ≤ b) (hb : b ≤ x.birthday) :
    plusCount (birthdayTruncation x a) ≤ plusCount (birthdayTruncation x b) := by
  have ha : a ≤ (birthdayTruncation x b).birthday := by
    rw [birthday_birthdayTruncation x hb]
    exact hab
  simpa only [birthdayTruncation_birthdayTruncation x hab hb] using
    plusCount_birthdayTruncation_le (birthdayTruncation x b) ha

private theorem plusCount_position_lt (x : Surreal.{u}) {a b : NatOrdinal.{u}}
    (hab : a < b) (hb : b ≤ x.birthday) (hl : birthdayTruncation x a < x) :
    plusCount (birthdayTruncation x a) < plusCount (birthdayTruncation x b) := by
  have ha : a < (birthdayTruncation x b).birthday := by
    rw [birthday_birthdayTruncation x hb]
    exact hab
  have hv := birthdayTruncation_birthdayTruncation x hab.le hb
  have h := plusCount_birthdayTruncation_lt (birthdayTruncation x b) ha
    (by rw [hv]; exact (birthdayTruncation_lt_birthdayTruncation_iff x hab hb).mpr hl)
  rwa [hv] at h

private theorem plusCount_cofinal_retained_tail (C x : Surreal.{u})
    (j : reducedOmegaPositions C x) :
    ∀ b < plusCount x, ∃ i : Set.Ici j,
      b ≤ plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) := by
  intro b hb
  obtain ⟨z, hz, hbz⟩ := exists_leftPrefixes_plusCount_ge hb
  obtain ⟨a, ha, hxa, hl⟩ := mem_leftPrefixes.mp hz
  let k : reducedOmegaPositions C x :=
    ⟨Ordinal.ToType.mk ⟨a.val, NatOrdinal.val.strictMono ha⟩, by
      apply mem_reducedOmegaPositions.mpr
      left
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val, hxa]
        using hl⟩
  refine ⟨⟨max j k, le_max_left j k⟩, ?_⟩
  have hk : b ≤ plusCount (birthdayTruncation x (NatOrdinal.of k.1.toOrd.1)) := by
    simpa only [k, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val, hxa]
      using hbz
  apply hk.trans
  apply plusCount_position_mono x
  · exact NatOrdinal.of.monotone (Ordinal.ToType.mk.symm.monotone (le_max_right j k))
  · exact (NatOrdinal.of.strictMono (max j k).1.toOrd.2).le

private theorem omega_le_retained_tail (C x : Surreal.{u}) (j : reducedOmegaPositions C x) :
    Ordinal.omega0 ≤ typeLT (Σₗ i : Set.Ici j,
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType) := by
  let W (i : Set.Ici j) :=
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType
  have h := Ordinal.type_sigma_block_le W ⟨j, le_refl j⟩
  rw [Ordinal.type_toType] at h
  apply le_trans ?_ h
  change Ordinal.omega0 ≤ (ω^ (plusCount (birthdayTruncation x
    (NatOrdinal.of j.1.toOrd.1)) + 1)).val
  simpa only [NatOrdinal.wpow_one, NatOrdinal.val_of] using
    NatOrdinal.val.monotone (NatOrdinal.wpow_le_wpow.mpr
      (show (1 : NatOrdinal.{u}) ≤
        plusCount (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1)) + 1 from
          le_add_of_nonneg_left bot_le))

/-- A nonempty final retained portion of pluses contributes the full final plus-count power. -/
theorem reducedOmegaCost_eq_prefix_add_wpow_of_plus_tail (C x : Surreal.{u})
    (j : reducedOmegaPositions C x)
    (hplus : ∀ i : Set.Ici j, birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1) < x) :
    reducedOmegaCost C x = NatOrdinal.of
      ((reducedOmegaCost C (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1))).val +
        (ω^ plusCount x).val) := by
  let p (i : Set.Ici j) := plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1))
  have hp : StrictMono p := by
    intro i k hik
    apply plusCount_position_lt x
    · exact NatOrdinal.of.strictMono (Ordinal.ToType.mk.symm.strictMono hik)
    · exact (NatOrdinal.of.strictMono k.1.1.toOrd.2).le
    · exact hplus i
  have he := NatOrdinal.of_one_add_type_sigma_wpow_eq p (plusCount x) hp
    (fun i ↦ plusCount_birthdayTruncation_lt x
      (NatOrdinal.of.strictMono i.1.1.toOrd.2) (hplus i))
    (plusCount_cofinal_retained_tail C x j)
  rw [Ordinal.one_add_of_omega0_le (omega_le_retained_tail C x j)] at he
  have hev := congrArg NatOrdinal.val he
  rw [NatOrdinal.val_of] at hev
  rw [reducedOmegaCost_eq_prefix_add_tail C x j, hev]

/-- Appending a nonempty plus block adds its exact final plus-count power to the reduced cost. -/
theorem reducedOmegaCost_appendPluses (C x : Surreal.{u}) {a : Ordinal.{u}} (ha : a ≠ 0) :
    reducedOmegaCost C (appendPluses x a) = NatOrdinal.of
      ((reducedOmegaCost C x).val + (ω^ plusCount (appendPluses x a)).val) := by
  have hba : x.birthday < (appendPluses x a).birthday := by
    simpa only [appendPluses_zero] using strictMono_birthday_appendPluses x
      (pos_iff_ne_zero.mpr ha)
  let j : reducedOmegaPositions C (appendPluses x a) :=
    ⟨Ordinal.ToType.mk ⟨x.birthday.val, NatOrdinal.val.strictMono hba⟩, by
      apply mem_reducedOmegaPositions.mpr
      left
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply,
        NatOrdinal.of_val, birthdayTruncation_appendPluses, appendPluses_zero] using
          strictMono_appendPluses x (pos_iff_ne_zero.mpr ha)⟩
  have hp (i : Set.Ici j) : birthdayTruncation (appendPluses x a)
      (NatOrdinal.of i.1.1.toOrd.1) < appendPluses x a := by
    apply birthdayTruncation_appendPluses_lt
    · have hi := Ordinal.ToType.mk.symm.monotone i.2
      change (Ordinal.ToType.mk _).toOrd.1 ≤ i.1.1.toOrd.1 at hi
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val] using
        NatOrdinal.of.monotone hi
    · exact NatOrdinal.of.strictMono i.1.1.toOrd.2
  simpa only [j, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val,
    birthdayTruncation_appendPluses] using
      reducedOmegaCost_eq_prefix_add_wpow_of_plus_tail C (appendPluses x a) j hp

/-- Appending one plus contributes its original omega-power block. -/
theorem reducedOmegaCost_appendPlus (C x : Surreal.{u}) :
    reducedOmegaCost C (appendPlus x) = NatOrdinal.of
      ((reducedOmegaCost C x).val + (ω^ (plusCount x + 1)).val) := by
  simpa only [appendPluses_one, plusCount_appendPlus] using
    reducedOmegaCost_appendPluses C x one_ne_zero

/-- A prefix missing a later plus has strictly smaller reduced cost at every cutoff. -/
theorem reducedOmegaCost_birthdayTruncation_lt_of_plusCount_lt (C x : Surreal.{u})
    {a : NatOrdinal.{u}} (ha : a ≤ x.birthday)
    (hp : plusCount (birthdayTruncation x a) < plusCount x) :
    reducedOmegaCost C (birthdayTruncation x a) < reducedOmegaCost C x := by
  obtain ⟨z, hz, hpz⟩ := exists_leftPrefixes_plusCount_ge hp
  obtain ⟨b, hb, hxb, hl⟩ := mem_leftPrefixes.mp hz
  have hab : a ≤ b := by
    apply le_of_not_gt
    intro hba
    have h := plusCount_position_lt x hba ha (hxb ▸ hl)
    rw [hxb] at h
    exact h.not_ge hpz
  have ha' : a ≤ (birthdayTruncation x b).birthday := by
    rw [birthday_birthdayTruncation x hb.le]
    exact hab
  have h := reducedOmegaCost_birthdayTruncation_le C (birthdayTruncation x b) ha'
  rw [birthdayTruncation_birthdayTruncation x hab hb.le, hxb] at h
  exact h.trans_lt (reducedOmegaCost_lt_of_mem_leftPrefixes C hz)

/-- A retained minus and any later plus pay for both original blocks in their original order. -/
theorem reducedOmegaCost_add_block_add_wpow_le_of_mem_rightPrefixes {C x y : Surreal.{u}}
    (hy : y ∈ rightPrefixes x) (hyC : y ≤ C) (hp : plusCount y < plusCount x) :
    NatOrdinal.of ((reducedOmegaCost C y).val + (ω^ (plusCount y + 1)).val +
      (ω^ plusCount x).val) ≤ reducedOmegaCost C x := by
  obtain ⟨a, ha, rfl, hr⟩ := mem_rightPrefixes.mp hy
  have ha1 : a + 1 ≤ x.birthday := Order.add_one_le_iff.mpr ha
  have he := birthdayTruncation_add_one_eq_appendMinus x ha1 hr
  have hp' : plusCount (birthdayTruncation x (a + 1)) < plusCount x := by
    rw [he, plusCount_appendMinus]
    exact hp
  have hs := reducedOmegaCost_birthdayTruncation_lt_of_plusCount_lt C x ha1 hp'
  have hR : birthdayTruncation x a ∈ rightPrefixes (appendMinus (birthdayTruncation x a)) :=
    mem_rightPrefixes_iff.mpr
      ⟨birthdayTruncation_appendMinus _, appendMinus_lt _⟩
  have hblock := reducedOmegaCost_add_block_le_of_mem_rightPrefixes hR hyC
  rw [← he] at hblock
  simpa only [NatOrdinal.val_of] using
    oadd_wpow_plusCount_le_reducedOmegaCost (hblock.trans_lt hs)

/-- A retained right prefix pays its next minus block and the final power of any later pluses. -/
theorem reducedOmegaCost_rightPrefix_budget {C x y : Surreal.{u}}
    (hy : y ∈ rightPrefixes x) (hyC : y ≤ C) :
    NatOrdinal.of ((reducedOmegaCost C y).val + (ω^ (plusCount y + 1)).val +
      if plusCount y < plusCount x then (ω^ plusCount x).val else 0) ≤
        reducedOmegaCost C x := by
  split_ifs with hp
  · exact reducedOmegaCost_add_block_add_wpow_le_of_mem_rightPrefixes hy hyC hp
  · simpa only [add_zero] using reducedOmegaCost_add_block_le_of_mem_rightPrefixes hy hyC

end Surreal
