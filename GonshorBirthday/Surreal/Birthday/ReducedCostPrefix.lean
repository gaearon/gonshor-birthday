/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCost

import GonshorBirthday.NatOrdinal.OrderedSum

/-!
# Reduced costs of prefixes and cofinal limits

A canonical prefix has exactly the earlier retained positions of the full word, with their
original weights. This identifies the cost as an ordinary prefix sum followed by its tail,
and bounds the complete cost from cofinal families of retained canonical prefixes.
-/

universe u

public noncomputable section

namespace Surreal

open Ordinal

/-- The cost before a retained position is exactly the sum of the earlier retained blocks. -/
theorem reducedOmegaCost_birthdayTruncation_eq_iio (C x : Surreal.{u})
    (j : reducedOmegaPositions C x) :
    reducedOmegaCost C (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1)) =
      NatOrdinal.of (1 + typeLT (Σₗ i : Set.Iio j,
        (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType)) := by
  let a : NatOrdinal.{u} := NatOrdinal.of j.1.toOrd.1
  have ha : a < x.birthday := NatOrdinal.of.strictMono j.1.toOrd.2
  rw [reducedOmegaCost_eq_of_birthday_eq C (birthday_birthdayTruncation x ha.le)]
  let S := {i : a.val.ToType |
    birthdayTruncation (birthdayTruncation x a) (NatOrdinal.of i.toOrd.1) <
      birthdayTruncation x a ∨
    birthdayTruncation (birthdayTruncation x a) (NatOrdinal.of i.toOrd.1) ≤ C}
  have hv (i : a.val.ToType) :
      birthdayTruncation (birthdayTruncation x a) (NatOrdinal.of i.toOrd.1) =
        birthdayTruncation x (NatOrdinal.of i.toOrd.1) :=
    birthdayTruncation_birthdayTruncation x (NatOrdinal.of.strictMono i.toOrd.2).le ha.le
  let f : S → Set.Iio j := fun i ↦
    ⟨⟨Ordinal.ToType.mk ⟨i.1.toOrd.1, i.1.toOrd.2.trans (NatOrdinal.val.strictMono ha)⟩, by
      apply mem_reducedOmegaPositions.mpr
      simp only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply]
      have h := i.2
      change _ ∨ _ at h
      rw [hv i.1] at h
      exact h.imp_left ((birthdayTruncation_lt_birthdayTruncation_iff x
        (NatOrdinal.of.strictMono i.1.toOrd.2) ha.le).mp)⟩, by
      change Ordinal.ToType.mk _ < j.1
      apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
      rw [OrderIso.symm_apply_apply]
      change i.1.toOrd.1 < j.1.toOrd.1
      exact i.1.toOrd.2.trans_eq (NatOrdinal.val_of _)⟩
  have hf : StrictMono f := by
    intro i k hik
    change Ordinal.ToType.mk _ < Ordinal.ToType.mk _
    exact Ordinal.ToType.mk.strictMono (Ordinal.ToType.mk.symm.strictMono hik)
  have honto : Function.Surjective f := by
    rintro ⟨i, hij⟩
    have hia : i.1.toOrd.1 < a.val := by
      have h := Ordinal.ToType.mk.symm.strictMono hij
      change i.1.toOrd.1 < j.1.toOrd.1 at h
      exact h.trans_eq (NatOrdinal.val_of _).symm
    let i' : a.val.ToType := Ordinal.ToType.mk ⟨i.1.toOrd.1, hia⟩
    have hi' : i' ∈ S := by
      have hi := mem_reducedOmegaPositions.mp i.2
      change _ ∨ _
      rw [hv i']
      simp only [i', Ordinal.ToType.toOrd, OrderIso.symm_apply_apply]
      exact hi.imp_left ((birthdayTruncation_lt_birthdayTruncation_iff x
        (NatOrdinal.of.strictMono hia) ha.le).mpr)
    refine ⟨⟨i', hi'⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Ordinal.ToType.mk.symm.injective
    apply Subtype.ext
    simp only [f, i', Ordinal.ToType.toOrd, OrderIso.symm_apply_apply]
  let e : S ≃o Set.Iio j := OrderIso.ofSurjective (OrderEmbedding.ofStrictMono f hf) honto
  let W (i : S) := (ω^ (plusCount (birthdayTruncation (birthdayTruncation x a)
    (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType
  let V (i : Set.Iio j) := (ω^ (plusCount (birthdayTruncation x
    (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType
  change NatOrdinal.of (1 + typeLT (Σₗ i : S, W i)) =
    NatOrdinal.of (1 + typeLT (Σₗ i : Set.Iio j, V i))
  apply congrArg NatOrdinal.of
  congr 1
  apply Ordinal.type_sigma_congr W V e
  intro i
  change typeLT (W i) = typeLT (V (f i))
  simp only [W, V, Ordinal.type_toType, f, Ordinal.ToType.toOrd,
    OrderIso.symm_apply_apply, hv]

/-- The full cost is the prefix cost followed by the retained tail, using ordinary addition. -/
theorem reducedOmegaCost_eq_prefix_add_tail (C x : Surreal.{u})
    (j : reducedOmegaPositions C x) :
    reducedOmegaCost C x = NatOrdinal.of
      ((reducedOmegaCost C (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1))).val +
        typeLT (Σₗ i : Set.Ici j,
          (ω^ (plusCount (birthdayTruncation x
            (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType)) := by
  rw [reducedOmegaCost_birthdayTruncation_eq_iio, NatOrdinal.val_of,
    reducedOmegaCost_eq_positions, omegaExpansionLength_eq,
    Ordinal.type_sigma_eq_add_iio_ici _ j, add_assoc]

/-- A retained position contributes its entire original block after its actual prefix cost. -/
theorem reducedOmegaCost_prefix_add_block_le (C x : Surreal.{u})
    (j : reducedOmegaPositions C x) :
    NatOrdinal.of ((reducedOmegaCost C
        (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1))).val +
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1)) + 1)).val) ≤
        reducedOmegaCost C x := by
  rw [reducedOmegaCost_eq_prefix_add_tail C x j]
  apply NatOrdinal.of.monotone
  apply add_le_add_right
  simpa only [Ordinal.type_toType] using
    (Ordinal.type_sigma_block_le (fun i : Set.Ici j ↦
      (ω^ (plusCount (birthdayTruncation x
        (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType) ⟨j, le_refl j⟩)

/-- A retained canonical right prefix is followed by its full original minus block. -/
theorem reducedOmegaCost_add_block_le_of_mem_rightPrefixes {C x y : Surreal.{u}}
    (hy : y ∈ rightPrefixes x) (hyC : y ≤ C) :
    NatOrdinal.of ((reducedOmegaCost C y).val + (ω^ (plusCount y + 1)).val) ≤
      reducedOmegaCost C x := by
  obtain ⟨a, ha, hxa, _⟩ := mem_rightPrefixes.mp hy
  let j : reducedOmegaPositions C x :=
    ⟨Ordinal.ToType.mk ⟨a.val, NatOrdinal.val.strictMono ha⟩, by
      apply mem_reducedOmegaPositions.mpr
      right
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val, hxa]
        using hyC⟩
  simpa only [j, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val, hxa]
    using reducedOmegaCost_prefix_add_block_le C x j

/-- Bounds on cofinally many retained prefixes bound the entire reduced cost. -/
theorem reducedOmegaCost_le_of_cofinal_prefixes (C x : Surreal.{u}) (M : NatOrdinal.{u})
    (hM : 1 ≤ M)
    (hm : ∀ i : reducedOmegaPositions C x, ∃ j : reducedOmegaPositions C x,
      i < j ∧ reducedOmegaCost C (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1)) ≤ M) :
    reducedOmegaCost C x ≤ M := by
  rw [reducedOmegaCost_eq_positions, omegaExpansionLength_eq]
  apply NatOrdinal.of.monotone
  change 1 + typeLT (Σₗ i : reducedOmegaPositions C x,
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType) ≤ M.val
  apply Ordinal.add_type_sigma_le_of_cofinal_prefixes
  · exact NatOrdinal.val.monotone hM
  · intro i
    obtain ⟨j, hij, hj⟩ := hm i
    refine ⟨j, hij, ?_⟩
    rw [reducedOmegaCost_birthdayTruncation_eq_iio] at hj
    exact NatOrdinal.val.monotone hj

/-- Cofinal retained right prefixes suffice to control the complete expanded cost. -/
theorem reducedOmegaCost_le_of_cofinal_rightPrefixes (C x : Surreal.{u})
    (M : NatOrdinal.{u}) (hM : 1 ≤ M)
    (hc : ∀ a < x.birthday, ∃ y ∈ rightPrefixes x, a < y.birthday ∧ y ≤ C)
    (hb : ∀ y ∈ rightPrefixes x, y ≤ C → reducedOmegaCost C y ≤ M) :
    reducedOmegaCost C x ≤ M := by
  apply reducedOmegaCost_le_of_cofinal_prefixes C x M hM
  intro i
  obtain ⟨y, hy, hiy, hyC⟩ := hc (NatOrdinal.of i.1.toOrd.1)
    (NatOrdinal.of.strictMono i.1.toOrd.2)
  obtain ⟨a, ha, hxa, _⟩ := mem_rightPrefixes.mp hy
  have hya : y.birthday = a := by
    rw [← hxa, birthday_birthdayTruncation x ha.le]
  let j : reducedOmegaPositions C x :=
    ⟨Ordinal.ToType.mk ⟨a.val, NatOrdinal.val.strictMono ha⟩, by
      apply mem_reducedOmegaPositions.mpr
      right
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val, hxa]
        using hyC⟩
  refine ⟨j, ?_, ?_⟩
  · change i.1 < Ordinal.ToType.mk _
    apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
    rw [OrderIso.symm_apply_apply]
    change i.1.toOrd.1 < a.val
    have h := NatOrdinal.val.strictMono hiy
    rw [NatOrdinal.val_of, hya] at h
    exact h
  · simpa only [j, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val, hxa]
      using hb y hy hyC

end Surreal
