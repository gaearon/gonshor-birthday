/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.Shuffle

/-!
# A sharp shuffle bound with a last singleton

Colour the final point of `ω+1` separately from all earlier points. The natural sum `1⊕ω` is the
correct sharp bound, whereas ordinary addition in that colour order gives only `1+ω=ω`.
-/

public noncomputable section

namespace Tests

open Set Ordinal NatOrdinal

private theorem type_compl_top :
    typeLT (({⊤} : Set (WithTop ℕ))ᶜ : Set (WithTop ℕ)) = Ordinal.omega0 := by
  let e : (({⊤} : Set (WithTop ℕ))ᶜ : Set (WithTop ℕ)) ≃o ℕ := {
    toFun x := x.val.untop (by simpa only [mem_compl_iff, mem_singleton_iff] using x.property)
    invFun n := ⟨n, by simp⟩
    left_inv x := Subtype.ext (WithTop.coe_untop ..)
    right_inv n := WithTop.untop_coe n
    map_rel_iff' := by intro x y; simp }
  exact e.ordinalType_congr.trans type_nat_lt

/-- The bound is sharp when a singleton is placed after an omega sequence. -/
theorem shuffle_final_singleton_sharp :
    of (typeLT (WithTop ℕ)) = of (typeLT ({⊤} : Set (WithTop ℕ))) +
      of (typeLT (({⊤} : Set (WithTop ℕ))ᶜ : Set (WithTop ℕ))) := by
  apply (of_type_le_add_of_type_compl ({⊤} : Set (WithTop ℕ))).antisymm
  rw [type_compl_top, type_eq_one_of_unique, type_lt_withTop, type_nat_lt, of_add_one]
  simp [add_comm]

/-- The corresponding ordinary sum is too small. -/
theorem shuffle_final_singleton_ordinary_sum_lt :
    typeLT ({⊤} : Set (WithTop ℕ)) +
      typeLT (({⊤} : Set (WithTop ℕ))ᶜ : Set (WithTop ℕ)) < typeLT (WithTop ℕ) := by
  rw [type_compl_top, type_eq_one_of_unique, type_lt_withTop, type_nat_lt]
  simp

end Tests
