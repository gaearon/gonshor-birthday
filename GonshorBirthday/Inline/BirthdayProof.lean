/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Inline.Birthday
public import GonshorBirthday.Inline.Bridge
public import CombinatorialGames.Surreal.Birthday.Basic
public import CombinatorialGames.Game.Birthday

/-! # Agreement of intrinsic birthdays -/

universe u
public noncomputable section
namespace GonshorBirthday.Inline

/-- The visible game-tree rank equals the native game's birthday. -/
theorem Game.rank_eq_toCG (x : Game.{u}) : rank x = (toCG x).birthday.val := by
  induction x with
  | mk Left Right left right ihLeft ihRight =>
      rw [rank_mk, toCG_mk, _root_.IGame.birthday_ofSets]
      simp only [← Set.range_comp]
      change max (⨆ i : Left, Order.succ (rank (left i)))
          (⨆ j : Right, Order.succ (rank (right j))) =
        max (⨆ i : Left, ((toCG (left i)).birthday + 1).val)
          (⨆ j : Right, ((toCG (right j)).birthday + 1).val)
      simp only [NatOrdinal.val_add_one, Order.succ_eq_add_one]
      congr 1
      · congr 1
        funext i
        rw [ihLeft i]
      · congr 1
        funext j
        rw [ihRight j]

/-- The displayed minimum over numeric representatives is CG's intrinsic birthday. -/
theorem Game.birthday_eq_toCG (x : Game.{u}) (hx : Numeric x) :
    birthday x = (@_root_.Surreal.mk (toCG x) hx.toCG).birthday.val := by
  let : _root_.IGame.Numeric (toCG x) := hx.toCG
  let sx : _root_.Surreal.{u} := .mk (toCG x)
  change birthday x = sx.birthday.val
  have equiv_iff (y : Game.{u}) (hy : Numeric y) :
      Equivalent x y ↔ sx = @_root_.Surreal.mk (toCG y) hy.toCG := by
    let : _root_.IGame.Numeric (toCG y) := hy.toCG
    rw [equivalent_iff, _root_.Surreal.mk_eq_mk]
    exact and_congr (toCG_le x y) (toCG_le y x)
  obtain ⟨z, hz, hzx, hzb⟩ := _root_.Surreal.birthday_eq_iGameBirthday sx
  let y := fromCG z
  have hy : Numeric y := Numeric.fromCG hz
  have he : Equivalent x y := (equiv_iff y hy).mpr (by
    simpa only [y, toCG_fromCG] using hzx.symm)
  have hr : rank y = sx.birthday.val := by
    rw [rank_eq_toCG, toCG_fromCG, hzb]
  have hm : sx.birthday.val ∈ rank '' {y | Numeric y ∧ Equivalent x y} :=
    ⟨y, ⟨hy, he⟩, hr⟩
  rw [birthday_eq]
  apply le_antisymm
  · exact csInf_le' hm
  · apply le_csInf ⟨_, hm⟩
    rintro _ ⟨w, ⟨hw, hew⟩, rfl⟩
    rw [rank_eq_toCG]
    apply NatOrdinal.val.monotone
    let : _root_.IGame.Numeric (toCG w) := hw.toCG
    rw [(equiv_iff w hw).mp hew]
    exact _root_.Surreal.birthday_mk_le _

end GonshorBirthday.Inline
