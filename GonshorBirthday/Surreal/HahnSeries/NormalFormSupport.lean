/-
Copyright (c) 2026 Dan Abramov, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Surreal.Birthday.Basic
public import CombinatorialGames.Surreal.Pow

/-!
# Support lemmas for the Conway normal-form construction

These inequalities and equivalences are used in the axiom-free Conway normal-form construction
of CombinatorialGames PR #263. Their names, statements, and namespaces agree with the
corresponding upstream declarations.
-/

public noncomputable section

universe u

namespace Surreal

theorem birthday_eq_iInf_fits (x : IGame) [hx : IGame.Numeric x] :
    birthday (.mk x) =
      ⨅ y : {y : Subtype IGame.Numeric // IGame.Fits y x}, birthday (.mk y.1.1) := by
  let f (y : {y : Subtype IGame.Numeric // IGame.Fits y x}) := birthday (.mk y.1)
  let : Inhabited {y : Subtype IGame.Numeric // IGame.Fits y x} :=
    ⟨⟨x, hx⟩, IGame.Fits.refl _⟩
  apply (ciInf_le' f default).antisymm'
  obtain ⟨⟨⟨y, _⟩, hy⟩, hy'⟩ := ciInf_mem f
  obtain ⟨z, _, hz, hz'⟩ := birthday_eq_iGameBirthday (.mk y)
  rw [← hz'.trans hy']
  apply (birthday_mk_le z).trans'
  congr! 1
  rw [eq_comm, mk_eq_mk] at hz ⊢
  refine (hy.congr hz).equiv_of_forall_birthday_le fun w hw hw' ↦ hz' ▸ ?_
  exact hy'.trans_le <| (ciInf_le' f ⟨⟨w, hw⟩, hw'⟩).trans (birthday_mk_le _)

end Surreal

namespace IGame

theorem Fits.birthday_le {x y : IGame} [hx : Numeric x] [Numeric y] (h : Fits x y) :
    Surreal.birthday (.mk y) ≤ Surreal.birthday (.mk x) := by
  let f (x : {x : Subtype Numeric // Fits x y}) := Surreal.birthday (.mk x.1)
  rw [Surreal.birthday_eq_iInf_fits y]
  exact ciInf_le' f ⟨⟨x, hx⟩, h⟩

theorem Fits.birthday_lt {x y : IGame} [Numeric x] [Numeric y]
    (h : Fits x y) (he : ¬ x ≈ y) : Surreal.birthday (.mk y) < Surreal.birthday (.mk x) := by
  apply h.birthday_le.lt_of_not_ge
  contrapose he
  obtain ⟨z, _, hz, hz'⟩ := Surreal.birthday_eq_iGameBirthday (.mk x)
  rw [← hz'] at he
  rw [eq_comm, Surreal.mk_eq_mk] at hz
  exact hz.trans <| (h.congr hz).equiv_of_forall_birthday_le fun w _ hw ↦
    he.trans (hw.birthday_le.trans <| Surreal.birthday_mk_le _)

end IGame
