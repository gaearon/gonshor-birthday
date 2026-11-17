/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Inline.Basic
public import CombinatorialGames.Surreal.Basic
public import CombinatorialGames.Game.Classes
public import CombinatorialGames.Game.IGame

/-!
# Direct correspondence between indexed Conway games and native CG

The compact representatives are mapped directly into the pinned CG construction.
The conversion preserves order and all recursive arithmetic before quotienting.
Every native game and every native surreal has a compact representative.
-/

open scoped Pointwise

public noncomputable section

namespace GonshorBirthday.Inline

universe u

abbrev NativeGame := _root_.IGame

noncomputable def Game.toCG : Game.{u} → NativeGame.{u}
  | .mk Left Right left right =>
      _root_.OfSets.ofSets
        (_root_.Player.cases
          (Set.range fun i : Left ↦ Game.toCG (left i))
          (Set.range fun i : Right ↦ Game.toCG (right i))) trivial

/-- The native left and right sets are precisely the images of the indexed options. -/
theorem Game.toCG_mk (Left Right : Type u) (left : Left → Game) (right : Right → Game) :
    Game.toCG (.mk Left Right left right) =
      _root_.OfSets.ofSets (_root_.Player.cases
        (Set.range fun i : Left ↦ Game.toCG (left i))
        (Set.range fun i : Right ↦ Game.toCG (right i))) trivial := by
  rw [Game.toCG]

@[expose] noncomputable def Game.fromCG (x : NativeGame.{u}) : Game.{u} :=
  _root_.IGame.ofSetsRecOn x fun s t _ _ hs ht ↦
    .mk (Shrink s) (Shrink t)
      (fun i ↦
        let z := (equivShrink s).symm i
        hs z.1 z.2)
      (fun i ↦
        let z := (equivShrink t).symm i
        ht z.1 z.2)

theorem Game.fromCG_ofSets (s t : Set NativeGame.{u}) [Small.{u} s] [Small.{u} t] :
    Game.fromCG
        (_root_.OfSets.ofSets
          (_root_.Player.cases s t) trivial) =
      .mk (Shrink s) (Shrink t)
        (fun i ↦ Game.fromCG ((equivShrink s).symm i).1)
        (fun i ↦ Game.fromCG ((equivShrink t).symm i).1) := by
  rw [Game.fromCG,
    _root_.IGame.ofSetsRecOn_ofSets]
  simp only [Game.fromCG]

theorem Game.toCG_fromCG (x : NativeGame.{u}) :
    Game.toCG (Game.fromCG x) = x := by
  induction x using _root_.IGame.ofSetsRecOn with
  | ofSets s t ihs iht =>
      simp only [Game.fromCG,
        _root_.IGame.ofSetsRecOn_ofSets, Game.toCG]
      apply _root_.IGame.ext
      intro p
      simp only [_root_.IGame.moves_ofSets]
      cases p
      · ext z
        constructor
        · rintro ⟨i, rfl⟩
          let y := (equivShrink s).symm i
          change Game.toCG (Game.fromCG y.1) ∈ s
          rw [ihs y.1 y.2]
          exact y.2
        · intro hz
          let i := equivShrink s ⟨z, hz⟩
          refine ⟨i, ?_⟩
          simpa only [i, Equiv.symm_apply_apply, Game.fromCG] using ihs z hz
      · ext z
        constructor
        · rintro ⟨i, rfl⟩
          let y := (equivShrink t).symm i
          change Game.toCG (Game.fromCG y.1) ∈ t
          rw [iht y.1 y.2]
          exact y.2
        · intro hz
          let i := equivShrink t ⟨z, hz⟩
          refine ⟨i, ?_⟩
          simpa only [i, Equiv.symm_apply_apply, Game.fromCG] using iht z hz

theorem Game.toCG_neg (x : Game.{u}) :
    Game.toCG (Game.neg x) = -Game.toCG x := by
  induction x with
  | mk Left Right left right ihLeft ihRight =>
      rw [Game.neg_mk]
      simp only [Game.toCG]
      rw [_root_.IGame.neg_ofSets]
      apply _root_.IGame.ext
      intro p
      simp only [_root_.IGame.moves_ofSets]
      cases p
      · calc
          Set.range (fun i ↦ Game.toCG (Game.neg (right i))) =
              Set.range (fun i ↦ -Game.toCG (right i)) := by
                congr 1
                funext i
                exact ihRight i
          _ = -Set.range (fun i ↦ Game.toCG (right i)) := by
                rw [← Set.image_neg_eq_neg]
                exact Set.range_comp' _ _
      · calc
          Set.range (fun i ↦ Game.toCG (Game.neg (left i))) =
              Set.range (fun i ↦ -Game.toCG (left i)) := by
                congr 1
                funext i
                exact ihLeft i
          _ = -Set.range (fun i ↦ Game.toCG (left i)) := by
                rw [← Set.image_neg_eq_neg]
                exact Set.range_comp' _ _

theorem Game.toCG_le (x y : Game.{u}) :
    Game.Le x y ↔ Game.toCG x ≤ Game.toCG y := by
  induction x, y using Sym2.GameAdd.recursion Game.move_wf with
  | _ x y ih =>
      cases x with
      | mk Lx Rx lx rx =>
        cases y with
        | mk Ly Ry ly ry =>
          rw [Game.le_mk]
          rw [_root_.IGame.le_iff_forall_lf]
          simp only [Game.toCG,
            _root_.IGame.moves_ofSets, Set.forall_mem_range]
          constructor
          · rintro ⟨hLeft, hRight⟩
            constructor
            · intro i h
              exact hLeft i ((ih _ _ (Sym2.GameAdd.snd_fst (Game.Move.left i))).mpr h)
            · intro j h
              exact hRight j ((ih _ _ (Sym2.GameAdd.fst_snd (Game.Move.right j))).mpr h)
          · rintro ⟨hLeft, hRight⟩
            constructor
            · intro i h
              exact hLeft i ((ih _ _ (Sym2.GameAdd.snd_fst (Game.Move.left i))).mp h)
            · intro j h
              exact hRight j ((ih _ _ (Sym2.GameAdd.fst_snd (Game.Move.right j))).mp h)

theorem Game.Numeric.toCG {x : Game.{u}} (h : Game.Numeric x) :
    _root_.IGame.Numeric (Game.toCG x) := by
  induction h with
  | mk hOrder hLeft hRight ihLeft ihRight =>
      rw [_root_.IGame.numeric_def]
      simp only [Game.toCG,
        _root_.IGame.moves_ofSets, Set.forall_mem_range]
      constructor
      · intro i j
        obtain ⟨hij, hji⟩ := Game.less_iff _ _ |>.mp (hOrder i j)
        rw [lt_iff_le_not_ge]
        exact ⟨Game.toCG_le _ _ |>.mp hij,
          fun h ↦ hji (Game.toCG_le _ _ |>.mpr h)⟩
      · intro p
        cases p
        · intro y hy
          obtain ⟨i, rfl⟩ := hy
          exact ihLeft i
        · intro y hy
          obtain ⟨j, rfl⟩ := hy
          exact ihRight j

theorem Game.Numeric.fromCG {x : NativeGame.{u}}
    (h : _root_.IGame.Numeric x) :
    Game.Numeric (Game.fromCG x) := by
  revert h
  induction x using _root_.IGame.ofSetsRecOn with
  | ofSets s t ihLeft ihRight =>
      intro h
      have hdef := _root_.IGame.numeric_def.mp h
      simp only [_root_.IGame.moves_ofSets] at hdef
      rw [Game.fromCG_ofSets]
      apply Game.Numeric.mk
      · intro i j
        let a := (equivShrink s).symm i
        let b := (equivShrink t).symm j
        have hab : a.1 < b.1 := hdef.1 a.1 a.2 b.1 b.2
        obtain ⟨hab, hba⟩ := lt_iff_le_not_ge.mp hab
        apply Game.less_iff _ _ |>.mpr
        constructor
        · apply Game.toCG_le _ _ |>.mpr
          simpa only [Game.toCG_fromCG] using hab
        · intro hrev
          apply hba
          have := Game.toCG_le _ _ |>.mp hrev
          simpa only [Game.toCG_fromCG] using this
      · intro i
        let a := (equivShrink s).symm i
        exact ihLeft a.1 a.2
          (hdef.2 _root_.Player.left a.1 a.2)
      · intro j
        let b := (equivShrink t).symm j
        exact ihRight b.1 b.2
          (hdef.2 _root_.Player.right b.1 b.2)

theorem Game.toCG_add (x y : Game.{u}) :
    Game.toCG (Game.add x y) = Game.toCG x + Game.toCG y := by
  induction x, y using Game.pairRec with
  | _ x y ih =>
      cases x with
      | mk Lx Rx lx rx =>
        cases y with
        | mk Ly Ry ly ry =>
          rw [Game.add_mk]
          simp only [Game.toCG]
          rw [_root_.IGame.ofSets_add_ofSets]
          apply _root_.IGame.ext
          intro p
          simp only [_root_.IGame.moves_ofSets]
          cases p
          · ext z
            simp only [Set.mem_range, Set.mem_union, Set.mem_image]
            constructor
            · rintro ⟨i | j, rfl⟩
              · left
                refine ⟨Game.toCG (lx i), ⟨i, rfl⟩, ?_⟩
                exact (ih (lx i) (.mk Ly Ry ly ry)
                  (Prod.Lex.left _ _ (Game.Move.left i))).symm
              · right
                refine ⟨Game.toCG (ly j), ⟨j, rfl⟩, ?_⟩
                exact (ih (.mk Lx Rx lx rx) (ly j)
                  (Prod.Lex.right _ (Game.Move.left j))).symm
            · rintro (⟨_, ⟨i, rfl⟩, rfl⟩ | ⟨_, ⟨j, rfl⟩, rfl⟩)
              · exact ⟨Sum.inl i, ih _ _ (Prod.Lex.left _ _ (Game.Move.left i))⟩
              · exact ⟨Sum.inr j, ih _ _ (Prod.Lex.right _ (Game.Move.left j))⟩
          · ext z
            simp only [Set.mem_range, Set.mem_union, Set.mem_image]
            constructor
            · rintro ⟨i | j, rfl⟩
              · left
                refine ⟨Game.toCG (rx i), ⟨i, rfl⟩, ?_⟩
                exact (ih (rx i) (.mk Ly Ry ly ry)
                  (Prod.Lex.left _ _ (Game.Move.right i))).symm
              · right
                refine ⟨Game.toCG (ry j), ⟨j, rfl⟩, ?_⟩
                exact (ih (.mk Lx Rx lx rx) (ry j)
                  (Prod.Lex.right _ (Game.Move.right j))).symm
            · rintro (⟨_, ⟨i, rfl⟩, rfl⟩ | ⟨_, ⟨j, rfl⟩, rfl⟩)
              · exact ⟨Sum.inl i, ih _ _ (Prod.Lex.left _ _ (Game.Move.right i))⟩
              · exact ⟨Sum.inr j, ih _ _ (Prod.Lex.right _ (Game.Move.right j))⟩

theorem Game.toCG_mul (x y : Game.{u}) :
    Game.toCG (Game.mul x y) = Game.toCG x * Game.toCG y := by
  induction x, y using Game.pairRec with
  | _ x y ih =>
      cases x with
      | mk Lx Rx lx rx =>
        cases y with
        | mk Ly Ry ly ry =>
          let x := Game.mk Lx Rx lx rx
          let y := Game.mk Ly Ry ly ry
          have option_eq (a b : Game) (ha : Game.Move a x) (hb : Game.Move b y) :
              Game.toCG
                  (Game.add (Game.add (Game.mul a y) (Game.mul x b))
                    (Game.neg (Game.mul a b))) =
                _root_.IGame.mulOption
                  (Game.toCG x) (Game.toCG y)
                  (Game.toCG a) (Game.toCG b) := by
            rw [Game.toCG_add, Game.toCG_add, Game.toCG_neg,
              ih a y (Prod.Lex.left y y ha), ih x b (Prod.Lex.right x hb),
              ih a b (Prod.Lex.left b y ha)]
            rfl
          rw [Game.mul_mk]
          simp only [Game.toCG]
          rw [_root_.IGame.mul_eq]
          apply _root_.IGame.ext
          intro p
          simp only [_root_.IGame.moves_ofSets]
          cases p
          · ext z
            simp only [Set.mem_range, Set.mem_image, Set.mem_union, Set.mem_prod]
            constructor
            · rintro ⟨ij | ij, rfl⟩
              · refine ⟨(Game.toCG (lx ij.1), Game.toCG (ly ij.2)), ?_, ?_⟩
                · left
                  exact ⟨⟨ij.1, rfl⟩, ⟨ij.2, rfl⟩⟩
                · exact (option_eq _ _ (Game.Move.left ij.1) (Game.Move.left ij.2)).symm
              · refine ⟨(Game.toCG (rx ij.1), Game.toCG (ry ij.2)), ?_, ?_⟩
                · right
                  exact ⟨⟨ij.1, rfl⟩, ⟨ij.2, rfl⟩⟩
                · exact (option_eq _ _ (Game.Move.right ij.1) (Game.Move.right ij.2)).symm
            · rintro ⟨⟨a, b⟩, (⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ | ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩), rfl⟩
              · exact ⟨Sum.inl (i, j),
                  option_eq _ _ (Game.Move.left i) (Game.Move.left j)⟩
              · exact ⟨Sum.inr (i, j),
                  option_eq _ _ (Game.Move.right i) (Game.Move.right j)⟩
          · ext z
            simp only [Set.mem_range, Set.mem_image, Set.mem_union, Set.mem_prod]
            constructor
            · rintro ⟨ij | ij, rfl⟩
              · refine ⟨(Game.toCG (lx ij.1), Game.toCG (ry ij.2)), ?_, ?_⟩
                · left
                  exact ⟨⟨ij.1, rfl⟩, ⟨ij.2, rfl⟩⟩
                · exact (option_eq _ _ (Game.Move.left ij.1) (Game.Move.right ij.2)).symm
              · refine ⟨(Game.toCG (rx ij.1), Game.toCG (ly ij.2)), ?_, ?_⟩
                · right
                  exact ⟨⟨ij.1, rfl⟩, ⟨ij.2, rfl⟩⟩
                · exact (option_eq _ _ (Game.Move.right ij.1) (Game.Move.left ij.2)).symm
            · rintro ⟨⟨a, b⟩, (⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ | ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩), rfl⟩
              · exact ⟨Sum.inl (i, j),
                  option_eq _ _ (Game.Move.left i) (Game.Move.right j)⟩
              · exact ⟨Sum.inr (i, j),
                  option_eq _ _ (Game.Move.right i) (Game.Move.left j)⟩

/-- Numericity is exactly the native CG predicate under the direct conversion. -/
theorem Game.numeric_iff_toCG (x : Game.{u}) :
    Game.Numeric x ↔ _root_.IGame.Numeric (Game.toCG x) := by
  refine ⟨fun h ↦ h.toCG, ?_⟩
  induction x with
  | mk Left Right left right ihLeft ihRight =>
    intro h
    have hd := _root_.IGame.numeric_def.mp h
    simp only [Game.toCG, _root_.IGame.moves_ofSets] at hd
    apply Game.Numeric.mk
    · intro i j
      have hlt := hd.1 _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      rw [lt_iff_le_not_ge] at hlt
      apply (Game.less_iff _ _).mpr
      exact ⟨(Game.toCG_le _ _).mpr hlt.1,
        fun h ↦ hlt.2 ((Game.toCG_le _ _).mp h)⟩
    · intro i
      exact ihLeft i (hd.2 _root_.Player.left _ ⟨i, rfl⟩)
    · intro i
      exact ihRight i (hd.2 _root_.Player.right _ ⟨i, rfl⟩)

/-- The compact empty cut is the native zero game. -/
theorem Game.toCG_zero : Game.toCG Game.zero = (0 : _root_.IGame.{u}) := by
  rw [Game.zero_eq, Game.toCG_mk]
  apply _root_.IGame.ext
  intro p
  cases p <;> simp only [_root_.IGame.moves_ofSets, _root_.IGame.moves_zero,
    Set.range_eq_empty_iff, isEmpty_ulift] <;> infer_instance

/-- The compact cut with zero as its sole left option is the native unit game. -/
theorem Game.toCG_one : Game.toCG Game.one = (1 : _root_.IGame.{u}) := by
  rw [Game.one_eq, Game.toCG_mk, _root_.IGame.one_def]
  apply _root_.IGame.ext
  intro p
  cases p <;> simp only [_root_.IGame.moves_ofSets, Game.toCG_zero,
    Set.range_const, Set.range_eq_empty_iff, isEmpty_ulift]
  infer_instance

noncomputable def Surreal.toCG (x : Surreal.{u}) :
    _root_.Surreal.{u} :=
  @_root_.Surreal.mk _ x.numeric.toCG

theorem Surreal.toCG_eq (x : Surreal.{u}) :
    x.toCG = @_root_.Surreal.mk _ x.numeric.toCG :=
  (rfl)

noncomputable def Surreal.fromCG
    (x : _root_.Surreal.{u}) : Surreal.{u} :=
  ⟨Game.fromCG x.out, Game.Numeric.fromCG inferInstance⟩

theorem Surreal.fromCG_game
    (x : _root_.Surreal.{u}) :
    (Surreal.fromCG x).game = Game.fromCG x.out := (rfl)

theorem Surreal.toCG_fromCG
    (x : _root_.Surreal.{u}) :
    (Surreal.fromCG x).toCG = x := by
  let : _root_.IGame.Numeric
      (Game.toCG (Surreal.fromCG x).game) :=
    (Surreal.fromCG x).numeric.toCG
  rw [Surreal.toCG_eq]
  calc
    _root_.Surreal.mk
        (Game.toCG (Surreal.fromCG x).game) =
        _root_.Surreal.mk x.out := by
      apply _root_.Surreal.mk_eq
      have heq : Game.toCG (Surreal.fromCG x).game = x.out :=
        congrArg Game.toCG (Surreal.fromCG_game x) |>.trans
          (Game.toCG_fromCG x.out)
      rw [heq]
    _ = x := _root_.Surreal.out_eq x

theorem Surreal.gameEquivalent_iff_toCG_eq (x y : Surreal.{u}) :
    Game.Equivalent x.game y.game ↔ x.toCG = y.toCG := by
  let : _root_.IGame.Numeric (Game.toCG x.game) :=
    x.numeric.toCG
  let : _root_.IGame.Numeric (Game.toCG y.game) :=
    y.numeric.toCG
  rw [Surreal.toCG_eq, Surreal.toCG_eq,
    _root_.Surreal.mk_eq_mk, Game.equivalent_iff]
  change (Game.Le x.game y.game ∧ Game.Le y.game x.game) ↔
    (Game.toCG x.game ≤ Game.toCG y.game ∧
      Game.toCG y.game ≤ Game.toCG x.game)
  rw [Game.toCG_le, Game.toCG_le]

/-- Numeric indexed games quotiented by Conway equivalence. -/
def Surreal.QuotientModel : Type (u + 1) :=
  Quotient
    { r := fun x y : Surreal.{u} ↦ Game.Equivalent x.game y.game
      iseqv := ⟨
        fun x ↦ Surreal.gameEquivalent_iff_toCG_eq x x |>.mpr rfl,
        fun h ↦ Surreal.gameEquivalent_iff_toCG_eq _ _ |>.mpr
          (Surreal.gameEquivalent_iff_toCG_eq _ _ |>.mp h).symm,
        fun hxy hyz ↦ Surreal.gameEquivalent_iff_toCG_eq _ _ |>.mpr
          ((Surreal.gameEquivalent_iff_toCG_eq _ _ |>.mp hxy).trans
            (Surreal.gameEquivalent_iff_toCG_eq _ _ |>.mp hyz))⟩ }

noncomputable def Surreal.QuotientModel.toCG : Surreal.QuotientModel.{u} →
    _root_.Surreal.{u} :=
  Quotient.lift Surreal.toCG fun _ _ h ↦
    Surreal.gameEquivalent_iff_toCG_eq _ _ |>.mp h

universe v

theorem Surreal.QuotientModel.toCG_bijective :
    Function.Bijective Surreal.QuotientModel.toCG.{v} := by
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂ x y ?_ hxy
    intro x y h
    apply Quotient.sound
    exact Surreal.gameEquivalent_iff_toCG_eq x y |>.mpr h
  · intro (x : _root_.Surreal.{v})
    exact ⟨Quotient.mk _ (Surreal.fromCG x), Surreal.toCG_fromCG x⟩

/-- The quotient of the compact numeric games is equivalent to native CG surreals. -/
noncomputable def Surreal.quotientEquivCG : Surreal.QuotientModel.{v} ≃
    _root_.Surreal.{v} :=
  Equiv.ofBijective Surreal.QuotientModel.toCG.{v}
    Surreal.QuotientModel.toCG_bijective

end GonshorBirthday.Inline
