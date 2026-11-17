/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Canonical
public import GonshorBirthday.Surreal.Birthday.PlusCount

/-!
# Canonical addition cuts and plus counts
-/

universe u

public noncomputable section

namespace Surreal
open Set IGame

/-- A nonnegative fitting summand can be translated past a head with distant right options. -/
theorem _root_.IGame.Fits.add_left_of_nonneg {a b c : IGame.{u}}
    [Numeric a] [Numeric b] [Numeric c] (h : Fits b c) (hc : 0 ≤ c) (hcb : c ≤ b)
    (hR : ∀ z ∈ aᴿ, a + b < z) : Fits (a + b) (a + c) := by
  constructor
  · intro z hz
    rw [moves_add] at hz
    rcases hz with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · exact (add_lt_add_of_lt_of_le (Numeric.left_lt hw) hcb).not_ge
    · numeric
      have hwb : w < b := by
        rw [← mk_lt_mk, lt_iff_not_ge, mk_le_mk]
        exact h.1 w hw
      exact (add_lt_add_right hwb a).not_ge
  · intro z hz
    rw [moves_add] at hz
    rcases hz with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · exact ((hR w hw).trans_le (le_add_of_nonneg_right hc)).not_ge
    · numeric
      have hbw : b < w := by
        rw [← mk_lt_mk, lt_iff_not_ge, mk_le_mk]
        exact h.2 w hw
      exact (add_lt_add_right hbw a).not_ge

/-- Addition of two surreal cuts has the usual two families of options on each side. -/
theorem ofSets_add_ofSets {s₁ t₁ s₂ t₂ : Set Surreal.{u}}
    [Small.{u} s₁] [Small.{u} t₁] [Small.{u} s₂] [Small.{u} t₂]
    {H₁ : ∀ x ∈ s₁, ∀ y ∈ t₁, x < y} {H₂ : ∀ x ∈ s₂, ∀ y ∈ t₂, x < y} :
    !{s₁ | t₁}'H₁ + !{s₂ | t₂}'H₂ =
      !{(· + !{s₂ | t₂}'H₂) '' s₁ ∪ (!{s₁ | t₁}'H₁ + ·) '' s₂ |
        (· + !{s₂ | t₂}'H₂) '' t₁ ∪ (!{s₁ | t₁}'H₁ + ·) '' t₂}'(by
          rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
          · exact add_lt_add_left (H₁ x hx y hy) _
          · exact add_lt_add (lt_ofSets_of_mem_left hx) (ofSets_lt_of_mem_right hy)
          · exact add_lt_add (ofSets_lt_of_mem_right hy) (lt_ofSets_of_mem_left hx)
          · exact add_lt_add_right (H₂ x hx y hy) _) := by
  conv_lhs =>
    rw [ofSets_eq_mk, ofSets_eq_mk, ← mk_add]
    simp only [IGame.ofSets_add_ofSets]
  apply toGame.injective
  rw [toGame_mk, Game.mk_ofSets, toGame_ofSets]
  have hfa (a : IGame.{u}) : (fun z : Surreal.{u} ↦ Game.mk (z.out + a)) =
      (fun z ↦ toGame z + Game.mk a) := by
    funext z
    exact (Game.mk_add z.out a).trans (congrArg (· + Game.mk a) (gameMk_out z))
  have hfb (a : IGame.{u}) : (fun z : Surreal.{u} ↦ Game.mk (a + z.out)) =
      (fun z ↦ Game.mk a + toGame z) := by
    funext z
    exact (Game.mk_add a z.out).trans (congrArg (Game.mk a + ·) (gameMk_out z))
  simp only [Set.image_union, Set.image_image]
  simp only [hfa, hfb]
  simp only [Game.mk_ofSets, Set.image_image, gameMk_out, toGame_add, toGame_ofSets]

/-- The canonical addition cut uses a canonical prefix on one side at a time. -/
theorem add_eq_ofSets_leftPrefixes (x y : Surreal.{u}) :
    x + y = !{(· + y) '' leftPrefixes x ∪ (x + ·) '' leftPrefixes y |
      (· + y) '' rightPrefixes x ∪ (x + ·) '' rightPrefixes y}'(by
        rintro _ (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) _ (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
        all_goals
          have ha' := (mem_leftPrefixes.mp ha).choose_spec.2.2
          have hb' := (mem_rightPrefixes.mp hb).choose_spec.2.2
        · exact add_lt_add_left (ha'.trans hb') _
        · exact add_lt_add ha' hb'
        · exact add_lt_add hb' ha'
        · exact add_lt_add_right (ha'.trans hb') _) := by
  simpa only [ofSets_leftPrefixes_rightPrefixes] using
    (ofSets_add_ofSets (H₁ := leftPrefixes_lt_rightPrefixes x)
      (H₂ := leftPrefixes_lt_rightPrefixes y))

/-- Every canonical left option of a sum is bounded by an option from one summand. -/
theorem exists_leftPrefixes_add_ge {x y z : Surreal.{u}} (hz : z ∈ leftPrefixes (x + y)) :
    (∃ a ∈ leftPrefixes x, z ≤ a + y) ∨ (∃ b ∈ leftPrefixes y, z ≤ x + b) := by
  have hzx : z < x + y := (mem_leftPrefixes.mp hz).choose_spec.2.2
  have hzb : z.birthday < (x + y).birthday := birthday_lt_of_mem_leftPrefixes hz
  rw [add_eq_ofSets_leftPrefixes] at hzx hzb
  obtain ⟨w, hw, hzw⟩ := exists_mem_left_ge_of_birthday_lt hzx hzb
  rcases hw with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
  · exact Or.inl ⟨a, ha, hzw⟩
  · exact Or.inr ⟨b, hb, hzw⟩

/-- Every canonical right option of a sum bounds an option from one summand. -/
theorem exists_rightPrefixes_add_le {a b v : Surreal.{u}}
    (hv : v ∈ rightPrefixes (a + b)) :
    (∃ u ∈ rightPrefixes a, u + b ≤ v) ∨ (∃ u ∈ rightPrefixes b, a + u ≤ v) := by
  have hev : a + b < v := (mem_rightPrefixes_iff.mp hv).2
  have hvb := birthday_lt_of_mem_rightPrefixes hv
  rw [add_eq_ofSets_leftPrefixes] at hev hvb
  obtain ⟨w, hw, hwv⟩ := exists_mem_right_le_of_birthday_lt hev hvb
  rcases hw with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
  · exact Or.inl ⟨u, hu, hwv⟩
  · exact Or.inr ⟨u, hu, hwv⟩

/-- Left prefixes of a natural multiple are bounded by a shifted prefix of one summand. -/
theorem exists_leftPrefixes_natCast_mul_ge (x : Surreal.{u}) (n : ℕ)
    {z : Surreal.{u}} (hz : z ∈ leftPrefixes (((n + 1 : ℕ) : Surreal) * x)) :
    ∃ a ∈ leftPrefixes x, z ≤ (n : Surreal) * x + a := by
  induction n generalizing z with
  | zero =>
    simp only [zero_add, Nat.cast_one, one_mul] at hz
    exact ⟨z, hz, by simp⟩
  | succ n ih =>
    have he : ((n + 2 : ℕ) : Surreal) * x = ((n + 1 : ℕ) : Surreal) * x + x := by
      change (((n + 1) + 1 : ℕ) : Surreal) * x = _
      rw [Nat.cast_add (n + 1) 1, Nat.cast_one, add_mul, one_mul]
    change z ∈ leftPrefixes (((n + 2 : ℕ) : Surreal) * x) at hz
    rw [he] at hz
    rcases exists_leftPrefixes_add_ge hz with ⟨a, ha, hza⟩ | ⟨a, ha, hza⟩
    · obtain ⟨b, hb, hab⟩ := ih ha
      refine ⟨b, hb, hza.trans ?_⟩
      calc
        a + x ≤ ((n : Surreal) * x + b) + x := add_le_add_left hab x
        _ = ((n + 1 : ℕ) : Surreal) * x + b := by
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_right_comm]
    · exact ⟨a, ha, hza⟩

/-- The plus count of a sum is at most the natural sum of the plus counts. See van den Dries
and Ehrlich, *Fields of surreal numbers and exponentiation*, Lemma 3.4(1). -/
theorem plusCount_add_le (x y : Surreal.{u}) :
    plusCount (x + y) ≤ plusCount x + plusCount y := by
  have aux : ∀ b : NatOrdinal.{u}, ∀ x y : Surreal.{u}, x.birthday + y.birthday = b →
      plusCount (x + y) ≤ plusCount x + plusCount y := by
    intro b
    induction b using NatOrdinal.lt_wf.induction with
    | h b ih =>
      intro x y hb
      apply (plusCount_le_iff_forall_birthdayTruncation (x + y) _).mpr
      intro a ha hl
      have hz : birthdayTruncation (x + y) a ∈ leftPrefixes (x + y) :=
        mem_leftPrefixes.mpr ⟨a, ha, rfl, hl⟩
      rcases exists_leftPrefixes_add_ge hz with ⟨u, hu, hzu⟩ | ⟨v, hv, hzv⟩
      · have hux : u < x := (mem_leftPrefixes.mp hu).choose_spec.2.2
        have hu' : u.birthday + y.birthday < b := by
          rw [← hb]
          exact add_lt_add_of_lt_of_le (birthday_lt_of_mem_leftPrefixes hu) le_rfl
        have hc := plusCount_le_of_left_between ha.le hzu (add_le_add_left hux.le y)
        exact (hc.trans (ih _ hu' u y rfl)).trans_lt
          (add_lt_add_of_lt_of_le (plusCount_lt_of_mem_leftPrefixes hu) le_rfl)
      · have hvy : v < y := (mem_leftPrefixes.mp hv).choose_spec.2.2
        have hv' : x.birthday + v.birthday < b := by
          rw [← hb]
          exact add_lt_add_of_le_of_lt le_rfl (birthday_lt_of_mem_leftPrefixes hv)
        have hc := plusCount_le_of_left_between ha.le hzv (add_le_add_right hvy.le x)
        exact (hc.trans (ih _ hv' x v rfl)).trans_lt
          (add_lt_add_of_le_of_lt le_rfl (plusCount_lt_of_mem_leftPrefixes hv))
  exact aux _ x y rfl

/-- A nonnegative canonical prefix translates past a head with distant right prefixes. -/
theorem birthdayTruncation_add_left_eq {a b c : Surreal.{u}}
    (hp : birthdayTruncation b c.birthday = c) (hc : 0 ≤ c) (hcb : c ≤ b)
    (hR : ∀ z ∈ rightPrefixes a, a + b < z) :
    birthdayTruncation (a + b) (a + c).birthday = a + c := by
  have heA := ofSets_eq_mk (s := leftPrefixes a) (t := rightPrefixes a)
    (H := leftPrefixes_lt_rightPrefixes a)
  generalize_proofs at heA
  rw [ofSets_leftPrefixes_rightPrefixes] at heA
  let A : IGame.{u} := !{out '' leftPrefixes a | out '' rightPrefixes a}
  have : Numeric A := by assumption
  change a = mk A at heA
  have heC := ofSets_eq_mk (s := leftPrefixes c) (t := rightPrefixes c)
    (H := leftPrefixes_lt_rightPrefixes c)
  generalize_proofs at heC
  rw [ofSets_leftPrefixes_rightPrefixes] at heC
  let C : IGame.{u} := !{out '' leftPrefixes c | out '' rightPrefixes c}
  have : Numeric C := by assumption
  change c = mk C at heC
  have hbc : c.birthday ≤ b.birthday := by
    have ht := birthday_birthdayTruncation_le_birthday b c.birthday
    rwa [hp] at ht
  have hf : Fits b.out C := by
    constructor
    · intro z hz
      change z ∈ (!{out '' leftPrefixes c | out '' rightPrefixes c} : IGame)ᴸ at hz
      rw [moves_left_ofSets] at hz
      obtain ⟨z, hz, rfl⟩ := hz
      have hzc := (mem_leftPrefixes.mp hz).choose_spec.2.2
      have hzb : z < b := (lt_birthdayTruncation_iff hbc
        (birthday_lt_of_mem_leftPrefixes hz)).mp (by rwa [hp])
      rw [← mk_le_mk, out_eq, out_eq]
      exact hzb.not_ge
    · intro z hz
      change z ∈ (!{out '' leftPrefixes c | out '' rightPrefixes c} : IGame)ᴿ at hz
      rw [moves_right_ofSets] at hz
      obtain ⟨z, hz, rfl⟩ := hz
      have hcz := (mem_rightPrefixes.mp hz).choose_spec.2.2
      have hbz : b < z := (birthdayTruncation_lt_iff hbc
        (birthday_lt_of_mem_rightPrefixes hz)).mp (by rwa [hp])
      rw [← mk_le_mk, out_eq, out_eq]
      exact hbz.not_ge
  have hc' : 0 ≤ C := by
    rw [← mk_le_mk, mk_zero, ← heC]
    exact hc
  have hcb' : C ≤ b.out := by
    rw [← mk_le_mk, ← heC, out_eq]
    exact hcb
  have hR' : ∀ z ∈ Aᴿ, A + b.out < z := by
    intro z hz
    change z ∈ (!{out '' leftPrefixes a | out '' rightPrefixes a} : IGame)ᴿ at hz
    rw [moves_right_ofSets] at hz
    obtain ⟨z, hz, rfl⟩ := hz
    rw [← mk_lt_mk, mk_add, ← heA, out_eq, out_eq]
    exact hR z hz
  have ht := (hf.add_left_of_nonneg hc' hcb' hR').birthdayTruncation_eq
  simpa only [mk_add, ← heA, ← heC, out_eq] using ht

/-- Sharp plus-count addition forbids cancellation of nonempty canonical suffixes. -/
theorem birthdayTruncation_eq_of_add_eq_of_plusCount_add_eq (x y : Surreal.{u})
    {a b : NatOrdinal.{u}} (ha : a ≤ x.birthday) (hb : b ≤ y.birthday)
    (hs : birthdayTruncation x a + birthdayTruncation y b = x + y)
    (hc : plusCount (x + y) = plusCount x + plusCount y) :
    birthdayTruncation x a = x ∧ birthdayTruncation y b = y := by
  have hxa := plusCount_birthdayTruncation_le x ha
  have hyb := plusCount_birthdayTruncation_le y hb
  have hsum : plusCount x + plusCount y ≤
      plusCount (birthdayTruncation x a) + plusCount (birthdayTruncation y b) := by
    rw [← hc, ← hs]
    exact plusCount_add_le _ _
  have hxe : plusCount (birthdayTruncation x a) = plusCount x := by
    apply hxa.antisymm
    by_contra h
    exact (add_lt_add_of_lt_of_le (lt_of_not_ge h) hyb).not_ge hsum
  have hye : plusCount (birthdayTruncation y b) = plusCount y := by
    apply hyb.antisymm
    by_contra h
    exact (add_lt_add_of_le_of_lt hxa (lt_of_not_ge h)).not_ge hsum
  have hx : x ≤ birthdayTruncation x a := le_birthdayTruncation_of_plusCount_eq x ha hxe
  have hy : y ≤ birthdayTruncation y b := le_birthdayTruncation_of_plusCount_eq y hb hye
  have hx' : birthdayTruncation x a ≤ x := by
    have h := (add_le_add_right hy (birthdayTruncation x a)).trans_eq hs
    simpa only [add_le_add_iff_right] using h
  have hy' : birthdayTruncation y b ≤ y := by
    have h := (add_le_add_left hx (birthdayTruncation y b)).trans_eq hs
    simpa only [add_le_add_iff_left] using h
  exact ⟨hx'.antisymm hx, hy'.antisymm hy⟩

end Surreal
