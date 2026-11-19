/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Addition

/-!
# The prefixes of a sum

A right prefix of a sum is the sum of two prefixes on the right, allowing either input
itself. The analogous statement holds on the left. Fornasiero's proof that the sum of two
initial sets is initial uses the same descent (Integration on Surreal Numbers, Lemma 4.7).
Keeping track of the side makes the gap above the sum a sum of nonnegative input gaps.
-/

universe u

public noncomputable section

namespace Surreal

/-- Split a right prefix of a sum into an upper prefix of each input, allowing the input itself. -/
theorem exists_add_eq_of_mem_rightPrefixes {a b z : Surreal.{u}}
    (hz : z ∈ rightPrefixes (a + b)) :
    ∃ x ∈ insert a (rightPrefixes a), ∃ y ∈ insert b (rightPrefixes b), x + y = z := by
  have descend {s : Surreal.{u}} (hs : a + b ≤ s) (hsz : s ≤ z) :
      s = z ∨ z ∈ rightPrefixes s := by
    rcases hsz.eq_or_lt with he | h
    · exact Or.inl he
    · apply Or.inr
      obtain ⟨ht, _⟩ := mem_rightPrefixes_iff.mp hz
      have hp := birthdayTruncation_eq_of_right_between (birthday_lt_of_mem_rightPrefixes hz).le
        hs (h.le.trans_eq ht.symm)
      exact mem_rightPrefixes_iff.mpr ⟨hp.trans ht, h⟩
  rcases exists_rightPrefixes_add_le hz with ⟨t, ht, htz⟩ | ⟨t, ht, htz⟩
  · rcases descend (add_le_add (mem_rightPrefixes_iff.mp ht).2.le le_rfl) htz with he | h
    · exact ⟨t, Set.mem_insert_of_mem _ ht, b, Set.mem_insert _ _, he⟩
    · obtain ⟨x, hx, y, hy, he⟩ := exists_add_eq_of_mem_rightPrefixes h
      refine ⟨x, Set.mem_insert_of_mem _ ?_, y, hy, he⟩
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ht
      · exact rightPrefixes_subset_of_birthdayTruncation_eq (mem_rightPrefixes_iff.mp ht).1 hx
  · rcases descend (add_le_add le_rfl (mem_rightPrefixes_iff.mp ht).2.le) htz with he | h
    · exact ⟨a, Set.mem_insert _ _, t, Set.mem_insert_of_mem _ ht, he⟩
    · obtain ⟨x, hx, y, hy, he⟩ := exists_add_eq_of_mem_rightPrefixes h
      refine ⟨x, hx, y, Set.mem_insert_of_mem _ ?_, he⟩
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · exact ht
      · exact rightPrefixes_subset_of_birthdayTruncation_eq (mem_rightPrefixes_iff.mp ht).1 hy
termination_by (a.birthday + b.birthday).val
decreasing_by
  · exact NatOrdinal.val.strictMono (add_lt_add_of_lt_of_le (birthday_lt_of_mem_rightPrefixes ht)
      (le_refl b.birthday))
  · exact NatOrdinal.val.strictMono (add_lt_add_of_le_of_lt (le_refl a.birthday)
      (birthday_lt_of_mem_rightPrefixes ht))

/-- Split a left prefix of a sum into a lower prefix of each input. -/
theorem exists_add_eq_of_mem_leftPrefixes {a b z : Surreal.{u}}
    (hz : z ∈ leftPrefixes (a + b)) :
    ∃ x ∈ insert a (leftPrefixes a), ∃ y ∈ insert b (leftPrefixes b), x + y = z := by
  have h : -z ∈ rightPrefixes (-a + -b) := by
    simpa only [neg_add] using neg_mem_rightPrefixes_iff.mpr hz
  obtain ⟨x, hx, y, hy, he⟩ := exists_add_eq_of_mem_rightPrefixes h
  have neg_mem {t s : Surreal.{u}} (ht : t ∈ insert (-s) (rightPrefixes (-s))) :
      -t ∈ insert s (leftPrefixes s) := by
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · simp
    · apply Set.mem_insert_of_mem
      exact neg_mem_rightPrefixes_iff.mp (by simpa only [neg_neg] using ht)
  exact ⟨-x, neg_mem hx, -y, neg_mem hy, by simpa only [neg_add, neg_neg] using congrArg Neg.neg he⟩

/-- Every sign prefix of a sum splits as an exact sum of sign prefixes. -/
theorem exists_prefixes_add_eq {a b z : Surreal.{u}}
    (hp : birthdayTruncation (a + b) z.birthday = z) :
    ∃ x y : Surreal.{u}, birthdayTruncation a x.birthday = x ∧
      birthdayTruncation b y.birthday = y ∧ x + y = z := by
  rcases lt_trichotomy z (a + b) with h | rfl | h
  · obtain ⟨x, hx, y, hy, he⟩ := exists_add_eq_of_mem_leftPrefixes
      (mem_leftPrefixes_iff.mpr ⟨hp, h⟩)
    have trunc_eq {u v : Surreal.{u}} (hv : v ∈ insert u (leftPrefixes u)) :
        birthdayTruncation u v.birthday = v := by
      rcases Set.mem_insert_iff.mp hv with rfl | hv
      · exact birthdayTruncation_birthday _
      · exact (mem_leftPrefixes_iff.mp hv).1
    exact ⟨x, y, trunc_eq hx, trunc_eq hy, he⟩
  · exact ⟨a, b, birthdayTruncation_birthday _, birthdayTruncation_birthday _, rfl⟩
  · obtain ⟨x, hx, y, hy, he⟩ := exists_add_eq_of_mem_rightPrefixes
      (mem_rightPrefixes_iff.mpr ⟨hp, h⟩)
    have trunc_eq {u v : Surreal.{u}} (hv : v ∈ insert u (rightPrefixes u)) :
        birthdayTruncation u v.birthday = v := by
      rcases Set.mem_insert_iff.mp hv with rfl | hv
      · exact birthdayTruncation_birthday _
      · exact (mem_rightPrefixes_iff.mp hv).1
    exact ⟨x, y, trunc_eq hx, trunc_eq hy, he⟩

/-- A right gap of a sum smaller than every right gap of the second input comes entirely
from the first input. -/
theorem sub_mem_rightPrefixes_of_gap {a b z : Surreal.{u}} (hz : z ∈ rightPrefixes (a + b))
    (hb : ∀ y ∈ rightPrefixes b, z - (a + b) < y - b) : z - b ∈ rightPrefixes a := by
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_add_eq_of_mem_rightPrefixes hz
  have hax : a ≤ x := (Set.mem_insert_iff.mp hx).elim (fun h ↦ h.ge)
    (fun h ↦ (mem_rightPrefixes_iff.mp h).2.le)
  rcases Set.mem_insert_iff.mp hy with rfl | hy
  · rw [add_sub_cancel_right]
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ((mem_rightPrefixes_iff.mp hz).2.false).elim
    · exact hx
  · have h := hb y hy
    rw [add_sub_add_comm] at h
    exact (h.not_ge (le_add_of_nonneg_left (sub_nonneg.mpr hax))).elim

/-- Every right prefix of a sum with an ordinal is a translate of a right prefix of the input. -/
theorem sub_toSurreal_mem_rightPrefixes {a z : Surreal.{u}} (o : NatOrdinal.{u})
    (hz : z ∈ rightPrefixes (a + o.toSurreal)) : z - o.toSurreal ∈ rightPrefixes a := by
  apply sub_mem_rightPrefixes_of_gap hz
  simp only [rightPrefixes_toSurreal, Set.mem_empty_iff_false, false_implies, implies_true]

end Surreal
