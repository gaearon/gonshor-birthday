/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.HeadPerturbation

/-!
# Headed right-prefix family clients

The negative unit boundary uses a zero coefficient predecessor. A nonempty higher
head and a genuine omega-scale lower monomial occur in the concrete family.
-/

universe u
open Surreal Set

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {v : Surreal.{u}}
    (hv : v ∈ leftPrefixes s) : K ∈ rightPrefixes (K - ω^ s) := by
  simpa using head_sub_natCast_mul_wpow_mem_rightPrefixes K s hK hv 0

example (n : ℕ) : ω^ (3 : Surreal.{u}) - (n : Surreal) * ω^ (1 : Surreal) ∈
    rightPrefixes (ω^ (3 : Surreal) - ω^ (2 : Surreal)) := by
  apply head_sub_natCast_mul_wpow_mem_rightPrefixes (ω^ (3 : Surreal)) 2 _
    one_mem_leftPrefixes_two n
  rw [support_wpow]
  intro i hi
  rw [mem_singleton_iff] at hi
  subst i
  norm_num

example (K u : Surreal.{u}) (hK : K.support ⊆ Ioi u) {r s : ℝ}
    (hsr : s < r)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = r)
    {a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ u)) :
    K + ((r : Surreal) * ω^ u - a) ∈ rightPrefixes (K + (s : Surreal) * ω^ u) :=
  head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K u hK hsr hp ha

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s)
    (hcof : ∀ a < (K - ω^ s).birthday,
      ∃ w ∈ rightPrefixes (K - ω^ s), a < w.birthday)
    {a : NatOrdinal.{u}} (ha : a < (K - ω^ s).birthday) :
    ∃ v ∈ leftPrefixes s, ∃ n : ℕ, 0 < n ∧
      a < (K - (n : Surreal) * ω^ v).birthday :=
  head_sub_natCast_mul_wpow_pos_cofinal K s hK hcof a ha
