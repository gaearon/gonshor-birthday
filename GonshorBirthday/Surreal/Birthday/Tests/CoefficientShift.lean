/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.CoefficientShift

/-!
# Public translated real coefficient-prefix clients
-/

universe u
open Surreal

example {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    birthdayTruncation ((s : Surreal) * ω^ x) ((r : Surreal) * ω^ x + a).birthday =
      (r : Surreal) * ω^ x + a :=
  birthdayTruncation_real_mul_wpow_add_leftPrefix hr hrs hp ha

example {r s : ℝ} (hs : 0 < s) (hsr : s < r)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    ((r : Surreal) * ω^ x - a).birthday =
      NatOrdinal.of (((r : Surreal) * ω^ x).birthday.val + (plusCount a).val) :=
  birthday_real_mul_wpow_sub_leftPrefix hs hsr hp ha
