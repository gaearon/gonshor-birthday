/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.ReducedCostCoefficient

/-!
# Actual reduced-cost coefficient interfaces

The cell estimates take the existing reduced-cost inequality as an explicit
hypothesis. Their axiom checks do not depend on the multiplication placeholder.
-/
