/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

/-!
# GonshorBirthday

The lakefile's `GonshorBirthday.*` glob builds every module in the library.
This root module has no re-exports. The axiom audit enumerates the source tree,
including modules that no other module imports.

Start with `GonshorBirthday/Surreal/Birthday/Multiplication.lean` or the README.
-/
