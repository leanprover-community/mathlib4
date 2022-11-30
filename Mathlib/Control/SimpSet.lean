/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Lean.Meta.Tactic.Simp

/-! Simp set for `functor_norm` and `monad_norm` -/

/-- Simp set for `functor_norm` -/
register_simp_attr functor_norm

-- Porting note:
-- in mathlib3 we declared `monad_norm` using:
--   mk_simp_attribute monad_norm none with functor_norm
-- This syntax is not supported by mathlib4's `register_simp_attr`.
-- See https://github.com/leanprover-community/mathlib4/issues/802

/-- Simp set for `functor_norm` -/
register_simp_attr monad_norm
