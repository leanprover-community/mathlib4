/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.SetLike.Basic

/-! # `SetLike` instance for `Finset` -/

instance (α : Type*) : SetLike (Finset α) α where
  coe s := s
  coe_injective' := Finset.coe_injective

