/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Order.Monoid.TypeTags
import Mathlib.Order.SuccPred.Basic

/-!
# Successor and predecessor on type tags

This file declates successor and predecessor orders on type tags.

-/

variable {X : Type*}

instance [Preorder X] [h : SuccOrder X] : SuccOrder (Multiplicative X) := h
instance [Preorder X] [h : SuccOrder X] : SuccOrder (Additive X) := h

instance [Preorder X] [h : PredOrder X] : PredOrder (Multiplicative X) := h
instance [Preorder X] [h : PredOrder X] : PredOrder (Additive X) := h

instance [Preorder X] [SuccOrder X] [h : IsSuccArchimedean X] :
  IsSuccArchimedean (Multiplicative X) := h
instance [Preorder X] [SuccOrder X] [h : IsSuccArchimedean X] :
  IsSuccArchimedean (Additive X) := h

instance [Preorder X] [PredOrder X] [h : IsPredArchimedean X] :
  IsPredArchimedean (Multiplicative X) := h
instance [Preorder X] [PredOrder X] [h : IsPredArchimedean X] :
  IsPredArchimedean (Additive X) := h
