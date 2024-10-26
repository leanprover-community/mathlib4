/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags

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

namespace Order

open Additive Multiplicative

@[simp] lemma succ_ofMul [Preorder X] [SuccOrder X] (x : X) : succ (ofMul x) = ofMul (succ x) := rfl
@[simp] lemma succ_toMul [Preorder X] [SuccOrder X] (x : X) : succ (toMul x) = toMul (succ x) := rfl

@[simp] lemma succ_ofAdd [Preorder X] [SuccOrder X] (x : X) : succ (ofAdd x) = ofAdd (succ x) := rfl
@[simp] lemma succ_toAdd [Preorder X] [SuccOrder X] (x : X) : succ (toAdd x) = toAdd (succ x) := rfl

@[simp] lemma pred_ofMul [Preorder X] [PredOrder X] (x : X) : pred (ofMul x) = ofMul (pred x) := rfl
@[simp] lemma pred_toMul [Preorder X] [PredOrder X] (x : X) : pred (toMul x) = toMul (pred x) := rfl

@[simp] lemma pred_ofAdd [Preorder X] [PredOrder X] (x : X) : pred (ofAdd x) = ofAdd (pred x) := rfl
@[simp] lemma pred_toAdd [Preorder X] [PredOrder X] (x : X) : pred (toAdd x) = toAdd (pred x) := rfl

end Order
