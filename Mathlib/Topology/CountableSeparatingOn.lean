/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Separation
import Mathlib.Order.Filter.CountableSeparatingOn

/-!
# Countable separating families of sets in topological spaces

In this file we show that a T₀ topological space with second countable
topology has a countable family of open (or closed) sets separating the points.
-/

set_option autoImplicit true

open Set TopologicalSpace

/-- If `X` is a topological space, `s` is a set in `X` such that the induced topology is T₀ and is
second countable, then there exists a countable family of open sets in `X` that separates points
of `s`. -/
instance [TopologicalSpace X] {s : Set X} [T0Space s] [SecondCountableTopology s] :
    HasCountableSeparatingOn X IsOpen s := by
  suffices HasCountableSeparatingOn s IsOpen univ from .of_subtype fun _ ↦ isOpen_induced_iff.1
  -- ⊢ HasCountableSeparatingOn (↑s) IsOpen univ
  refine ⟨⟨countableBasis s, countable_countableBasis _, fun _ ↦ isOpen_of_mem_countableBasis,
    fun x _ y _ h ↦ ?_⟩⟩
  exact ((isBasis_countableBasis _).inseparable_iff.2 h).eq
  -- 🎉 no goals

/-- If there exists a countable family of open sets separating points of `s`, then there exists
a countable family of closed sets separating points of `s`. -/
instance [TopologicalSpace X] {s : Set X} [h : HasCountableSeparatingOn X IsOpen s] :
    HasCountableSeparatingOn X IsClosed s :=
  let ⟨S, hSc, hSo, hS⟩ := h.1
  ⟨compl '' S, hSc.image _, ball_image_iff.2 fun U hU ↦ (hSo U hU).isClosed_compl,
    fun x hx y hy h ↦ hS x hx y hy fun _U hU ↦ not_iff_not.1 <| h _ (mem_image_of_mem _ hU)⟩
