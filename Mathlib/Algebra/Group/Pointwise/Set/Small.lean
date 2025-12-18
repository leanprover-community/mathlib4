/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Logic.Small.Set

/-!
# Small instances for pointwise operations
-/

@[expose] public section

universe u

variable {α β : Type*} (s t : Set α)

open Pointwise

instance small_set_zero [Zero α] : Small.{u} (0 : Set α) := small_single _
instance small_set_one [One α] : Small.{u} (1 : Set α) := small_single _

instance small_neg [InvolutiveNeg α] [Small.{u} s] : Small.{u} (-s :) := by
  rw [← Set.image_neg_eq_neg]
  infer_instance

instance small_add [Add α] [Small.{u} s] [Small.{u} t] : Small.{u} (s + t) := small_image2 ..
instance small_sub [Sub α] [Small.{u} s] [Small.{u} t] : Small.{u} (s - t) := small_image2 ..
instance small_mul [Mul α] [Small.{u} s] [Small.{u} t] : Small.{u} (s * t) := small_image2 ..
instance small_div [Div α] [Small.{u} s] [Small.{u} t] : Small.{u} (s / t) := small_image2 ..
