/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Logic.Small.Set

/-!
# Small instances for pointwise operations
-/

universe u

variable {α β : Type*} (s t : Set α)

open Pointwise

instance [Zero α] : Small.{u} (0 : Set α) := small_single _
instance [One α] : Small.{u} (1 : Set α) := small_single _

instance [InvolutiveNeg α] [Small.{u} s] : Small.{u} (-s :) := by
  rw [← Set.image_neg_eq_neg]
  infer_instance

instance [Add α] [Small.{u} s] [Small.{u} t] : Small.{u} (s + t :) := small_image2 ..
instance [Sub α] [Small.{u} s] [Small.{u} t] : Small.{u} (s - t :) := small_image2 ..
instance [Mul α] [Small.{u} s] [Small.{u} t] : Small.{u} (s * t :) := small_image2 ..
instance [Div α] [Small.{u} s] [Small.{u} t] : Small.{u} (s / t :) := small_image2 ..
