/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Small.Basic

/-!
# Additional results about small sets
-/

universe u v w

theorem small_iUnion {α : Type v} {ι : Type w} [Small.{u} ι] (s : ι → Set α)
    [∀ i, Small.{u} (s i)] : Small.{u} (⋃ i, s i) :=
  small_of_surjective <| Set.sigmaToiUnion_surjective _

theorem small_sUnion {α : Type v} (s : Set (Set α)) [Small.{u} s] [∀ t : s, Small.{u} t] :
    Small.{u} (⋃₀ s) :=
  Set.sUnion_eq_iUnion ▸ small_iUnion _
