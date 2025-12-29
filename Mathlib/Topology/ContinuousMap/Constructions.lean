/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Constructions

In this file we accumulate various constructions of continuous maps whose imports prevent them from
being in `Mathlib.Topology.ContinuousMap.Basic`.

-/

@[expose] public section

open Topology
namespace ContinuousMap
variable {X} [TopologicalSpace X]

def uliftUp : C(X, ULift X) :=
  Homeomorph.ulift (X := X) |>.symm

@[simp]
lemma uliftUp_apply (x : X) :
    ContinuousMap.uliftUp x = ⟨x⟩ := rfl


def uliftDown : C(ULift X, X) :=
  Homeomorph.ulift (X := X)

@[simp]
lemma uliftDown_apply (x : ULift X) :
    ContinuousMap.uliftDown x = x.down := rfl

end ContinuousMap

lemma IsOpenEmbedding.uliftUp {X} [TopologicalSpace X] :
    IsOpenEmbedding (ContinuousMap.uliftUp : C(X, ULift X)) :=
  Homeomorph.ulift.symm.isOpenEmbedding

lemma IsClosedEmbedding.uliftUp {X} [TopologicalSpace X] :
    IsClosedEmbedding (ContinuousMap.uliftUp : C(X, ULift X)) :=
  Homeomorph.ulift.symm.isClosedEmbedding

lemma IsOpenEmbedding.uliftDown {X} [TopologicalSpace X] :
    IsOpenEmbedding (ContinuousMap.uliftDown : C(ULift X, X)) :=
  Homeomorph.ulift.isOpenEmbedding

lemma IsClosedEmbedding.uliftDown {X} [TopologicalSpace X] :
    IsClosedEmbedding (ContinuousMap.uliftDown : C(ULift X, X)) :=
  Homeomorph.ulift.isClosedEmbedding
