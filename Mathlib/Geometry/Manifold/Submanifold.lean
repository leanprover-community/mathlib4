/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.SliceModel
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-! # Immersed and embedded submanifolds

to be written!
-/

public section

open scoped ContDiff
open Manifold Topology Function Set

universe u
-- Let `M` and `N` be `C^n` manifolds over a field `𝕜`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ E₃ E₄ E₅ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [NormedAddCommGroup E₄] [NormedSpace 𝕜 E₄]
  [NormedAddCommGroup E₅] [NormedSpace 𝕜 E₅]
  {H H' H'' G G' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E₁ H} {I' : ModelWithCorners 𝕜 E₂ H'}
  {J : ModelWithCorners 𝕜 E₃ G} {J' : ModelWithCorners 𝕜 E₄ G'} {J'' : ModelWithCorners 𝕜 E₅ H''}
  {M M' N N' P : Type*} [TopologicalSpace M] --[ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  [TopologicalSpace P] [ChartedSpace H'' P]
  {n : WithTop ℕ∞}
  {F F' : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

-- TODO: F is required here; have a second version without it?
variable (F I J M N n) in
class ImmersedSubmanifold where
  map : M → N
  sliceModel : SliceModel F I J := by infer_instance
  -- TODO: this is too strong a condition; placeholder for the real one!
  real_condition : n = n --IsImmersionOfComplement F I J n map

-- instance [h : ImmersedSubmanifold I J M N n F] : ChartedSpace H M := sorry

#exit
namespace ImmersedSubmanifold

lemma isImmersionOfComplement [h : ImmersedSubmanifold I J M N n F] :
    IsImmersionOfComplement F I J n h.map := sorry

lemma isImmersion [h : ImmersedSubmanifold I J M N n F] :
    IsImmersion I J n h.map :=
  h.isImmersionOfComplement.isImmersion

def of_isImmersionOfComplement [SliceModel F I J]
    {f : M → N} (hf : IsImmersionOfComplement F I J n f) :
  ImmersedSubmanifold I J M N n F where
  map := f
  real_condition := sorry -- placeholder!

-- This lemma is strange, and probably not useful in practice.
-- If you have a slice model, you have a complement at hand already.
-- Better lemma: drop the slice model hypothesis, and infer a slice model from hf!
def of_isImmersion {f : M → N} (hf : IsImmersion I J n f) : --[SliceModel hf.complement I J] :
  ImmersedSubmanifold I J M N n hf.complement := by
  have : SliceModel hf.complement I J := sorry -- hopefully!! removable
  apply of_isImmersionOfComplement hf.isImmersionOfComplement_complement

-- TODO: is this true? if so, prove this and simplify the lemma above!
-- This does not work if M is empty, but `f` being an immersion at `x` should suffice.
-- Let's postpone the details...
def SliceModel.of_isImmersionOfComplement {f : M → N} (hf : IsImmersionOfComplement F I J n f) :
    SliceModel F I J := sorry

def trans [h : ImmersedSubmanifold I J M N n F] [h' : ImmersedSubmanifold J J'' N P n F'] :
    ImmersedSubmanifold I J'' M P n (F × F') where
  map := h'.map ∘ h.map
  sliceModel := h.sliceModel.trans h'.sliceModel
  real_condition := sorry

end ImmersedSubmanifold

variable (F I J M N n) in
class EmbeddedSubmanifold extends ImmersedSubmanifold I J M N n F where
  isEmbedding : Topology.IsEmbedding map

namespace EmbeddedSubmanifold

lemma isSmoothEmbedding [h : EmbeddedSubmanifold I J M N n F] :
    IsSmoothEmbedding I J n h.map := sorry

def of_isSmoothEmbedding --[SliceModel F I J]
    {f : M → N} (hf : IsSmoothEmbedding I J n f) :
    EmbeddedSubmanifold I J M N n hf.isImmersion.complement where
  toImmersedSubmanifold := .of_isImmersion hf.isImmersion
  isEmbedding := sorry

def trans [h : EmbeddedSubmanifold I J M N n F] [h' : EmbeddedSubmanifold J J'' N P n F'] :
    EmbeddedSubmanifold I J'' M P n (F × F') where
  toImmersedSubmanifold := .trans (h := h.1)
  isEmbedding := h'.isEmbedding.comp h.isEmbedding

end EmbeddedSubmanifold
