/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Ring.WithAbs

/-!
# WithAbs for fields

This extends the `WithAbs` mechanism to fields, providing a type synonym for a field which depends
on an absolute value. This is useful when dealing with several absolute values on the same field.

In particular this allows us to define the completion of a field at a given absolute value.
-/

open Topology

noncomputable section

variable {R S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]

namespace WithAbs

section more_instances

instance normedField [Field R] (v : AbsoluteValue R ℝ) : NormedField (WithAbs v) :=
  v.toNormedField

end more_instances

/-!
### The completion of a field at an absolute value.
-/

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [NormedField L] {f : WithAbs v →+* L}

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is an isometry. -/
@[deprecated AddMonoidHomClass.isometry_of_norm (since := "2025-09-25")]
theorem isometry_of_comp (h : ∀ x, ‖f x‖ = v x) : Isometry f :=
  AddMonoidHomClass.isometry_of_norm _ h

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the pseudo metric space associated to the absolute value is the same as the pseudo metric space
induced by `f`. -/
@[deprecated "Use Isometry.dist_eq in combination with AddMonoidHomClass.isometry_of_norm"
  (since := "2025-09-25")]
theorem pseudoMetricSpace_induced_of_comp (h : ∀ x, ‖f x‖ = v x) :
    PseudoMetricSpace.induced f inferInstance = (normedField v).toPseudoMetricSpace := by
  ext; exact AddMonoidHomClass.isometry_of_norm _ h |>.dist_eq _ _

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the uniform structure associated to the absolute value is the same as the uniform structure
induced by `f`. -/
@[deprecated "Use IsUniformInducing.comap_uniformSpace in combination with
  AddMonoidHomClass.isometry_of_norm" (since := "2025-09-25")]
theorem uniformSpace_comap_eq_of_comp (h : ∀ x, ‖f x‖ = v x) :
    UniformSpace.comap f inferInstance = (normedField v).toUniformSpace :=
  IsUniformInducing.comap_uniformSpace
    (AddMonoidHomClass.isometry_of_norm _ h).isUniformInducing

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is uniform inducing. -/
@[deprecated "Use Isometry.isUniformInducing in combination with
  AddMonoidHomClass.isometry_of_norm" (since := "2025-09-25")]
theorem isUniformInducing_of_comp (h : ∀ x, ‖f x‖ = v x) : IsUniformInducing f :=
  (AddMonoidHomClass.isometry_of_norm _ h).isUniformInducing

end WithAbs

namespace AbsoluteValue

open WithAbs

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The completion of a field with respect to a real absolute value. -/
abbrev Completion := UniformSpace.Completion (WithAbs v)

namespace Completion

instance : Coe K v.Completion :=
  inferInstanceAs <| Coe (WithAbs v) (UniformSpace.Completion (WithAbs v))

variable {L : Type*} [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L} {v}

/-- If the absolute value of a normed field factors through an embedding into another normed field
`L`, then we can extend that embedding to an embedding on the completion `v.Completion →+* L`. -/
@[deprecated Isometry.extensionHom (since := "2025-09-25")]
abbrev extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) : v.Completion →+* L :=
  (AddMonoidHomClass.isometry_of_norm _ h).extensionHom

@[deprecated "Use Isometry.extensionHom_coe in combination with AddMonoidHomClass.isometry_of_norm"
  (since := "2025-09-25")]
theorem extensionEmbedding_of_comp_coe (h : ∀ x, ‖f x‖ = v x) (x : K) :
    (AddMonoidHomClass.isometry_of_norm _ h).extensionHom x = f x :=
  AddMonoidHomClass.isometry_of_norm _ h |>.extensionHom_coe _

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.Completion →+* L` preserves distances. -/
@[deprecated "Use Isometry.dist_eq in combination with AddMonoidHomClass.isometry_of_norm"
  (since := "2025-09-25")]
theorem extensionEmbedding_dist_eq_of_comp (h : ∀ x, ‖f x‖ = v x) (x y : v.Completion) :
    let f := AddMonoidHomClass.isometry_of_norm _ h |>.extensionHom
    dist (f x) (f y) = dist x y :=
  AddMonoidHomClass.isometry_of_norm _ h |>.completion_extension.dist_eq _ _

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.Completion →+* L` is an isometry. -/
@[deprecated "Use Isometry.completion_extension in combination with
  AddMonoidHomClass.isometry_of_norm" (since := "2025-09-25")]
theorem isometry_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) :
    Isometry (AddMonoidHomClass.isometry_of_norm _ h |>.extensionHom) :=
  AddMonoidHomClass.isometry_of_norm _ h |>.completion_extension

/-- If the absolute value of a normed field factors through an embedding into another normed field,
then the extended embedding `v.Completion →+* L` is a closed embedding. -/
@[deprecated "Use Isometry.isClosedEmbedding in combination with Isometry.completion_extension
  and AddMonoidHomClass.isometry_of_norm" (since := "2025-09-25")]
theorem isClosedEmbedding_extensionEmbedding_of_comp (h : ∀ x, ‖f x‖ = v x) :
    IsClosedEmbedding (AddMonoidHomClass.isometry_of_norm _ h |>.extensionHom) :=
  (AddMonoidHomClass.isometry_of_norm _ h).completion_extension.isClosedEmbedding

/-- If the absolute value of a normed field factors through an embedding into another normed field
that is locally compact, then the completion of the first normed field is also locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace L] (h : Isometry f) :
    LocallyCompactSpace (v.Completion) :=
  h.completion_extension.isClosedEmbedding.locallyCompactSpace

end AbsoluteValue.Completion
