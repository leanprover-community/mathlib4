/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.UniformRing

/-!
# Completion of topological fields

The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion `hat K` of a Hausdorff topological field is a field if the image under
the mapping `x ↦ x⁻¹` of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at `0` is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does not give any detail here, he refers to the general discussion of extending
functions defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

Note that the separated completion of a non-separated topological field is the zero ring, hence
the separation assumption is needed. Indeed the kernel of the completion map is the closure of
zero which is an ideal. Hence it's either zero (and the field is separated) or the full field,
which implies one is sent to zero and the completion ring is trivial.

The main definition is `CompletableTopField` which packages the assumptions as a Prop-valued
type class and the main results are the instances `UniformSpace.Completion.Field` and
`UniformSpace.Completion.IsTopologicalDivisionRing`.
-/

noncomputable section

open uniformity Topology

open Set UniformSpace UniformSpace.Completion Filter

variable (K : Type*) [Field K] [UniformSpace K]

local notation "hat" => Completion

/-- A topological field is completable if it is separated and the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure). This ensures the completion is
a field.
-/
class CompletableTopField : Prop extends T0Space K where
  nice : ∀ F : Filter K, Cauchy F → 𝓝 0 ⊓ F = ⊥ → Cauchy (map (fun x => x⁻¹) F)

namespace UniformSpace

namespace Completion

instance (priority := 100) [T0Space K] : Nontrivial (hat K) :=
  (isUniformEmbedding_coe K).injective.nontrivial

variable {K}

/-- extension of inversion to the completion of a field. -/
def hatInv : hat K → hat K :=
  isDenseInducing_coe.extend fun x : K => (↑x⁻¹ : hat K)

@[fun_prop]
theorem continuous_hatInv [CompletableTopField K] {x : hat K} (h : x ≠ 0) :
    ContinuousAt hatInv x := by
  refine isDenseInducing_coe.continuousAt_extend ?_
  apply mem_of_superset (compl_singleton_mem_nhds h)
  intro y y_ne
  rw [mem_compl_singleton_iff] at y_ne
  apply CompleteSpace.complete
  have : (fun (x : K) => (↑x⁻¹ : hat K)) =
      ((fun (y : K) => (↑y : hat K))∘(fun (x : K) => (x⁻¹ : K))) := by
    unfold Function.comp
    simp
  rw [this, ← Filter.map_map]
  apply Cauchy.map _ (Completion.uniformContinuous_coe K)
  apply CompletableTopField.nice
  · haveI := isDenseInducing_coe.comap_nhds_neBot y
    apply cauchy_nhds.comap
    rw [Completion.comap_coe_eq_uniformity]
  · have eq_bot : 𝓝 (0 : hat K) ⊓ 𝓝 y = ⊥ := by
      by_contra h
      exact y_ne (eq_of_nhds_neBot <| neBot_iff.mpr h).symm
    rw [isDenseInducing_coe.nhds_eq_comap (0 : K), ← Filter.comap_inf]
    norm_cast
    rw [eq_bot]
    exact comap_bot

open Classical in
/--
The value of `hat_inv` at zero is not really specified, although it's probably zero.
Here we explicitly enforce the `inv_zero` axiom.
-/
instance instInvCompletion : Inv (hat K) :=
  ⟨fun x => if x = 0 then 0 else hatInv x⟩

variable [IsTopologicalDivisionRing K]

theorem hatInv_extends {x : K} (h : x ≠ 0) : hatInv (x : hat K) = ↑(x⁻¹ : K) :=
  isDenseInducing_coe.extend_eq_at ((continuous_coe K).continuousAt.comp (continuousAt_inv₀ h))

variable [CompletableTopField K]

@[norm_cast]
theorem coe_inv (x : K) : (x : hat K)⁻¹ = ((x⁻¹ : K) : hat K) := by
  by_cases h : x = 0
  · rw [h, inv_zero]
    dsimp [Inv.inv]
    norm_cast
    simp
  · conv_lhs => dsimp [Inv.inv]
    rw [if_neg]
    · exact hatInv_extends h
    · exact fun H => h (isDenseEmbedding_coe.injective H)

variable [IsUniformAddGroup K]

theorem mul_hatInv_cancel {x : hat K} (x_ne : x ≠ 0) : x * hatInv x = 1 := by
  haveI : T1Space (hat K) := T2Space.t1Space
  let f := fun x : hat K => x * hatInv x
  let c := (fun (x : K) => (x : hat K))
  change f x = 1
  have cont : ContinuousAt f x := by
    fun_prop (disch := assumption)
  have clo : x ∈ closure (c '' {0}ᶜ) := by
    have := isDenseInducing_coe.dense x
    rw [← image_univ, show (univ : Set K) = {0} ∪ {0}ᶜ from (union_compl_self _).symm,
      image_union] at this
    apply mem_closure_of_mem_closure_union this
    rw [image_singleton]
    exact compl_singleton_mem_nhds x_ne
  have fxclo : f x ∈ closure (f '' (c '' {0}ᶜ)) := mem_closure_image cont clo
  have : f '' (c '' {0}ᶜ) ⊆ {1} := by
    rw [image_image]
    rintro _ ⟨z, z_ne, rfl⟩
    rw [mem_singleton_iff]
    rw [mem_compl_singleton_iff] at z_ne
    dsimp [f]
    rw [hatInv_extends z_ne, ← coe_mul]
    rw [mul_inv_cancel₀ z_ne, coe_one]
  replace fxclo := closure_mono this fxclo
  rwa [closure_singleton, mem_singleton_iff] at fxclo

instance instField : Field (hat K) where
  mul_inv_cancel := fun x x_ne => by simp only [Inv.inv, if_neg x_ne, mul_hatInv_cancel x_ne]
  inv_zero := by simp only [Inv.inv, ite_true]
  -- TODO: use a better defeq
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

instance : IsTopologicalDivisionRing (hat K) :=
  { Completion.topologicalRing with
    continuousAt_inv₀ := by
      intro x x_ne
      have : { y | hatInv y = y⁻¹ } ∈ 𝓝 x :=
        haveI : {(0 : hat K)}ᶜ ⊆ { y : hat K | hatInv y = y⁻¹ } := by
          intro y y_ne
          rw [mem_compl_singleton_iff] at y_ne
          dsimp [Inv.inv]
          rw [if_neg y_ne]
        mem_of_superset (compl_singleton_mem_nhds x_ne) this
      exact ContinuousAt.congr (continuous_hatInv x_ne) this }

end Completion

end UniformSpace

variable (L : Type*) [Field L] [UniformSpace L] [CompletableTopField L]

instance Subfield.completableTopField (K : Subfield L) : CompletableTopField K where
  nice F F_cau inf_F := by
    let i : K →+* L := K.subtype
    have hi : IsUniformInducing i := isUniformEmbedding_subtype_val.isUniformInducing
    rw [← hi.cauchy_map_iff] at F_cau ⊢
    rw [map_comm (show (i ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ i by ext; rfl)]
    apply CompletableTopField.nice _ F_cau
    rw [← Filter.push_pull', ← map_zero i, ← hi.isInducing.nhds_eq_comap, inf_F, Filter.map_bot]

instance (priority := 100) completableTopField_of_complete (L : Type*) [Field L] [UniformSpace L]
    [IsTopologicalDivisionRing L] [T0Space L] [CompleteSpace L] : CompletableTopField L where
  nice F cau_F hF := by
    haveI : NeBot F := cau_F.1
    rcases CompleteSpace.complete cau_F with ⟨x, hx⟩
    have hx' : x ≠ 0 := by
      rintro rfl
      rw [inf_eq_right.mpr hx] at hF
      exact cau_F.1.ne hF
    exact Filter.Tendsto.cauchy_map <|
      calc
        map (fun x => x⁻¹) F ≤ map (fun x => x⁻¹) (𝓝 x) := map_mono hx
        _ ≤ 𝓝 x⁻¹ := continuousAt_inv₀ hx'

variable {α β : Type*} [Field β] [b : UniformSpace β] [CompletableTopField β]
  [Field α]

/-- The pullback of a completable topological field along a uniform inducing
ring homomorphism is a completable topological field. -/
theorem IsUniformInducing.completableTopField
    [UniformSpace α] [T0Space α]
    {f : α →+* β} (hf : IsUniformInducing f) :
    CompletableTopField α := by
  refine CompletableTopField.mk (fun F F_cau inf_F => ?_)
  rw [← IsUniformInducing.cauchy_map_iff hf] at F_cau ⊢
  have h_comm : (f ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ f := by
    ext; simp only [Function.comp_apply, map_inv₀]
  rw [Filter.map_comm h_comm]
  apply CompletableTopField.nice _ F_cau
  rw [← Filter.push_pull', ← map_zero f, ← hf.isInducing.nhds_eq_comap, inf_F, Filter.map_bot]
