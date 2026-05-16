/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Star.TransferInstance
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology

/-!
# The weak operator topology in Hilbert spaces

This file gives a few properties of the weak operator topology that are specific to operators on
Hilbert spaces. This mostly involves using the Fréchet-Riesz representation to convert between
applications of elements of the dual and inner products with vectors in the space.
-/

public section

/-- A type endowed with `star` is a star module over some other type with `star` if it admits an
injective map that preserves `star` and `•` to a star module. See note [reducible non-instances]. -/
protected lemma Function.Injective.starModule {R S : Type*} (𝕜 : Type*) [Star 𝕜] [SMul 𝕜 R]
    [Star R] [SMul 𝕜 S] [Star S] [StarModule 𝕜 S] {f : R → S}
    (star : ∀ x, f (star x) = star (f x)) (smul : ∀ (r : 𝕜) x, f (r • x) = r • f x)
    (hf : Injective f) :
    StarModule 𝕜 R where
  star_smul r x := hf <| by rw [star, smul, star_smul, smul, star]

/-- Transfer `StarModule` across an `Equiv` -/
protected lemma Equiv.starModule {R S : Type*} (e : R ≃ S) (𝕜 : Type*)
    [Star 𝕜] [Star S] [SMul 𝕜 S] [StarModule 𝕜 S] :
    letI := e.star
    letI := e.smul 𝕜
    StarModule 𝕜 R := by
  let := e.star
  let := e.smul 𝕜
  apply e.injective.starModule 𝕜 <;> (intros; exact e.apply_symm_apply _)

open scoped Topology InnerProductSpace

namespace ContinuousLinearMapWOT

variable {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [Module 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

@[ext]
lemma ext_inner {A B : E →WOT[𝕜] F} (h : ∀ x y, ⟪y, A x⟫_𝕜 = ⟪y, B x⟫_𝕜) : A = B := by
  rw [ContinuousLinearMapWOT.ext_iff]
  exact fun x => ext_inner_left 𝕜 fun y => h x y

variable [CompleteSpace F]

open Filter in
/-- The defining property of the weak operator topology: a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `⟪y, (f a) x⟫` tends to `⟪y, A x⟫` along the same filter. -/
lemma tendsto_iff_forall_inner_apply_tendsto {α : Type*} {l : Filter α}
    {f : α → E →WOT[𝕜] F} {A : E →WOT[𝕜] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x y, Tendsto (fun a => ⟪y, (f a) x⟫_𝕜) l (𝓝 ⟪y, A x⟫_𝕜) := by
  simp_rw [tendsto_iff_forall_dual_apply_tendsto]
  exact .symm <| forall_congr' fun _ ↦
    Equiv.forall_congr (InnerProductSpace.toDual 𝕜 F) fun _ ↦ Iff.rfl

lemma le_nhds_iff_forall_inner_apply_le_nhds {l : Filter (E →WOT[𝕜] F)}
    {A : E →WOT[𝕜] F} : l ≤ 𝓝 A ↔ ∀ x y, l.map (fun T => ⟪y, T x⟫_𝕜) ≤ 𝓝 (⟪y, A x⟫_𝕜) :=
  tendsto_iff_forall_inner_apply_tendsto (f := id)

lemma continuousWithinAt_iff {α : Type*} [TopologicalSpace α]
    {f : α → E →WOT[𝕜] F} {s : Set α} {a : α} :
    ContinuousWithinAt f s a ↔ ∀ x y, ContinuousWithinAt (⟪y, f · x⟫_𝕜) s a :=
  tendsto_iff_forall_inner_apply_tendsto

lemma continuousAt_iff {α : Type*} [TopologicalSpace α] {f : α → E →WOT[𝕜] F} {a : α} :
    ContinuousAt f a ↔ ∀ x y, ContinuousAt (⟪y, f · x⟫_𝕜) a :=
  tendsto_iff_forall_inner_apply_tendsto

lemma continuousOn_iff {α : Type*} [TopologicalSpace α] {f : α → E →WOT[𝕜] F} {s : Set α} :
    ContinuousOn f s ↔ ∀ x y, ContinuousOn (⟪y, f · x⟫_𝕜) s := by
  simp_rw [ContinuousOn, forall_comm (α := E) , forall_comm (α := F), continuousWithinAt_iff]

lemma continuous_iff {α : Type*} [TopologicalSpace α] {f : α → E →WOT[𝕜] F} :
    Continuous f ↔ ∀ x y, Continuous (⟪y, f · x⟫_𝕜) := by
  simp_rw [continuous_iff_continuousAt, forall_comm (α := E) , forall_comm (α := F),
    continuousAt_iff]

alias ⟨continuousWithinAt_of, continuousWithinAt⟩ := continuousWithinAt_iff
alias ⟨continuousOn_of, continuousOn⟩ := continuousOn_iff
alias ⟨continuousAt_of, continuousAt⟩ := continuousAt_iff
alias ⟨continuous_of, continuous⟩ := continuous_iff

noncomputable instance : StarRing (F →WOT[𝕜] F) := equiv.starRing

lemma star_apply (A : F →WOT[𝕜] F) (x : F) : star A x = star (toCLM A) x := rfl

instance : StarModule 𝕜 (F →WOT[𝕜] F) := equiv.starModule 𝕜

instance : ContinuousStar (F →WOT[𝕜] F) where
  continuous_star := by
    simp_rw [continuous_iff, star_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, coe_toCLM]
    rw [forall_comm]
    simp +singlePass only [← inner_conj_symm]
    exact (continuous_star.comp <| continuous_of continuous_id · ·)

end ContinuousLinearMapWOT
