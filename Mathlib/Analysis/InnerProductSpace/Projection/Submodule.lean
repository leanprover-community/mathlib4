/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Subspaces associated with orthogonal projections

Here, the orthogonal projection is used to prove a series of more subtle lemmas about the
orthogonal complement of subspaces of `E` (the orthogonal complement itself was
defined in `Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`) such that they admit
orthogonal projections; the lemma
`Submodule.sup_orthogonal_of_hasOrthogonalProjection`,
stating that for a subspace `K` of `E` such that `K` admits an orthogonal projection we have
`K ⊔ Kᗮ = ⊤`, is a typical example.
-/

public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (K : Submodule 𝕜 E)

namespace Submodule

/-- If `K₁` admits an orthogonal projection and is contained in `K₂`,
then `K₁` and `K₁ᗮ ⊓ K₂` span `K₂`. -/
theorem sup_orthogonal_inf_of_hasOrthogonalProjection {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂)
    [K₁.HasOrthogonalProjection] : K₁ ⊔ K₁ᗮ ⊓ K₂ = K₂ := by
  ext x
  rw [Submodule.mem_sup]
  let v : K₁ := orthogonalProjection K₁ x
  have hvm : x - v ∈ K₁ᗮ := sub_starProjection_mem_orthogonal x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact K₂.add_mem (h hy) hz.2
  · exact fun hx => ⟨v, v.prop, x - v, ⟨hvm, K₂.sub_mem hx (h v.prop)⟩, add_sub_cancel _ _⟩

variable {K} in
/-- If `K` admits an orthogonal projection, then `K` and `Kᗮ` span the whole space. -/
theorem sup_orthogonal_of_hasOrthogonalProjection [K.HasOrthogonalProjection] : K ⊔ Kᗮ = ⊤ := by
  convert Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (le_top : K ≤ ⊤) using 2
  simp

/-- If `K` admits an orthogonal projection, then the orthogonal complement of its orthogonal
complement is itself. -/
@[simp]
theorem orthogonal_orthogonal [K.HasOrthogonalProjection] : Kᗮᗮ = K := by
  ext v
  constructor
  · obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal v
    intro hv
    have hz' : z = 0 := by
      have hyz : ⟪z, y⟫ = 0 := by simp [hz y hy, inner_eq_zero_symm]
      simpa [inner_add_right, hyz] using hv z hz
    simp [hy, hz']
  · intro hv w hw
    rw [inner_eq_zero_symm]
    exact hw v hv

lemma orthogonal_le_orthogonal_iff {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ᗮ ≤ K₁ᗮ ↔ K₁ ≤ K₀ :=
  ⟨fun h ↦ by simpa using orthogonal_le h, orthogonal_le⟩

lemma orthogonal_le_iff_orthogonal_le {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ᗮ ≤ K₁ ↔ K₁ᗮ ≤ K₀ := by
  rw [← orthogonal_le_orthogonal_iff, orthogonal_orthogonal]

lemma le_orthogonal_iff_le_orthogonal {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ ≤ K₁ᗮ ↔ K₁ ≤ K₀ᗮ := by
  rw [← orthogonal_le_orthogonal_iff, orthogonal_orthogonal]

/-- In a Hilbert space, the orthogonal complement of the orthogonal complement of a subspace `K`
is the topological closure of `K`.

Note that the completeness assumption is necessary. Let `E` be the space `ℕ →₀ ℝ` with inner space
structure inherited from `PiLp 2 (fun _ : ℕ ↦ ℝ)`. Let `K` be the subspace of sequences with the sum
of all elements equal to zero. Then `Kᗮ = ⊥`, `Kᗮᗮ = ⊤`. -/
theorem orthogonal_orthogonal_eq_closure [CompleteSpace E] :
    Kᗮᗮ = K.topologicalClosure := by
  refine le_antisymm ?_ ?_
  · convert Submodule.orthogonal_orthogonal_monotone K.le_topologicalClosure using 1
    rw [K.topologicalClosure.orthogonal_orthogonal]
  · exact K.topologicalClosure_minimal K.le_orthogonal_orthogonal Kᗮ.isClosed_orthogonal

variable {K}

/-- If `K` admits an orthogonal projection, `K` and `Kᗮ` are complements of each other. -/
theorem isCompl_orthogonal_of_hasOrthogonalProjection [K.HasOrthogonalProjection] : IsCompl K Kᗮ :=
  ⟨K.orthogonal_disjoint, codisjoint_iff.2 Submodule.sup_orthogonal_of_hasOrthogonalProjection⟩

@[simp]
theorem orthogonalComplement_eq_orthogonalComplement {L : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] : Kᗮ = Lᗮ ↔ K = L :=
  ⟨fun h ↦ by simpa using congr(Submodule.orthogonal $(h)),
    fun h ↦ congr(Submodule.orthogonal $(h))⟩

@[simp]
theorem orthogonal_eq_bot_iff [K.HasOrthogonalProjection] : Kᗮ = ⊥ ↔ K = ⊤ := by
  refine ⟨?_, fun h => by rw [h, Submodule.top_orthogonal_eq_bot]⟩
  intro h
  have : K ⊔ Kᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
  rwa [h, sup_comm, bot_sup_eq] at this

open Topology Finsupp RCLike Real Filter

/-- Given a monotone family `U` of complete submodules of `E` and a fixed `x : E`,
the orthogonal projection of `x` on `U i` tends to the orthogonal projection of `x` on
`(⨆ i, U i).topologicalClosure` along `atTop`. -/
theorem starProjection_tendsto_closure_iSup {ι : Type*} [Preorder ι]
    (U : ι → Submodule 𝕜 E) [∀ i, (U i).HasOrthogonalProjection]
    [(⨆ i, U i).topologicalClosure.HasOrthogonalProjection] (hU : Monotone U) (x : E) :
    Filter.Tendsto (fun i => (U i).starProjection x) atTop
      (𝓝 ((⨆ i, U i).topologicalClosure.starProjection x)) := by
  refine .of_neBot_imp fun h ↦ ?_
  cases atTop_neBot_iff.mp h
  let y := (⨆ i, U i).topologicalClosure.starProjection x
  have proj_x : ∀ i, (U i).orthogonalProjection x = (U i).orthogonalProjection y := fun i =>
    (orthogonalProjection_starProjection_of_le
        ((le_iSup U i).trans (iSup U).le_topologicalClosure) _).symm
  suffices ∀ ε > 0, ∃ I, ∀ i ≥ I, ‖(U i).starProjection y - y‖ < ε by
    simpa only [starProjection_apply, proj_x, NormedAddCommGroup.tendsto_atTop] using this
  intro ε hε
  obtain ⟨a, ha, hay⟩ : ∃ a ∈ ⨆ i, U i, dist y a < ε := by
    have y_mem : y ∈ (⨆ i, U i).topologicalClosure := Submodule.coe_mem _
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at y_mem
    exact y_mem ε hε
  rw [dist_eq_norm] at hay
  obtain ⟨I, hI⟩ : ∃ I, a ∈ U I := by rwa [Submodule.mem_iSup_of_directed _ hU.directed_le] at ha
  refine ⟨I, fun i (hi : I ≤ i) => ?_⟩
  rw [norm_sub_rev, starProjection_minimal]
  refine lt_of_le_of_lt ?_ hay
  change _ ≤ ‖y - (⟨a, hU hi hI⟩ : U i)‖
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ _

/-- Given a monotone family `U` of complete submodules of `E` with dense span supremum,
and a fixed `x : E`, the orthogonal projection of `x` on `U i` tends to `x` along `at_top`. -/
theorem starProjection_tendsto_self {ι : Type*} [Preorder ι]
    (U : ι → Submodule 𝕜 E) [∀ t, (U t).HasOrthogonalProjection] (hU : Monotone U) (x : E)
    (hU' : ⊤ ≤ (⨆ t, U t).topologicalClosure) :
    Filter.Tendsto (fun t => (U t).starProjection x) atTop (𝓝 x) := by
  have : (⨆ i, U i).topologicalClosure.HasOrthogonalProjection := by
    rw [top_unique hU']
    infer_instance
  convert starProjection_tendsto_closure_iSup U hU x
  rw [eq_comm, starProjection_eq_self_iff, top_unique hU']
  trivial

/-- The orthogonal complement satisfies `Kᗮᗮᗮ = Kᗮ`. -/
theorem triorthogonal_eq_orthogonal : Kᗮᗮᗮ = Kᗮ :=
  (orthogonal_gc 𝕜 E).u_l_u_eq_u K

/-- The closure of `K` is the full space iff `Kᗮ` is trivial. -/
theorem topologicalClosure_eq_top_iff [CompleteSpace E] :
    K.topologicalClosure = ⊤ ↔ Kᗮ = ⊥ := by
  rw [← K.orthogonal_orthogonal_eq_closure]
  constructor <;> intro h
  · rw [← Submodule.triorthogonal_eq_orthogonal, h, Submodule.top_orthogonal_eq_bot]
  · rw [h, Submodule.bot_orthogonal_eq_top]

theorem orthogonalProjection_apply_eq_linearProjOfIsCompl [K.HasOrthogonalProjection] (x : E) :
    K.orthogonalProjection x =
      K.linearProjOfIsCompl _ Submodule.isCompl_orthogonal_of_hasOrthogonalProjection x := by
  have : IsCompl K Kᗮ := Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  conv_lhs => rw [← IsCompl.projection_add_projection_eq_self this x]
  simp_rw [IsCompl.projection_apply]
  rw [map_add, orthogonalProjection_mem_subspace_eq_self,
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero (Submodule.coe_mem _), add_zero]

@[deprecated (since := "2025-12-26")] alias orthogonalProjection_eq_linearProjOfIsCompl :=
  orthogonalProjection_apply_eq_linearProjOfIsCompl

theorem toLinearMap_orthogonalProjection_eq_linearProjOfIsCompl [K.HasOrthogonalProjection] :
    (K.orthogonalProjection : E →ₗ[𝕜] K) =
      K.linearProjOfIsCompl _ Submodule.isCompl_orthogonal_of_hasOrthogonalProjection :=
  LinearMap.ext orthogonalProjection_apply_eq_linearProjOfIsCompl

@[deprecated (since := "2025-12-26")] alias orthogonalProjection_coe_eq_linearProjOfIsCompl :=
  toLinearMap_orthogonalProjection_eq_linearProjOfIsCompl

open Submodule in
theorem toLinearMap_starProjection_eq_isComplProjection [K.HasOrthogonalProjection] :
    K.starProjection.toLinearMap = K.isCompl_orthogonal_of_hasOrthogonalProjection.projection := by
  simp [starProjection, toLinearMap_orthogonalProjection_eq_linearProjOfIsCompl, IsCompl.projection]

@[deprecated (since := "2025-12-26")] alias starProjection_coe_eq_isCompl_projection :=
  toLinearMap_starProjection_eq_isComplProjection

open Submodule in
theorem starProjection_apply_eq_isComplProjection [K.HasOrthogonalProjection] (x : E) :
    K.starProjection x = K.isCompl_orthogonal_of_hasOrthogonalProjection.projection x :=
  congr($toLinearMap_starProjection_eq_isComplProjection x)

end Submodule

namespace Dense

open Submodule

variable {K} {x y : E}

theorem eq_zero_of_mem_orthogonal (hK : Dense (K : Set E)) (h : x ∈ Kᗮ) : x = 0 :=
  eq_zero_of_inner_left 𝕜 hK fun _ ↦ (mem_orthogonal' _ _).1 h _

/-- If `S` is dense and `x - y ∈ Kᗮ`, then `x = y`. -/
theorem eq_of_sub_mem_orthogonal (hK : Dense (K : Set E)) (h : x - y ∈ Kᗮ) : x = y :=
  sub_eq_zero.1 <| eq_zero_of_mem_orthogonal hK h

end Dense

namespace ClosedSubmodule

@[simp]
theorem orthogonal_orthogonal_eq (K : ClosedSubmodule 𝕜 E) [K.HasOrthogonalProjection] :
    (Kᗮ)ᗮ = K := by ext x; simp

theorem orthogonal_eq_orthogonal_iff (K₁ K₂ : ClosedSubmodule 𝕜 E) [K₁.HasOrthogonalProjection]
    [K₂.HasOrthogonalProjection] : K₁ᗮ = K₂ᗮ ↔ K₁ = K₂ :=
  ⟨fun h ↦ by simpa using congr($hᗮ), fun h ↦ congr($hᗮ)⟩

theorem orthogonal_injective [CompleteSpace E] :
    Function.Injective (fun K : ClosedSubmodule 𝕜 E ↦ Kᗮ) :=
  (orthogonal_eq_orthogonal_iff · · |>.mp)

/-- The sup of two orthogonal subspaces equals the subspace orthogonal
to the inf. -/
theorem sup_orthogonal [CompleteSpace E] (K₁ K₂ : ClosedSubmodule 𝕜 E) :
    K₁ᗮ ⊔ K₂ᗮ = (K₁ ⊓ K₂)ᗮ := by
  simpa using congr($(inf_orthogonal K₁ᗮ K₂ᗮ)ᗮ).symm

end ClosedSubmodule
