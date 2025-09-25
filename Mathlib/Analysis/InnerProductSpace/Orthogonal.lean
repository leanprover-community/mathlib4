/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.SesquilinearForm

/-!
# Orthogonal complements of submodules

In this file, the `orthogonal` complement of a submodule `K` is defined, and basic API established.
Some of the more subtle results about the orthogonal complement are delayed to
`Analysis.InnerProductSpace.Projection`.

See also `BilinForm.orthogonal` for orthogonality with respect to a general bilinear form.

## Notation

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.

The proposition that two submodules are orthogonal, `Submodule.IsOrtho`, is denoted by `U ⟂ V`.
Note this is not the same unicode symbol as `⊥` (`Bot`).
-/

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace Submodule

variable (K : Submodule 𝕜 E)

/-- The subspace of vectors orthogonal to a given subspace, denoted `Kᗮ`. -/
def orthogonal : Submodule 𝕜 E where
  carrier := { v | ∀ u ∈ K, ⟪u, v⟫ = 0 }
  zero_mem' _ _ := inner_zero_right _
  add_mem' hx hy u hu := by rw [inner_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' c x hx u hu := by rw [inner_smul_right, hx u hu, mul_zero]

@[inherit_doc]
notation:1200 K "ᗮ" => orthogonal K

/-- When a vector is in `Kᗮ`. -/
theorem mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫ = 0 :=
  Iff.rfl

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
theorem mem_orthogonal' (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪v, u⟫ = 0 := by
  simp_rw [mem_orthogonal, inner_eq_zero_symm]

variable {K}

/-- A vector in `K` is orthogonal to one in `Kᗮ`. -/
theorem inner_right_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪u, v⟫ = 0 :=
  (K.mem_orthogonal v).1 hv u hu

/-- A vector in `Kᗮ` is orthogonal to one in `K`. -/
theorem inner_left_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪v, u⟫ = 0 := by
  rw [inner_eq_zero_symm]; exact inner_right_of_mem_orthogonal hu hv

/-- A vector is in `(𝕜 ∙ u)ᗮ` iff it is orthogonal to `u`. -/
theorem mem_orthogonal_singleton_iff_inner_right {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0 := by
  refine ⟨inner_right_of_mem_orthogonal (mem_span_singleton_self u), ?_⟩
  intro hv w hw
  rw [mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  simp [inner_smul_left, hv]

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
theorem mem_orthogonal_singleton_iff_inner_left {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0 := by
  rw [mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm]

theorem sub_mem_orthogonal_of_inner_left {x y : E} (h : ∀ v : K, ⟪x, v⟫ = ⟪y, v⟫) : x - y ∈ Kᗮ := by
  rw [mem_orthogonal']
  intro u hu
  rw [inner_sub_left, sub_eq_zero]
  exact h ⟨u, hu⟩

theorem sub_mem_orthogonal_of_inner_right {x y : E} (h : ∀ v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) :
    x - y ∈ Kᗮ := by
  intro u hu
  rw [inner_sub_right, sub_eq_zero]
  exact h ⟨u, hu⟩

variable (K)

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro x
  rw [mem_inf]
  exact fun ⟨hx, ho⟩ => inner_self_eq_zero.1 (ho x hx)

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem orthogonal_disjoint : Disjoint K Kᗮ := by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
theorem orthogonal_eq_inter : Kᗮ = ⨅ v : K, LinearMap.ker (innerSL 𝕜 (v : E)) := by
  apply le_antisymm
  · rw [le_iInf_iff]
    rintro ⟨v, hv⟩ w hw
    simpa using hw _ hv
  · intro v hv w hw
    simp only [mem_iInf] at hv
    exact hv ⟨w, hw⟩

/-- The orthogonal complement of any submodule `K` is closed. -/
theorem isClosed_orthogonal : IsClosed (Kᗮ : Set E) := by
  rw [orthogonal_eq_inter K]
  convert isClosed_iInter <| fun v : K => ContinuousLinearMap.isClosed_ker (innerSL 𝕜 (v : E))
  simp only [coe_iInf]

/-- In a complete space, the orthogonal complement of any submodule `K` is complete. -/
instance instOrthogonalCompleteSpace [CompleteSpace E] : CompleteSpace Kᗮ :=
  K.isClosed_orthogonal.completeSpace_coe

variable (𝕜 E)

/-- `orthogonal` gives a `GaloisConnection` between
`Submodule 𝕜 E` and its `OrderDual`. -/
theorem orthogonal_gc :
    @GaloisConnection (Submodule 𝕜 E) (Submodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal := fun _K₁ _K₂ =>
  ⟨fun h _v hv _u hu => inner_left_of_mem_orthogonal hv (h hu), fun h _v hv _u hu =>
    inner_left_of_mem_orthogonal hv (h hu)⟩

variable {𝕜 E}

/-- `orthogonal` reverses the `≤` ordering of two
subspaces. -/
theorem orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ K₁ᗮ :=
  (orthogonal_gc 𝕜 E).monotone_l h

/-- `orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
theorem orthogonal_orthogonal_monotone {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₁ᗮᗮ ≤ K₂ᗮᗮ :=
  orthogonal_le (orthogonal_le h)

/-- `K` is contained in `Kᗮᗮ`. -/
theorem le_orthogonal_orthogonal : K ≤ Kᗮᗮ :=
  (orthogonal_gc 𝕜 E).le_u_l _

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
theorem inf_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sup.symm

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
theorem iInf_orthogonal {ι : Type*} (K : ι → Submodule 𝕜 E) : ⨅ i, (K i)ᗮ = (iSup K)ᗮ :=
  (orthogonal_gc 𝕜 E).l_iSup.symm

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
theorem sInf_orthogonal (s : Set <| Submodule 𝕜 E) : ⨅ K ∈ s, Kᗮ = (sSup s)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sSup.symm

@[simp]
theorem top_orthogonal_eq_bot : (⊤ : Submodule 𝕜 E)ᗮ = ⊥ := by
  ext x
  rw [mem_bot, mem_orthogonal]
  exact
    ⟨fun h => inner_self_eq_zero.mp (h x mem_top), by
      rintro rfl
      simp⟩

@[simp]
theorem bot_orthogonal_eq_top : (⊥ : Submodule 𝕜 E)ᗮ = ⊤ := by
  rw [← top_orthogonal_eq_bot, eq_top_iff]
  exact le_orthogonal_orthogonal ⊤

@[simp]
theorem orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ := by
  refine
    ⟨?_, by
      rintro rfl
      exact bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this

/-- The closure of a submodule has the same orthogonal complement and the submodule itself. -/
@[simp]
lemma orthogonal_closure (K : Submodule 𝕜 E) : K.topologicalClosureᗮ = Kᗮ :=
  le_antisymm (orthogonal_le <| le_topologicalClosure _)
    fun x hx y hy ↦ closure_minimal hx (isClosed_eq (by fun_prop) (by fun_prop)) hy

theorem orthogonalFamily_self :
    OrthogonalFamily 𝕜 (fun b => ↥(cond b K Kᗮ)) fun b => (cond b K Kᗮ).subtypeₗᵢ
  | true, true => absurd rfl
  | true, false => fun _ x y => inner_right_of_mem_orthogonal x.prop y.prop
  | false, true => fun _ x y => inner_left_of_mem_orthogonal y.prop x.prop
  | false, false => absurd rfl

end Submodule

@[simp]
theorem bilinFormOfRealInner_orthogonal {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) : K.orthogonalBilin bilinFormOfRealInner = Kᗮ :=
  rfl

/-!
### Orthogonality of submodules

In this section we define `Submodule.IsOrtho U V`, denoted as `U ⟂ V`.

The API roughly matches that of `Disjoint`.
-/


namespace Submodule

/-- The proposition that two submodules are orthogonal, denoted as `U ⟂ V`. -/
def IsOrtho (U V : Submodule 𝕜 E) : Prop :=
  U ≤ Vᗮ

@[inherit_doc]
infixl:50 " ⟂ " => Submodule.IsOrtho

theorem isOrtho_iff_le {U V : Submodule 𝕜 E} : U ⟂ V ↔ U ≤ Vᗮ :=
  Iff.rfl

@[symm]
theorem IsOrtho.symm {U V : Submodule 𝕜 E} (h : U ⟂ V) : V ⟂ U :=
  (le_orthogonal_orthogonal _).trans (orthogonal_le h)

theorem isOrtho_comm {U V : Submodule 𝕜 E} : U ⟂ V ↔ V ⟂ U :=
  ⟨IsOrtho.symm, IsOrtho.symm⟩

theorem symmetric_isOrtho : Symmetric (IsOrtho : Submodule 𝕜 E → Submodule 𝕜 E → Prop) := fun _ _ =>
  IsOrtho.symm

theorem IsOrtho.inner_eq {U V : Submodule 𝕜 E} (h : U ⟂ V) {u v : E} (hu : u ∈ U) (hv : v ∈ V) :
    ⟪u, v⟫ = 0 :=
  h.symm hv _ hu

theorem isOrtho_iff_inner_eq {U V : Submodule 𝕜 E} : U ⟂ V ↔ ∀ u ∈ U, ∀ v ∈ V, ⟪u, v⟫ = 0 :=
  forall₄_congr fun _u _hu _v _hv => inner_eq_zero_symm

/- TODO: generalize `Submodule.map₂` to semilinear maps, so that we can state
`U ⟂ V ↔ Submodule.map₂ (innerₛₗ 𝕜) U V ≤ ⊥`. -/
@[simp]
theorem isOrtho_bot_left {V : Submodule 𝕜 E} : ⊥ ⟂ V :=
  bot_le

@[simp]
theorem isOrtho_bot_right {U : Submodule 𝕜 E} : U ⟂ ⊥ :=
  isOrtho_bot_left.symm

theorem IsOrtho.mono_left {U₁ U₂ V : Submodule 𝕜 E} (hU : U₂ ≤ U₁) (h : U₁ ⟂ V) : U₂ ⟂ V :=
  hU.trans h

theorem IsOrtho.mono_right {U V₁ V₂ : Submodule 𝕜 E} (hV : V₂ ≤ V₁) (h : U ⟂ V₁) : U ⟂ V₂ :=
  (h.symm.mono_left hV).symm

theorem IsOrtho.mono {U₁ V₁ U₂ V₂ : Submodule 𝕜 E} (hU : U₂ ≤ U₁) (hV : V₂ ≤ V₁) (h : U₁ ⟂ V₁) :
    U₂ ⟂ V₂ :=
  (h.mono_right hV).mono_left hU

@[simp]
theorem isOrtho_self {U : Submodule 𝕜 E} : U ⟂ U ↔ U = ⊥ :=
  ⟨fun h => eq_bot_iff.mpr fun x hx => inner_self_eq_zero.mp (h hx x hx), fun h =>
    h.symm ▸ isOrtho_bot_left⟩

@[simp]
theorem isOrtho_orthogonal_right (U : Submodule 𝕜 E) : U ⟂ Uᗮ :=
  le_orthogonal_orthogonal _

@[simp]
theorem isOrtho_orthogonal_left (U : Submodule 𝕜 E) : Uᗮ ⟂ U :=
  (isOrtho_orthogonal_right U).symm

theorem IsOrtho.le {U V : Submodule 𝕜 E} (h : U ⟂ V) : U ≤ Vᗮ :=
  h

theorem IsOrtho.ge {U V : Submodule 𝕜 E} (h : U ⟂ V) : V ≤ Uᗮ :=
  h.symm

@[simp]
theorem isOrtho_top_right {U : Submodule 𝕜 E} : U ⟂ ⊤ ↔ U = ⊥ :=
  ⟨fun h => eq_bot_iff.mpr fun _x hx => inner_self_eq_zero.mp (h hx _ mem_top), fun h =>
    h.symm ▸ isOrtho_bot_left⟩

@[simp]
theorem isOrtho_top_left {V : Submodule 𝕜 E} : ⊤ ⟂ V ↔ V = ⊥ :=
  isOrtho_comm.trans isOrtho_top_right

/-- Orthogonal submodules are disjoint. -/
theorem IsOrtho.disjoint {U V : Submodule 𝕜 E} (h : U ⟂ V) : Disjoint U V :=
  (Submodule.orthogonal_disjoint _).mono_right h.symm

@[simp]
theorem isOrtho_sup_left {U₁ U₂ V : Submodule 𝕜 E} : U₁ ⊔ U₂ ⟂ V ↔ U₁ ⟂ V ∧ U₂ ⟂ V :=
  sup_le_iff

@[simp]
theorem isOrtho_sup_right {U V₁ V₂ : Submodule 𝕜 E} : U ⟂ V₁ ⊔ V₂ ↔ U ⟂ V₁ ∧ U ⟂ V₂ :=
  isOrtho_comm.trans <| isOrtho_sup_left.trans <| isOrtho_comm.and isOrtho_comm

@[simp]
theorem isOrtho_sSup_left {U : Set (Submodule 𝕜 E)} {V : Submodule 𝕜 E} :
    sSup U ⟂ V ↔ ∀ Uᵢ ∈ U, Uᵢ ⟂ V :=
  sSup_le_iff

@[simp]
theorem isOrtho_sSup_right {U : Submodule 𝕜 E} {V : Set (Submodule 𝕜 E)} :
    U ⟂ sSup V ↔ ∀ Vᵢ ∈ V, U ⟂ Vᵢ :=
  isOrtho_comm.trans <| isOrtho_sSup_left.trans <| by simp_rw [isOrtho_comm]

@[simp]
theorem isOrtho_iSup_left {ι : Sort*} {U : ι → Submodule 𝕜 E} {V : Submodule 𝕜 E} :
    iSup U ⟂ V ↔ ∀ i, U i ⟂ V :=
  iSup_le_iff

@[simp]
theorem isOrtho_iSup_right {ι : Sort*} {U : Submodule 𝕜 E} {V : ι → Submodule 𝕜 E} :
    U ⟂ iSup V ↔ ∀ i, U ⟂ V i :=
  isOrtho_comm.trans <| isOrtho_iSup_left.trans <| by simp_rw [isOrtho_comm]

@[simp]
theorem isOrtho_span {s t : Set E} :
    span 𝕜 s ⟂ span 𝕜 t ↔ ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ t → ⟪u, v⟫ = 0 := by
  simp_rw [span_eq_iSup_of_singleton_spans s, span_eq_iSup_of_singleton_spans t, isOrtho_iSup_left,
    isOrtho_iSup_right, isOrtho_iff_le, span_le, Set.subset_def, SetLike.mem_coe,
    mem_orthogonal_singleton_iff_inner_left, Set.mem_singleton_iff, forall_eq]

theorem IsOrtho.map (f : E →ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E} (h : U ⟂ V) : U.map f ⟂ V.map f := by
  rw [isOrtho_iff_inner_eq] at *
  simp_rw [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    LinearIsometry.inner_map_map]
  exact h

theorem IsOrtho.comap (f : E →ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F} (h : U ⟂ V) :
    U.comap f ⟂ V.comap f := by
  rw [isOrtho_iff_inner_eq] at *
  simp_rw [mem_comap, ← f.inner_map_map]
  intro u hu v hv
  exact h _ hu _ hv

@[simp]
theorem IsOrtho.map_iff (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E} : U.map f ⟂ V.map f ↔ U ⟂ V :=
  ⟨fun h => by
    have hf : ∀ p : Submodule 𝕜 E, (p.map f).comap f.toLinearIsometry = p :=
      comap_map_eq_of_injective f.injective
    simpa only [hf] using h.comap f.toLinearIsometry, IsOrtho.map f.toLinearIsometry⟩

@[simp]
theorem IsOrtho.comap_iff (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F} : U.comap f ⟂ V.comap f ↔ U ⟂ V :=
  ⟨fun h => by
    have hf : ∀ p : Submodule 𝕜 F, (p.comap f).map f.toLinearIsometry = p :=
      map_comap_eq_of_surjective f.surjective
    simpa only [hf] using h.map f.toLinearIsometry, IsOrtho.comap f.toLinearIsometry⟩

end Submodule

open scoped Function in -- required for scoped `on` notation
theorem orthogonalFamily_iff_pairwise {ι} {V : ι → Submodule 𝕜 E} :
    (OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) ↔ Pairwise ((· ⟂ ·) on V) :=
  forall₃_congr fun _i _j _hij =>
    Subtype.forall.trans <|
      forall₂_congr fun _x _hx => Subtype.forall.trans <|
        forall₂_congr fun _y _hy => inner_eq_zero_symm

alias ⟨OrthogonalFamily.pairwise, OrthogonalFamily.of_pairwise⟩ := orthogonalFamily_iff_pairwise

/-- Two submodules in an orthogonal family with different indices are orthogonal. -/
theorem OrthogonalFamily.isOrtho {ι} {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) {i j : ι} (hij : i ≠ j) :
    V i ⟂ V j :=
  hV.pairwise hij
