/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis

! This file was ported from Lean 3 source module analysis.inner_product_space.orthogonal
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.BilinearForm
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Orthogonal complements of submodules

In this file, the `orthogonal` complement of a submodule `K` is defined, and basic API established.
Some of the more subtle results about the orthogonal complement are delayed to
`analysis.inner_product_space.projection`.

See also `bilin_form.orthogonal` for orthogonality with respect to a general bilinear form.

## Notation

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.

The proposition that two submodules are orthogonal, `submodule.is_ortho`, is denoted by `U ⟂ V`.
Note this is not the same unicode symbol as `⊥` (`has_bot`).
-/


variable {𝕜 E F : Type _} [IsROrC 𝕜]

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

namespace Submodule

variable (K : Submodule 𝕜 E)

/-- The subspace of vectors orthogonal to a given subspace. -/
def orthogonal : Submodule 𝕜 E
    where
  carrier := { v | ∀ u ∈ K, ⟪u, v⟫ = 0 }
  zero_mem' _ _ := inner_zero_right _
  add_mem' x y hx hy u hu := by rw [inner_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' c x hx u hu := by rw [inner_smul_right, hx u hu, MulZeroClass.mul_zero]
#align submodule.orthogonal Submodule.orthogonal

-- mathport name: «expr ᗮ»
notation:1200 K "ᗮ" => orthogonal K

/-- When a vector is in `Kᗮ`. -/
theorem mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫ = 0 :=
  Iff.rfl
#align submodule.mem_orthogonal Submodule.mem_orthogonal

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
theorem mem_orthogonal' (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪v, u⟫ = 0 := by
  simp_rw [mem_orthogonal, inner_eq_zero_symm]
#align submodule.mem_orthogonal' Submodule.mem_orthogonal'

variable {K}

/-- A vector in `K` is orthogonal to one in `Kᗮ`. -/
theorem inner_right_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪u, v⟫ = 0 :=
  (K.mem_orthogonal v).1 hv u hu
#align submodule.inner_right_of_mem_orthogonal Submodule.inner_right_of_mem_orthogonal

/-- A vector in `Kᗮ` is orthogonal to one in `K`. -/
theorem inner_left_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪v, u⟫ = 0 := by
  rw [inner_eq_zero_symm] <;> exact inner_right_of_mem_orthogonal hu hv
#align submodule.inner_left_of_mem_orthogonal Submodule.inner_left_of_mem_orthogonal

/-- A vector is in `(𝕜 ∙ u)ᗮ` iff it is orthogonal to `u`. -/
theorem mem_orthogonal_singleton_iff_inner_right {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0 :=
  by
  refine' ⟨inner_right_of_mem_orthogonal (mem_span_singleton_self u), _⟩
  intro hv w hw
  rw [mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  simp [inner_smul_left, hv]
#align submodule.mem_orthogonal_singleton_iff_inner_right Submodule.mem_orthogonal_singleton_iff_inner_right

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
theorem mem_orthogonal_singleton_iff_inner_left {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0 := by
  rw [mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm]
#align submodule.mem_orthogonal_singleton_iff_inner_left Submodule.mem_orthogonal_singleton_iff_inner_left

theorem sub_mem_orthogonal_of_inner_left {x y : E} (h : ∀ v : K, ⟪x, v⟫ = ⟪y, v⟫) : x - y ∈ Kᗮ :=
  by
  rw [mem_orthogonal']
  intro u hu
  rw [inner_sub_left, sub_eq_zero]
  exact h ⟨u, hu⟩
#align submodule.sub_mem_orthogonal_of_inner_left Submodule.sub_mem_orthogonal_of_inner_left

theorem sub_mem_orthogonal_of_inner_right {x y : E} (h : ∀ v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) :
    x - y ∈ Kᗮ := by
  intro u hu
  rw [inner_sub_right, sub_eq_zero]
  exact h ⟨u, hu⟩
#align submodule.sub_mem_orthogonal_of_inner_right Submodule.sub_mem_orthogonal_of_inner_right

variable (K)

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥ :=
  by
  rw [eq_bot_iff]
  intro x
  rw [mem_inf]
  exact fun ⟨hx, ho⟩ => inner_self_eq_zero.1 (ho x hx)
#align submodule.inf_orthogonal_eq_bot Submodule.inf_orthogonal_eq_bot

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem orthogonal_disjoint : Disjoint K Kᗮ := by simp [disjoint_iff, K.inf_orthogonal_eq_bot]
#align submodule.orthogonal_disjoint Submodule.orthogonal_disjoint

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
theorem orthogonal_eq_inter : Kᗮ = ⨅ v : K, LinearMap.ker (innerSL 𝕜 (v : E)) :=
  by
  apply le_antisymm
  · rw [le_iInf_iff]
    rintro ⟨v, hv⟩ w hw
    simpa using hw _ hv
  · intro v hv w hw
    simp only [mem_infi] at hv
    exact hv ⟨w, hw⟩
#align submodule.orthogonal_eq_inter Submodule.orthogonal_eq_inter

/-- The orthogonal complement of any submodule `K` is closed. -/
theorem isClosed_orthogonal : IsClosed (Kᗮ : Set E) :=
  by
  rw [orthogonal_eq_inter K]
  have := fun v : K => ContinuousLinearMap.isClosed_ker (innerSL 𝕜 (v : E))
  convert isClosed_iInter this
  simp only [infi_coe]
#align submodule.is_closed_orthogonal Submodule.isClosed_orthogonal

/-- In a complete space, the orthogonal complement of any submodule `K` is complete. -/
instance [CompleteSpace E] : CompleteSpace Kᗮ :=
  K.isClosed_orthogonal.completeSpace_coe

variable (𝕜 E)

/-- `orthogonal` gives a `galois_connection` between
`submodule 𝕜 E` and its `order_dual`. -/
theorem orthogonal_gc :
    @GaloisConnection (Submodule 𝕜 E) (Submodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal := fun K₁ K₂ =>
  ⟨fun h v hv u hu => inner_left_of_mem_orthogonal hv (h hu), fun h v hv u hu =>
    inner_left_of_mem_orthogonal hv (h hu)⟩
#align submodule.orthogonal_gc Submodule.orthogonal_gc

variable {𝕜 E}

/-- `orthogonal` reverses the `≤` ordering of two
subspaces. -/
theorem orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ K₁ᗮ :=
  (orthogonal_gc 𝕜 E).monotone_l h
#align submodule.orthogonal_le Submodule.orthogonal_le

/-- `orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
theorem orthogonal_orthogonal_monotone {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₁ᗮᗮ ≤ K₂ᗮᗮ :=
  orthogonal_le (orthogonal_le h)
#align submodule.orthogonal_orthogonal_monotone Submodule.orthogonal_orthogonal_monotone

/-- `K` is contained in `Kᗮᗮ`. -/
theorem le_orthogonal_orthogonal : K ≤ Kᗮᗮ :=
  (orthogonal_gc 𝕜 E).le_u_l _
#align submodule.le_orthogonal_orthogonal Submodule.le_orthogonal_orthogonal

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
theorem inf_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sup.symm
#align submodule.inf_orthogonal Submodule.inf_orthogonal

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
theorem iInf_orthogonal {ι : Type _} (K : ι → Submodule 𝕜 E) : (⨅ i, (K i)ᗮ) = (iSup K)ᗮ :=
  (orthogonal_gc 𝕜 E).l_iSup.symm
#align submodule.infi_orthogonal Submodule.iInf_orthogonal

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
theorem Inf_orthogonal (s : Set <| Submodule 𝕜 E) : (⨅ K ∈ s, Kᗮ) = (sSup s)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sSup.symm
#align submodule.Inf_orthogonal Submodule.Inf_orthogonal

@[simp]
theorem top_orthogonal_eq_bot : (⊤ : Submodule 𝕜 E)ᗮ = ⊥ :=
  by
  ext
  rw [mem_bot, mem_orthogonal]
  exact
    ⟨fun h => inner_self_eq_zero.mp (h x mem_top),
      by
      rintro rfl
      simp⟩
#align submodule.top_orthogonal_eq_bot Submodule.top_orthogonal_eq_bot

@[simp]
theorem bot_orthogonal_eq_top : (⊥ : Submodule 𝕜 E)ᗮ = ⊤ :=
  by
  rw [← top_orthogonal_eq_bot, eq_top_iff]
  exact le_orthogonal_orthogonal ⊤
#align submodule.bot_orthogonal_eq_top Submodule.bot_orthogonal_eq_top

@[simp]
theorem orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ :=
  by
  refine'
    ⟨_, by
      rintro rfl
      exact bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this
#align submodule.orthogonal_eq_top_iff Submodule.orthogonal_eq_top_iff

theorem orthogonalFamily_self :
    OrthogonalFamily 𝕜 (fun b => ↥(cond b K Kᗮ)) fun b => (cond b K Kᗮ).subtypeₗᵢ
  | tt, tt => absurd rfl
  | tt, ff => fun _ x y => inner_right_of_mem_orthogonal x.Prop y.Prop
  | ff, tt => fun _ x y => inner_left_of_mem_orthogonal y.Prop x.Prop
  | ff, ff => absurd rfl
#align submodule.orthogonal_family_self Submodule.orthogonalFamily_self

end Submodule

@[simp]
theorem bilinFormOfRealInner_orthogonal {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) : bilinFormOfRealInner.orthogonal K = Kᗮ :=
  rfl
#align bilin_form_of_real_inner_orthogonal bilinFormOfRealInner_orthogonal

/-!
### Orthogonality of submodules

In this section we define `submodule.is_ortho U V`, with notation `U ⟂ V`.

The API roughly matches that of `disjoint`.
-/


namespace Submodule

/-- The proposition that two submodules are orthogonal. Has notation `U ⟂ V`. -/
def IsOrtho (U V : Submodule 𝕜 E) : Prop :=
  U ≤ Vᗮ
#align submodule.is_ortho Submodule.IsOrtho

-- mathport name: «expr ⟂ »
infixl:50 " ⟂ " => Submodule.IsOrtho

theorem isOrtho_iff_le {U V : Submodule 𝕜 E} : U ⟂ V ↔ U ≤ Vᗮ :=
  Iff.rfl
#align submodule.is_ortho_iff_le Submodule.isOrtho_iff_le

@[symm]
theorem IsOrtho.symm {U V : Submodule 𝕜 E} (h : U ⟂ V) : V ⟂ U :=
  (le_orthogonal_orthogonal _).trans (orthogonal_le h)
#align submodule.is_ortho.symm Submodule.IsOrtho.symm

theorem isOrtho_comm {U V : Submodule 𝕜 E} : U ⟂ V ↔ V ⟂ U :=
  ⟨IsOrtho.symm, IsOrtho.symm⟩
#align submodule.is_ortho_comm Submodule.isOrtho_comm

theorem symmetric_isOrtho : Symmetric (IsOrtho : Submodule 𝕜 E → Submodule 𝕜 E → Prop) := fun _ _ =>
  IsOrtho.symm
#align submodule.symmetric_is_ortho Submodule.symmetric_isOrtho

theorem IsOrtho.inner_eq {U V : Submodule 𝕜 E} (h : U ⟂ V) {u v : E} (hu : u ∈ U) (hv : v ∈ V) :
    ⟪u, v⟫ = 0 :=
  h.symm hv _ hu
#align submodule.is_ortho.inner_eq Submodule.IsOrtho.inner_eq

theorem isOrtho_iff_inner_eq {U V : Submodule 𝕜 E} : U ⟂ V ↔ ∀ u ∈ U, ∀ v ∈ V, ⟪u, v⟫ = 0 :=
  forall₄_congr fun u hu v hv => inner_eq_zero_symm
#align submodule.is_ortho_iff_inner_eq Submodule.isOrtho_iff_inner_eq

/- TODO: generalize `submodule.map₂` to semilinear maps, so that we can state
`U ⟂ V ↔ submodule.map₂ (innerₛₗ 𝕜) U V ≤ ⊥`. -/
@[simp]
theorem isOrtho_bot_left {V : Submodule 𝕜 E} : ⊥ ⟂ V :=
  bot_le
#align submodule.is_ortho_bot_left Submodule.isOrtho_bot_left

@[simp]
theorem isOrtho_bot_right {U : Submodule 𝕜 E} : U ⟂ ⊥ :=
  isOrtho_bot_left.symm
#align submodule.is_ortho_bot_right Submodule.isOrtho_bot_right

theorem IsOrtho.mono_left {U₁ U₂ V : Submodule 𝕜 E} (hU : U₂ ≤ U₁) (h : U₁ ⟂ V) : U₂ ⟂ V :=
  hU.trans h
#align submodule.is_ortho.mono_left Submodule.IsOrtho.mono_left

theorem IsOrtho.mono_right {U V₁ V₂ : Submodule 𝕜 E} (hV : V₂ ≤ V₁) (h : U ⟂ V₁) : U ⟂ V₂ :=
  (h.symm.mono_left hV).symm
#align submodule.is_ortho.mono_right Submodule.IsOrtho.mono_right

theorem IsOrtho.mono {U₁ V₁ U₂ V₂ : Submodule 𝕜 E} (hU : U₂ ≤ U₁) (hV : V₂ ≤ V₁) (h : U₁ ⟂ V₁) :
    U₂ ⟂ V₂ :=
  (h.mono_right hV).mono_left hU
#align submodule.is_ortho.mono Submodule.IsOrtho.mono

@[simp]
theorem isOrtho_self {U : Submodule 𝕜 E} : U ⟂ U ↔ U = ⊥ :=
  ⟨fun h => eq_bot_iff.mpr fun x hx => inner_self_eq_zero.mp (h hx x hx), fun h =>
    h.symm ▸ isOrtho_bot_left⟩
#align submodule.is_ortho_self Submodule.isOrtho_self

@[simp]
theorem isOrtho_orthogonal_right (U : Submodule 𝕜 E) : U ⟂ Uᗮ :=
  le_orthogonal_orthogonal _
#align submodule.is_ortho_orthogonal_right Submodule.isOrtho_orthogonal_right

@[simp]
theorem isOrtho_orthogonal_left (U : Submodule 𝕜 E) : Uᗮ ⟂ U :=
  (isOrtho_orthogonal_right U).symm
#align submodule.is_ortho_orthogonal_left Submodule.isOrtho_orthogonal_left

theorem IsOrtho.le {U V : Submodule 𝕜 E} (h : U ⟂ V) : U ≤ Vᗮ :=
  h
#align submodule.is_ortho.le Submodule.IsOrtho.le

theorem IsOrtho.ge {U V : Submodule 𝕜 E} (h : U ⟂ V) : V ≤ Uᗮ :=
  h.symm
#align submodule.is_ortho.ge Submodule.IsOrtho.ge

@[simp]
theorem isOrtho_top_right {U : Submodule 𝕜 E} : U ⟂ ⊤ ↔ U = ⊥ :=
  ⟨fun h => eq_bot_iff.mpr fun x hx => inner_self_eq_zero.mp (h hx _ mem_top), fun h =>
    h.symm ▸ isOrtho_bot_left⟩
#align submodule.is_ortho_top_right Submodule.isOrtho_top_right

@[simp]
theorem isOrtho_top_left {V : Submodule 𝕜 E} : ⊤ ⟂ V ↔ V = ⊥ :=
  isOrtho_comm.trans isOrtho_top_right
#align submodule.is_ortho_top_left Submodule.isOrtho_top_left

/-- Orthogonal submodules are disjoint. -/
theorem IsOrtho.disjoint {U V : Submodule 𝕜 E} (h : U ⟂ V) : Disjoint U V :=
  (Submodule.orthogonal_disjoint _).mono_right h.symm
#align submodule.is_ortho.disjoint Submodule.IsOrtho.disjoint

@[simp]
theorem isOrtho_sup_left {U₁ U₂ V : Submodule 𝕜 E} : U₁ ⊔ U₂ ⟂ V ↔ U₁ ⟂ V ∧ U₂ ⟂ V :=
  sup_le_iff
#align submodule.is_ortho_sup_left Submodule.isOrtho_sup_left

@[simp]
theorem isOrtho_sup_right {U V₁ V₂ : Submodule 𝕜 E} : U ⟂ V₁ ⊔ V₂ ↔ U ⟂ V₁ ∧ U ⟂ V₂ :=
  isOrtho_comm.trans <| isOrtho_sup_left.trans <| isOrtho_comm.And isOrtho_comm
#align submodule.is_ortho_sup_right Submodule.isOrtho_sup_right

@[simp]
theorem isOrtho_sSup_left {U : Set (Submodule 𝕜 E)} {V : Submodule 𝕜 E} :
    sSup U ⟂ V ↔ ∀ Uᵢ ∈ U, Uᵢ ⟂ V :=
  sSup_le_iff
#align submodule.is_ortho_Sup_left Submodule.isOrtho_sSup_left

@[simp]
theorem isOrtho_sSup_right {U : Submodule 𝕜 E} {V : Set (Submodule 𝕜 E)} :
    U ⟂ sSup V ↔ ∀ Vᵢ ∈ V, U ⟂ Vᵢ :=
  isOrtho_comm.trans <| isOrtho_sSup_left.trans <| by simp_rw [is_ortho_comm]
#align submodule.is_ortho_Sup_right Submodule.isOrtho_sSup_right

@[simp]
theorem isOrtho_iSup_left {ι : Sort _} {U : ι → Submodule 𝕜 E} {V : Submodule 𝕜 E} :
    iSup U ⟂ V ↔ ∀ i, U i ⟂ V :=
  iSup_le_iff
#align submodule.is_ortho_supr_left Submodule.isOrtho_iSup_left

@[simp]
theorem isOrtho_iSup_right {ι : Sort _} {U : Submodule 𝕜 E} {V : ι → Submodule 𝕜 E} :
    U ⟂ iSup V ↔ ∀ i, U ⟂ V i :=
  isOrtho_comm.trans <| isOrtho_iSup_left.trans <| by simp_rw [is_ortho_comm]
#align submodule.is_ortho_supr_right Submodule.isOrtho_iSup_right

@[simp]
theorem isOrtho_span {s t : Set E} :
    span 𝕜 s ⟂ span 𝕜 t ↔ ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ t → ⟪u, v⟫ = 0 := by
  simp_rw [span_eq_supr_of_singleton_spans s, span_eq_supr_of_singleton_spans t, is_ortho_supr_left,
    is_ortho_supr_right, is_ortho_iff_le, span_le, Set.subset_def, SetLike.mem_coe,
    mem_orthogonal_singleton_iff_inner_left, Set.mem_singleton_iff, forall_eq]
#align submodule.is_ortho_span Submodule.isOrtho_span

theorem IsOrtho.map (f : E →ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E} (h : U ⟂ V) : U.map f ⟂ V.map f :=
  by
  rw [is_ortho_iff_inner_eq] at *
  simp_rw [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    LinearIsometry.inner_map_map]
  exact h
#align submodule.is_ortho.map Submodule.IsOrtho.map

theorem IsOrtho.comap (f : E →ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F} (h : U ⟂ V) : U.comap f ⟂ V.comap f :=
  by
  rw [is_ortho_iff_inner_eq] at *
  simp_rw [mem_comap, ← f.inner_map_map]
  intro u hu v hv
  exact h _ hu _ hv
#align submodule.is_ortho.comap Submodule.IsOrtho.comap

@[simp]
theorem IsOrtho.map_iff (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E} : U.map f ⟂ V.map f ↔ U ⟂ V :=
  ⟨fun h =>
    by
    have hf : ∀ p : Submodule 𝕜 E, (p.map f).comap f.to_linear_isometry = p :=
      comap_map_eq_of_injective f.injective
    simpa only [hf] using h.comap f.to_linear_isometry, IsOrtho.map f.toLinearIsometry⟩
#align submodule.is_ortho.map_iff Submodule.IsOrtho.map_iff

@[simp]
theorem IsOrtho.comap_iff (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F} : U.comap f ⟂ V.comap f ↔ U ⟂ V :=
  ⟨fun h =>
    by
    have hf : ∀ p : Submodule 𝕜 F, (p.comap f).map f.to_linear_isometry = p :=
      map_comap_eq_of_surjective f.surjective
    simpa only [hf] using h.map f.to_linear_isometry, IsOrtho.comap f.toLinearIsometry⟩
#align submodule.is_ortho.comap_iff Submodule.IsOrtho.comap_iff

end Submodule

theorem orthogonalFamily_iff_pairwise {ι} {V : ι → Submodule 𝕜 E} :
    (OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) ↔ Pairwise ((· ⟂ ·) on V) :=
  forall₃_congr fun i j hij =>
    Subtype.forall.trans <|
      forall₂_congr fun x hx => Subtype.forall.trans <| forall₂_congr fun y hy => inner_eq_zero_symm
#align orthogonal_family_iff_pairwise orthogonalFamily_iff_pairwise

alias orthogonalFamily_iff_pairwise ↔ OrthogonalFamily.pairwise OrthogonalFamily.of_pairwise
#align orthogonal_family.pairwise OrthogonalFamily.pairwise
#align orthogonal_family.of_pairwise OrthogonalFamily.of_pairwise

/-- Two submodules in an orthogonal family with different indices are orthogonal. -/
theorem OrthogonalFamily.isOrtho {ι} {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) {i j : ι} (hij : i ≠ j) :
    V i ⟂ V j :=
  hV.Pairwise hij
#align orthogonal_family.is_ortho OrthogonalFamily.isOrtho

