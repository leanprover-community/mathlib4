/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Geometry.Convex.Cone.Pointed.Basic

/-!
# Faces of pointed cones

This file defines what it means for a pointed cone to be a face of another pointed cone and
establishes basic properties of this relation.
A subcone `F` of a cone `C` is a face if any two points in `C` that have a positive combination
in `F` are also in `F`.

## Main declarations

* `IsFaceOf F C`: States that the pointed cone `F` is a face of the pointed cone `C`.

## Implementation notes

* We prove that every face is an extreme set of its cone. We do not use `IsExtreme` as a
  definition because this is an affine notion and does not allow the flexibility necessary to
  deal wth cones over general rings. E.g. the cone of positive integers has no proper subset that
  are extreme.
* Most results proven over a field hold more generally over an Archimedean ring. In particular,
  `iff_mem_of_add_mem` holds whenever for every `x ∈ R` there is a `y ∈ R` with `1 ≤ x * y`.

-/

open Submodule

@[expose] public section

namespace PointedCone

variable {R M N : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M] in
/-- A sub-cone `F` of a pointed cone `C` is a face of `C` if any two points of `C` with a strictly
positive combination in `F` are also in `F`. -/
structure IsFaceOf (F C : PointedCone R M) where
  le : F ≤ C
  mem_of_smul_add_mem :
    ∀ {x y : M} {a : R}, x ∈ C → y ∈ C → 0 < a → a • x + y ∈ F → x ∈ F

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C C₁ C₂ F F₁ F₂ : PointedCone R M}

theorem iff_mem_of_smul_add_smul_mem :
    (F ≤ C ∧ ∀ {x y : M} {a b : R}, x ∈ C → y ∈ C → 0 < a → 0 < b → a • x + b • y ∈ F → x ∈ F) ↔
    F.IsFaceOf C := by
  constructor <;> intro h
  · refine ⟨h.1, ?_⟩
    by_cases hc : 0 < (1 : R)
    · intros xc yc a0 haxy
      exact h.2 xc yc a0 hc (by simpa)
    · simp [(subsingleton_of_zero_eq_one (zero_le_one.eq_or_lt.resolve_right hc)).eq_zero]
  · refine ⟨h.1, fun xC yC a0 b0 hab => ?_⟩
    exact h.2 xC (Submodule.smul_mem C ⟨_, le_of_lt b0⟩ yC) a0 hab

/-- Two faces of a cone are contained in each other if and only if one is a face of the other. -/
theorem iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : F₁ ≤ F₂ ↔ F₁.IsFaceOf F₂ := by
  refine ⟨fun h => ?_, IsFaceOf.le⟩
  rw [← iff_mem_of_smul_add_smul_mem] at ⊢ h₁
  exact ⟨h, fun hx hy => h₁.2 (h₂.le hx) (h₂.le hy)⟩

namespace IsFaceOf

/-- A pointed cone `C` as a face of itself. -/
@[refl, simp]
theorem refl (C : PointedCone R M) : C.IsFaceOf C := ⟨fun _ a => a, fun hx _ _ _ => hx⟩

protected theorem rfl {C : PointedCone R M} : C.IsFaceOf C := ⟨fun _ a => a, fun hx _ _ _ => hx⟩

/-- The face of a face of a cone is also a face of the cone. -/
@[trans]
theorem trans (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) : F₂.IsFaceOf C := by
  rw [← iff_mem_of_smul_add_smul_mem] at h₁ h₂ ⊢
  refine ⟨h₁.1.trans h₂.1, fun hx hy a0 b0 h ↦ ?_⟩
  exact h₁.2 (h₂.2 hx hy a0 b0 (h₁.1 h)) (h₂.2 hy hx b0 a0 (by rw [add_comm]; exact h₁.1 h)) a0 b0 h

/-- A face of a cone is an extreme subset of the cone. -/
theorem isExtreme (h : F.IsFaceOf C) : IsExtreme R (C : Set M) F := by
  apply iff_mem_of_smul_add_smul_mem.mpr at h
  refine ⟨h.1, ?_⟩
  rintro x xc y yc z zf ⟨a, b, a0, b0, -, hz⟩
  apply h.2 xc yc a0 b0
  rwa [← hz] at zf

/-- The intersection of two faces of two cones is a face of the intersection of the cones. -/
theorem inf (h₁ : F₁.IsFaceOf C₁) (h₂ : F₂.IsFaceOf C₂) :
    (F₁ ⊓ F₂).IsFaceOf (C₁ ⊓ C₂) := by
  use le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.le, Set.inter_subset_right.trans h₂.le⟩
  simp only [mem_inf, and_imp]
  refine fun xc₁ xc₂ yc₁ yc₂ a0 hz₁ hz₂ => ⟨?_, ?_⟩
  · exact h₁.mem_of_smul_add_mem xc₁ yc₁ a0 hz₁
  · exact h₂.mem_of_smul_add_mem xc₂ yc₂ a0 hz₂

/-- The intersection of two faces of a cone is a face of the cone. -/
theorem inf_left (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C :=
  inf_idem C ▸ inf h₁ h₂

/-- If a cone is a face of two cones simultaneously, then it's also a face of their intersection. -/
theorem inf_right (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂) : F.IsFaceOf (C₁ ⊓ C₂) :=
  inf_idem F ▸ inf h₁ h₂

theorem mem_of_add_mem (hF : F.IsFaceOf C) {x y : M}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x + y ∈ F) : x ∈ F := by
  nontriviality R using Module.subsingleton R M
  simpa [hxy] using hF.mem_of_smul_add_mem hx hy zero_lt_one

theorem mem_iff_add_mem (hF : F.IsFaceOf C) {x y : M}
    (hx : x ∈ C) (hy : y ∈ C) : x + y ∈ F ↔  x ∈ F ∧ y ∈ F := by
  refine ⟨?_, fun ⟨hx, hy⟩ => F.add_mem hx hy⟩
  exact fun h => ⟨mem_of_add_mem hF hx hy h, mem_of_add_mem hF hy hx (by rwa [add_comm])⟩

theorem mem_of_sum_mem {ι : Type*} [Fintype ι] {f : ι → M} (hF : F.IsFaceOf C)
    (hsC : ∀ i, f i ∈ C) (hs : ∑ i, f i ∈ F) (i : ι) : f i ∈ F := by
  classical
  refine hF.mem_of_add_mem (hsC i) (sum_mem (fun j (_ : j ∈ Finset.univ.erase i) => hsC j)) ?_
  simp [hs]

section Map

variable [AddCommGroup N] [Module R N]

/-- The image of a face of a cone under an injective linear map is a face of the
  image of the cone. -/
theorem map (f : M →ₗ[R] N) (hf : Function.Injective f) (hF : F.IsFaceOf C) :
    (F.map f).IsFaceOf (C.map f) := by
  refine ⟨map_mono hF.le, ?_⟩
  simp only [mem_map, forall_exists_index, and_imp]
  intro _ _ a b bC fbx _ cC fcy ha _ x'F h
  refine ⟨b, ?_, fbx⟩
  apply hF.mem_of_smul_add_mem bC cC ha
  convert x'F
  apply hf
  simp [h, fbx, fcy]

/-- The image of a face of a cone under an equivalence is a face of the image of the cone. -/
theorem map_equiv (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C) :
    (F.map (e : M →ₗ[R] N)).IsFaceOf (C.map e) := hF.map _ e.injective

/-- The comap of a face of a cone under a linear map is a face of the comap of the cone. -/
theorem comap (f : N →ₗ[R] M) (hF : F.IsFaceOf C) :
    (F.comap f).IsFaceOf (C.comap f) := by
  refine ⟨comap_mono hF.le, ?_⟩
  simp only [mem_comap, map_add, map_smul]
  exact hF.mem_of_smul_add_mem

theorem of_comap_surjective {f : N →ₗ[R] M} (hf : Function.Surjective f)
    (hc : (F.comap f).IsFaceOf (C.comap f)) : F.IsFaceOf C := by
  constructor
  · intro x xF
    rw [← (hf x).choose_spec] at xF ⊢
    exact mem_comap.mp (hc.1 xF)
  · intro x y a xC yC a0 h
    rw [← (hf x).choose_spec] at h ⊢ xC
    rw [← (hf y).choose_spec] at h yC
    exact hc.2 xC yC a0 (by simpa)

end Map

end IsFaceOf

variable [AddCommGroup N] [Module R N] in
/-- The image of a face of a cone under an injective linear map is a face of the
  image of the cone. -/
theorem map_iff {f : M →ₗ[R] N} (hf : Function.Injective f) :
    (F.map f).IsFaceOf (C.map f) ↔ F.IsFaceOf C := by
  refine ⟨?_, IsFaceOf.map _ hf⟩
  · intro ⟨sub, hF⟩
    refine ⟨fun x xf => ?_, fun hx hy ha h => ?_⟩
    · obtain ⟨y, yC, hy⟩ := mem_map.mp <| sub (mem_map_of_mem xf)
      rwa [hf hy] at yC
    · simp only [mem_map, forall_exists_index, and_imp] at hF
      obtain ⟨_, ⟨hx', hhx'⟩⟩ := hF _ hx rfl _ hy rfl ha _ h (by simp)
      convert hx'
      exact hf hhx'.symm

end Semiring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C F F₁ F₂ : PointedCone R M}

theorem iff_mem_of_add_mem :
    (F ≤ C ∧ ∀ {x y : M}, x ∈ C → y ∈ C → x + y ∈ F → x ∈ F) ↔ F.IsFaceOf C := by
  constructor <;> intro h
  · refine ⟨h.1, fun xC yC c0 hcxy => ?_⟩
    have cxF := h.2 (smul_mem _ (le_of_lt c0) xC) yC hcxy
    convert smul_mem _ (inv_nonneg.mpr (le_of_lt c0)) cxF
    simp [← smul_assoc, smul_eq_mul, mul_comm, Field.mul_inv_cancel _ (ne_of_lt c0).symm]
  · exact ⟨h.le, IsFaceOf.mem_of_add_mem h⟩

namespace IsFaceOf

/-- If the positive combination of points of a cone is in a face, then all the points are
  in the face. -/
theorem mem_of_sum_smul_mem {ι : Type*} [Fintype ι] {f : ι → M} {c : ι → R}
    (hF : F.IsFaceOf C) (hsC : ∀ i : ι, f i ∈ C) (hc : ∀ i, 0 ≤ c i) (hs : ∑ i : ι, c i • f i ∈ F)
    (i : ι) (hci : 0 < c i) : f i ∈ F := by
  classical
  have := mem_of_sum_mem hF (fun i => C.smul_mem (hc i) (hsC i)) hs i
  convert smul_mem (C := F) (x := (c i : R) • f i) (le_of_lt (Right.inv_pos.mpr hci)) this
  rw [← smul_assoc, smul_eq_mul, mul_comm, Field.mul_inv_cancel]
  · exact (MulAction.one_smul (f i)).symm
  · exact Ne.symm (ne_of_lt hci)

/-- The lineality space of a cone is a face. -/
lemma lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
  rw [← iff_mem_of_add_mem]
  simp only [lineal_le, true_and]
  intro _ _ xc yc xyf
  simp [neg_add_rev, xc, true_and] at xyf ⊢
  simpa [neg_add_cancel_comm] using add_mem xyf.2 yc

/-- The lineality space of a cone lies in every face. -/
lemma lineal_le (hF : F.IsFaceOf C) : C.lineal ≤ F :=
  fun _ hx => hF.mem_of_add_mem hx.1 hx.2 (by simp)

/-- The lineality space of a face of a cone agrees with the lineality space of the cone. -/
lemma lineal_eq_lineal (hF : F.IsFaceOf C) : F.lineal = C.lineal := by
  ext
  constructor <;> intro ⟨hx, hx'⟩
  · exact ⟨hF.le hx, hF.le hx'⟩
  constructor
  · exact hF.mem_of_add_mem hx hx' (by simp)
  · exact hF.mem_of_add_mem hx' hx (by simp)

section Prod

variable [AddCommGroup N] [Module R N]

/-- The product of two faces of two cones is a face of the product of the cones. -/
theorem prod {C₁ F₁ : PointedCone R M} {C₂ F₂ : PointedCone R N}
    (hF₁ : F₁.IsFaceOf C₁) (hF₂ : F₂.IsFaceOf C₂) : IsFaceOf (F₁.prod F₂) (C₁.prod C₂) := by
  constructor
  · intro x hx; simpa [mem_prod] using ⟨hF₁.le hx.1, hF₂.le hx.2⟩
  · simp only [mem_prod, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
      Prod.smul_snd, and_imp, Prod.forall]
    intro _ _ _ _ _ xc₁ xc₂ yc₁ yc₂ a0 hab₁ hab₂
    constructor
    · exact hF₁.mem_of_smul_add_mem xc₁ yc₁ a0 hab₁
    · exact hF₂.mem_of_smul_add_mem xc₂ yc₂ a0 hab₂

/-- The projection of a face of a product cone onto the first component is a face of the
  projection of the product cone onto the first component. -/
theorem fst {C₁ : PointedCone R M} {C₂ : PointedCone R N}
    {F : PointedCone R (M × N)}
    (hF : F.IsFaceOf (C₁.prod C₂)) : (F.map (.fst R M N)).IsFaceOf C₁ := by
  constructor
  · intro x hx
    simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right] at hx
    exact (Set.mem_prod.mp <| hF.le hx.choose_spec).1
  · simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right,
      forall_exists_index]
    intro x y a hx hy ha z h
    refine ⟨0, hF.mem_of_smul_add_mem (x := (x, 0)) (y := (y, z)) ?_ ?_ ha (by simpa)⟩
    · exact mem_prod.mp ⟨hx, zero_mem C₂⟩
    · exact mem_prod.mp ⟨hy, (hF.le h).2⟩

/-- The projection of a face of a product cone onto the second component is a face of the
  projection of the product cone onto the second component. -/
theorem snd {C₁ : PointedCone R M} {C₂ : PointedCone R N} {F : PointedCone R (M × N)}
    (hF : F.IsFaceOf (C₁.prod C₂)) : (F.map (.snd R M N)).IsFaceOf C₂ := by
  have := map _ (LinearEquiv.prodComm R M N).injective hF
  convert fst (by simpa [PointedCone.map, Submodule.map])
  ext; simp

end Prod

end IsFaceOf

end Field

end PointedCone
