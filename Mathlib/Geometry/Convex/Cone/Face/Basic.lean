/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Faces of pointed cones

This file defines what it means for a pointed cone to be a face of another pointed cone and
establishes basic properties of this relation.
A subcone `F` of a cone `C` is a face if any two points in `C` that have a positive combination
in `F` are also in `F`.

## Main declarations

* `IsFaceOf F C`: States that the pointed cone `F` is a face of the pointed cone `C`.

## Implementation notes

* We do not use `IsExtreme` as a definition because this is an affine notion and does not allow the
  flexibility necessary to deal wth cones over general rings. E.g. the cone of positive integers has
  no proper subset that are extreme. We prove that every face is an extreme set of its cone.
* Most results proven over a division rin hold more generally over an Archimedean ring. In
  particular, `iff_mem_of_add_mem` holds whenever for every `x ∈ R` there is a `y ∈ R` with
  `1 ≤ x * y`.

-/

open Submodule

public section

namespace PointedCone

variable {R M N : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

/-- A sub-cone `F` of a pointed cone `C` is a face of `C` if any two points of `C` with a strictly
positive combination in `F` are also in `F`. -/
structure IsFaceOf (F C : PointedCone R M) : Prop where
  le : F ≤ C
  mem_of_smul_add_mem {x y : M} {a : R} :
    x ∈ C → y ∈ C → 0 < a → a • x + y ∈ F → x ∈ F
variable {C C₁ C₂ F F₁ F₂ : PointedCone R M}

theorem isFaceOf_iff_mem_of_smul_add_smul_mem : F.IsFaceOf C ↔
    F ≤ C ∧ ∀ {x y : M} {a b : R}, x ∈ C → y ∈ C → 0 < a → 0 < b → a • x + b • y ∈ F → x ∈ F where
  mp h := ⟨h.1, fun xC yC a0 b0 hab ↦ h.2 xC (Submodule.smul_mem C ⟨_, b0.le⟩ yC) a0 hab⟩
  mpr h := by
    refine ⟨h.1, ?_⟩
    by_cases hc : 0 < (1 : R)
    · exact fun xc yc a0 _ ↦ h.2 xc yc a0 hc (by simpa)
    · simp [(subsingleton_of_zero_eq_one (zero_le_one.eq_or_lt.resolve_right hc)).eq_zero]

namespace IsFaceOf

/-- A pointed cone `C` is a face of itself. -/
@[refl, simp]
protected theorem refl (C : PointedCone R M) : C.IsFaceOf C := ⟨fun _ a ↦ a, fun hx _ _ _ ↦ hx⟩

protected theorem rfl {C : PointedCone R M} : C.IsFaceOf C := ⟨fun _ a ↦ a, fun hx _ _ _ ↦ hx⟩

/-- The face of a face of a cone is also a face of the cone. -/
@[trans]
protected theorem trans (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) : F₂.IsFaceOf C := by
  rw [isFaceOf_iff_mem_of_smul_add_smul_mem] at h₁ h₂ ⊢
  refine ⟨h₁.1.trans h₂.1, fun hx hy a0 b0 h ↦ ?_⟩
  exact h₁.2 (h₂.2 hx hy a0 b0 (h₁.1 h)) (h₂.2 hy hx b0 a0 (by rw [add_comm]; exact h₁.1 h)) a0 b0 h

/-- A face of a cone is a face of another if and only if they are contained in each other. -/
theorem isFaceOf_iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    F₁.IsFaceOf F₂ ↔ F₁ ≤ F₂ := by
  refine ⟨IsFaceOf.le, fun h ↦ ?_⟩
  rw [isFaceOf_iff_mem_of_smul_add_smul_mem] at ⊢ h₁
  exact ⟨h, fun hx hy ↦ h₁.2 (h₂.le hx) (h₂.le hy)⟩

/-- A face of a cone is an extreme subset of the cone. -/
theorem isExtreme (h : F.IsFaceOf C) : IsExtreme R (C : Set M) F := by
  apply isFaceOf_iff_mem_of_smul_add_smul_mem.mp at h
  refine ⟨h.1, ?_⟩
  rintro x xc y yc z zf ⟨a, b, a0, b0, -, hz⟩
  apply h.2 xc yc a0 b0
  rwa [← hz] at zf

/-- The intersection of two faces of two cones is a face of the intersection of the cones. -/
theorem inf (h₁ : F₁.IsFaceOf C₁) (h₂ : F₂.IsFaceOf C₂) :
    (F₁ ⊓ F₂).IsFaceOf (C₁ ⊓ C₂) := by
  use le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.le, Set.inter_subset_right.trans h₂.le⟩
  simp only [mem_inf, and_imp]
  refine fun xc₁ xc₂ yc₁ yc₂ a0 hz₁ hz₂ ↦ ⟨?_, ?_⟩
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

theorem add_mem_iff (hF : F.IsFaceOf C) {x y : M} (hx : x ∈ C) (hy : y ∈ C) :
    x + y ∈ F ↔ x ∈ F ∧ y ∈ F := by
  refine ⟨?_, fun ⟨hx, hy⟩ ↦ F.add_mem hx hy⟩
  exact fun h ↦ ⟨mem_of_add_mem hF hx hy h, mem_of_add_mem hF hy hx (by rwa [add_comm])⟩

theorem sum_mem_iff_mem {ι : Type*} [Fintype ι] {f : ι → M} (hF : F.IsFaceOf C)
    (hsC : ∀ i, f i ∈ C) : ∑ i, f i ∈ F ↔ ∀ i, f i ∈ F := by
  classical
  refine ⟨fun hs i ↦ ?_, fun a ↦ Submodule.sum_mem F fun c _ ↦ a c⟩
  refine hF.mem_of_add_mem (hsC i) (sum_mem (fun j (_ : j ∈ Finset.univ.erase i) ↦ hsC j)) ?_
  simp [hs]

/-- If the positive combination of points of a cone is in a face, then all the points are
in the face. -/
theorem mem_of_sum_smul_mem {ι : Type*} [Fintype ι] {f : ι → M} {c : ι → R}
    (hF : F.IsFaceOf C) (hsC : ∀ i : ι, f i ∈ C) (hc : ∀ i, 0 ≤ c i) (hs : ∑ i : ι, c i • f i ∈ F)
    (i : ι) (hci : 0 < c i) : f i ∈ F := by classical
  rw [Finset.sum_eq_add_sum_diff_singleton i] at hs
  · refine hF.mem_of_smul_add_mem (hsC i) ?_ hci hs
    exact C.sum_mem fun i _ ↦ C.smul_mem (hc i) (hsC i)
  · simp

section Map

variable [AddCommGroup N] [Module R N]

/-- The image of a face of a cone under an injective linear map is a face of the
image of the cone. -/
protected theorem map (f : M →ₗ[R] N) (hf : Function.Injective f) (hF : F.IsFaceOf C) :
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
protected theorem comap (f : N →ₗ[R] M) (hF : F.IsFaceOf C) : (F.comap f).IsFaceOf (C.comap f) := by
  refine ⟨comap_mono hF.le, ?_⟩
  simp only [mem_comap, map_add, map_smul]
  exact hF.mem_of_smul_add_mem

theorem of_comap_surjective {f : N →ₗ[R] M} (hf : Function.Surjective f)
    (hc : (F.comap f).IsFaceOf (C.comap f)) : F.IsFaceOf C := by
  refine ⟨fun x xF ↦ ?_, fun {x y _} xC yC a0 h ↦ ?_⟩
  · rw [← (hf x).choose_spec] at xF ⊢
    exact mem_comap.mp (hc.1 xF)
  · rw [← (hf x).choose_spec] at h ⊢ xC
    rw [← (hf y).choose_spec] at h yC
    exact hc.2 xC yC a0 (by simpa)

end Map

end IsFaceOf

variable [AddCommGroup N] [Module R N] in
/-- The image of a cone `F` under an injective linear map is a face of the
image of another cone `C` if and only if `F` is a face of `C`. -/
theorem isFaceOf_map_iff {f : M →ₗ[R] N} (hf : Function.Injective f) :
    (F.map f).IsFaceOf (C.map f) ↔ F.IsFaceOf C := by
  refine ⟨?_, IsFaceOf.map _ hf⟩
  · intro ⟨sub, hF⟩
    refine ⟨fun x xf ↦ ?_, fun hx hy ha h ↦ ?_⟩
    · obtain ⟨y, yC, hy⟩ := mem_map.mp <| sub (mem_map_of_mem xf)
      rwa [hf hy] at yC
    · simp only [mem_map, forall_exists_index, and_imp] at hF
      obtain ⟨_, ⟨hx', hhx'⟩⟩ := hF _ hx rfl _ hy rfl ha _ h (by simp)
      convert hx'
      exact hf hhx'.symm

variable [AddCommGroup N] [Module R N] in
/-- The comap of a cone `F` under a surjective linear map is a face of the
comap of another cone `F` if and only if `F` is a face of `C`. -/
theorem isFaceOf_comap_iff {f : N →ₗ[R] M} (hf : Function.Surjective f) :
    (F.comap f).IsFaceOf (C.comap f) ↔ F.IsFaceOf C := by
  refine ⟨IsFaceOf.of_comap_surjective hf, IsFaceOf.comap _⟩

end Semiring

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C F F₁ F₂ : PointedCone R M}

theorem isFaceOf_iff_mem_of_add_mem : F.IsFaceOf C ↔
    (F ≤ C ∧ ∀ {x y : M}, x ∈ C → y ∈ C → x + y ∈ F → x ∈ F) := by
  refine ⟨fun h ↦ ⟨h.le, h.mem_of_add_mem⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun hx hy ha haxy ↦ ?_⟩⟩
  simpa [← smul_assoc, inv_mul_cancel₀ (ne_of_gt ha)] using smul_mem _
    (inv_nonneg.mpr (le_of_lt ha)) <| h₂ (smul_mem _ (le_of_lt ha) hx) hy haxy

namespace IsFaceOf

/-- The lineality space of a cone is a face. -/
lemma lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
  rw [isFaceOf_iff_mem_of_add_mem]
  simp only [lineal_le, true_and]
  intro _ _ xc yc xyf
  simp [neg_add_rev, xc, true_and] at xyf ⊢
  simpa [neg_add_cancel_comm] using add_mem xyf.2 yc

/-- The lineality space of a cone lies in every face. -/
lemma lineal_le (hF : F.IsFaceOf C) : C.lineal ≤ F :=
  fun _ hx ↦ hF.mem_of_add_mem hx.1 hx.2 (by simp)

/-- The lineality space of a face of a cone agrees with the lineality space of the cone. -/
lemma lineal_congr (hF : F.IsFaceOf C) : F.lineal = C.lineal := by
  ext
  constructor <;> intro ⟨hx, hx'⟩
  · exact ⟨hF.le hx, hF.le hx'⟩
  constructor
  · exact hF.mem_of_add_mem hx hx' (by simp)
  · exact hF.mem_of_add_mem hx' hx (by simp)

section Prod

variable [AddCommGroup N] [Module R N]

/-- The product of two faces of two cones is a face of the product of the cones. -/
protected theorem prod {C₁ F₁ : PointedCone R M} {C₂ F₂ : PointedCone R N}
    (hF₁ : F₁.IsFaceOf C₁) (hF₂ : F₂.IsFaceOf C₂) : IsFaceOf (F₁.prod F₂) (C₁.prod C₂) := by
  refine ⟨fun x hx ↦ by simpa [mem_prod] using ⟨hF₁.le hx.1, hF₂.le hx.2⟩, ?_⟩
  simp only [mem_prod, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, and_imp, Prod.forall]
  intro _ _ _ _ _ xc₁ xc₂ yc₁ yc₂ a0 hab₁ hab₂
  exact ⟨hF₁.mem_of_smul_add_mem xc₁ yc₁ a0 hab₁, hF₂.mem_of_smul_add_mem xc₂ yc₂ a0 hab₂⟩

/-- The projection of a face of a product cone onto the first component is a face of the
projection of the product cone onto the first component. -/
protected theorem fst {C₁ : PointedCone R M} {C₂ : PointedCone R N}
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
protected theorem snd {C₁ : PointedCone R M} {C₂ : PointedCone R N} {F : PointedCone R (M × N)}
    (hF : F.IsFaceOf (C₁.prod C₂)) : (F.map (.snd R M N)).IsFaceOf C₂ := by
  have := hF.map _ (LinearEquiv.prodComm R M N).injective
  convert IsFaceOf.fst (by simpa [PointedCone.map, Submodule.map])
  ext; simp

end Prod

end IsFaceOf

end DivisionRing

end PointedCone
