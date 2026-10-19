/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/
module

public import Mathlib.Geometry.Convex.Segment
public import Mathlib.Geometry.Convex.Set.Basic

/-!
# Faces of sets

This file defines what it means for a set in a convex space to be a face of another set and
establishes basic properties of this relation.

## Main declarations

* `IsFaceOf F C`: States that the set `F` is a face of the set `C`.

-/

open Function Convexity

@[expose] public section

namespace Convexity

variable {R M N : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R M] [ConvexSpace R N]

variable (R) in
/-- A subset `F` of a set `F` is a face of `C` iff it is an extreme convex subset. -/
@[mk_iff]
structure IsFaceOf (F C : Set M) : Prop where
  isConvexSet : IsConvexSet R F
  le : F ⊆ C
  left_mem_of_mem_Ioo {x y z : M} : x ∈ C → y ∈ C →
    z ∈ F → z ∈ Ioo R x y → x ∈ F

variable {C C₁ C₂ F F₁ F₂ : Set M}

namespace IsFaceOf

/-- A convex set `C` is a face of itself. -/
@[refl, simp]
protected theorem refl {C : Set M} (h : IsConvexSet R C) : IsFaceOf R C C :=
  ⟨h, fun _ a ↦ a, fun hx _ _ _ ↦ hx⟩

protected theorem rfl {C : Set M} {h : IsConvexSet R C} : IsFaceOf R C C := .refl h

/-- A face of a set is a face of another if and only if they are contained in each other. -/
theorem isFaceOf_iff_le (h₁ : IsFaceOf R F₁ C) (h₂ : IsFaceOf R F₂ C) :
    IsFaceOf R F₁ F₂ ↔ F₁ ⊆ F₂ :=
  ⟨IsFaceOf.le, fun h ↦ ⟨h₁.isConvexSet, h, fun hx hy hz hs↦ h₁.3 (h₂.le hx) (h₂.le hy) hz hs⟩⟩

/-- The empty set is a face of every set. -/
protected theorem empty {C : Set M} : IsFaceOf R ∅ C :=
  ⟨IsConvexSet.empty, Set.empty_subset C, fun _ _ h _ ↦ h⟩

/-- The intersection of two faces of two sets is a face of the intersection of the sets. -/
protected theorem inf (h₁ : IsFaceOf R F₁ C₁) (h₂ : IsFaceOf R F₂ C₂) :
    IsFaceOf R (F₁ ∩ F₂) (C₁ ∩ C₂) where
  isConvexSet := IsConvexSet.inter h₁.isConvexSet h₂.isConvexSet
  le := le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.le, Set.inter_subset_right.trans h₂.le⟩
  left_mem_of_mem_Ioo := by
    simp only [Set.mem_inter_iff, and_imp]
    refine fun xC₁ xC₂ yC₁ yC₂ zF₁ zF₂ hz ↦ ⟨?_, ?_⟩
    · exact h₁.left_mem_of_mem_Ioo xC₁ yC₁ zF₁ hz
    · exact h₂.left_mem_of_mem_Ioo xC₂ yC₂ zF₂ hz

/-- The intersection of two faces of a set is a face of the set. -/
theorem inf_left (h₁ : IsFaceOf R F₁ C) (h₂ : IsFaceOf R F₂ C) : IsFaceOf R (F₁ ∩ F₂) C :=
  inf_idem C ▸ IsFaceOf.inf h₁ h₂

/-- If a set is a face of two sets simultaneously, then it's also a face of their intersection. -/
theorem inf_right (h₁ : IsFaceOf R F C₁) (h₂ : IsFaceOf R F C₂) : IsFaceOf R F (C₁ ∩ C₂) :=
  inf_idem F ▸ IsFaceOf.inf h₁ h₂

protected theorem sInf (hc : IsConvexSet R C) {F : Set (Set M)} (h : ∀ f ∈ F, IsFaceOf R f C) :
    IsFaceOf R (C ∩ sInf F) C where
  isConvexSet := IsConvexSet.inter hc <| IsConvexSet.sInter (fun f hf ↦ (h f hf).isConvexSet)
  le _ sm := sm.1
  left_mem_of_mem_Ioo := by
    simp only [Set.sInf_eq_sInter, Set.mem_inter_iff, Set.mem_sInter, and_imp]
    intro _ _ _ xc yc zc zf zs
    simpa [xc] using fun f hf ↦ (h f hf).left_mem_of_mem_Ioo xc yc (zf f hf) zs

protected theorem sInf' {F : Set (Set M)} (hne : F.Nonempty) (h : ∀ f ∈ F, IsFaceOf R f C) :
    IsFaceOf R (sInf F) C where
  isConvexSet := IsConvexSet.sInter (fun f hf ↦ (h f hf).isConvexSet)
  le := by
    obtain ⟨f, hf⟩ := hne
    exact fun z hz ↦ (h f hf).le (Set.mem_sInter.mp hz f hf)
  left_mem_of_mem_Ioo := by
    intro x y z hx hy hz hseg
    rw [Set.sInf_eq_sInter, Set.mem_sInter] at hz ⊢
    exact fun f hf ↦ (h f hf).left_mem_of_mem_Ioo hx hy (hz f hf) hseg

/-- The face of a face of a set is also a face of the set. -/
@[trans]
protected theorem trans (h₁ : IsFaceOf R F₂ F₁) (h₂ : IsFaceOf R F₁ C) : IsFaceOf R F₂ C := by
  refine ⟨h₁.isConvexSet, h₁.le.trans h₂.le, ?_⟩
  intro x y z hx hy hz hhz
  have hz' : z ∈ F₁ := h₁.le hz
  exact h₁.3 (h₂.3 hx hy hz' hhz)
      (h₂.3 hy hx hz' (by simpa [Ioo_symm, Ioo_symm] using hhz)) hz hhz

section Map

variable {C₁ F₁ : Set M} {C₂ F₂ : Set N}

/- The image of a face under an injective affine map is a face of the image. -/
theorem map {φ : M → N} (hφ : IsAffineMap R φ) (hinj : Injective φ)
    (hF : IsFaceOf R F₁ C₁) : IsFaceOf R (φ '' F₁) (φ '' C₁) where
  isConvexSet := IsConvexSet.image hφ hF.isConvexSet
  le := Set.image_mono hF.le
  left_mem_of_mem_Ioo := by
    rintro _ _ a ⟨x, hmC, rfl⟩ ⟨y, hnC, rfl⟩ ⟨z, hlF, rfl⟩ ⟨_, _, ha, hb, hab, hcomb⟩
    refine Set.mem_image_of_mem _ (hF.3 hmC hnC hlF ⟨_, _, ha, hb, hab, hinj ?_⟩)
    simpa [hφ.map_convexCombPair] using hcomb

/- The preimage of a face is a face of the preimage. -/
theorem preimage {φ : M → N} (hφ : IsAffineMap R φ) (hF : IsFaceOf R F₂ C₂) :
    IsFaceOf R (φ ⁻¹' F₂) (φ ⁻¹' C₂) where
  isConvexSet := IsConvexSet.preimage hφ hF.isConvexSet
  le := Set.preimage_mono hF.le
  left_mem_of_mem_Ioo := by
    rintro x y z hx hy hz ⟨a, b, ha, hb, hab, hcomb⟩
    refine hF.3 hx hy hz ⟨a, b, ha, hb, hab, ?_⟩
    exact hcomb ▸ (hφ.map_convexCombPair ha.le hb.le hab x y).symm

theorem of_map_injective {φ : M → N} (hφ : IsAffineMap R φ) (hinj : Injective φ)
    (hF : IsFaceOf R (φ '' F₁) (φ '' C₁)) : IsFaceOf R F₁ C₁ := by
  have h' := IsFaceOf.preimage hφ hF
  rwa [Set.preimage_image_eq _ hinj, Set.preimage_image_eq _ hinj] at h'

theorem of_preimage_surjective {φ : M → N} (hφ : IsAffineMap R φ) (hsurj : Function.Surjective φ)
    (hc : IsFaceOf R (φ ⁻¹' F₂) (φ ⁻¹' C₂)) : IsFaceOf R F₂ C₂ := by
  have hcv := IsConvexSet.image hφ hc.isConvexSet
  rw [Set.image_preimage_eq _ hsurj] at hcv
  refine ⟨hcv, fun x xF ↦ ?_, fun {x y z} xC yC zF h ↦ ?_⟩
  · rw [← (hsurj x).choose_spec] at xF ⊢
    exact Set.mem_preimage.mp (hc.le xF)
  · rw [← (hsurj x).choose_spec] at h ⊢ xC
    rw [← (hsurj y).choose_spec] at h yC
    rw [← hφ.image_Ioo] at h
    obtain ⟨a, b, rfl⟩ := h
    exact hc.left_mem_of_mem_Ioo xC yC zF b

end Map

end IsFaceOf

/- `F` is a face of `C` iff the image of `F` is a face of the image of `C` under an injective affine
map -/
theorem isFaceOf_map_iff {φ : M → N} (hφ : IsAffineMap R φ) (hinj : Injective φ) :
    IsFaceOf R (φ '' F₁) (φ '' C₁) ↔ IsFaceOf R F₁ C₁ :=
  ⟨IsFaceOf.of_map_injective hφ hinj, IsFaceOf.map hφ hinj⟩

variable {C₂ F₂ : Set N} in
/-- The preimage of a set `F` under a surjective affine map is a face of the
preimage of another set `F` if and only if `F` is a face of `C`. -/
theorem isFaceOf_preimage_iff {φ : M → N} (hφ : IsAffineMap R φ) (hsurj : Function.Surjective φ) :
    IsFaceOf R (φ ⁻¹' F₂) (φ ⁻¹' C₂) ↔ IsFaceOf R F₂ C₂ :=
  ⟨IsFaceOf.of_preimage_surjective hφ hsurj, IsFaceOf.preimage hφ⟩

namespace IsFaceOf

section Prod

/-- The product of two faces of two sets is a face of the product of the sets. -/
protected theorem prod {C₁ F₁ : Set M} {C₂ F₂ : Set N}
    (hF₁ : IsFaceOf R F₁ C₁) (hF₂ : IsFaceOf R F₂ C₂) : IsFaceOf R (F₁ ×ˢ F₂) (C₁ ×ˢ C₂) where
  isConvexSet := IsConvexSet.prod hF₁.isConvexSet hF₂.isConvexSet
  le := fun x hx ↦ by simpa [Set.mem_prod] using ⟨hF₁.le hx.1, hF₂.le hx.2⟩
  left_mem_of_mem_Ioo := by
    simp only [Set.mem_prod, and_imp, Prod.forall]
    intro _ _ _ _ _ _ xC₁ xC₂ yC₁ yC₂ ha hb hs
    have := Prod.Ioo_subset R _ _ hs
    exact ⟨hF₁.3 xC₁ yC₁ ha this.1, hF₂.3 xC₂ yC₂ hb this.2⟩

/-- The projection of a face of a product set onto the first component is a face of the
projection of the product set onto the first component. -/
protected theorem fst {C₁ : Set M} {C₂ : Set N} {F : Set (M × N)}
    (hF : IsFaceOf R F (C₁ ×ˢ C₂)) : IsFaceOf R (Prod.fst '' F) C₁ where
  isConvexSet := IsConvexSet.image Prod.isAffineMap_fst hF.isConvexSet
  le := by
    intro x hx
    simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right] at hx
    exact (Set.mem_prod.mp <| hF.le hx.choose_spec).1
  left_mem_of_mem_Ioo := by
    simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right, forall_exists_index]
    intro x y a hx hy ha z h
    refine ⟨ha, hF.left_mem_of_mem_Ioo (x := (x, ha)) (y := (y, ha)) (z := (a, ha)) ?_ ?_ z ?_⟩
    · exact Set.mem_prod.mp ⟨hx, (hF.le z).2⟩
    · exact Set.mem_prod.mp ⟨hy, (hF.le z).2⟩
    · rw [← Prod.image_mk_Ioo_left R x y ha]
      simpa

/-- The projection of a face of a product set onto the second component is a face of the
projection of the product set onto the second component. -/
protected theorem snd {C₁ : Set M} {C₂ : Set N} {F : Set (M × N)}
    (hF : IsFaceOf R F (C₁ ×ˢ C₂)) : IsFaceOf R (Prod.snd '' F) C₂ := by
  have := hF.map (φ := Prod.swap) ((Prod.isAffineMap_snd).prodMk (Prod.isAffineMap_fst))
    Prod.swap_injective
  convert IsFaceOf.fst (by simpa)
  simp [Set.image_image]

end Prod

end IsFaceOf

end Semiring

end Convexity
