/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth, Antoine Chambert-Loir
-/
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Data.Set.Function
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Algebra.Group.Units.Hom

/-!
# Pointwise actions of equivariant maps

- `image_smul_setₛₗ` : under a `σ`-equivariant map,
  one has `f '' (c • s) = (σ c) • f '' s`.

- `preimage_smul_setₛₗ'` is a general version of the equality
  `f ⁻¹' (σ c • s) = c • f⁻¹' s`.
  It requires that `c` acts surjectively and `σ c` acts injectively and
  is provided with specific versions:
  - `preimage_smul_setₛₗ_of_isUnit_isUnit` when `c` and `σ c` are units
  - `IsUnit.preimage_smul_setₛₗ` when `σ` belongs to a `MonoidHomClass`and `c` is a unit
  - `MonoidHom.preimage_smul_setₛₗ` when `σ` is a `MonoidHom` and `c` is a unit
  - `Group.preimage_smul_setₛₗ` : when the types of `c` and `σ c` are groups.

- `image_smul_set`, `preimage_smul_set` and `Group.preimage_smul_set` are
  the variants when `σ` is the identity.

-/

open Function Set Pointwise


section MulActionSemiHomClass

section SMul

variable {M N F : Type*} {α β : Type*} {σ : M → N} [SMul M α] [SMul N β] [FunLike F α β]
  [MulActionSemiHomClass F σ α β] {f : F} {s : Set α} {t : Set β}

@[to_additive (attr := simp)]
theorem image_smul_setₛₗ (f : F) (c : M) (s : Set α) :
    f '' (c • s) = σ c • f '' s :=
  Semiconj.set_image (map_smulₛₗ f c) s

@[to_additive]
theorem Set.MapsTo.smul_setₛₗ (hst : MapsTo f s t) (c : M) : MapsTo f (c • s) (σ c • t) :=
  Function.Semiconj.mapsTo_image_right (map_smulₛₗ _ _) hst

/-- Translation of preimage is contained in preimage of translation -/
@[to_additive]
theorem smul_preimage_set_subsetₛₗ (f : F) (c : M) (t : Set β) : c • f ⁻¹' t ⊆ f ⁻¹' (σ c • t) :=
  ((mapsTo_preimage f t).smul_setₛₗ c).subset_preimage

@[deprecated (since := "2025-03-03")]
alias vadd_preimage_set_leₛₗ := vadd_preimage_set_subsetₛₗ

@[to_additive existing, deprecated (since := "2025-03-03")]
alias smul_preimage_set_leₛₗ := smul_preimage_set_subsetₛₗ

/-- General version of `preimage_smul_setₛₗ`.
This version assumes that the scalar multiplication by `c` is surjective
while the scalar multiplication by `σ c` is injective. -/
@[to_additive "General version of `preimage_vadd_setₛₗ`.
This version assumes that the vector addition of `c` is surjective
while the vector addition of `σ c` is injective."]
theorem preimage_smul_setₛₗ' {c : M}
    (hc : Function.Surjective (fun (m : α) ↦ c • m))
    (hc' : Function.Injective (fun (n : β) ↦ σ c • n)) :
    f ⁻¹' (σ c • t) = c • f ⁻¹' t := by
  refine Subset.antisymm ?_ (smul_preimage_set_subsetₛₗ f c t)
  rw [subset_def, hc.forall]
  rintro x ⟨y, hy, hxy⟩
  rw [map_smulₛₗ, hc'.eq_iff] at hxy
  subst y
  exact smul_mem_smul_set hy

end SMul

section Monoid

variable {M N F : Type*} {α β : Type*} {σ : M → N} [Monoid M] [Monoid N]
  [MulAction M α] [MulAction N β] [FunLike F α β] [MulActionSemiHomClass F σ α β]
  {f : F} {s : Set α} {t : Set β} {c : M}

/-- `preimage_smul_setₛₗ` when both scalars act by unit -/
@[to_additive]
theorem preimage_smul_setₛₗ_of_isUnit_isUnit (f : F)
    (hc : IsUnit c) (hc' : IsUnit (σ c)) (t : Set β) : f ⁻¹' (σ c • t) = c • f ⁻¹' t :=
  preimage_smul_setₛₗ' hc.smul_bijective.surjective hc'.smul_bijective.injective

@[deprecated (since := "2025-03-04")]
alias preimage_vadd_setₛₗ_of_addUnits := preimage_vadd_setₛₗ_of_isAddUnit_isAddUnit

@[to_additive existing, deprecated (since := "2025-03-04")]
alias preimage_smul_setₛₗ_of_units := preimage_smul_setₛₗ_of_isUnit_isUnit

/-- `preimage_smul_setₛₗ` when `c` is a unit and `σ` is a monoid homomorphism. -/
@[to_additive]
theorem IsUnit.preimage_smul_setₛₗ {F G : Type*} [FunLike G M N] [MonoidHomClass G M N]
    (σ : G) [FunLike F α β] [MulActionSemiHomClass F σ α β] (f : F) (hc : IsUnit c) (t : Set β) :
    f ⁻¹' (σ c • t) = c • f ⁻¹' t :=
  preimage_smul_setₛₗ_of_isUnit_isUnit _ hc (hc.map _) _

-- TODO: when you remove the next 2 aliases,
-- please move the group version below out of the `Group` namespace.
@[deprecated (since := "2025-03-04")]
alias preimage_vadd_setₛₗ := IsAddUnit.preimage_vadd_setₛₗ

@[to_additive existing, deprecated (since := "2025-03-04")]
alias preimage_smul_setₛₗ := IsUnit.preimage_smul_setₛₗ

/-- `preimage_smul_setₛₗ` when `c` is a unit and `σ` is a monoid homomorphism. -/
@[to_additive]
protected theorem MonoidHom.preimage_smul_setₛₗ {F : Type*} (σ : M →* N) [FunLike F α β]
    [MulActionSemiHomClass F σ α β] (f : F) (hc : IsUnit c) (t : Set β) :
    f ⁻¹' (σ c • t) = c • f ⁻¹' t :=
  hc.preimage_smul_setₛₗ σ f t

end Monoid

/-- `preimage_smul_setₛₗ` in the context of groups -/
@[to_additive]
theorem Group.preimage_smul_setₛₗ {G H α β : Type*} [Group G] [Group H] (σ : G → H)
    [MulAction G α] [MulAction H β]
    {F : Type*} [FunLike F α β] [MulActionSemiHomClass F σ α β] (f : F) (c : G) (t : Set β) :
    f ⁻¹' (σ c • t) = c • f ⁻¹' t :=
  preimage_smul_setₛₗ_of_isUnit_isUnit _ (Group.isUnit _) (Group.isUnit _) _

end MulActionSemiHomClass

section MulActionHomClass

section SMul

variable {M α β F : Type*} [SMul M α] [SMul M β] [FunLike F α β] [MulActionHomClass F M α β]

@[to_additive]
theorem image_smul_set (f : F) (c : M) (s : Set α) : f '' (c • s) = c • f '' s :=
  image_smul_setₛₗ f c s

@[to_additive]
theorem smul_preimage_set_subset (f : F) (c : M) (t : Set β) : c • f ⁻¹' t ⊆ f ⁻¹' (c • t) :=
  smul_preimage_set_subsetₛₗ f c t

@[deprecated (since := "2025-03-04")]
alias vadd_preimage_set_le := vadd_preimage_set_subset

@[to_additive existing, deprecated (since := "2025-03-04")]
alias smul_preimage_set_le := smul_preimage_set_subset

@[to_additive]
theorem Set.MapsTo.smul_set {f : F} {s : Set α} {t : Set β} (hst : MapsTo f s t) (c : M) :
    MapsTo f (c • s) (c • t) :=
  hst.smul_setₛₗ c

end SMul

@[to_additive]
theorem IsUnit.preimage_smul_set {M α β F : Type*} [Monoid M] [MulAction M α] [MulAction M β]
    [FunLike F α β] [MulActionHomClass F M α β] (f : F) {c : M} (hc : IsUnit c) (t : Set β) :
    f ⁻¹' (c • t) = c • f ⁻¹' t :=
  preimage_smul_setₛₗ_of_isUnit_isUnit f hc hc t

-- TODO: when you remove the next 2 aliases,
-- please move the `Group` version to the root namespace.
@[deprecated (since := "2025-03-04")]
alias preimage_vadd_set := IsAddUnit.preimage_vadd_set

@[deprecated (since := "2025-03-04")]
alias preimage_smul_set := IsUnit.preimage_smul_set

@[to_additive]
theorem Group.preimage_smul_set {G : Type*} [Group G] {α β : Type*} [MulAction G α] [MulAction G β]
    {F : Type*} [FunLike F α β] [MulActionHomClass F G α β] (f : F) (c : G) (t : Set β) :
    f ⁻¹' (c • t) = c • f ⁻¹' t :=
  (Group.isUnit c).preimage_smul_set f t

end MulActionHomClass
