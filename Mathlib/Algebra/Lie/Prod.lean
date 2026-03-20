/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module
public import Mathlib.Algebra.Lie.Ideal

/-! ### Products of Lie algebras

This file defines the Lie algebra structure the Product of two Lie algebras

## Main definitions

- products in the domain:
  - `LieHom.fst`
  - `LieHom.snd`
  - `LieHom.prod_ext`
- products in the codomain:
  - `LieHom.inl`
  - `LieHom.inr`
  - `LieHom.prod`
- products in both domain and codomain:
  - `LieHom.prodMap`

## Todo: Extend to further functionality from LinearMap.prod e.g.
 - Lie Equivalences related to products
 - Lie Submodule statements

-/

@[expose] public section

variable {R L₁ L₂ L L₃ L₄ L₅ L₆ : Type*}
  [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
  [LieRing L] [LieAlgebra R L] [LieRing L₃] [LieAlgebra R L₃] [LieRing L₄] [LieAlgebra R L₄]
  [LieRing L₅] [LieAlgebra R L₅] [LieRing L₆] [LieAlgebra R L₆]

namespace Prod

instance instLieRing : LieRing (L₁ × L₂) where
  bracket x y := ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩
  add_lie := by simp
  lie_add := by simp
  lie_self := by simp
  leibniz_lie := by simp

@[simp]
theorem bracket_apply (x y : L₁ × L₂) : ⁅x, y⁆ = ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩ := rfl

instance instLieAlgebra : LieAlgebra R (L₁ × L₂) where
  __ := inferInstanceAs (Module R (L₁ × L₂))
  lie_smul _ _ _ := by simp

end Prod

namespace LieHom

section
variable (R L₁ L₂)

/-- The first projection of a product is a Lie algebra map. -/
def fst : L₁ × L₂ →ₗ⁅R⁆ L₁ where
  toLinearMap := LinearMap.fst R L₁ L₂
  map_lie' := by simp

/-- The second projection of a product is a Lie algebra map. -/
def snd : L₁ × L₂ →ₗ⁅R⁆ L₂ where
  toLinearMap := LinearMap.snd R L₁ L₂
  map_lie' := by simp

/-- The left injection into a product is a Lie algebra map. -/
def inl : L₁ →ₗ⁅R⁆ L₁ × L₂ where
  toLinearMap := LinearMap.inl R L₁ L₂
  map_lie' := by simp

/-- The right injection into a product is a Lie algebra map. -/
def inr : L₂ →ₗ⁅R⁆ L₁ × L₂ where
  toLinearMap := LinearMap.inr R L₁ L₂
  map_lie' := by simp

end

@[simp] theorem fst_apply (x : L₁ × L₂) : fst R L₁ L₂ x = x.1 := rfl

@[simp] theorem snd_apply (x : L₁ × L₂) : snd R L₁ L₂ x = x.2 := rfl

@[simp, norm_cast] lemma coe_fst : ⇑(fst R L₁ L₂) = Prod.fst := rfl

@[simp, norm_cast] lemma coe_snd : ⇑(snd R L₁ L₂) = Prod.snd := rfl

theorem fst_surjective : Function.Surjective (fst R L₁ L₂) := fun x => ⟨(x, 0), rfl⟩

theorem snd_surjective : Function.Surjective (snd R L₁ L₂) := fun x => ⟨(0, x), rfl⟩

/-- The prod of two Lie algebra homomorphisms is a Lie algebra homomorphism. -/
@[simps!]
def prod (f : L →ₗ⁅R⁆ L₁) (g : L →ₗ⁅R⁆ L₂) : L →ₗ⁅R⁆ L₁ × L₂ where
  toLinearMap := LinearMap.prod f g
  map_lie' := by simp

theorem coe_prod (f : L →ₗ⁅R⁆ L₁) (g : L →ₗ⁅R⁆ L₂) : ⇑(f.prod g) = Pi.prod f g :=
  rfl

@[simp]
theorem fst_prod (f : L →ₗ⁅R⁆ L₁) (g : L →ₗ⁅R⁆ L₂) : (fst R L₁ L₂).comp (prod f g) = f := rfl

@[simp]
theorem snd_prod (f : L →ₗ⁅R⁆ L₁) (g : L →ₗ⁅R⁆ L₂) : (snd R L₁ L₂).comp (prod f g) = g := rfl

@[simp]
theorem pair_fst_snd : prod (fst R L₁ L₂) (snd R L₁ L₂) = LieHom.id := rfl

theorem prod_comp (f : L₁ →ₗ⁅R⁆ L₂) (g : L₁ →ₗ⁅R⁆ L)
    (h : L →ₗ⁅R⁆ L₁) : (f.prod g).comp h = (f.comp h).prod (g.comp h) :=
  rfl

theorem inl_apply (x : L₁) : inl R L₁ L₂ x = (x, 0) := rfl

theorem inr_apply (x : L₂) : inr R L₁ L₂ x = (0, x) := rfl

@[simp] theorem coe_inl : (inl R L₁ L₂ : L₁ → L₁ × L₂) = fun x => (x, 0) := rfl

@[simp] theorem coe_inr : (inr R L₁ L₂ : L₂ → L₁ × L₂) = Prod.mk 0 := rfl

theorem inl_injective : Function.Injective (inl R L₁ L₂) := fun _ => by simp

theorem inr_injective : Function.Injective (inr R L₁ L₂) := fun _ => by simp

section
variable (R L₁ L₂)

theorem range_inl : range (inl R L₁ L₂) = ker (snd R L₁ L₂) := by
  rw [← LieSubalgebra.toSubmodule_inj, range_toSubmodule, LieIdeal.toLieSubalgebra_toSubmodule,
   ker_toSubmodule]
  exact LinearMap.range_inl R L₁ L₂

theorem ker_snd : ker (snd R L₁ L₂) = range (inl R L₁ L₂) :=
  Eq.symm <| range_inl R L₁ L₂

theorem range_inr : range (inr R L₁ L₂) = ker (fst R L₁ L₂) := by
  rw [← LieSubalgebra.toSubmodule_inj, range_toSubmodule, LieIdeal.toLieSubalgebra_toSubmodule,
   ker_toSubmodule]
  exact LinearMap.range_inr R L₁ L₂

theorem ker_fst : ker (fst R L₁ L₂) = range (inr R L₁ L₂) :=
  Eq.symm <| range_inr R L₁ L₂

@[simp] theorem fst_comp_inl : (fst R L₁ L₂).comp (inl R L₁ L₂) = id := rfl

@[simp] theorem snd_comp_inl : (snd R L₁ L₂).comp (inl R L₁ L₂) = 0 := rfl

@[simp] theorem fst_comp_inr : (fst R L₁ L₂).comp (inr R L₁ L₂) = 0 := rfl

@[simp] theorem snd_comp_inr : (snd R L₁ L₂).comp (inr R L₁ L₂) = id := rfl

theorem inl_eq_prod : inl R L₁ L₂ = prod LieHom.id 0 :=
  rfl

theorem inr_eq_prod : inr R L₁ L₂ = prod 0 LieHom.id :=
  rfl

theorem prod_ext_iff {f g : L₁ × L₂ →ₗ⁅R⁆ L} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) := by
  simp_rw [LieHom.ext_iff]
  have h := LinearMap.prod_ext_iff (f:=f.toLinearMap) (g:= g.toLinearMap)
  simp_rw [LinearMap.ext_iff] at h
  exact h

/--
Split equality of Lie algebra homomorphisms from a product into Lie algebra homomorphism over
each component, to allow `ext` to apply lemmas specific to `L₁ →ₗ L` and `L₂ →ₗ L`.

See note [partially-applied ext lemmas]. -/
@[ext 1100]
theorem prod_ext {f g : L₁ × L₂ →ₗ⁅R⁆ L} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g := by
  refine (prod_ext_iff R L₁ L₂).mpr ⟨hl,hr⟩

end

/-- `Prod.map` of two Lie algebra homomorphisms. -/
def prodMap (f : L₁ →ₗ⁅R⁆ L₃) (g : L₂ →ₗ⁅R⁆ L₄) : L₁ × L₂ →ₗ⁅R⁆ L₃ × L₄ :=
  (f.comp (fst R L₁ L₂)).prod (g.comp (snd R L₁ L₂))

theorem coe_prodMap (f : L₁ →ₗ⁅R⁆ L₃) (g : L₂ →ₗ⁅R⁆ L₄) : ⇑(prodMap f g) = Prod.map f g :=
  rfl

@[simp]
theorem prodMap_apply (f : L₁ →ₗ⁅R⁆ L₃) (g : L₂ →ₗ⁅R⁆ L₄) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl

@[simp]
theorem prodMap_id : (id : L →ₗ⁅R⁆ L).prodMap (id : L₁ →ₗ⁅R⁆ L₁) = id :=
  rfl

@[simp]
theorem prodMap_one : (1 : L →ₗ⁅R⁆ L).prodMap (1 : L₁ →ₗ⁅R⁆ L₁) = 1 :=
  rfl

theorem prodMap_comp (f₁₂ : L₁ →ₗ⁅R⁆ L₂) (f₂₃ : L₂ →ₗ⁅R⁆ L₃) (g₁₂ : L₄ →ₗ⁅R⁆ L₅)
    (g₂₃ : L₅ →ₗ⁅R⁆ L₆) :
    (f₂₃.prodMap g₂₃).comp (f₁₂.prodMap g₁₂) = (f₂₃.comp f₁₂).prodMap (g₂₃.comp g₁₂) :=
  rfl

@[simp]
theorem prodMap_zero : (0 : L₁ →ₗ⁅R⁆ L₃).prodMap (0 : L₂ →ₗ⁅R⁆ L₄) = 0 :=
  rfl

end LieHom

end
