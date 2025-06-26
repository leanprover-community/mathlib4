/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Group.Graph
import Mathlib.LinearAlgebra.Span.Basic

/-! ### Products of modules

This file defines constructors for linear maps whose domains or codomains are products.

It contains theorems relating these to each other, as well as to `Submodule.prod`, `Submodule.map`,
`Submodule.comap`, `LinearMap.range`, and `LinearMap.ker`.

## Main definitions

- products in the domain:
  - `LinearMap.fst`
  - `LinearMap.snd`
  - `LinearMap.coprod`
  - `LinearMap.prod_ext`
- products in the codomain:
  - `LinearMap.inl`
  - `LinearMap.inr`
  - `LinearMap.prod`
- products in both domain and codomain:
  - `LinearMap.prodMap`
  - `LinearEquiv.prodMap`
  - `LinearEquiv.skewProd`
- product with the trivial module:
  - `LinearEquiv.prodUnique`
  - `LinearEquiv.uniqueProd`
-/


universe u v w x y z u' v' w' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}
variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x}
variable {M₅ M₆ : Type*}

section Prod

namespace LinearMap

variable (S : Type*) [Semiring R] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [AddCommMonoid M₅] [AddCommMonoid M₆]
variable [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]
variable [Module R M₅] [Module R M₆]
variable (f : M →ₗ[R] M₂)

section

variable (R M M₂)

/-- The first projection of a product is a linear map. -/
def fst : M × M₂ →ₗ[R] M where
  toFun := Prod.fst
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

/-- The second projection of a product is a linear map. -/
def snd : M × M₂ →ₗ[R] M₂ where
  toFun := Prod.snd
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

end

@[simp]
theorem fst_apply (x : M × M₂) : fst R M M₂ x = x.1 :=
  rfl

@[simp]
theorem snd_apply (x : M × M₂) : snd R M M₂ x = x.2 :=
  rfl

@[simp, norm_cast] lemma coe_fst : ⇑(fst R M M₂) = Prod.fst := rfl

@[simp, norm_cast] lemma coe_snd : ⇑(snd R M M₂) = Prod.snd := rfl

theorem fst_surjective : Function.Surjective (fst R M M₂) := fun x => ⟨(x, 0), rfl⟩

theorem snd_surjective : Function.Surjective (snd R M M₂) := fun x => ⟨(0, x), rfl⟩

/-- The prod of two linear maps is a linear map. -/
@[simps]
def prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : M →ₗ[R] M₂ × M₃ where
  toFun := Pi.prod f g
  map_add' x y := by simp only [Pi.prod, Prod.mk_add_mk, map_add]
  map_smul' c x := by simp only [Pi.prod, Prod.smul_mk, map_smul, RingHom.id_apply]

theorem coe_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : ⇑(f.prod g) = Pi.prod f g :=
  rfl

@[simp]
theorem fst_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : (fst R M₂ M₃).comp (prod f g) = f := rfl

@[simp]
theorem snd_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : (snd R M₂ M₃).comp (prod f g) = g := rfl

@[simp]
theorem pair_fst_snd : prod (fst R M M₂) (snd R M M₂) = LinearMap.id := rfl

theorem prod_comp (f : M₂ →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄)
    (h : M →ₗ[R] M₂) : (f.prod g).comp h = (f.comp h).prod (g.comp h) :=
  rfl

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
def prodEquiv [Module S M₂] [Module S M₃] [SMulCommClass R S M₂] [SMulCommClass R S M₃] :
    ((M →ₗ[R] M₂) × (M →ₗ[R] M₃)) ≃ₗ[S] M →ₗ[R] M₂ × M₃ where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section

variable (R M M₂)

/-- The left injection into a product is a linear map. -/
def inl : M →ₗ[R] M × M₂ :=
  prod LinearMap.id 0

/-- The right injection into a product is a linear map. -/
def inr : M₂ →ₗ[R] M × M₂ :=
  prod 0 LinearMap.id

theorem range_inl : range (inl R M M₂) = ker (snd R M M₂) := by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    exact ⟨x.fst, Prod.ext rfl h.symm⟩

theorem ker_snd : ker (snd R M M₂) = range (inl R M M₂) :=
  Eq.symm <| range_inl R M M₂

theorem range_inr : range (inr R M M₂) = ker (fst R M M₂) := by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    exact ⟨x.snd, Prod.ext h.symm rfl⟩

theorem ker_fst : ker (fst R M M₂) = range (inr R M M₂) :=
  Eq.symm <| range_inr R M M₂

@[simp] theorem fst_comp_inl : fst R M M₂ ∘ₗ inl R M M₂ = id := rfl

@[simp] theorem snd_comp_inl : snd R M M₂ ∘ₗ inl R M M₂ = 0 := rfl

@[simp] theorem fst_comp_inr : fst R M M₂ ∘ₗ inr R M M₂ = 0 := rfl

@[simp] theorem snd_comp_inr : snd R M M₂ ∘ₗ inr R M M₂ = id := rfl

end

@[simp]
theorem coe_inl : (inl R M M₂ : M → M × M₂) = fun x => (x, 0) :=
  rfl

theorem inl_apply (x : M) : inl R M M₂ x = (x, 0) :=
  rfl

@[simp]
theorem coe_inr : (inr R M M₂ : M₂ → M × M₂) = Prod.mk 0 :=
  rfl

theorem inr_apply (x : M₂) : inr R M M₂ x = (0, x) :=
  rfl

theorem inl_eq_prod : inl R M M₂ = prod LinearMap.id 0 :=
  rfl

theorem inr_eq_prod : inr R M M₂ = prod 0 LinearMap.id :=
  rfl

theorem inl_injective : Function.Injective (inl R M M₂) := fun _ => by simp

theorem inr_injective : Function.Injective (inr R M M₂) := fun _ => by simp

/-- The coprod function `x : M × M₂ ↦ f x.1 + g x.2` is a linear map. -/
def coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : M × M₂ →ₗ[R] M₃ :=
  f.comp (fst _ _ _) + g.comp (snd _ _ _)

@[simp]
theorem coprod_apply (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (x : M × M₂) :
    coprod f g x = f x.1 + g x.2 :=
  rfl

@[simp]
theorem coprod_inl (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : (coprod f g).comp (inl R M M₂) = f := by
  ext; simp only [map_zero, add_zero, coprod_apply, inl_apply, comp_apply]

@[simp]
theorem coprod_inr (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : (coprod f g).comp (inr R M M₂) = g := by
  ext; simp only [map_zero, coprod_apply, inr_apply, zero_add, comp_apply]

@[simp]
theorem coprod_inl_inr : coprod (inl R M M₂) (inr R M M₂) = LinearMap.id := by
  ext <;>
    simp only [Prod.mk_add_mk, add_zero, id_apply, coprod_apply, inl_apply, inr_apply, zero_add]

theorem coprod_zero_left (g : M₂ →ₗ[R] M₃) : (0 : M →ₗ[R] M₃).coprod g = g.comp (snd R M M₂) :=
  zero_add _

theorem coprod_zero_right (f : M →ₗ[R] M₃) : f.coprod (0 : M₂ →ₗ[R] M₃) = f.comp (fst R M M₂) :=
  add_zero _

theorem comp_coprod (f : M₃ →ₗ[R] M₄) (g₁ : M →ₗ[R] M₃) (g₂ : M₂ →ₗ[R] M₃) :
    f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂) :=
  ext fun x => f.map_add (g₁ x.1) (g₂ x.2)

theorem fst_eq_coprod : fst R M M₂ = coprod LinearMap.id 0 := by ext; simp

theorem snd_eq_coprod : snd R M M₂ = coprod 0 LinearMap.id := by ext; simp

@[simp]
theorem coprod_comp_prod (f : M₂ →ₗ[R] M₄) (g : M₃ →ₗ[R] M₄) (f' : M →ₗ[R] M₂) (g' : M →ₗ[R] M₃) :
    (f.coprod g).comp (f'.prod g') = f.comp f' + g.comp g' :=
  rfl

@[simp]
theorem coprod_map_prod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (S : Submodule R M)
    (S' : Submodule R M₂) : (Submodule.prod S S').map (LinearMap.coprod f g) = S.map f ⊔ S'.map g :=
  SetLike.coe_injective <| by
    simp only [LinearMap.coprod_apply, Submodule.coe_sup, Submodule.map_coe]
    rw [← Set.image2_add, Set.image2_image_left, Set.image2_image_right]
    exact Set.image_prod fun m m₂ => f m + g m₂

@[simp]
theorem coprod_comp_inl_inr (f : M × M₂ →ₗ[R] M₃) :
    (f.comp (inl R M M₂)).coprod (f.comp (inr R M M₂)) = f := by
  rw [← comp_coprod, coprod_inl_inr, comp_id]

/-- Taking the product of two maps with the same codomain is equivalent to taking the product of
their domains.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
def coprodEquiv [Module S M₃] [SMulCommClass R S M₃] :
    ((M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃)) ≃ₗ[S] M × M₂ →ₗ[R] M₃ where
  toFun f := f.1.coprod f.2
  invFun f := (f.comp (inl _ _ _), f.comp (inr _ _ _))
  left_inv f := by simp only [coprod_inl, coprod_inr]
  right_inv f := by simp only [← comp_coprod, comp_id, coprod_inl_inr]
  map_add' a b := by
    ext
    simp only [Prod.snd_add, add_apply, coprod_apply, Prod.fst_add, add_add_add_comm]
  map_smul' r a := by
    dsimp
    ext
    simp only [smul_add, smul_apply, Prod.smul_snd, Prod.smul_fst, coprod_apply]

theorem prod_ext_iff {f g : M × M₂ →ₗ[R] M₃} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) :=
  (coprodEquiv ℕ).symm.injective.eq_iff.symm.trans Prod.ext_iff

/--
Split equality of linear maps from a product into linear maps over each component, to allow `ext`
to apply lemmas specific to `M →ₗ M₃` and `M₂ →ₗ M₃`.

See note [partially-applied ext lemmas]. -/
@[ext 1100]
theorem prod_ext {f g : M × M₂ →ₗ[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩

/-- `Prod.map` of two linear maps. -/
def prodMap (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) : M × M₂ →ₗ[R] M₃ × M₄ :=
  (f.comp (fst R M M₂)).prod (g.comp (snd R M M₂))

theorem coe_prodMap (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) : ⇑(f.prodMap g) = Prod.map f g :=
  rfl

@[simp]
theorem prodMap_apply (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl

theorem prodMap_comap_prod (f : M →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄) (S : Submodule R M₂)
    (S' : Submodule R M₄) :
    (Submodule.prod S S').comap (LinearMap.prodMap f g) = (S.comap f).prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _

theorem ker_prodMap (f : M →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄) :
    ker (LinearMap.prodMap f g) = Submodule.prod (ker f) (ker g) := by
  dsimp only [ker]
  rw [← prodMap_comap_prod, Submodule.prod_bot]

@[simp]
theorem prodMap_id : (id : M →ₗ[R] M).prodMap (id : M₂ →ₗ[R] M₂) = id :=
  rfl

@[simp]
theorem prodMap_one : (1 : M →ₗ[R] M).prodMap (1 : M₂ →ₗ[R] M₂) = 1 :=
  rfl

theorem prodMap_comp (f₁₂ : M →ₗ[R] M₂) (f₂₃ : M₂ →ₗ[R] M₃) (g₁₂ : M₄ →ₗ[R] M₅)
    (g₂₃ : M₅ →ₗ[R] M₆) :
    f₂₃.prodMap g₂₃ ∘ₗ f₁₂.prodMap g₁₂ = (f₂₃ ∘ₗ f₁₂).prodMap (g₂₃ ∘ₗ g₁₂) :=
  rfl

theorem prodMap_mul (f₁₂ : M →ₗ[R] M) (f₂₃ : M →ₗ[R] M) (g₁₂ : M₂ →ₗ[R] M₂) (g₂₃ : M₂ →ₗ[R] M₂) :
    f₂₃.prodMap g₂₃ * f₁₂.prodMap g₁₂ = (f₂₃ * f₁₂).prodMap (g₂₃ * g₁₂) :=
  rfl

theorem prodMap_add (f₁ : M →ₗ[R] M₃) (f₂ : M →ₗ[R] M₃) (g₁ : M₂ →ₗ[R] M₄) (g₂ : M₂ →ₗ[R] M₄) :
    (f₁ + f₂).prodMap (g₁ + g₂) = f₁.prodMap g₁ + f₂.prodMap g₂ :=
  rfl

@[simp]
theorem prodMap_zero : (0 : M →ₗ[R] M₂).prodMap (0 : M₃ →ₗ[R] M₄) = 0 :=
  rfl

@[simp]
theorem prodMap_smul [DistribMulAction S M₃] [DistribMulAction S M₄] [SMulCommClass R S M₃]
    [SMulCommClass R S M₄] (s : S) (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) :
    prodMap (s • f) (s • g) = s • prodMap f g :=
  rfl

variable (R M M₂ M₃ M₄)

/-- `LinearMap.prodMap` as a `LinearMap` -/
@[simps]
def prodMapLinear [Module S M₃] [Module S M₄] [SMulCommClass R S M₃] [SMulCommClass R S M₄] :
    (M →ₗ[R] M₃) × (M₂ →ₗ[R] M₄) →ₗ[S] M × M₂ →ₗ[R] M₃ × M₄ where
  toFun f := prodMap f.1 f.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `LinearMap.prodMap` as a `RingHom` -/
@[simps]
def prodMapRingHom : (M →ₗ[R] M) × (M₂ →ₗ[R] M₂) →+* M × M₂ →ₗ[R] M × M₂ where
  toFun f := prodMap f.1 f.2
  map_one' := prodMap_one
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

variable {R M M₂ M₃ M₄}

section map_mul

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
variable {B : Type*} [NonUnitalNonAssocSemiring B] [Module R B]

theorem inl_map_mul (a₁ a₂ : A) :
    LinearMap.inl R A B (a₁ * a₂) = LinearMap.inl R A B a₁ * LinearMap.inl R A B a₂ :=
  Prod.ext rfl (by simp)

theorem inr_map_mul (b₁ b₂ : B) :
    LinearMap.inr R A B (b₁ * b₂) = LinearMap.inr R A B b₁ * LinearMap.inr R A B b₂ :=
  Prod.ext (by simp) rfl

end map_mul

end LinearMap

end Prod

namespace LinearMap

variable (R M M₂)
variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]

/-- `LinearMap.prodMap` as an `AlgHom` -/
@[simps!]
def prodMapAlgHom : Module.End R M × Module.End R M₂ →ₐ[R] Module.End R (M × M₂) :=
  { prodMapRingHom R M M₂ with commutes' := fun _ => rfl }

end LinearMap

namespace LinearMap

open Submodule

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

theorem range_coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : range (f.coprod g) = range f ⊔ range g :=
  Submodule.ext fun x => by simp [mem_sup]

theorem isCompl_range_inl_inr : IsCompl (range <| inl R M M₂) (range <| inr R M M₂) := by
  constructor
  · rw [disjoint_def]
    rintro ⟨_, _⟩ ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Prod.ext_iff, inl_apply, inr_apply, mem_bot] at hx hy ⊢
    exact ⟨hy.1.symm, hx.2.symm⟩
  · rw [codisjoint_iff_le_sup]
    rintro ⟨x, y⟩ -
    simp only [mem_sup, mem_range, exists_prop]
    refine ⟨(x, 0), ⟨x, rfl⟩, (0, y), ⟨y, rfl⟩, ?_⟩
    simp

theorem sup_range_inl_inr : (range <| inl R M M₂) ⊔ (range <| inr R M M₂) = ⊤ :=
  IsCompl.sup_eq_top isCompl_range_inl_inr

theorem disjoint_inl_inr : Disjoint (range <| inl R M M₂) (range <| inr R M M₂) := by
  simp +contextual [disjoint_def, @eq_comm M 0, @eq_comm M₂ 0]

theorem map_coprod_prod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (p : Submodule R M)
    (q : Submodule R M₂) : map (coprod f g) (p.prod q) = map f p ⊔ map g q := by
  refine le_antisymm ?_ (sup_le (map_le_iff_le_comap.2 ?_) (map_le_iff_le_comap.2 ?_))
  · rw [SetLike.le_def]
    rintro _ ⟨x, ⟨h₁, h₂⟩, rfl⟩
    exact mem_sup.2 ⟨_, ⟨_, h₁, rfl⟩, _, ⟨_, h₂, rfl⟩, rfl⟩
  · exact fun x hx => ⟨(x, 0), by simp [hx]⟩
  · exact fun x hx => ⟨(0, x), by simp [hx]⟩

theorem comap_prod_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) (p : Submodule R M₂)
    (q : Submodule R M₃) : comap (prod f g) (p.prod q) = comap f p ⊓ comap g q :=
  Submodule.ext fun _x => Iff.rfl

theorem prod_eq_inf_comap (p : Submodule R M) (q : Submodule R M₂) :
    p.prod q = p.comap (LinearMap.fst R M M₂) ⊓ q.comap (LinearMap.snd R M M₂) :=
  Submodule.ext fun _x => Iff.rfl

theorem prod_eq_sup_map (p : Submodule R M) (q : Submodule R M₂) :
    p.prod q = p.map (LinearMap.inl R M M₂) ⊔ q.map (LinearMap.inr R M M₂) := by
  rw [← map_coprod_prod, coprod_inl_inr, map_id]

theorem span_inl_union_inr {s : Set M} {t : Set M₂} :
    span R (inl R M M₂ '' s ∪ inr R M M₂ '' t) = (span R s).prod (span R t) := by
  rw [span_union, prod_eq_sup_map, ← span_image, ← span_image]

@[simp]
theorem ker_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : ker (prod f g) = ker f ⊓ ker g := by
  rw [ker, ← prod_bot, comap_prod_prod]; rfl

theorem range_prod_le (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
    range (prod f g) ≤ (range f).prod (range g) := by
  simp only [SetLike.le_def, prod_apply, mem_range, SetLike.mem_coe, mem_prod, exists_imp]
  rintro _ x rfl
  exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩

theorem ker_prod_ker_le_ker_coprod {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] {M₃ : Type*}
    [AddCommMonoid M₃] [Module R M₃] (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
    (ker f).prod (ker g) ≤ ker (f.coprod g) := by
  rintro ⟨y, z⟩
  simp +contextual

theorem ker_coprod_of_disjoint_range {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] {M₃ : Type*}
    [AddCommGroup M₃] [Module R M₃] (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃)
    (hd : Disjoint (range f) (range g)) : ker (f.coprod g) = (ker f).prod (ker g) := by
  apply le_antisymm _ (ker_prod_ker_le_ker_coprod f g)
  rintro ⟨y, z⟩ h
  simp only [mem_ker, mem_prod, coprod_apply] at h ⊢
  have : f y ∈ (range f) ⊓ (range g) := by
    simp only [true_and, mem_range, mem_inf, exists_apply_eq_apply]
    use -z
    rwa [eq_comm, map_neg, ← sub_eq_zero, sub_neg_eq_add]
  rw [hd.eq_bot, mem_bot] at this
  rw [this] at h
  simpa [this] using h

end LinearMap

namespace Submodule

open LinearMap

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]

theorem sup_eq_range (p q : Submodule R M) : p ⊔ q = range (p.subtype.coprod q.subtype) :=
  Submodule.ext fun x => by simp [Submodule.mem_sup, SetLike.exists]

variable (p : Submodule R M) (q : Submodule R M₂)

@[simp]
theorem map_inl : p.map (inl R M M₂) = prod p ⊥ := by
  ext ⟨x, y⟩
  simp only [and_left_comm, eq_comm, mem_map, Prod.mk_inj, inl_apply, mem_bot, exists_eq_left',
    mem_prod]

@[simp]
theorem map_inr : q.map (inr R M M₂) = prod ⊥ q := by
  ext ⟨x, y⟩; simp [and_left_comm, eq_comm, and_comm]

@[simp]
theorem comap_fst : p.comap (fst R M M₂) = prod p ⊤ := by ext ⟨x, y⟩; simp

@[simp]
theorem comap_snd : q.comap (snd R M M₂) = prod ⊤ q := by ext ⟨x, y⟩; simp

@[simp]
theorem prod_comap_inl : (prod p q).comap (inl R M M₂) = p := by ext; simp

@[simp]
theorem prod_comap_inr : (prod p q).comap (inr R M M₂) = q := by ext; simp

@[simp]
theorem prod_map_fst : (prod p q).map (fst R M M₂) = p := by
  ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ q)]

@[simp]
theorem prod_map_snd : (prod p q).map (snd R M M₂) = q := by
  ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ p)]

@[simp]
theorem ker_inl : ker (inl R M M₂) = ⊥ := by rw [ker, ← prod_bot, prod_comap_inl]

@[simp]
theorem ker_inr : ker (inr R M M₂) = ⊥ := by rw [ker, ← prod_bot, prod_comap_inr]

@[simp]
theorem range_fst : range (fst R M M₂) = ⊤ := by rw [range_eq_map, ← prod_top, prod_map_fst]

@[simp]
theorem range_snd : range (snd R M M₂) = ⊤ := by rw [range_eq_map, ← prod_top, prod_map_snd]

variable (R M M₂)

/-- `M` as a submodule of `M × N`. -/
def fst : Submodule R (M × M₂) :=
  (⊥ : Submodule R M₂).comap (LinearMap.snd R M M₂)

/-- `M` as a submodule of `M × N` is isomorphic to `M`. -/
@[simps]
def fstEquiv : Submodule.fst R M M₂ ≃ₗ[R] M where
  -- Porting note: proofs were `tidy` or `simp`
  toFun x := x.1.1
  invFun m := ⟨⟨m, 0⟩, by simp [fst]⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv := by
    rintro ⟨⟨x, y⟩, hy⟩
    simp only [fst, comap_bot, mem_ker, snd_apply] at hy
    simpa only [Subtype.mk.injEq, Prod.mk.injEq, true_and] using hy.symm
  right_inv := by rintro x; rfl

theorem fst_map_fst : (Submodule.fst R M M₂).map (LinearMap.fst R M M₂) = ⊤ := by
  aesop

theorem fst_map_snd : (Submodule.fst R M M₂).map (LinearMap.snd R M M₂) = ⊥ := by
  aesop (add simp fst)

/-- `N` as a submodule of `M × N`. -/
def snd : Submodule R (M × M₂) :=
  (⊥ : Submodule R M).comap (LinearMap.fst R M M₂)

/-- `N` as a submodule of `M × N` is isomorphic to `N`. -/
@[simps]
def sndEquiv : Submodule.snd R M M₂ ≃ₗ[R] M₂ where
  -- Porting note: proofs were `tidy` or `simp`
  toFun x := x.1.2
  invFun n := ⟨⟨0, n⟩, by simp [snd]⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv := by
    rintro ⟨⟨x, y⟩, hx⟩
    simp only [snd, comap_bot, mem_ker, fst_apply] at hx
    simpa only [Subtype.mk.injEq, Prod.mk.injEq, and_true] using hx.symm

theorem snd_map_fst : (Submodule.snd R M M₂).map (LinearMap.fst R M M₂) = ⊥ := by
  aesop (add simp snd)

theorem snd_map_snd : (Submodule.snd R M M₂).map (LinearMap.snd R M M₂) = ⊤ := by
  aesop

theorem fst_sup_snd : Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂ = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨m, n⟩ -
  rw [show (m, n) = (m, 0) + (0, n) by simp]
  apply Submodule.add_mem (Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂)
  · exact Submodule.mem_sup_left (Submodule.mem_comap.mpr (by simp))
  · exact Submodule.mem_sup_right (Submodule.mem_comap.mpr (by simp))

theorem fst_inf_snd : Submodule.fst R M M₂ ⊓ Submodule.snd R M M₂ = ⊥ := by
  aesop

theorem le_prod_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M × M₂)} :
    q ≤ p₁.prod p₂ ↔ map (LinearMap.fst R M M₂) q ≤ p₁ ∧ map (LinearMap.snd R M M₂) q ≤ p₂ := by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩

theorem prod_le_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M × M₂)} :
    p₁.prod p₂ ≤ q ↔ map (LinearMap.inl R M M₂) p₁ ≤ q ∧ map (LinearMap.inr R M M₂) p₂ ≤ q := by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, zero_mem p₂⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨zero_mem p₁, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : (LinearMap.inl R _ _) x1 ∈ q := by
      apply hH
      simpa using h1
    have h2' : (LinearMap.inr R _ _) x2 ∈ q := by
      apply hK
      simpa using h2
    simpa using add_mem h1' h2'

theorem prod_eq_bot_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} :
    p₁.prod p₂ = ⊥ ↔ p₁ = ⊥ ∧ p₂ = ⊥ := by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot, ker_inl, ker_inr]

theorem prod_eq_top_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} :
    p₁.prod p₂ = ⊤ ↔ p₁ = ⊤ ∧ p₂ = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, ← (gc_map_comap _).le_iff_le, map_top, range_fst, range_snd]

end Submodule

namespace LinearEquiv

/-- Product of modules is commutative up to linear isomorphism. -/
@[simps apply]
def prodComm (R M N : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
    [Module R N] : (M × N) ≃ₗ[R] N × M :=
  { AddEquiv.prodComm with
    toFun := Prod.swap
    map_smul' := fun _r ⟨_m, _n⟩ => rfl }

section prodComm

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]

theorem fst_comp_prodComm :
    (LinearMap.fst R M₂ M).comp (prodComm R M M₂).toLinearMap = (LinearMap.snd R M M₂) := by
  ext <;> simp

theorem snd_comp_prodComm :
    (LinearMap.snd R M₂ M).comp (prodComm R M M₂).toLinearMap = (LinearMap.fst R M M₂) := by
  ext <;> simp

end prodComm

/-- Product of modules is associative up to linear isomorphism. -/
@[simps apply]
def prodAssoc (R M₁ M₂ M₃ : Type*) [Semiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [Module R M₁] [Module R M₂] [Module R M₃] : ((M₁ × M₂) × M₃) ≃ₗ[R] (M₁ × (M₂ × M₃)) :=
  { AddEquiv.prodAssoc with
    map_smul' := fun _r ⟨_m, _n⟩ => rfl }

section prodAssoc

variable {M₁ : Type*}
variable [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃]

theorem fst_comp_prodAssoc :
    (LinearMap.fst R M₁ (M₂ × M₃)).comp (prodAssoc R M₁ M₂ M₃).toLinearMap =
    (LinearMap.fst R M₁ M₂).comp (LinearMap.fst R (M₁ × M₂) M₃) := by
  ext <;> simp

theorem snd_comp_prodAssoc :
    (LinearMap.snd R M₁ (M₂ × M₃)).comp (prodAssoc R M₁ M₂ M₃).toLinearMap =
    (LinearMap.snd R M₁ M₂).prodMap (LinearMap.id : M₃ →ₗ[R] M₃):= by
  ext <;> simp

end prodAssoc

section

variable (R M M₂ M₃ M₄)
variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

/-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
@[simps apply]
def prodProdProdComm : ((M × M₂) × M₃ × M₄) ≃ₗ[R] (M × M₃) × M₂ × M₄ :=
  { AddEquiv.prodProdProdComm M M₂ M₃ M₄ with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_smul' := fun _c _mnmn => rfl }

@[simp]
theorem prodProdProdComm_symm :
    (prodProdProdComm R M M₂ M₃ M₄).symm = prodProdProdComm R M M₃ M₂ M₄ :=
  rfl

@[simp]
theorem prodProdProdComm_toAddEquiv :
    (prodProdProdComm R M M₂ M₃ M₄ : _ ≃+ _) = AddEquiv.prodProdProdComm M M₂ M₃ M₄ :=
  rfl

end

section

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable {module_M : Module R M} {module_M₂ : Module R M₂}
variable {module_M₃ : Module R M₃} {module_M₄ : Module R M₄}
variable (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

/-- Product of linear equivalences; the maps come from `Equiv.prodCongr`. -/
protected def prodCongr : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
  { e₁.toAddEquiv.prodCongr e₂.toAddEquiv with
    map_smul' := fun c _x => Prod.ext (e₁.map_smulₛₗ c _) (e₂.map_smulₛₗ c _) }

@[deprecated (since := "2025-04-17")] alias prod := LinearEquiv.prodCongr

theorem prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm :=
  rfl

@[deprecated (since := "2025-04-17")] alias prod_symm := prodCongr_symm

@[simp]
theorem prodCongr_apply (p) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) :=
  rfl

@[deprecated (since := "2025-04-17")] alias prod_apply := prodCongr_apply

@[simp, norm_cast]
theorem coe_prodCongr :
    (e₁.prodCongr e₂ : M × M₃ →ₗ[R] M₂ × M₄) = (e₁ : M →ₗ[R] M₂).prodMap (e₂ : M₃ →ₗ[R] M₄) :=
  rfl

@[deprecated (since := "2025-04-17")] alias coe_prod := coe_prodCongr

end

section

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommGroup M₄]
variable {module_M : Module R M} {module_M₂ : Module R M₂}
variable {module_M₃ : Module R M₃} {module_M₄ : Module R M₄}
variable (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

/-- Equivalence given by a block lower diagonal matrix. `e₁` and `e₂` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
protected def skewProd (f : M →ₗ[R] M₄) : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
  { ((e₁ : M →ₗ[R] M₂).comp (LinearMap.fst R M M₃)).prod
      ((e₂ : M₃ →ₗ[R] M₄).comp (LinearMap.snd R M M₃) +
        f.comp (LinearMap.fst R M M₃)) with
    invFun := fun p : M₂ × M₄ => (e₁.symm p.1, e₂.symm (p.2 - f (e₁.symm p.1)))
    left_inv := fun p => by simp
    right_inv := fun p => by simp }

@[simp]
theorem skewProd_apply (f : M →ₗ[R] M₄) (x) : e₁.skewProd e₂ f x = (e₁ x.1, e₂ x.2 + f x.1) :=
  rfl

@[simp]
theorem skewProd_symm_apply (f : M →ₗ[R] M₄) (x) :
    (e₁.skewProd e₂ f).symm x = (e₁.symm x.1, e₂.symm (x.2 - f (e₁.symm x.1))) :=
  rfl

end

section Unique

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂] [Unique M₂]

/-- Multiplying by the trivial module from the left does not change the structure.
This is the `LinearEquiv` version of `AddEquiv.uniqueProd`. -/
@[simps!]
def uniqueProd : (M₂ × M) ≃ₗ[R] M :=
  AddEquiv.uniqueProd.toLinearEquiv (by simp [AddEquiv.uniqueProd])

lemma coe_uniqueProd :
  (uniqueProd (R := R) (M := M) (M₂ := M₂) : (M₂ × M) ≃ M) = Equiv.uniqueProd M M₂ := rfl

/-- Multiplying by the trivial module from the right does not change the structure.
This is the `LinearEquiv` version of `AddEquiv.prodUnique`. -/
@[simps!]
def prodUnique : (M × M₂) ≃ₗ[R] M :=
  AddEquiv.prodUnique.toLinearEquiv (by simp [AddEquiv.prodUnique])

lemma coe_prodUnique :
  (prodUnique (R := R) (M := M) (M₂ := M₂) : (M × M₂) ≃ M) = Equiv.prodUnique M M₂ := rfl

end Unique

end LinearEquiv

namespace LinearMap

open Submodule

variable [Ring R]
variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

/-- If the union of the kernels `ker f` and `ker g` spans the domain, then the range of
`Prod f g` is equal to the product of `range f` and `range g`. -/
theorem range_prod_eq {f : M →ₗ[R] M₂} {g : M →ₗ[R] M₃} (h : ker f ⊔ ker g = ⊤) :
    range (prod f g) = (range f).prod (range g) := by
  refine le_antisymm (f.range_prod_le g) ?_
  simp only [SetLike.le_def, prod_apply, mem_range, SetLike.mem_coe, mem_prod, exists_imp, and_imp,
    Prod.forall, Pi.prod]
  rintro _ _ x rfl y rfl
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify `(f := f)`
  simp only [Prod.mk_inj, ← sub_mem_ker_iff (f := f)]
  have : y - x ∈ ker f ⊔ ker g := by simp only [h, mem_top]
  rcases mem_sup.1 this with ⟨x', hx', y', hy', H⟩
  refine ⟨x' + x, ?_, ?_⟩
  · rwa [add_sub_cancel_right]
  · simp [← eq_sub_iff_add_eq.1 H, map_add, add_left_inj, left_eq_add, mem_ker.mp hy']

end LinearMap

namespace LinearMap

/-!
## Tunnels and tailings

NOTE: The proof of strong rank condition for noetherian rings is changed.
`LinearMap.tunnel` and `LinearMap.tailing` are not used in mathlib anymore.
These are marked as deprecated with no replacements.
If you use them in external projects, please consider using other arguments instead.

Some preliminary work for establishing the strong rank condition for noetherian rings.

Given a morphism `f : M × N →ₗ[R] M` which is `i : Injective f`,
we can find an infinite decreasing `tunnel f i n` of copies of `M` inside `M`,
and sitting beside these, an infinite sequence of copies of `N`.

We picturesquely name these as `tailing f i n` for each individual copy of `N`,
and `tailings f i n` for the supremum of the first `n+1` copies:
they are the pieces left behind, sitting inside the tunnel.

By construction, each `tailing f i (n+1)` is disjoint from `tailings f i n`;
later, when we assume `M` is noetherian, this implies that `N` must be trivial,
and establishes the strong rank condition for any left-noetherian ring.
-/

section Graph

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommGroup M₃] [AddCommGroup M₄]
  [Module R M] [Module R M₂] [Module R M₃] [Module R M₄] (f : M →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄)

/-- Graph of a linear map. -/
def graph : Submodule R (M × M₂) where
  carrier := { p | p.2 = f p.1 }
  add_mem' (ha : _ = _) (hb : _ = _) := by
    change _ + _ = f (_ + _)
    rw [map_add, ha, hb]
  zero_mem' := Eq.symm (map_zero f)
  smul_mem' c x (hx : _ = _) := by
    change _ • _ = f (_ • _)
    rw [map_smul, hx]

@[simp]
theorem mem_graph_iff (x : M × M₂) : x ∈ f.graph ↔ x.2 = f x.1 :=
  Iff.rfl

theorem graph_eq_ker_coprod : g.graph = ker ((-g).coprod LinearMap.id) := by
  ext x
  change _ = _ ↔ -g x.1 + x.2 = _
  rw [add_comm, add_neg_eq_zero]

theorem graph_eq_range_prod : f.graph = range (LinearMap.id.prod f) := by
  ext x
  exact ⟨fun hx => ⟨x.1, Prod.ext rfl hx.symm⟩, fun ⟨u, hu⟩ => hu ▸ rfl⟩

end Graph

end LinearMap

section LineTest

open Set Function

variable {R S G H I : Type*}
  [Semiring R] [Semiring S] {σ : R →+* S} [RingHomSurjective σ]
  [AddCommMonoid G] [Module R G]
  [AddCommMonoid H] [Module S H]
  [AddCommMonoid I] [Module S I]

/-- **Vertical line test** for linear maps.

Let `f : G → H × I` be a linear (or semilinear) map to a product. Assume that `f` is surjective on
the first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at
most once. Then the image of `f` is the graph of some linear map `f' : H → I`. -/
lemma LinearMap.exists_range_eq_graph {f : G →ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
    ∃ f' : H →ₗ[S] I, LinearMap.range f = LinearMap.graph f' := by
  obtain ⟨f', hf'⟩ :=
    AddMonoidHom.exists_mrange_eq_mgraph (G := G) (H := H) (I := I) (f := f) hf₁ hf
  simp only [SetLike.ext_iff, AddMonoidHom.mem_mrange, AddMonoidHom.coe_coe,
    AddMonoidHom.mem_mgraph] at hf'
  use
  { toFun := f'.toFun
    map_add' := f'.map_add'
    map_smul' := by
      intro s h
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
      refine (hf' (s • h, _)).mp ?_
      rw [← Prod.smul_mk, ← LinearMap.mem_range]
      apply Submodule.smul_mem
      rw [LinearMap.mem_range, hf'] }
  ext x
  simpa only [mem_range, Eq.comm, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mem_graph_iff,
    coe_mk, AddHom.coe_mk, AddMonoidHom.coe_coe, Set.mem_range] using hf' x

/-- **Vertical line test** for linear maps.

Let `G ≤ H × I` be a submodule of a product of modules. Assume that `G` maps bijectively to the
first factor. Then `G` is the graph of some linear map `f : H →ₗ[R] I`. -/
lemma Submodule.exists_eq_graph {G : Submodule S (H × I)} (hf₁ : Bijective (Prod.fst ∘ G.subtype)) :
    ∃ f : H →ₗ[S] I, G = LinearMap.graph f := by
  simpa only [range_subtype] using LinearMap.exists_range_eq_graph hf₁.surjective
      (fun a b h ↦ congr_arg (Prod.snd ∘ G.subtype) (hf₁.injective h))

/-- **Line test** for module isomorphisms.

Let `f : G → H × I` be a linear (or semilinear) map to a product of modules. Assume that `f` is
surjective onto both factors and that the image of `f` intersects every "vertical line"
`{(h, i) | i : I}` and every "horizontal line" `{(h, i) | h : H}` at most once. Then the image of
`f` is the graph of some module isomorphism `f' : H ≃ I`. -/
lemma LinearMap.exists_linearEquiv_eq_graph {f : G →ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    ∃ e : H ≃ₗ[S] I, range f = e.toLinearMap.graph := by
  obtain ⟨e₁, he₁⟩ := f.exists_range_eq_graph hf₁ fun _ _ ↦ (hf _ _).1
  obtain ⟨e₂, he₂⟩ := ((LinearEquiv.prodComm _ _ _).toLinearMap.comp f).exists_range_eq_graph
    (by simpa) <| by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    simp only [SetLike.ext_iff, LinearMap.mem_graph_iff] at he₁ he₂
    rw [Eq.comm, ← he₁ (h, i), Eq.comm, ← he₂ (i, h)]
    simp only [mem_range, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.prodComm_apply, Prod.swap_eq_iff_eq_swap, Prod.swap_prod_mk]
  exact ⟨
  { toFun := e₁
    map_smul' := e₁.map_smul'
    map_add' := e₁.map_add'
    invFun := e₂
    left_inv := fun h ↦ by rw [← he₁₂]
    right_inv := fun i ↦ by rw [he₁₂] }, he₁⟩

/-- **Goursat's lemma** for module isomorphisms.

Let `G ≤ H × I` be a submodule of a product of modules. Assume that the natural maps from `G` to
both factors are bijective. Then `G` is the graph of some module isomorphism `f : H ≃ I`. -/
lemma Submodule.exists_equiv_eq_graph {G : Submodule S (H × I)}
    (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) :
    ∃ e : H ≃ₗ[S] I, G = e.toLinearMap.graph := by
  simpa only [range_subtype] using LinearMap.exists_linearEquiv_eq_graph
    hG₁.surjective hG₂.surjective fun _ _ ↦ hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

end LineTest
