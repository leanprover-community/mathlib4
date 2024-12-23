/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# Continuous linear maps on products and Pi types
-/

assert_not_exists Star.star

open LinearMap (ker range)
open Topology Filter Pointwise

universe u v w u'

namespace ContinuousLinearMap

section Semiring

/-!
### Properties that hold for non-necessarily commutative semirings.
-/

variable
  {R : Type*} [Semiring R]
  {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R M₄]

/-- The cartesian product of two bounded linear maps, as a bounded linear map. -/
protected def prod (f₁ : M₁ →L[R] M₂) (f₂ : M₁ →L[R] M₃) :
    M₁ →L[R] M₂ × M₃ :=
  ⟨(f₁ : M₁ →ₗ[R] M₂).prod f₂, f₁.2.prod_mk f₂.2⟩

@[simp, norm_cast]
theorem coe_prod (f₁ : M₁ →L[R] M₂) (f₂ : M₁ →L[R] M₃) :
    (f₁.prod f₂ : M₁ →ₗ[R] M₂ × M₃) = LinearMap.prod f₁ f₂ :=
  rfl

@[simp, norm_cast]
theorem prod_apply (f₁ : M₁ →L[R] M₂) (f₂ : M₁ →L[R] M₃) (x : M₁) :
    f₁.prod f₂ x = (f₁ x, f₂ x) :=
  rfl

section

variable (R M₁ M₂)

/-- The left injection into a product is a continuous linear map. -/
def inl : M₁ →L[R] M₁ × M₂ :=
  (id R M₁).prod 0

/-- The right injection into a product is a continuous linear map. -/
def inr : M₂ →L[R] M₁ × M₂ :=
  (0 : M₂ →L[R] M₁).prod (id R M₂)

end

@[simp]
theorem inl_apply (x : M₁) : inl R M₁ M₂ x = (x, 0) :=
  rfl

@[simp]
theorem inr_apply (x : M₂) : inr R M₁ M₂ x = (0, x) :=
  rfl

@[simp, norm_cast]
theorem coe_inl : (inl R M₁ M₂ : M₁ →ₗ[R] M₁ × M₂) = LinearMap.inl R M₁ M₂ :=
  rfl

@[simp, norm_cast]
theorem coe_inr : (inr R M₁ M₂ : M₂ →ₗ[R] M₁ × M₂) = LinearMap.inr R M₁ M₂ :=
  rfl

@[simp]
theorem ker_prod (f : M₁ →L[R] M₂) (g : M₁ →L[R] M₃) :
    ker (f.prod g) = ker f ⊓ ker g :=
  LinearMap.ker_prod (f : M₁ →ₗ[R] M₂) (g : M₁ →ₗ[R] M₃)

variable (R M₁ M₂)

/-- `Prod.fst` as a `ContinuousLinearMap`. -/
def fst : M₁ × M₂ →L[R] M₁ where
  cont := continuous_fst
  toLinearMap := LinearMap.fst R M₁ M₂

/-- `Prod.snd` as a `ContinuousLinearMap`. -/
def snd : M₁ × M₂ →L[R] M₂ where
  cont := continuous_snd
  toLinearMap := LinearMap.snd R M₁ M₂

variable {R M₁ M₂}

@[simp, norm_cast]
theorem coe_fst : ↑(fst R M₁ M₂) = LinearMap.fst R M₁ M₂ :=
  rfl

@[simp, norm_cast]
theorem coe_fst' : ⇑(fst R M₁ M₂) = Prod.fst :=
  rfl

@[simp, norm_cast]
theorem coe_snd : ↑(snd R M₁ M₂) = LinearMap.snd R M₁ M₂ :=
  rfl

@[simp, norm_cast]
theorem coe_snd' : ⇑(snd R M₁ M₂) = Prod.snd :=
  rfl

@[simp]
theorem fst_prod_snd : (fst R M₁ M₂).prod (snd R M₁ M₂) = id R (M₁ × M₂) :=
  ext fun ⟨_x, _y⟩ => rfl

@[simp]
theorem fst_comp_prod (f : M₁ →L[R] M₂) (g : M₁ →L[R] M₃) :
    (fst R M₂ M₃).comp (f.prod g) = f :=
  ext fun _x => rfl

@[simp]
theorem snd_comp_prod (f : M₁ →L[R] M₂) (g : M₁ →L[R] M₃) :
    (snd R M₂ M₃).comp (f.prod g) = g :=
  ext fun _x => rfl

/-- `Prod.map` of two continuous linear maps. -/
def prodMap (f₁ : M₁ →L[R] M₂) (f₂ : M₃ →L[R] M₄) :
    M₁ × M₃ →L[R] M₂ × M₄ :=
  (f₁.comp (fst R M₁ M₃)).prod (f₂.comp (snd R M₁ M₃))

@[simp, norm_cast]
theorem coe_prodMap (f₁ : M₁ →L[R] M₂)
    (f₂ : M₃ →L[R] M₄) : ↑(f₁.prodMap f₂) = (f₁ : M₁ →ₗ[R] M₂).prodMap (f₂ : M₃ →ₗ[R] M₄) :=
  rfl

@[simp, norm_cast]
theorem coe_prodMap' (f₁ : M₁ →L[R] M₂)
    (f₂ : M₃ →L[R] M₄) : ⇑(f₁.prodMap f₂) = Prod.map f₁ f₂ :=
  rfl

/-- The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`. -/
def coprod [ContinuousAdd M₃] (f₁ : M₁ →L[R] M₃)
    (f₂ : M₂ →L[R] M₃) : M₁ × M₂ →L[R] M₃ :=
  ⟨LinearMap.coprod f₁ f₂, (f₁.cont.comp continuous_fst).add (f₂.cont.comp continuous_snd)⟩

@[norm_cast, simp]
theorem coe_coprod [ContinuousAdd M₃] (f₁ : M₁ →L[R] M₃)
    (f₂ : M₂ →L[R] M₃) : (f₁.coprod f₂ : M₁ × M₂ →ₗ[R] M₃) = LinearMap.coprod f₁ f₂ :=
  rfl

@[simp]
theorem coprod_apply [ContinuousAdd M₃] (f₁ : M₁ →L[R] M₃)
    (f₂ : M₂ →L[R] M₃) (x) : f₁.coprod f₂ x = f₁ x.1 + f₂ x.2 :=
  rfl

theorem range_coprod [ContinuousAdd M₃] (f₁ : M₁ →L[R] M₃)
    (f₂ : M₂ →L[R] M₃) : range (f₁.coprod f₂) = range f₁ ⊔ range f₂ :=
  LinearMap.range_coprod _ _

theorem comp_fst_add_comp_snd [ContinuousAdd M₃] (f : M₁ →L[R] M₃)
    (g : M₂ →L[R] M₃) :
    f.comp (ContinuousLinearMap.fst R M₁ M₂) + g.comp (ContinuousLinearMap.snd R M₁ M₂) =
      f.coprod g :=
  rfl

theorem coprod_inl_inr [ContinuousAdd M₁] [ContinuousAdd M₂] :
    (ContinuousLinearMap.inl R M₁ M₂).coprod (ContinuousLinearMap.inr R M₁ M₂) =
      ContinuousLinearMap.id R (M₁ × M₂) := by
  apply coe_injective; apply LinearMap.coprod_inl_inr

end Semiring

section Pi

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] {ι : Type*} {φ : ι → Type*}
  [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

/-- `pi` construction for continuous linear functions. From a family of continuous linear functions
it produces a continuous linear function into a family of topological modules. -/
def pi (f : ∀ i, M →L[R] φ i) : M →L[R] ∀ i, φ i :=
  ⟨LinearMap.pi fun i => f i, continuous_pi fun i => (f i).continuous⟩

@[simp]
theorem coe_pi' (f : ∀ i, M →L[R] φ i) : ⇑(pi f) = fun c i => f i c :=
  rfl

@[simp]
theorem coe_pi (f : ∀ i, M →L[R] φ i) : (pi f : M →ₗ[R] ∀ i, φ i) = LinearMap.pi fun i => f i :=
  rfl

theorem pi_apply (f : ∀ i, M →L[R] φ i) (c : M) (i : ι) : pi f c i = f i c :=
  rfl

theorem pi_eq_zero (f : ∀ i, M →L[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [ContinuousLinearMap.ext_iff, pi_apply, funext_iff]
  exact forall_swap

theorem pi_zero : pi (fun _ => 0 : ∀ i, M →L[R] φ i) = 0 :=
  ext fun _ => rfl

theorem pi_comp (f : ∀ i, M →L[R] φ i) (g : M₂ →L[R] M) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/-- The projections from a family of topological modules are continuous linear maps. -/
def proj (i : ι) : (∀ i, φ i) →L[R] φ i :=
  ⟨LinearMap.proj i, continuous_apply _⟩

@[simp]
theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →L[R] φ i) b = b i :=
  rfl

theorem proj_pi (f : ∀ i, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
  ext fun _c => rfl

theorem iInf_ker_proj : (⨅ i, ker (proj i : (∀ i, φ i) →L[R] φ i) : Submodule R (∀ i, φ i)) = ⊥ :=
  LinearMap.iInf_ker_proj

variable (R φ)

/-- Given a function `f : α → ι`, it induces a continuous linear function by right composition on
product types. For `f = Subtype.val`, this corresponds to forgetting some set of variables. -/
def _root_.Pi.compRightL {α : Type*} (f : α → ι) : ((i : ι) → φ i) →L[R] ((i : α) → φ (f i)) where
  toFun := fun v i ↦ v (f i)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp
  cont := by continuity

@[simp] lemma _root_.Pi.compRightL_apply {α : Type*} (f : α → ι) (v : (i : ι) → φ i) (i : α) :
    Pi.compRightL R φ f v i = v (f i) := rfl

end Pi

section Ring

variable {R : Type*} [Ring R]
  {M : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃] [Module R M₃]

theorem range_prod_eq {f : M →L[R] M₂} {g : M →L[R] M₃} (h : ker f ⊔ ker g = ⊤) :
    range (f.prod g) = (range f).prod (range g) :=
  LinearMap.range_prod_eq h

theorem ker_prod_ker_le_ker_coprod [ContinuousAdd M₃] (f : M →L[R] M₃) (g : M₂ →L[R] M₃) :
    (LinearMap.ker f).prod (LinearMap.ker g) ≤ LinearMap.ker (f.coprod g) :=
  LinearMap.ker_prod_ker_le_ker_coprod f.toLinearMap g.toLinearMap

theorem ker_coprod_of_disjoint_range [ContinuousAdd M₃] (f : M →L[R] M₃) (g : M₂ →L[R] M₃)
    (hd : Disjoint (range f) (range g)) :
    LinearMap.ker (f.coprod g) = (LinearMap.ker f).prod (LinearMap.ker g) :=
  LinearMap.ker_coprod_of_disjoint_range f.toLinearMap g.toLinearMap hd

end Ring

section SMul

variable
  {R : Type*} [Semiring R]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]

/-- `ContinuousLinearMap.prod` as an `Equiv`. -/
@[simps apply]
def prodEquiv : (M →L[R] M₂) × (M →L[R] M₃) ≃ (M →L[R] M₂ × M₃) where
  toFun f := f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl

theorem prod_ext_iff {f g : M × M₂ →L[R] M₃} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) := by
  simp only [← coe_inj, LinearMap.prod_ext_iff]
  rfl

@[ext]
theorem prod_ext {f g : M × M₂ →L[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩

variable (S : Type*) [Semiring S]
  [Module S M₂] [ContinuousAdd M₂] [SMulCommClass R S M₂] [ContinuousConstSMul S M₂]
  [Module S M₃] [ContinuousAdd M₃] [SMulCommClass R S M₃] [ContinuousConstSMul S M₃]

/-- `ContinuousLinearMap.prod` as a `LinearEquiv`. -/
@[simps apply]
def prodₗ : ((M →L[R] M₂) × (M →L[R] M₃)) ≃ₗ[S] M →L[R] M₂ × M₃ :=
  { prodEquiv with
    map_add' := fun _f _g => rfl
    map_smul' := fun _c _f => rfl }

end SMul

end ContinuousLinearMap
