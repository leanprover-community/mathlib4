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

assert_not_exists TrivialStar

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
  ⟨(f₁ : M₁ →ₗ[R] M₂).prod f₂, f₁.2.prodMk f₂.2⟩

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

lemma comp_inl_add_comp_inr (L : M₁ × M₂ →L[R] M₃) (v : M₁ × M₂) :
    L.comp (.inl R M₁ M₂) v.1 + L.comp (.inr R M₁ M₂) v.2 = L v := by simp [← map_add]

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

@[simp]
theorem proj_pi (f : ∀ i, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i := rfl

@[simp]
theorem coe_proj (i : ι) : (proj i).toLinearMap = (LinearMap.proj i : ((i : ι) → φ i) →ₗ[R] _) :=
  rfl

@[simp]
theorem pi_proj : pi proj = .id R (∀ i, φ i) := rfl

@[simp]
theorem pi_proj_comp (f : M₂ →L[R] ∀ i, φ i) : pi (proj · ∘L f) = f := rfl

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

/-- `Pi.single` as a bundled continuous linear map. -/
@[simps! -fullyApplied]
def single [DecidableEq ι] (i : ι) : φ i →L[R] (∀ i, φ i) where
  toLinearMap := .single R φ i
  cont := continuous_single _

end Pi

section Ring

variable {R : Type*} [Ring R]
  {M : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃] [Module R M₃]

theorem range_prod_eq {f : M →L[R] M₂} {g : M →L[R] M₃} (h : ker f ⊔ ker g = ⊤) :
    range (f.prod g) = (range f).prod (range g) :=
  LinearMap.range_prod_eq h

theorem ker_prod_ker_le_ker_coprod (f : M →L[R] M₃) (g : M₂ →L[R] M₃) :
    (LinearMap.ker f).prod (LinearMap.ker g) ≤ LinearMap.ker (f.coprod g) :=
  LinearMap.ker_prod_ker_le_ker_coprod f.toLinearMap g.toLinearMap

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

section coprod

variable {R S M N M₁ M₂ : Type*}
  [Semiring R] [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace M₁] [TopologicalSpace M₂]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M] [ContinuousAdd M] [AddCommMonoid N] [Module R N]
  [ContinuousAdd N] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`. -/
@[simps! coe apply]
def coprod (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) : M₁ × M₂ →L[R] M :=
  ⟨.coprod f₁ f₂, (f₁.cont.comp continuous_fst).add (f₂.cont.comp continuous_snd)⟩

@[simp] lemma coprod_add (f₁ g₁ : M₁ →L[R] M) (f₂ g₂ : M₂ →L[R] M) :
    (f₁ + g₁).coprod (f₂ + g₂) = f₁.coprod f₂ + g₁.coprod g₂ := by ext <;> simp

lemma range_coprod (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) :
    range (f₁.coprod f₂) = range f₁ ⊔ range f₂ := LinearMap.range_coprod ..

lemma comp_fst_add_comp_snd (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) :
    f₁.comp (.fst _ _ _) + f₂.comp (.snd _ _ _) = f₁.coprod f₂ := rfl

lemma comp_coprod (f : M →L[R] N) (g₁ : M₁ →L[R] M) (g₂ : M₂ →L[R] M) :
    f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂) :=
  coe_injective <| LinearMap.comp_coprod ..

@[simp] lemma coprod_comp_inl (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) :
    (f₁.coprod f₂).comp (.inl _ _ _) = f₁ := coe_injective <| LinearMap.coprod_inl ..

@[simp] lemma coprod_comp_inr (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) :
    (f₁.coprod f₂).comp (.inr _ _ _) = f₂ := coe_injective <| LinearMap.coprod_inr ..

@[simp]
lemma coprod_inl_inr : ContinuousLinearMap.coprod (.inl R M N) (.inr R M N) = .id R (M × N) :=
  coe_injective <| LinearMap.coprod_inl_inr

/-- Taking the product of two maps with the same codomain is equivalent to taking the product of
their domains.
See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.

TODO: Upgrade this to a `ContinuousLinearEquiv`. This should be true for any topological
vector space over a normed field thanks to `ContinuousLinearMap.precomp` and
`ContinuousLinearMap.postcomp`. -/
@[simps]
def coprodEquiv [ContinuousAdd M₁] [ContinuousAdd M₂] [Semiring S] [Module S M]
    [ContinuousConstSMul S M] [SMulCommClass R S M] :
    ((M₁ →L[R] M) × (M₂ →L[R] M)) ≃ₗ[S] M₁ × M₂ →L[R] M where
  toFun f := f.1.coprod f.2
  invFun f := (f.comp (.inl ..), f.comp (.inr ..))
  left_inv f := by simp
  right_inv f := by simp [← comp_coprod f (.inl R M₁ M₂)]
  map_add' a b := coprod_add ..
  map_smul' r a := by
    dsimp
    ext <;> simp [smul_apply]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module R M] [ContinuousAdd M] [AddCommMonoid M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]

lemma ker_coprod_of_disjoint_range {f₁ : M₁ →L[R] M} {f₂ : M₂ →L[R] M}
    (hf : Disjoint (range f₁) (range f₂)) :
    LinearMap.ker (f₁.coprod f₂) = (LinearMap.ker f₁).prod (LinearMap.ker f₂) :=
  LinearMap.ker_coprod_of_disjoint_range f₁.toLinearMap f₂.toLinearMap hf

end AddCommGroup

end coprod

end ContinuousLinearMap
