/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-!
# Continuous linear equivalences

Continuous semilinear / linear / star-linear equivalences between topological modules are denoted
by `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.
-/

assert_not_exists Star.star

open LinearMap (ker range)
open Topology Filter Pointwise

universe u v w u'

section

variable {R : Type*} {M : Type*} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [ContinuousAdd M] [Module R M] [ContinuousSMul R M]

variable (R M)

/-- Continuous linear equivalences between modules. We only put the type classes that are necessary
for the definition, although in applications `M` and `M₂` will be topological modules over the
topological semiring `R`. -/
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/5171): linter not ported yet; was @[nolint has_nonempty_instance]
structure ContinuousLinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] extends M ≃ₛₗ[σ] M₂ where
  continuous_toFun : Continuous toFun := by continuity
  continuous_invFun : Continuous invFun := by continuity

attribute [inherit_doc ContinuousLinearEquiv] ContinuousLinearEquiv.continuous_toFun
ContinuousLinearEquiv.continuous_invFun

@[inherit_doc]
notation:50 M " ≃SL[" σ "] " M₂ => ContinuousLinearEquiv σ M M₂

@[inherit_doc]
notation:50 M " ≃L[" R "] " M₂ => ContinuousLinearEquiv (RingHom.id R) M M₂

/-- `ContinuousSemilinearEquivClass F σ M M₂` asserts `F` is a type of bundled continuous
`σ`-semilinear equivs `M → M₂`.  See also `ContinuousLinearEquivClass F R M M₂` for the case
where `σ` is the identity map on `R`.  A map `f` between an `R`-module and an `S`-module over a ring
homomorphism `σ : R →+* S` is semilinear if it satisfies the two properties `f (x + y) = f x + f y`
and `f (c • x) = (σ c) • f x`. -/
class ContinuousSemilinearEquivClass (F : Type*) {R : outParam Type*} {S : outParam Type*}
    [Semiring R] [Semiring S] (σ : outParam <| R →+* S) {σ' : outParam <| S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : outParam Type*) [TopologicalSpace M]
    [AddCommMonoid M] (M₂ : outParam Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] [EquivLike F M M₂] extends SemilinearEquivClass F σ M M₂ : Prop where
  map_continuous : ∀ f : F, Continuous f := by continuity
  inv_continuous : ∀ f : F, Continuous (EquivLike.inv f) := by continuity

attribute [inherit_doc ContinuousSemilinearEquivClass]
ContinuousSemilinearEquivClass.map_continuous
ContinuousSemilinearEquivClass.inv_continuous

/-- `ContinuousLinearEquivClass F σ M M₂` asserts `F` is a type of bundled continuous
`R`-linear equivs `M → M₂`. This is an abbreviation for
`ContinuousSemilinearEquivClass F (RingHom.id R) M M₂`. -/
abbrev ContinuousLinearEquivClass (F : Type*) (R : outParam Type*) [Semiring R]
    (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*)
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] [EquivLike F M M₂] :=
  ContinuousSemilinearEquivClass F (RingHom.id R) M M₂

namespace ContinuousSemilinearEquivClass

variable (F : Type*) {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M]
  (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂]
  [Module R M] [Module S M₂]

-- `σ'` becomes a metavariable, but it's OK since it's an outparam
instance (priority := 100) continuousSemilinearMapClass [EquivLike F M M₂]
    [s : ContinuousSemilinearEquivClass F σ M M₂] : ContinuousSemilinearMapClass F σ M M₂ :=
  { s with }

instance (priority := 100) [EquivLike F M M₂]
    [s : ContinuousSemilinearEquivClass F σ M M₂] : HomeomorphClass F M M₂ :=
  { s with }

end ContinuousSemilinearEquivClass

namespace ContinuousLinearMap

section Pi

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] {ι : Type*} {φ : ι → Type*}
  [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

variable (R φ)

/-- If `I` and `J` are complementary index sets, the product of the kernels of the `J`th projections
of `φ` is linearly equivalent to the product over `I`. -/
def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →L[R] φ i) :
    Submodule R (∀ i, φ i)) ≃L[R] ∀ i : I, φ i where
  toLinearEquiv := LinearMap.iInfKerProjEquiv R φ hd hu
  continuous_toFun :=
    continuous_pi fun i =>
      Continuous.comp (continuous_apply (π := φ) i) <|
        @continuous_subtype_val _ _ fun x =>
          x ∈ (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →L[R] φ i) : Submodule R (∀ i, φ i))
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun i => by
        dsimp
        split_ifs <;> [apply continuous_apply; exact continuous_zero])
      _

end Pi

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section AddCommMonoid

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] {M₁ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁]
  [Module R₂ M₂] [Module R₃ M₃]

/-- A continuous linear equivalence induces a continuous linear map. -/
@[coe]
def toContinuousLinearMap (e : M₁ ≃SL[σ₁₂] M₂) : M₁ →SL[σ₁₂] M₂ :=
  { e.toLinearEquiv.toLinearMap with cont := e.continuous_toFun }

/-- Coerce continuous linear equivs to continuous linear maps. -/
instance ContinuousLinearMap.coe : Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ →SL[σ₁₂] M₂) :=
  ⟨toContinuousLinearMap⟩

instance equivLike :
    EquivLike (M₁ ≃SL[σ₁₂] M₂) M₁ M₂ where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    cases' f with f' _
    cases' g with g' _
    rcases f' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    rcases g' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

instance continuousSemilinearEquivClass :
    ContinuousSemilinearEquivClass (M₁ ≃SL[σ₁₂] M₂) σ₁₂ M₁ M₂ where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

theorem coe_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : (e : M₁ →SL[σ₁₂] M₂) b = e b :=
  rfl

@[simp]
theorem coe_toLinearEquiv (f : M₁ ≃SL[σ₁₂] M₂) : ⇑f.toLinearEquiv = f :=
  rfl

@[simp, norm_cast]
theorem coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ →SL[σ₁₂] M₂) = e :=
  rfl

theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : (M₁ ≃SL[σ₁₂] M₂) → M₁ ≃ₛₗ[σ₁₂] M₂) := by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[ext]
theorem ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ → M₂) = g) : f = g :=
  toLinearEquiv_injective <| LinearEquiv.ext <| congr_fun h

theorem coe_injective : Function.Injective ((↑) : (M₁ ≃SL[σ₁₂] M₂) → M₁ →SL[σ₁₂] M₂) :=
  fun _e _e' h => ext <| funext <| ContinuousLinearMap.ext_iff.1 h

@[simp, norm_cast]
theorem coe_inj {e e' : M₁ ≃SL[σ₁₂] M₂} : (e : M₁ →SL[σ₁₂] M₂) = e' ↔ e = e' :=
  coe_injective.eq_iff

/-- A continuous linear equivalence induces a homeomorphism. -/
def toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ≃ₜ M₂ :=
  { e with toEquiv := e.toLinearEquiv.toEquiv }

@[simp]
theorem coe_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph = e :=
  rfl

theorem isOpenMap (e : M₁ ≃SL[σ₁₂] M₂) : IsOpenMap e :=
  (ContinuousLinearEquiv.toHomeomorph e).isOpenMap

theorem image_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' closure s = closure (e '' s) :=
  e.toHomeomorph.image_closure s

theorem preimage_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e ⁻¹' closure s = closure (e ⁻¹' s) :=
  e.toHomeomorph.preimage_closure s

@[simp]
theorem isClosed_image (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : IsClosed (e '' s) ↔ IsClosed s :=
  e.toHomeomorph.isClosed_image

theorem map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e (𝓝 x) = 𝓝 (e x) :=
  e.toHomeomorph.map_nhds_eq x

-- Make some straightforward lemmas available to `simp`.
theorem map_zero (e : M₁ ≃SL[σ₁₂] M₂) : e (0 : M₁) = 0 :=
  (e : M₁ →SL[σ₁₂] M₂).map_zero

theorem map_add (e : M₁ ≃SL[σ₁₂] M₂) (x y : M₁) : e (x + y) = e x + e y :=
  (e : M₁ →SL[σ₁₂] M₂).map_add x y

@[simp]
theorem map_smulₛₗ (e : M₁ ≃SL[σ₁₂] M₂) (c : R₁) (x : M₁) : e (c • x) = σ₁₂ c • e x :=
  (e : M₁ →SL[σ₁₂] M₂).map_smulₛₗ c x

theorem map_smul [Module R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁) : e (c • x) = c • e x :=
  (e : M₁ →L[R₁] M₂).map_smul c x

theorem map_eq_zero_iff (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : e x = 0 ↔ x = 0 :=
  e.toLinearEquiv.map_eq_zero_iff

attribute [continuity]
  ContinuousLinearEquiv.continuous_toFun ContinuousLinearEquiv.continuous_invFun

@[continuity]
protected theorem continuous (e : M₁ ≃SL[σ₁₂] M₂) : Continuous (e : M₁ → M₂) :=
  e.continuous_toFun

protected theorem continuousOn (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : ContinuousOn (e : M₁ → M₂) s :=
  e.continuous.continuousOn

protected theorem continuousAt (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : ContinuousAt (e : M₁ → M₂) x :=
  e.continuous.continuousAt

protected theorem continuousWithinAt (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} {x : M₁} :
    ContinuousWithinAt (e : M₁ → M₂) s x :=
  e.continuous.continuousWithinAt

theorem comp_continuousOn_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁}
    {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.toHomeomorph.comp_continuousOn_iff _ _

theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁} :
    Continuous (e ∘ f) ↔ Continuous f :=
  e.toHomeomorph.comp_continuous_iff

/-- An extensionality lemma for `R ≃L[R] M`. -/
theorem ext₁ [TopologicalSpace R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  ext <| funext fun x => mul_one x ▸ by rw [← smul_eq_mul, map_smul, h, map_smul]

section

variable (R₁ M₁)

/-- The identity map as a continuous linear equivalence. -/
@[refl]
protected def refl : M₁ ≃L[R₁] M₁ :=
  { LinearEquiv.refl R₁ M₁ with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

@[simp]
theorem refl_apply (x : M₁) :
    ContinuousLinearEquiv.refl R₁ M₁ x = x := rfl

end

@[simp, norm_cast]
theorem coe_refl : ↑(ContinuousLinearEquiv.refl R₁ M₁) = ContinuousLinearMap.id R₁ M₁ :=
  rfl

@[simp, norm_cast]
theorem coe_refl' : ⇑(ContinuousLinearEquiv.refl R₁ M₁) = id :=
  rfl

/-- The inverse of a continuous linear equivalence as a continuous linear equivalence -/
@[symm]
protected def symm (e : M₁ ≃SL[σ₁₂] M₂) : M₂ ≃SL[σ₂₁] M₁ :=
  { e.toLinearEquiv.symm with
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }

@[simp]
theorem symm_toLinearEquiv (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.toLinearEquiv = e.toLinearEquiv.symm := by
  ext
  rfl

@[simp]
theorem symm_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : e.toHomeomorph.symm = e.symm.toHomeomorph :=
  rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : M₁ ≃SL[σ₁₂] M₂) : M₁ → M₂ :=
  h

/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : M₁ ≃SL[σ₁₂] M₂) : M₂ → M₁ :=
  h.symm

initialize_simps_projections ContinuousLinearEquiv (toFun → apply, invFun → symm_apply)

theorem symm_map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  e.toHomeomorph.symm_map_nhds_eq x

/-- The composition of two continuous linear equivalences as a continuous linear equivalence. -/
@[trans]
protected def trans (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) : M₁ ≃SL[σ₁₃] M₃ :=
  { e₁.toLinearEquiv.trans e₂.toLinearEquiv with
    continuous_toFun := e₂.continuous_toFun.comp e₁.continuous_toFun
    continuous_invFun := e₁.continuous_invFun.comp e₂.continuous_invFun }

@[simp]
theorem trans_toLinearEquiv (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv := by
  ext
  rfl

/-- Product of two continuous linear equivalences. The map comes from `Equiv.prodCongr`. -/
def prod [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) :
    (M₁ × M₃) ≃L[R₁] M₂ × M₄ :=
  { e.toLinearEquiv.prod e'.toLinearEquiv with
    continuous_toFun := e.continuous_toFun.prodMap e'.continuous_toFun
    continuous_invFun := e.continuous_invFun.prodMap e'.continuous_invFun }

@[simp, norm_cast]
theorem prod_apply [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) (x) : e.prod e' x = (e x.1, e' x.2) :=
  rfl

@[simp, norm_cast]
theorem coe_prod [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) :
    (e.prod e' : M₁ × M₃ →L[R₁] M₂ × M₄) = (e : M₁ →L[R₁] M₂).prodMap (e' : M₃ →L[R₁] M₄) :=
  rfl

theorem prod_symm [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) : (e.prod e').symm = e.symm.prod e'.symm :=
  rfl

variable (R₁ M₁ M₂)

/-- Product of modules is commutative up to continuous linear isomorphism. -/
@[simps! apply toLinearEquiv]
def prodComm [Module R₁ M₂] : (M₁ × M₂) ≃L[R₁] M₂ × M₁ :=
  { LinearEquiv.prodComm R₁ M₁ M₂ with
    continuous_toFun := continuous_swap
    continuous_invFun := continuous_swap }

@[simp] lemma prodComm_symm [Module R₁ M₂] : (prodComm R₁ M₁ M₂).symm = prodComm R₁ M₂ M₁ := rfl

variable {R₁ M₁ M₂}

protected theorem bijective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Bijective e :=
  e.toLinearEquiv.toEquiv.bijective

protected theorem injective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Injective e :=
  e.toLinearEquiv.toEquiv.injective

protected theorem surjective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Surjective e :=
  e.toLinearEquiv.toEquiv.surjective

@[simp]
theorem trans_apply (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) (c : M₁) :
    (e₁.trans e₂) c = e₂ (e₁ c) :=
  rfl

@[simp]
theorem apply_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂) : e (e.symm c) = c :=
  e.1.right_inv c

@[simp]
theorem symm_apply_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : e.symm (e b) = b :=
  e.1.left_inv b

@[simp]
theorem symm_trans_apply (e₁ : M₂ ≃SL[σ₂₁] M₁) (e₂ : M₃ ≃SL[σ₃₂] M₂) (c : M₁) :
    (e₂.trans e₁).symm c = e₂.symm (e₁.symm c) :=
  rfl

@[simp]
theorem symm_image_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e.symm '' (e '' s) = s :=
  e.toLinearEquiv.toEquiv.symm_image_image s

@[simp]
theorem image_symm_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image s

@[simp, norm_cast]
theorem comp_coe (f : M₁ ≃SL[σ₁₂] M₂) (f' : M₂ ≃SL[σ₂₃] M₃) :
    (f' : M₂ →SL[σ₂₃] M₃).comp (f : M₁ →SL[σ₁₂] M₂) = (f.trans f' : M₁ →SL[σ₁₃] M₃) :=
  rfl

-- Porting note: The priority should be higher than `comp_coe`.
@[simp high]
theorem coe_comp_coe_symm (e : M₁ ≃SL[σ₁₂] M₂) :
    (e : M₁ →SL[σ₁₂] M₂).comp (e.symm : M₂ →SL[σ₂₁] M₁) = ContinuousLinearMap.id R₂ M₂ :=
  ContinuousLinearMap.ext e.apply_symm_apply

-- Porting note: The priority should be higher than `comp_coe`.
@[simp high]
theorem coe_symm_comp_coe (e : M₁ ≃SL[σ₁₂] M₂) :
    (e.symm : M₂ →SL[σ₂₁] M₁).comp (e : M₁ →SL[σ₁₂] M₂) = ContinuousLinearMap.id R₁ M₁ :=
  ContinuousLinearMap.ext e.symm_apply_apply

@[simp]
theorem symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂) : (e.symm : M₂ → M₁) ∘ (e : M₁ → M₂) = id := by
  ext x
  exact symm_apply_apply e x

@[simp]
theorem self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂) : (e : M₁ → M₂) ∘ (e.symm : M₂ → M₁) = id := by
  ext x
  exact apply_symm_apply e x

@[simp]
theorem symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.symm = e := rfl

@[simp]
theorem refl_symm : (ContinuousLinearEquiv.refl R₁ M₁).symm = ContinuousLinearEquiv.refl R₁ M₁ :=
  rfl

theorem symm_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : e.symm.symm x = e x :=
  rfl

theorem symm_apply_eq (e : M₁ ≃SL[σ₁₂] M₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toLinearEquiv.symm_apply_eq

theorem eq_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toLinearEquiv.eq_symm_apply

protected theorem image_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' s = e.symm ⁻¹' s :=
  e.toLinearEquiv.toEquiv.image_eq_preimage s

protected theorem image_symm_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm '' s = e ⁻¹' s := by rw [e.symm.image_eq_preimage, e.symm_symm]

@[simp]
protected theorem symm_preimage_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toLinearEquiv.toEquiv.symm_preimage_preimage s

@[simp]
protected theorem preimage_symm_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) :
    e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.symm.symm_preimage_preimage s

lemma isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [UniformAddGroup E₁]
    [UniformAddGroup E₂] (e : E₁ ≃SL[σ₁₂] E₂) : IsUniformEmbedding e :=
  e.toLinearEquiv.toEquiv.isUniformEmbedding e.toContinuousLinearMap.uniformContinuous
    e.symm.toContinuousLinearMap.uniformContinuous

@[deprecated (since := "2024-10-01")] alias uniformEmbedding := isUniformEmbedding

protected theorem _root_.LinearEquiv.isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁]
    [UniformSpace E₂] [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂]
    [UniformAddGroup E₁] [UniformAddGroup E₂] (e : E₁ ≃ₛₗ[σ₁₂] E₂)
    (h₁ : Continuous e) (h₂ : Continuous e.symm) : IsUniformEmbedding e :=
  ContinuousLinearEquiv.isUniformEmbedding
    ({ e with
        continuous_toFun := h₁
        continuous_invFun := h₂ } :
      E₁ ≃SL[σ₁₂] E₂)

@[deprecated (since := "2024-10-01")]
alias _root_.LinearEquiv.uniformEmbedding := _root_.LinearEquiv.isUniformEmbedding

/-- Create a `ContinuousLinearEquiv` from two `ContinuousLinearMap`s that are
inverse of each other. See also `equivOfInverse'`. -/
def equivOfInverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁) (h₁ : Function.LeftInverse f₂ f₁)
    (h₂ : Function.RightInverse f₂ f₁) : M₁ ≃SL[σ₁₂] M₂ :=
  { f₁ with
    continuous_toFun := f₁.continuous
    invFun := f₂
    continuous_invFun := f₂.continuous
    left_inv := h₁
    right_inv := h₂ }

@[simp]
theorem equivOfInverse_apply (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
    equivOfInverse f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl

@[simp]
theorem symm_equivOfInverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂) :
    (equivOfInverse f₁ f₂ h₁ h₂).symm = equivOfInverse f₂ f₁ h₂ h₁ :=
  rfl

/-- Create a `ContinuousLinearEquiv` from two `ContinuousLinearMap`s that are
inverse of each other, in the `ContinuousLinearMap.comp` sense. See also `equivOfInverse`. -/
def equivOfInverse' (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁)
    (h₁ : f₁.comp f₂ = .id R₂ M₂) (h₂ : f₂.comp f₁ = .id R₁ M₁) : M₁ ≃SL[σ₁₂] M₂ :=
  equivOfInverse f₁ f₂
    (fun x ↦ by simpa using congr($(h₂) x)) (fun x ↦ by simpa using congr($(h₁) x))

@[simp]
theorem equivOfInverse'_apply (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
    equivOfInverse' f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl

/-- The inverse of `equivOfInverse'` is obtained by swapping the order of its parameters. -/
@[simp]
theorem symm_equivOfInverse' (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂) :
    (equivOfInverse' f₁ f₂ h₁ h₂).symm = equivOfInverse' f₂ f₁ h₂ h₁ :=
  rfl

variable (M₁)

/-- The continuous linear equivalences from `M` to itself form a group under composition. -/
instance automorphismGroup : Group (M₁ ≃L[R₁] M₁) where
  mul f g := g.trans f
  one := ContinuousLinearEquiv.refl R₁ M₁
  inv f := f.symm
  mul_assoc f g h := by
    ext
    rfl
  mul_one f := by
    ext
    rfl
  one_mul f := by
    ext
    rfl
  inv_mul_cancel f := by
    ext x
    exact f.left_inv x

variable {M₁} {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃}
  [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄] {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄}
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]

/-- The continuous linear equivalence between `ULift M₁` and `M₁`.

This is a continuous version of `ULift.moduleEquiv`. -/
def ulift : ULift M₁ ≃L[R₁] M₁ :=
  { ULift.moduleEquiv with
    continuous_toFun := continuous_uLift_down
    continuous_invFun := continuous_uLift_up }

/-- A pair of continuous (semi)linear equivalences generates an equivalence between the spaces of
continuous linear maps. See also `ContinuousLinearEquiv.arrowCongr`. -/
@[simps]
def arrowCongrEquiv (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) :
    (M₁ →SL[σ₁₄] M₄) ≃ (M₂ →SL[σ₂₃] M₃) where
  toFun f := (e₄₃ : M₄ →SL[σ₄₃] M₃).comp (f.comp (e₁₂.symm : M₂ →SL[σ₂₁] M₁))
  invFun f := (e₄₃.symm : M₃ →SL[σ₃₄] M₄).comp (f.comp (e₁₂ : M₁ →SL[σ₁₂] M₂))
  left_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, symm_apply_apply, coe_coe]
  right_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, apply_symm_apply, coe_coe]

section piCongrRight

variable {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R₁ (M i)] {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)]
  [∀ i, Module R₁ (N i)] (f : (i : ι) → M i ≃L[R₁] N i)

/-- Combine a family of continuous linear equivalences into a continuous linear equivalence of
pi-types. -/
def piCongrRight : ((i : ι) → M i) ≃L[R₁] (i : ι) → N i :=
  { LinearEquiv.piCongrRight fun i ↦ f i with
    continuous_toFun := by
      exact continuous_pi fun i ↦ (f i).continuous_toFun.comp (continuous_apply i)
    continuous_invFun := by
      exact continuous_pi fun i => (f i).continuous_invFun.comp (continuous_apply i) }

@[simp]
theorem piCongrRight_apply (m : (i : ι) → M i) (i : ι) :
    piCongrRight f m i = (f i) (m i) := rfl

@[simp]
theorem piCongrRight_symm_apply (n : (i : ι) → N i) (i : ι) :
    (piCongrRight f).symm n i = (f i).symm (n i) := rfl

end piCongrRight

end AddCommMonoid

section AddCommGroup

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommGroup M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommGroup M₄] [Module R M] [Module R M₂] [Module R M₃]
  [Module R M₄]

variable [TopologicalAddGroup M₄]

/-- Equivalence given by a block lower diagonal matrix. `e` and `e'` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
def skewProd (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) : (M × M₃) ≃L[R] M₂ × M₄ :=
  {
    e.toLinearEquiv.skewProd e'.toLinearEquiv
      ↑f with
    continuous_toFun :=
      (e.continuous_toFun.comp continuous_fst).prod_mk
        ((e'.continuous_toFun.comp continuous_snd).add <| f.continuous.comp continuous_fst)
    continuous_invFun :=
      (e.continuous_invFun.comp continuous_fst).prod_mk
        (e'.continuous_invFun.comp <|
          continuous_snd.sub <| f.continuous.comp <| e.continuous_invFun.comp continuous_fst) }

@[simp]
theorem skewProd_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
    e.skewProd e' f x = (e x.1, e' x.2 + f x.1) :=
  rfl

@[simp]
theorem skewProd_symm_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
    (e.skewProd e' f).symm x = (e.symm x.1, e'.symm (x.2 - f (e.symm x.1))) :=
  rfl

variable (R) in
/-- The negation map as a continuous linear equivalence. -/
def neg [ContinuousNeg M] :
    M ≃L[R] M :=
  { LinearEquiv.neg R with
    continuous_toFun := continuous_neg
    continuous_invFun := continuous_neg }

@[simp]
theorem coe_neg [ContinuousNeg M] :
    (neg R : M → M) = -id := rfl

@[simp]
theorem neg_apply [ContinuousNeg M] (x : M) :
    neg R x = -x := by simp

@[simp]
theorem symm_neg [ContinuousNeg M] :
    (neg R : M ≃L[R] M).symm = neg R := rfl

end AddCommGroup

section Ring

variable {R : Type*} [Ring R] {R₂ : Type*} [Ring R₂] {M : Type*} [TopologicalSpace M]
  [AddCommGroup M] [Module R M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

theorem map_sub (e : M ≃SL[σ₁₂] M₂) (x y : M) : e (x - y) = e x - e y :=
  (e : M →SL[σ₁₂] M₂).map_sub x y

theorem map_neg (e : M ≃SL[σ₁₂] M₂) (x : M) : e (-x) = -e x :=
  (e : M →SL[σ₁₂] M₂).map_neg x

section

/-! The next theorems cover the identification between `M ≃L[R] M`and the group of units of the ring
`M →L[R] M`. -/

/-- An invertible continuous linear map `f` determines a continuous equivalence from `M` to itself.
-/
def ofUnit (f : (M →L[R] M)ˣ) : M ≃L[R] M where
  toLinearEquiv :=
    { toFun := f.val
      map_add' := by simp
      map_smul' := by simp
      invFun := f.inv
      left_inv := fun x =>
        show (f.inv * f.val) x = x by
          rw [f.inv_val]
          simp
      right_inv := fun x =>
        show (f.val * f.inv) x = x by
          rw [f.val_inv]
          simp }
  continuous_toFun := f.val.continuous
  continuous_invFun := f.inv.continuous

/-- A continuous equivalence from `M` to itself determines an invertible continuous linear map. -/
def toUnit (f : M ≃L[R] M) : (M →L[R] M)ˣ where
  val := f
  inv := f.symm
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp

variable (R M)

/-- The units of the algebra of continuous `R`-linear endomorphisms of `M` is multiplicatively
equivalent to the type of continuous linear equivalences between `M` and itself. -/
def unitsEquiv : (M →L[R] M)ˣ ≃* M ≃L[R] M where
  toFun := ofUnit
  invFun := toUnit
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl
  map_mul' x y := by
    ext
    rfl

@[simp]
theorem unitsEquiv_apply (f : (M →L[R] M)ˣ) (x : M) : unitsEquiv R M f x = (f : M →L[R] M) x :=
  rfl

end

section

variable (R) [TopologicalSpace R]
variable [ContinuousMul R]

/-- Continuous linear equivalences `R ≃L[R] R` are enumerated by `Rˣ`. -/
def unitsEquivAut : Rˣ ≃ R ≃L[R] R where
  toFun u :=
    equivOfInverse (ContinuousLinearMap.smulRight (1 : R →L[R] R) ↑u)
      (ContinuousLinearMap.smulRight (1 : R →L[R] R) ↑u⁻¹) (fun x => by simp) fun x => by simp
  invFun e :=
    ⟨e 1, e.symm 1, by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, symm_apply_apply], by
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, apply_symm_apply]⟩
  left_inv u := Units.ext <| by simp
  right_inv e := ext₁ <| by simp

variable {R}

@[simp]
theorem unitsEquivAut_apply (u : Rˣ) (x : R) : unitsEquivAut R u x = x * u :=
  rfl

@[simp]
theorem unitsEquivAut_apply_symm (u : Rˣ) (x : R) : (unitsEquivAut R u).symm x = x * ↑u⁻¹ :=
  rfl

@[simp]
theorem unitsEquivAut_symm_apply (e : R ≃L[R] R) : ↑((unitsEquivAut R).symm e) = e 1 :=
  rfl

end

variable [Module R M₂] [TopologicalAddGroup M]

/-- A pair of continuous linear maps such that `f₁ ∘ f₂ = id` generates a continuous
linear equivalence `e` between `M` and `M₂ × f₁.ker` such that `(e x).2 = x` for `x ∈ f₁.ker`,
`(e x).1 = f₁ x`, and `(e (f₂ y)).2 = 0`. The map is given by `e x = (f₁ x, x - f₂ (f₁ x))`. -/
def equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) :
    M ≃L[R] M₂ × ker f₁ :=
  equivOfInverse (f₁.prod (f₁.projKerOfRightInverse f₂ h)) (f₂.coprod (ker f₁).subtypeL)
    (fun x => by simp) fun ⟨x, y⟩ => by
      -- Porting note: `simp` timeouts.
      rw [ContinuousLinearMap.coprod_apply,
        Submodule.subtypeL_apply, _root_.map_add, ContinuousLinearMap.prod_apply, h x,
        ContinuousLinearMap.projKerOfRightInverse_comp_inv,
        ContinuousLinearMap.prod_apply, LinearMap.map_coe_ker,
        ContinuousLinearMap.projKerOfRightInverse_apply_idem, Prod.mk_add_mk, add_zero, zero_add]

@[simp]
theorem fst_equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) : (equivOfRightInverse f₁ f₂ h x).1 = f₁ x :=
  rfl

@[simp]
theorem snd_equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) :
    ((equivOfRightInverse f₁ f₂ h x).2 : M) = x - f₂ (f₁ x) :=
  rfl

@[simp]
theorem equivOfRightInverse_symm_apply (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (y : M₂ × ker f₁) :
    (equivOfRightInverse f₁ f₂ h).symm y = f₂ y.1 + y.2 :=
  rfl

end Ring

section

variable (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M]

/-- If `ι` has a unique element, then `ι → M` is continuously linear equivalent to `M`. -/
def funUnique : (ι → M) ≃L[R] M :=
  { Homeomorph.funUnique ι M with toLinearEquiv := LinearEquiv.funUnique ι R M }

variable {ι R M}

@[simp]
theorem coe_funUnique : ⇑(funUnique ι R M) = Function.eval default :=
  rfl

@[simp]
theorem coe_funUnique_symm : ⇑(funUnique ι R M).symm = Function.const ι :=
  rfl

variable (R M)

/-- Continuous linear equivalence between dependent functions `(i : Fin 2) → M i` and `M 0 × M 1`.
-/
@[simps! (config := .asFn) apply symm_apply]
def piFinTwo (M : Fin 2 → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] : ((i : _) → M i) ≃L[R] M 0 × M 1 :=
  { Homeomorph.piFinTwo M with toLinearEquiv := LinearEquiv.piFinTwo R M }

/-- Continuous linear equivalence between vectors in `M² = Fin 2 → M` and `M × M`. -/
@[simps! (config := .asFn) apply symm_apply]
def finTwoArrow : (Fin 2 → M) ≃L[R] M × M :=
  { piFinTwo R fun _ => M with toLinearEquiv := LinearEquiv.finTwoArrow R M }

end

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {R : Type*} {M M₂ M₃ : Type*}
  [TopologicalSpace M] [TopologicalSpace M₂] [TopologicalSpace M₃]

section

variable [Semiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid M₃] [Module R M₃]

/-- A continuous linear map is invertible if it is the forward direction of a continuous linear
equivalence. -/
def IsInvertible (f : M →L[R] M₂) : Prop :=
  ∃ (A : M ≃L[R] M₂), A = f

open Classical in
/-- Introduce a function `inverse` from `M →L[R] M₂` to `M₂ →L[R] M`, which sends `f` to `f.symm` if
`f` is a continuous linear equivalence and to `0` otherwise.  This definition is somewhat ad hoc,
but one needs a fully (rather than partially) defined inverse function for some purposes, including
for calculus. -/
noncomputable def inverse : (M →L[R] M₂) → M₂ →L[R] M := fun f =>
  if h : f.IsInvertible then ((Classical.choose h).symm : M₂ →L[R] M) else 0

@[simp] lemma isInvertible_equiv {f : M ≃L[R] M₂} : IsInvertible (f : M →L[R] M₂) := ⟨f, rfl⟩

/-- By definition, if `f` is invertible then `inverse f = f.symm`. -/
@[simp]
theorem inverse_equiv (e : M ≃L[R] M₂) : inverse (e : M →L[R] M₂) = e.symm := by
  simp [inverse]

/-- By definition, if `f` is not invertible then `inverse f = 0`. -/
@[simp] lemma inverse_of_not_isInvertible
    {f : M →L[R] M₂} (hf : ¬ f.IsInvertible) : f.inverse = 0 :=
  dif_neg hf

@[deprecated (since := "2024-10-29")] alias inverse_non_equiv := inverse_of_not_isInvertible

@[simp] theorem inverse_zero : inverse (0 : M →L[R] M₂) = 0 := by
  by_cases h : IsInvertible (0 : M →L[R] M₂)
  · rcases h with ⟨e', he'⟩
    simp only [← he', inverse_equiv]
    ext v
    apply e'.injective
    rw [← ContinuousLinearEquiv.coe_coe, he']
    rfl
  · exact inverse_of_not_isInvertible h

lemma IsInvertible.comp {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hg : g.IsInvertible) (hf : f.IsInvertible) : (g ∘L f).IsInvertible := by
  rcases hg with ⟨N, rfl⟩
  rcases hf with ⟨M, rfl⟩
  exact ⟨M.trans N, rfl⟩

lemma IsInvertible.of_inverse {f : M →L[R] M₂} {g : M₂ →L[R] M}
    (hf : f ∘L g = id R M₂) (hg : g ∘L f = id R M) :
    f.IsInvertible :=
  ⟨ContinuousLinearEquiv.equivOfInverse' _ _ hf hg, rfl⟩

lemma inverse_eq {f : M →L[R] M₂} {g : M₂ →L[R] M} (hf : f ∘L g = id R M₂) (hg : g ∘L f = id R M) :
    f.inverse = g := by
  have : f = ContinuousLinearEquiv.equivOfInverse' f g hf hg := rfl
  rw [this, inverse_equiv]
  rfl

lemma IsInvertible.inverse_apply_eq {f : M →L[R] M₂} {x : M} {y : M₂} (hf : f.IsInvertible) :
    f.inverse y = x ↔ y = f x := by
  rcases hf with ⟨M, rfl⟩
  simp only [inverse_equiv, ContinuousLinearEquiv.coe_coe]
  exact ContinuousLinearEquiv.symm_apply_eq M

@[simp] lemma isInvertible_equiv_comp {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂} :
    ((e : M₂ →L[R] M₃) ∘L f).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = e.symm ∘L ((e : M₂ →L[R] M₃) ∘L f) := by ext; simp
    rw [this, ← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma isInvertible_comp_equiv {e : M₃ ≃L[R] M} {f : M →L[R] M₂} :
    (f ∘L (e : M₃ →L[R] M)).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = (f ∘L (e : M₃ →L[R] M)) ∘L e.symm := by ext; simp
    rw [this, ← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma inverse_equiv_comp {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂} :
    (e ∘L f).inverse = f.inverse ∘L (e.symm : M₃ →L[R] M₂) := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf]
    rfl

@[simp] lemma inverse_comp_equiv {e : M₃ ≃L[R] M} {f : M →L[R] M₂} :
    (f ∘L e).inverse = (e.symm : M →L[R] M₃) ∘L f.inverse := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf]
    simp

lemma IsInvertible.inverse_comp_of_left {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hg : g.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hg with ⟨N, rfl⟩
  simp

lemma IsInvertible.inverse_comp_apply_of_left {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : M₃}
    (hg : g.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hg.inverse_comp_of_left, coe_comp', Function.comp_apply]

lemma IsInvertible.inverse_comp_of_right {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hf : f.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hf with ⟨M, rfl⟩
  simp

lemma IsInvertible.inverse_comp_apply_of_right {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : M₃}
    (hf : f.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hf.inverse_comp_of_right, coe_comp', Function.comp_apply]

end

section

variable [Ring R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M₂] [Module R M₂]

@[simp]
theorem ring_inverse_equiv (e : M ≃L[R] M) : Ring.inverse ↑e = inverse (e : M →L[R] M) := by
  suffices Ring.inverse ((ContinuousLinearEquiv.unitsEquiv _ _).symm e : M →L[R] M) = inverse ↑e by
    convert this
  simp
  rfl

/-- The function `ContinuousLinearEquiv.inverse` can be written in terms of `Ring.inverse` for the
ring of self-maps of the domain. -/
theorem to_ring_inverse (e : M ≃L[R] M₂) (f : M →L[R] M₂) :
    inverse f = Ring.inverse ((e.symm : M₂ →L[R] M).comp f) ∘L e.symm := by
  by_cases h₁ : f.IsInvertible
  · obtain ⟨e', he'⟩ := h₁
    rw [← he']
    change _ = Ring.inverse (e'.trans e.symm : M →L[R] M) ∘L (e.symm : M₂ →L[R] M)
    ext
    simp
  · suffices ¬IsUnit ((e.symm : M₂ →L[R] M).comp f) by simp [this, h₁]
    contrapose! h₁
    rcases h₁ with ⟨F, hF⟩
    use (ContinuousLinearEquiv.unitsEquiv _ _ F).trans e
    ext
    dsimp
    rw [hF]
    simp

theorem ring_inverse_eq_map_inverse : Ring.inverse = @inverse R M M _ _ _ _ _ _ _ := by
  ext
  simp [to_ring_inverse (ContinuousLinearEquiv.refl R M)]

@[simp] theorem inverse_id : (id R M).inverse = id R M := by
  rw [← ring_inverse_eq_map_inverse]
  exact Ring.inverse_one _

end

end ContinuousLinearMap

namespace Submodule

variable {R : Type*} [Ring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M]

open ContinuousLinearMap

/-- If `p` is a closed complemented submodule,
then there exists a submodule `q` and a continuous linear equivalence `M ≃L[R] (p × q)` such that
`e (x : p) = (x, 0)`, `e (y : q) = (0, y)`, and `e.symm x = x.1 + x.2`.

In fact, the properties of `e` imply the properties of `e.symm` and vice versa,
but we provide both for convenience. -/
lemma ClosedComplemented.exists_submodule_equiv_prod [TopologicalAddGroup M]
    {p : Submodule R M} (hp : p.ClosedComplemented) :
    ∃ (q : Submodule R M) (e : M ≃L[R] (p × q)),
      (∀ x : p, e x = (x, 0)) ∧ (∀ y : q, e y = (0, y)) ∧ (∀ x, e.symm x = x.1 + x.2) :=
  let ⟨f, hf⟩ := hp
  ⟨LinearMap.ker f, .equivOfRightInverse _ p.subtypeL hf,
    fun _ ↦ by ext <;> simp [hf], fun _ ↦ by ext <;> simp [hf], fun _ ↦ rfl⟩

end Submodule

namespace MulOpposite

variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [TopologicalSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousSMul R M]

/-- The function `op` is a continuous linear equivalence. -/
@[simps!]
def opContinuousLinearEquiv : M ≃L[R] Mᵐᵒᵖ where
  __ := MulOpposite.opLinearEquiv R

end MulOpposite

end
