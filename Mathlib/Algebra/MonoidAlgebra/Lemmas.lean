/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Monoid algebras

-/

noncomputable section

open Finset

open Finsupp hiding single mapDomain

universe u₁ u₂ u₃ u₄

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

variable {k G}

/-! #### Non-unital, non-associative algebra structure -/


section NonUnitalNonAssocAlgebra

variable (k) [Semiring k] [DistribSMul R k] [Mul G]

variable {A : Type u₃} [NonUnitalNonAssocSemiring A]

/-- A non_unital `k`-algebra homomorphism from `MonoidAlgebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
theorem nonUnitalAlgHom_ext [DistribMulAction k A] {φ₁ φ₂ : MonoidAlgebra k G →ₙₐ[k] A}
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  NonUnitalAlgHom.to_distribMulActionHom_injective <|
    Finsupp.distribMulActionHom_ext' fun a => DistribMulActionHom.ext_ring (h a)

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem nonUnitalAlgHom_ext' [DistribMulAction k A] {φ₁ φ₂ : MonoidAlgebra k G →ₙₐ[k] A}
    (h : φ₁.toMulHom.comp (ofMagma k G) = φ₂.toMulHom.comp (ofMagma k G)) : φ₁ = φ₂ :=
  nonUnitalAlgHom_ext k <| DFunLike.congr_fun h

/-- The functor `G ↦ MonoidAlgebra k G`, from the category of magmas to the category of non-unital,
non-associative algebras over `k` is adjoint to the forgetful functor in the other direction. -/
@[simps apply_apply symm_apply]
def liftMagma [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] :
    (G →ₙ* A) ≃ (MonoidAlgebra k G →ₙₐ[k] A) where
  toFun f :=
    { liftAddHom fun x => (smulAddHom k A).flip (f x) with
      toFun := fun a => a.sum fun m t => t • f m
      map_smul' := fun t' a => by
        -- Porting note (https://github.com/leanprover-community/mathlib4/issues/12129): additional beta reduction needed
        beta_reduce
        rw [Finsupp.smul_sum, sum_smul_index']
        · simp_rw [smul_assoc, MonoidHom.id_apply]
        · intro m
          exact zero_smul k (f m)
      map_mul' := fun a₁ a₂ => by
        let g : G → k → A := fun m t => t • f m
        have h₁ : ∀ m, g m 0 = 0 := by
          intro m
          exact zero_smul k (f m)
        have h₂ : ∀ (m) (t₁ t₂ : k), g m (t₁ + t₂) = g m t₁ + g m t₂ := by
          intros
          rw [← add_smul]
        -- Porting note: `reducible` cannot be `local` so proof gets long.
        simp_rw [Finsupp.mul_sum, Finsupp.sum_mul, smul_mul_smul_comm, ← f.map_mul, mul_def,
          sum_comm a₂ a₁]
        rw [sum_sum_index h₁ h₂]; congr; ext
        rw [sum_sum_index h₁ h₂]; congr; ext
        rw [sum_single_index (h₁ _)] }
  invFun F := F.toMulHom.comp (ofMagma k G)
  left_inv f := by
    ext m
    simp only [NonUnitalAlgHom.coe_mk, ofMagma_apply, NonUnitalAlgHom.toMulHom_eq_coe,
      sum_single_index, Function.comp_apply, one_smul, zero_smul, MulHom.coe_comp,
      NonUnitalAlgHom.coe_to_mulHom]
  right_inv F := by
    ext m
    simp only [NonUnitalAlgHom.coe_mk, ofMagma_apply, NonUnitalAlgHom.toMulHom_eq_coe,
      sum_single_index, Function.comp_apply, one_smul, zero_smul, MulHom.coe_comp,
      NonUnitalAlgHom.coe_to_mulHom]

end NonUnitalNonAssocAlgebra

/-! #### Algebra structure -/

section lift

variable [CommSemiring k] [Monoid G] [Monoid H]
variable {A : Type u₃} [Semiring A] [Algebra k A] {B : Type*} [Semiring B] [Algebra k B]

variable {H}

/-- If `f : G → H` is a homomorphism between two magmas, then
`Finsupp.mapDomain f` is a non-unital algebra homomorphism between their magma algebras. -/
@[simps apply]
def mapDomainNonUnitalAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A]
    {G H F : Type*} [Mul G] [Mul H] [FunLike F G H] [MulHomClass F G H] (f : F) :
    MonoidAlgebra A G →ₙₐ[k] MonoidAlgebra A H :=
  { (Finsupp.mapDomain.addMonoidHom f : MonoidAlgebra A G →+ MonoidAlgebra A H) with
    map_mul' := fun x y => mapDomain_mul f x y
    map_smul' := fun r x => mapDomain_smul r x }

variable (A) in
theorem mapDomain_algebraMap {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F) (r : k) :
    mapDomain f (algebraMap k (MonoidAlgebra A G) r) = algebraMap k (MonoidAlgebra A H) r := by
  simp only [coe_algebraMap, mapDomain_single, map_one, (· ∘ ·)]

/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`Finsupp.mapDomain f` is an algebra homomorphism between their monoid algebras. -/
@[simps!]
def mapDomainAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] {H F : Type*}
    [Monoid H] [FunLike F G H] [MonoidHomClass F G H] (f : F) :
    MonoidAlgebra A G →ₐ[k] MonoidAlgebra A H :=
  { mapDomainRingHom A f with commutes' := mapDomain_algebraMap A f }

@[simp]
lemma mapDomainAlgHom_id (k A) [CommSemiring k] [Semiring A] [Algebra k A] :
    mapDomainAlgHom k A (MonoidHom.id G) = AlgHom.id k (MonoidAlgebra A G) := by
  ext; simp [MonoidHom.id, ← Function.id_def]

@[simp]
lemma mapDomainAlgHom_comp (k A) {G₁ G₂ G₃} [CommSemiring k] [Semiring A] [Algebra k A]
    [Monoid G₁] [Monoid G₂] [Monoid G₃] (f : G₁ →* G₂) (g : G₂ →* G₃) :
    mapDomainAlgHom k A (g.comp f) = (mapDomainAlgHom k A g).comp (mapDomainAlgHom k A f) := by
  ext; simp [mapDomain_comp]

variable (k A)

/-- If `e : G ≃* H` is a multiplicative equivalence between two monoids, then
`MonoidAlgebra.domCongr e` is an algebra equivalence between their monoid algebras. -/
def domCongr (e : G ≃* H) : MonoidAlgebra A G ≃ₐ[k] MonoidAlgebra A H :=
  AlgEquiv.ofLinearEquiv
    (Finsupp.domLCongr e : (G →₀ A) ≃ₗ[k] (H →₀ A))
    ((equivMapDomain_eq_mapDomain _ _).trans <| mapDomain_one e)
    (fun f g => (equivMapDomain_eq_mapDomain _ _).trans <| (mapDomain_mul e f g).trans <|
        congr_arg₂ _ (equivMapDomain_eq_mapDomain _ _).symm (equivMapDomain_eq_mapDomain _ _).symm)

theorem domCongr_toAlgHom (e : G ≃* H) : (domCongr k A e).toAlgHom = mapDomainAlgHom k A e :=
  AlgHom.ext fun _ => equivMapDomain_eq_mapDomain _ _

@[simp] theorem domCongr_apply (e : G ≃* H) (f : MonoidAlgebra A G) (h : H) :
    domCongr k A e f h = f (e.symm h) :=
  rfl

@[simp] theorem domCongr_support (e : G ≃* H) (f : MonoidAlgebra A G) :
    (domCongr k A e f).support = f.support.map e :=
  rfl

@[simp] theorem domCongr_single (e : G ≃* H) (g : G) (a : A) :
    domCongr k A e (single g a) = single (e g) a :=
  Finsupp.equivMapDomain_single _ _ _

@[simp] theorem domCongr_refl : domCongr k A (MulEquiv.refl G) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ => Finsupp.ext fun _ => rfl

@[simp] theorem domCongr_symm (e : G ≃* H) : (domCongr k A e).symm = domCongr k A e.symm := rfl

end lift

section

end

end MonoidAlgebra

namespace AddMonoidAlgebra

variable {k G H}

/-! #### Non-unital, non-associative algebra structure -/

section NonUnitalNonAssocAlgebra

variable (k) [Semiring k] [DistribSMul R k] [Add G]
variable {A : Type u₃} [NonUnitalNonAssocSemiring A]

/-- A non_unital `k`-algebra homomorphism from `k[G]` is uniquely defined by its
values on the functions `single a 1`. -/
theorem nonUnitalAlgHom_ext [DistribMulAction k A] {φ₁ φ₂ : k[G] →ₙₐ[k] A}
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  @MonoidAlgebra.nonUnitalAlgHom_ext k (Multiplicative G) _ _ _ _ _ φ₁ φ₂ h

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem nonUnitalAlgHom_ext' [DistribMulAction k A] {φ₁ φ₂ : k[G] →ₙₐ[k] A}
    (h : φ₁.toMulHom.comp (ofMagma k G) = φ₂.toMulHom.comp (ofMagma k G)) : φ₁ = φ₂ :=
  @MonoidAlgebra.nonUnitalAlgHom_ext' k (Multiplicative G) _ _ _ _ _ φ₁ φ₂ h

/-- The functor `G ↦ k[G]`, from the category of magmas to the category of
non-unital, non-associative algebras over `k` is adjoint to the forgetful functor in the other
direction. -/
@[simps apply_apply symm_apply]
def liftMagma [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] :
    (Multiplicative G →ₙ* A) ≃ (k[G] →ₙₐ[k] A) :=
  { (MonoidAlgebra.liftMagma k : (Multiplicative G →ₙ* A) ≃ (_ →ₙₐ[k] A)) with
    toFun := fun f =>
      { (MonoidAlgebra.liftMagma k f : _) with
        toFun := fun a => sum a fun m t => t • f (Multiplicative.ofAdd m) }
    invFun := fun F => F.toMulHom.comp (ofMagma k G) }

end NonUnitalNonAssocAlgebra

/-! #### Algebra structure -/

theorem mapDomain_algebraMap (A : Type*) {H F : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
    [AddMonoid G] [AddMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
    (f : F) (r : k) :
    mapDomain f (algebraMap k A[G] r) = algebraMap k A[H] r := by
  simp only [Function.comp_apply, mapDomain_single, AddMonoidAlgebra.coe_algebraMap, map_zero]

/-- If `f : G → H` is a homomorphism between two additive magmas, then `Finsupp.mapDomain f` is a
non-unital algebra homomorphism between their additive magma algebras. -/
@[simps apply]
def mapDomainNonUnitalAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A]
    {G H F : Type*} [Add G] [Add H] [FunLike F G H] [AddHomClass F G H] (f : F) :
    A[G] →ₙₐ[k] A[H] :=
  { (Finsupp.mapDomain.addMonoidHom f : MonoidAlgebra A G →+ MonoidAlgebra A H) with
    map_mul' := fun x y => mapDomain_mul f x y
    map_smul' := fun r x => mapDomain_smul r x }

/-- If `f : G → H` is an additive homomorphism between two additive monoids, then
`Finsupp.mapDomain f` is an algebra homomorphism between their add monoid algebras. -/
@[simps!]
def mapDomainAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] [AddMonoid G]
    {H F : Type*} [AddMonoid H] [FunLike F G H] [AddMonoidHomClass F G H] (f : F) :
    A[G] →ₐ[k] A[H] :=
  { mapDomainRingHom A f with commutes' := mapDomain_algebraMap A f }

@[simp]
lemma mapDomainAlgHom_id (k A) [CommSemiring k] [Semiring A] [Algebra k A] [AddMonoid G] :
    mapDomainAlgHom k A (AddMonoidHom.id G) = AlgHom.id k (AddMonoidAlgebra A G) := by
  ext; simp [AddMonoidHom.id, ← Function.id_def]

@[simp]
lemma mapDomainAlgHom_comp (k A) {G₁ G₂ G₃} [CommSemiring k] [Semiring A] [Algebra k A]
    [AddMonoid G₁] [AddMonoid G₂] [AddMonoid G₃] (f : G₁ →+ G₂) (g : G₂ →+ G₃) :
    mapDomainAlgHom k A (g.comp f) = (mapDomainAlgHom k A g).comp (mapDomainAlgHom k A f) := by
  ext; simp [mapDomain_comp]

variable (k A)
variable [CommSemiring k] [AddMonoid G] [AddMonoid H] [Semiring A] [Algebra k A]


/-- If `e : G ≃* H` is a multiplicative equivalence between two monoids, then
`AddMonoidAlgebra.domCongr e` is an algebra equivalence between their monoid algebras. -/
def domCongr (e : G ≃+ H) : A[G] ≃ₐ[k] A[H] :=
  AlgEquiv.ofLinearEquiv
    (Finsupp.domLCongr e : (G →₀ A) ≃ₗ[k] (H →₀ A))
    ((equivMapDomain_eq_mapDomain _ _).trans <| mapDomain_one e)
    (fun f g => (equivMapDomain_eq_mapDomain _ _).trans <| (mapDomain_mul e f g).trans <|
        congr_arg₂ _ (equivMapDomain_eq_mapDomain _ _).symm (equivMapDomain_eq_mapDomain _ _).symm)

theorem domCongr_toAlgHom (e : G ≃+ H) : (domCongr k A e).toAlgHom = mapDomainAlgHom k A e :=
  AlgHom.ext fun _ => equivMapDomain_eq_mapDomain _ _

@[simp] theorem domCongr_apply (e : G ≃+ H) (f : MonoidAlgebra A G) (h : H) :
    domCongr k A e f h = f (e.symm h) :=
  rfl

@[simp] theorem domCongr_support (e : G ≃+ H) (f : MonoidAlgebra A G) :
    (domCongr k A e f).support = f.support.map e :=
  rfl

@[simp] theorem domCongr_single (e : G ≃+ H) (g : G) (a : A) :
    domCongr k A e (single g a) = single (e g) a :=
  Finsupp.equivMapDomain_single _ _ _

@[simp] theorem domCongr_refl : domCongr k A (AddEquiv.refl G) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ => Finsupp.ext fun _ => rfl

@[simp] theorem domCongr_symm (e : G ≃+ H) : (domCongr k A e).symm = domCongr k A e.symm := rfl

end AddMonoidAlgebra

variable [CommSemiring R]

/-- The algebra equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative`. -/
def AddMonoidAlgebra.toMultiplicativeAlgEquiv [Semiring k] [Algebra R k] [AddMonoid G] :
    AddMonoidAlgebra k G ≃ₐ[R] MonoidAlgebra k (Multiplicative G) :=
  { AddMonoidAlgebra.toMultiplicative k G with
    commutes' := fun r => by simp [AddMonoidAlgebra.toMultiplicative] }

/-- The algebra equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of
`Additive`. -/
def MonoidAlgebra.toAdditiveAlgEquiv [Semiring k] [Algebra R k] [Monoid G] :
    MonoidAlgebra k G ≃ₐ[R] AddMonoidAlgebra k (Additive G) :=
  { MonoidAlgebra.toAdditive k G with commutes' := fun r => by simp [MonoidAlgebra.toAdditive] }
