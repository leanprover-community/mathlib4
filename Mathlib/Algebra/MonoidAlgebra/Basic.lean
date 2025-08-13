/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.Finsupp.SMul
import Mathlib.LinearAlgebra.Finsupp.SumProd

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

section Algebra

/-- The instance `Algebra k (MonoidAlgebra A G)` whenever we have `Algebra k A`.

In particular this provides the instance `Algebra k (MonoidAlgebra k G)`.
-/
instance algebra {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    Algebra k (MonoidAlgebra A G) where
  algebraMap := singleOneRingHom.comp (algebraMap k A)
  smul_def' := fun r a => by
    ext
    rw [Finsupp.coe_smul]
    simp [single_one_mul_apply, Algebra.smul_def, Pi.smul_apply]
  commutes' := fun r f => by
    refine Finsupp.ext fun _ => ?_
    simp [single_one_mul_apply, mul_single_one_apply, Algebra.commutes]

/-- `Finsupp.single 1` as an `AlgHom` -/
@[simps! apply]
def singleOneAlgHom {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    A →ₐ[k] MonoidAlgebra A G :=
  { singleOneRingHom with
    commutes' := fun r => by
      ext
      simp
      rfl }

@[simp]
theorem coe_algebraMap {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    ⇑(algebraMap k (MonoidAlgebra A G)) = single 1 ∘ algebraMap k A :=
  rfl

theorem single_eq_algebraMap_mul_of [CommSemiring k] [Monoid G] (a : G) (b : k) :
    single a b = algebraMap k (MonoidAlgebra k G) b * of k G a := by simp

theorem single_algebraMap_eq_algebraMap_mul_of {A : Type*} [CommSemiring k] [Semiring A]
    [Algebra k A] [Monoid G] (a : G) (b : k) :
    single a (algebraMap k A b) = algebraMap k (MonoidAlgebra A G) b * of A G a := by simp

instance isLocalHom_singleOneAlgHom
    {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    IsLocalHom (singleOneAlgHom : A →ₐ[k] MonoidAlgebra A G) where
  map_nonunit := isLocalHom_singleOneRingHom.map_nonunit

instance isLocalHom_algebraMap
    {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G]
    [IsLocalHom (algebraMap k A)] :
    IsLocalHom (algebraMap k (MonoidAlgebra A G)) where
  map_nonunit _ hx := .of_map _ _ <| isLocalHom_singleOneAlgHom (k := k).map_nonunit _ hx

end Algebra

section lift

variable [CommSemiring k] [Monoid G] [Monoid H]
variable {A : Type u₃} [Semiring A] [Algebra k A] {B : Type*} [Semiring B] [Algebra k B]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
def liftNCAlgHom (f : A →ₐ[k] B) (g : G →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    MonoidAlgebra A G →ₐ[k] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

/-- A `k`-algebra homomorphism from `MonoidAlgebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
theorem algHom_ext ⦃φ₁ φ₂ : MonoidAlgebra k G →ₐ[k] A⦄
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  AlgHom.toLinearMap_injective <| Finsupp.lhom_ext' fun a => LinearMap.ext_ring (h a)

-- The priority must be `high`.
/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem algHom_ext' ⦃φ₁ φ₂ : MonoidAlgebra k G →ₐ[k] A⦄
    (h :
      (φ₁ : MonoidAlgebra k G →* A).comp (of k G) = (φ₂ : MonoidAlgebra k G →* A).comp (of k G)) :
    φ₁ = φ₂ :=
  algHom_ext <| DFunLike.congr_fun h

variable (k G A)

/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
`MonoidAlgebra k G →ₐ[k] A`. -/
def lift : (G →* A) ≃ (MonoidAlgebra k G →ₐ[k] A) where
  invFun f := (f : MonoidAlgebra k G →* A).comp (of k G)
  toFun F := liftNCAlgHom (Algebra.ofId k A) F fun _ _ => Algebra.commutes _ _
  left_inv f := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]
  right_inv F := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]

variable {k G H A}

theorem lift_apply' (F : G →* A) (f : MonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b => algebraMap k A b * F a :=
  rfl

theorem lift_apply (F : G →* A) (f : MonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b => b • F a := by simp only [lift_apply', Algebra.smul_def]

theorem lift_def (F : G →* A) : ⇑(lift k G A F) = liftNC ((algebraMap k A : k →+* A) : k →+ A) F :=
  rfl

@[simp]
theorem lift_symm_apply (F : MonoidAlgebra k G →ₐ[k] A) (x : G) :
    (lift k G A).symm F x = F (single x 1) :=
  rfl

@[simp]
theorem lift_single (F : G →* A) (a b) : lift k G A F (single a b) = b • F a := by
  rw [lift_def, liftNC_single, Algebra.smul_def, AddMonoidHom.coe_coe]

theorem lift_of (F : G →* A) (x) : lift k G A F (of k G x) = F x := by simp

theorem lift_unique' (F : MonoidAlgebra k G →ₐ[k] A) :
    F = lift k G A ((F : MonoidAlgebra k G →* A).comp (of k G)) :=
  ((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `MonoidAlgebra k G` by
its values on `F (single a 1)`. -/
theorem lift_unique (F : MonoidAlgebra k G →ₐ[k] A) (f : MonoidAlgebra k G) :
    F f = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

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

@[simp] lemma domCongr_comp_lsingle (e : G ≃* H) (g : G) :
    (domCongr k A e).toLinearMap ∘ₗ lsingle g = lsingle (e g) := by ext; simp

@[simp] theorem domCongr_refl : domCongr k A (MulEquiv.refl G) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ => Finsupp.ext fun _ => rfl

@[simp] theorem domCongr_symm (e : G ≃* H) : (domCongr k A e).symm = domCongr k A e.symm := rfl

end lift

section

variable (k)

/-- When `V` is a `k[G]`-module, multiplication by a group element `g` is a `k`-linear map. -/
def GroupSMul.linearMap [Monoid G] [CommSemiring k] (V : Type u₃) [AddCommMonoid V] [Module k V]
    [Module (MonoidAlgebra k G) V] [IsScalarTower k (MonoidAlgebra k G) V] (g : G) : V →ₗ[k] V where
  toFun v := single g (1 : k) • v
  map_add' x y := smul_add (single g (1 : k)) x y
  map_smul' _c _x := smul_algebra_smul_comm _ _ _

@[simp]
theorem GroupSMul.linearMap_apply [Monoid G] [CommSemiring k] (V : Type u₃) [AddCommMonoid V]
    [Module k V] [Module (MonoidAlgebra k G) V] [IsScalarTower k (MonoidAlgebra k G) V] (g : G)
    (v : V) : (GroupSMul.linearMap k V g) v = single g (1 : k) • v :=
  rfl

section

variable {k}
variable [Monoid G] [CommSemiring k] {V : Type u₃} {W : Type u₄} [AddCommMonoid V] [Module k V]
  [Module (MonoidAlgebra k G) V] [IsScalarTower k (MonoidAlgebra k G) V] [AddCommMonoid W]
  [Module k W] [Module (MonoidAlgebra k G) W] [IsScalarTower k (MonoidAlgebra k G) W]
  (f : V →ₗ[k] W)

/-- Build a `k[G]`-linear map from a `k`-linear map and evidence that it is `G`-equivariant. -/
def equivariantOfLinearOfComm
    (h : ∀ (g : G) (v : V), f (single g (1 : k) • v) = single g (1 : k) • f v) :
    V →ₗ[MonoidAlgebra k G] W where
  toFun := f
  map_add' v v' := by simp
  map_smul' c v := by
    refine Finsupp.induction c ?_ ?_
    · simp
    · intro g r c' _nm _nz w
      dsimp at *
      simp only [add_smul, f.map_add, w, single_eq_algebraMap_mul_of, ← smul_smul]
      rw [algebraMap_smul (MonoidAlgebra k G) r, algebraMap_smul (MonoidAlgebra k G) r, f.map_smul,
        of_apply, h g v]

variable (h : ∀ (g : G) (v : V), f (single g (1 : k) • v) = single g (1 : k) • f v)

@[simp]
theorem equivariantOfLinearOfComm_apply (v : V) : (equivariantOfLinearOfComm f h) v = f v :=
  rfl

end

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
      { (MonoidAlgebra.liftMagma k f :) with
        toFun := fun a => sum a fun m t => t • f (Multiplicative.ofAdd m) }
    invFun := fun F => F.toMulHom.comp (ofMagma k G) }

end NonUnitalNonAssocAlgebra

/-! #### Algebra structure -/


section Algebra

/-- The instance `Algebra R k[G]` whenever we have `Algebra R k`.

In particular this provides the instance `Algebra k k[G]`.
-/
instance algebra [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] :
    Algebra R k[G] where
  algebraMap := singleZeroRingHom.comp (algebraMap R k)
  smul_def' := fun r a => by
    ext
    rw [Finsupp.coe_smul]
    simp [single_zero_mul_apply, Algebra.smul_def, Pi.smul_apply]
  commutes' := fun r f => by
    refine Finsupp.ext fun _ => ?_
    simp [single_zero_mul_apply, mul_single_zero_apply, Algebra.commutes]

/-- `Finsupp.single 0` as an `AlgHom` -/
@[simps! apply]
def singleZeroAlgHom [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] : k →ₐ[R] k[G] :=
  { singleZeroRingHom with
    commutes' := fun r => by
      ext
      simp
      rfl }

@[simp]
theorem coe_algebraMap [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] :
    (algebraMap R k[G] : R → k[G]) = single 0 ∘ algebraMap R k :=
  rfl

instance isLocalHom_singleZeroAlgHom [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] :
    IsLocalHom (singleZeroAlgHom : k →ₐ[R] k[G]) where
  map_nonunit := isLocalHom_singleZeroRingHom.map_nonunit

instance isLocalHom_algebraMap [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G]
    [IsLocalHom (algebraMap R k)] :
    IsLocalHom (algebraMap R k[G]) where
  map_nonunit _ hx := .of_map _ _ <| isLocalHom_singleZeroAlgHom (R := R).map_nonunit _ hx

end Algebra

section lift

variable [CommSemiring k] [AddMonoid G]
variable {A : Type u₃} [Semiring A] [Algebra k A] {B : Type*} [Semiring B] [Algebra k B]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
def liftNCAlgHom (f : A →ₐ[k] B) (g : Multiplicative G →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    A[G] →ₐ[k] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

/-- A `k`-algebra homomorphism from `k[G]` is uniquely defined by its
values on the functions `single a 1`. -/
theorem algHom_ext ⦃φ₁ φ₂ : k[G] →ₐ[k] A⦄
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  @MonoidAlgebra.algHom_ext k (Multiplicative G) _ _ _ _ _ _ _ h

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem algHom_ext' ⦃φ₁ φ₂ : k[G] →ₐ[k] A⦄
    (h : (φ₁ : k[G] →* A).comp (of k G) = (φ₂ : k[G] →* A).comp (of k G)) :
    φ₁ = φ₂ :=
  algHom_ext <| DFunLike.congr_fun h

variable (k G A)

/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
`k[G] →ₐ[k] A`. -/
def lift : (Multiplicative G →* A) ≃ (k[G] →ₐ[k] A) :=
  { @MonoidAlgebra.lift k (Multiplicative G) _ _ A _ _ with
    invFun := fun f => (f : k[G] →* A).comp (of k G)
    toFun := fun F =>
      { @MonoidAlgebra.lift k (Multiplicative G) _ _ A _ _ F with
        toFun := liftNCAlgHom (Algebra.ofId k A) F fun _ _ => Algebra.commutes _ _ } }

variable {k G A}

theorem lift_apply' (F : Multiplicative G →* A) (f : MonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b => algebraMap k A b * F (Multiplicative.ofAdd a) :=
  rfl

theorem lift_apply (F : Multiplicative G →* A) (f : MonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b => b • F (Multiplicative.ofAdd a) := by
  simp only [lift_apply', Algebra.smul_def]

theorem lift_def (F : Multiplicative G →* A) :
    ⇑(lift k G A F) = liftNC ((algebraMap k A : k →+* A) : k →+ A) F :=
  rfl

@[simp]
theorem lift_symm_apply (F : k[G] →ₐ[k] A) (x : Multiplicative G) :
    (lift k G A).symm F x = F (single x.toAdd 1) :=
  rfl

theorem lift_of (F : Multiplicative G →* A) (x : Multiplicative G) :
    lift k G A F (of k G x) = F x := MonoidAlgebra.lift_of F x

@[simp]
theorem lift_single (F : Multiplicative G →* A) (a b) :
    lift k G A F (single a b) = b • F (Multiplicative.ofAdd a) :=
  MonoidAlgebra.lift_single F (.ofAdd a) b

lemma lift_of' (F : Multiplicative G →* A) (x : G) :
    lift k G A F (of' k G x) = F (Multiplicative.ofAdd x) :=
  lift_of F x

theorem lift_unique' (F : k[G] →ₐ[k] A) :
    F = lift k G A ((F : k[G] →* A).comp (of k G)) :=
  ((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `MonoidAlgebra k G` by
its values on `F (single a 1)`. -/
theorem lift_unique (F : k[G] →ₐ[k] A) (f : MonoidAlgebra k G) :
    F f = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

theorem algHom_ext_iff {φ₁ φ₂ : k[G] →ₐ[k] A} :
    (∀ x, φ₁ (Finsupp.single x 1) = φ₂ (Finsupp.single x 1)) ↔ φ₁ = φ₂ :=
  ⟨fun h => algHom_ext h, by rintro rfl _; rfl⟩

end lift

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

@[simp] lemma domCongr_comp_lsingle (e : G ≃+ H) (g : G) :
    (domCongr k A e).toLinearMap ∘ₗ lsingle g = lsingle (e g) := by ext; simp

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
