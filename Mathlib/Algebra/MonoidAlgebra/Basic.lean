/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.LinearAlgebra.Finsupp.SumProd

/-!
# Monoid algebras

-/

@[expose] public noncomputable section

open Finset

open Finsupp hiding single mapDomain

variable {k G H R S T A B M N : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

/-! #### Non-unital, non-associative algebra structure -/


section NonUnitalNonAssocAlgebra

variable (k) [Semiring k] [DistribSMul R k] [Mul G] [NonUnitalNonAssocSemiring A]

/-- A non-unital `k`-algebra homomorphism from `k[G]` is uniquely defined by its
values on the functions `single a 1`. -/
@[to_additive (dont_translate := k) /--
A non-unital `k`-algebra homomorphism from `k[G]` is uniquely defined by its
values on the functions `single a 1`. -/]
theorem nonUnitalAlgHom_ext [DistribMulAction k A] {φ₁ φ₂ : k[G] →ₙₐ[k] A}
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  NonUnitalAlgHom.to_distribMulActionHom_injective <|
    Finsupp.distribMulActionHom_ext' fun a => DistribMulActionHom.ext_ring (h a)

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem nonUnitalAlgHom_ext' [DistribMulAction k A] {φ₁ φ₂ : k[G] →ₙₐ[k] A}
    (h : φ₁.toMulHom.comp (ofMagma k G) = φ₂.toMulHom.comp (ofMagma k G)) : φ₁ = φ₂ :=
  nonUnitalAlgHom_ext k <| DFunLike.congr_fun h

/-- The functor `G ↦ k[G]`, from the category of magmas to the category of non-unital,
non-associative algebras over `k` is adjoint to the forgetful functor in the other direction. -/
@[simps apply_apply symm_apply]
def liftMagma [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] :
    (G →ₙ* A) ≃ (k[G] →ₙₐ[k] A) where
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
  left_inv f := by ext; simp
  right_inv F := by ext; simp

end NonUnitalNonAssocAlgebra

/-! #### Algebra structure -/

section Algebra

/-- The instance `Algebra k A[G]` whenever we have `Algebra k A`.

In particular this provides the instance `Algebra k k[G]`. -/
@[to_additive (dont_translate := k A)
/-- The instance `Algebra R k[G]` whenever we have `Algebra R k`.

In particular this provides the instance `Algebra k k[G]`. -/]
instance algebra {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    Algebra k A[G] where
  algebraMap := singleOneRingHom.comp (algebraMap k A)
  smul_def' := fun r a => by
    ext
    dsimp
    rw [single_one_mul_apply, Algebra.smul_def]
  commutes' := fun r f => by
    ext
    dsimp
    rw [single_one_mul_apply, mul_single_one_apply, Algebra.commutes]

/-- `Finsupp.single 1` as an `AlgHom` -/
@[to_additive (dont_translate := k A) (attr := simps! apply) /--
`Finsupp.single 0` as an `AlgHom` -/]
def singleOneAlgHom {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    A →ₐ[k] A[G] :=
  { singleOneRingHom with
    commutes' := fun r => by
      ext
      simp
      rfl }

@[to_additive (attr := simp)]
theorem coe_algebraMap {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    ⇑(algebraMap k A[G]) = single 1 ∘ algebraMap k A :=
  rfl

theorem single_eq_algebraMap_mul_of [CommSemiring k] [Monoid G] (a : G) (b : k) :
    single a b = algebraMap k k[G] b * of k G a := by simp

theorem single_algebraMap_eq_algebraMap_mul_of {A : Type*} [CommSemiring k] [Semiring A]
    [Algebra k A] [Monoid G] (a : G) (b : k) :
    single a (algebraMap k A b) = algebraMap k A[G] b * of A G a := by simp

@[to_additive]
instance isLocalHom_singleOneAlgHom
    {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    IsLocalHom (singleOneAlgHom : A →ₐ[k] A[G]) where
  map_nonunit := isLocalHom_singleOneRingHom.map_nonunit

@[to_additive (dont_translate := k)]
instance isLocalHom_algebraMap
    {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G]
    [IsLocalHom (algebraMap k A)] :
    IsLocalHom (algebraMap k A[G]) where
  map_nonunit _ hx := .of_map _ _ <| isLocalHom_singleOneAlgHom (k := k).map_nonunit _ hx

end Algebra

section lift

variable [CommSemiring k] [Monoid G] [Monoid H] [Semiring A] [Algebra k A] [Semiring B]
  [Algebra k B]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
def liftNCAlgHom (f : A →ₐ[k] B) (g : G →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    A[G] →ₐ[k] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

@[simp] lemma coe_liftNCAlgHom (f : A →ₐ[k] B) (g : G →* B) (h_comm) :
    ⇑(liftNCAlgHom f g h_comm) = liftNC f g := rfl

/-- A `k`-algebra homomorphism from `k[G]` is uniquely defined by its
values on the functions `single a 1`. -/
@[to_additive (dont_translate := k) /--
A `k`-algebra homomorphism from `k[G]` is uniquely defined by its
values on the functions `single a 1`. -/]
theorem algHom_ext ⦃φ₁ φ₂ : k[G] →ₐ[k] A⦄ (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  AlgHom.toLinearMap_injective <| lhom_ext' fun a ↦ LinearMap.ext_ring (h a)

-- The priority must be `high`.
/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem algHom_ext' ⦃φ₁ φ₂ : k[G] →ₐ[k] A⦄
    (h :
      (φ₁ : k[G] →* A).comp (of k G) = (φ₂ : k[G] →* A).comp (of k G)) :
    φ₁ = φ₂ :=
  algHom_ext <| DFunLike.congr_fun h

variable (k G A) in
/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism `k[G] →ₐ[k] A`. -/
def lift : (G →* A) ≃ (k[G] →ₐ[k] A) where
  toFun F := liftNCAlgHom (Algebra.ofId k A) F fun _ _ ↦ Algebra.commutes _ _
  invFun f := (f : k[G] →* A).comp (of k G)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

theorem lift_apply' (F : G →* A) (f : k[G]) :
    lift k G A F f = f.sum fun a b => algebraMap k A b * F a :=
  rfl

theorem lift_apply (F : G →* A) (f : k[G]) :
    lift k G A F f = f.sum fun a b => b • F a := by simp only [lift_apply', Algebra.smul_def]

theorem lift_def (F : G →* A) : ⇑(lift k G A F) = liftNC ((algebraMap k A : k →+* A) : k →+ A) F :=
  rfl

@[simp]
theorem lift_symm_apply (F : k[G] →ₐ[k] A) (x : G) : (lift k G A).symm F x = F (single x 1) := rfl

@[simp]
theorem lift_single (F : G →* A) (a b) : lift k G A F (single a b) = b • F a := by
  rw [lift_def, liftNC_single, Algebra.smul_def, AddMonoidHom.coe_coe]

theorem lift_of (F : G →* A) (x) : lift k G A F (of k G x) = F x := by simp

theorem lift_unique' (F : k[G] →ₐ[k] A) : F = lift k G A ((F : k[G] →* A).comp (of k G)) :=
  ((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `k[G]` by
its values on `F (single a 1)`. -/
theorem lift_unique (F : k[G] →ₐ[k] A) (f : k[G]) :
    F f = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

/-- If `f : G → H` is a homomorphism between two magmas, then
`Finsupp.mapDomain f` is a non-unital algebra homomorphism between their magma algebras. -/
@[to_additive (dont_translate := k) (attr := simps apply) /--
If `f : G → H` is a homomorphism between two additive magmas, then `Finsupp.mapDomain f` is a
non-unital algebra homomorphism between their additive magma algebras. -/]
def mapDomainNonUnitalAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A]
    {G H F : Type*} [Mul G] [Mul H] [FunLike F G H] [MulHomClass F G H] (f : F) :
    A[G] →ₙₐ[k] A[H] :=
  { (Finsupp.mapDomain.addMonoidHom f : A[G] →+ A[H]) with
    map_mul' := fun x y => mapDomain_mul f x y
    map_smul' := fun r x => mapDomain_smul r x }

variable (A) in
@[to_additive]
theorem mapDomain_algebraMap {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F) (r : k) :
    mapDomain f (algebraMap k A[G] r) = algebraMap k A[H] r := by
  simp only [coe_algebraMap, mapDomain_single, map_one, (· ∘ ·)]

/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`Finsupp.mapDomain f` is an algebra homomorphism between their monoid algebras. -/
@[to_additive (attr := simps!) /--
If `f : G → H` is an additive homomorphism between two additive monoids, then
`Finsupp.mapDomain f` is an algebra homomorphism between their additive monoid algebras. -/]
def mapDomainAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] {H F : Type*}
    [Monoid H] [FunLike F G H] [MonoidHomClass F G H] (f : F) :
    A[G] →ₐ[k] A[H] :=
  { mapDomainRingHom A f with commutes' := mapDomain_algebraMap A f }

@[to_additive (attr := simp)]
lemma mapDomainAlgHom_id (k A) [CommSemiring k] [Semiring A] [Algebra k A] :
    mapDomainAlgHom k A (MonoidHom.id G) = AlgHom.id k A[G] := by
  ext; simp [MonoidHom.id, ← Function.id_def]

@[to_additive (attr := simp)]
lemma mapDomainAlgHom_comp (k A) {G₁ G₂ G₃} [CommSemiring k] [Semiring A] [Algebra k A]
    [Monoid G₁] [Monoid G₂] [Monoid G₃] (f : G₁ →* G₂) (g : G₂ →* G₃) :
    mapDomainAlgHom k A (g.comp f) = (mapDomainAlgHom k A g).comp (mapDomainAlgHom k A f) := by
  ext; simp [mapDomain_comp]

variable (k A)

/-- If `e : G ≃* H` is a multiplicative equivalence between two monoids, then
`MonoidAlgebra.domCongr e` is an algebra equivalence between their monoid algebras. -/
@[to_additive (dont_translate := A)
/-- If `e : G ≃+ H` is an additive equivalence between two additive monoids, then
`AddMonoidAlgebra.domCongr e` is an algebra equivalence between their additive monoid algebras. -/]
def domCongr (e : G ≃* H) : A[G] ≃ₐ[k] A[H] where
  toRingEquiv := mapDomainRingEquiv A e
  __ := Finsupp.domLCongr (R := k) (M := A) e.toEquiv
  commutes' _ := by ext; simp

@[to_additive (attr := simp)]
lemma domCongr_apply (e : G ≃* H) (x : A[G]) (h : H) : domCongr k A e x h = x (e.symm h) := by
  simp [domCongr]

@[to_additive]
theorem domCongr_toAlgHom (e : G ≃* H) : (domCongr k A e).toAlgHom = mapDomainAlgHom k A e := rfl

@[to_additive (attr := simp)]
lemma domCongr_support (e : G ≃* H) (f : A[G]) : (domCongr k A e f).support = f.support.map e := by
  ext; simp

@[to_additive (attr := simp)]
theorem domCongr_single (e : G ≃* H) (g : G) (a : A) :
    domCongr k A e (single g a) = single (e g) a := by simp [domCongr]

@[to_additive (attr := simp)]
lemma domCongr_comp_lsingle (e : G ≃* H) (g : G) :
    (domCongr k A e).toLinearMap ∘ₗ lsingle g = lsingle (e g) := by ext; simp

@[to_additive (attr := simp)]
theorem domCongr_refl : domCongr k A (.refl G) = .refl := by ext; simp

@[to_additive (attr := simp)]
theorem domCongr_symm (e : G ≃* H) : (domCongr k A e).symm = domCongr k A e.symm := rfl

end lift

section mapRange
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [Monoid M] [Monoid N]

@[to_additive (attr := simp)]
lemma mapDomainRingHom_comp_algebraMap (f : M →* N) :
    (mapDomainRingHom A f).comp (algebraMap R A[M]) = algebraMap R A[N] := by ext; simp

@[to_additive (attr := simp)]
lemma mapRangeRingHom_comp_algebraMap (f : R →+* S) :
    (mapRangeRingHom (M := M) f).comp (algebraMap _ _) = (algebraMap _ _).comp f := by ext; simp

variable (M) in
/-- The algebra homomorphism of monoid algebras induced by a homomorphism of the base algebras. -/
@[to_additive
/-- The algebra homomorphism of additive monoid algebras induced by a homomorphism of the base
algebras. -/]
noncomputable def mapRangeAlgHom (f : A →ₐ[R] B) : A[M] →ₐ[R] B[M] where
  __ := mapRangeRingHom M f
  commutes' := by simp

variable (M) in
@[to_additive (attr := simp)]
lemma toRingHom_mapRangeAlgHom (f : A →ₐ[R] B) :
    mapRangeAlgHom M f = mapRangeRingHom M f.toRingHom := rfl

@[to_additive (attr := simp)]
lemma mapRangeAlgHom_apply (f : A →ₐ[R] B) (x : A[M]) (m : M) :
    mapRangeAlgHom M f x m = f (x m) := mapRangeRingHom_apply f.toRingHom x m

@[to_additive (attr := simp)]
lemma mapRangeAlgHom_single (f : A →ₐ[R] B) (m : M) (a : A) :
    mapRangeAlgHom M f (single m a) = single m (f a) := by
  classical ext; simp [single_apply, apply_ite f]

variable (R M) in
/-- The algebra isomorphism of monoid algebras induced by an isomorphism of the base algebras. -/
@[to_additive (attr := simps apply)
/-- The algebra isomorphism of additive monoid algebras induced by an isomorphism of the base
algebras. -/]
noncomputable def mapRangeAlgEquiv (e : A ≃ₐ[R] B) : A[M] ≃ₐ[R] B[M] where
  __ := mapRangeAlgHom M e
  invFun := mapRangeAlgHom M (e.symm : B →ₐ[R] A)
  left_inv _ := by aesop
  right_inv _ := by aesop

@[simp] lemma symm_mapRangeAlgEquiv (e : A ≃ₐ[R] B) :
    (mapRangeAlgEquiv R M e).symm = mapRangeAlgEquiv R M e.symm := rfl

end mapRange

section

variable (k) in
/-- When `V` is a `k[G]`-module, multiplication by a group element `g` is a `k`-linear map. -/
def GroupSMul.linearMap [Monoid G] [CommSemiring k] (V : Type*) [AddCommMonoid V] [Module k V]
    [Module k[G] V] [IsScalarTower k k[G] V] (g : G) : V →ₗ[k] V where
  toFun v := single g (1 : k) • v
  map_add' x y := smul_add (single g (1 : k)) x y
  map_smul' _c _x := smul_algebra_smul_comm _ _ _

variable (k) in
@[simp]
theorem GroupSMul.linearMap_apply [Monoid G] [CommSemiring k] (V : Type*) [AddCommMonoid V]
    [Module k V] [Module k[G] V] [IsScalarTower k k[G] V] (g : G) (v : V) :
    (GroupSMul.linearMap k V g) v = single g (1 : k) • v :=
  rfl

variable [Monoid G] [CommSemiring k] {V W : Type*} [AddCommMonoid V] [Module k V]
  [Module k[G] V] [IsScalarTower k k[G] V] [AddCommMonoid W]
  [Module k W] [Module k[G] W] [IsScalarTower k k[G] W]
  (f : V →ₗ[k] W)

/-- Build a `k[G]`-linear map from a `k`-linear map and evidence that it is `G`-equivariant. -/
def equivariantOfLinearOfComm
    (h : ∀ (g : G) (v : V), f (single g (1 : k) • v) = single g (1 : k) • f v) :
    V →ₗ[k[G]] W where
  toFun := f
  map_add' v v' := by simp
  map_smul' c v := by
    refine Finsupp.induction c ?_ ?_
    · simp
    · intro g r c' _nm _nz w
      dsimp at *
      simp only [add_smul, f.map_add, w, single_eq_algebraMap_mul_of, ← smul_smul]
      rw [algebraMap_smul, algebraMap_smul, f.map_smul, of_apply, h g v]

variable (h : ∀ (g : G) (v : V), f (single g (1 : k) • v) = single g (1 : k) • f v)

@[simp]
theorem equivariantOfLinearOfComm_apply (v : V) : (equivariantOfLinearOfComm f h) v = f v :=
  rfl

end

variable [CommMonoid M] [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- If `S` is an `R`-algebra, then `S[M]` is a `R[M]` algebra.

Warning: This produces a diamond for `Algebra R[M] S[M][M]` and another one for `Algebra R[M] R[M]`.
That's why it is not a global instance. -/
@[to_additive
/-- If `S` is an `R`-algebra, then `S[M]` is an `R[M]`-algebra.

Warning: This produces a diamond for `Algebra R[M] S[M][M]` and another one for `Algebra R[M] R[M]`.
That's why it is not a global instance. -/]
noncomputable abbrev algebraMonoidAlgebra : Algebra R[M] S[M] :=
  (mapRangeRingHom M (algebraMap R S)).toAlgebra

scoped[AlgebraMonoidAlgebra] attribute [instance] MonoidAlgebra.algebraMonoidAlgebra
  AddMonoidAlgebra.algebraAddMonoidAlgebra

open scoped AlgebraMonoidAlgebra

@[to_additive (attr := simp)]
lemma algebraMap_def : algebraMap R[M] S[M] = mapRangeRingHom M (algebraMap R S) := rfl

@[to_additive (dont_translate := R)]
lemma isScalarTower_monoidAlgebra [CommSemiring T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] : IsScalarTower R S[M] T[M] :=
  .of_algebraMap_eq' (mapRangeAlgHom _ (IsScalarTower.toAlgHom R S T)).comp_algebraMap.symm

scoped[AlgebraMonoidAlgebra] attribute [instance] MonoidAlgebra.isScalarTower_monoidAlgebra
  AddMonoidAlgebra.vaddAssocClass_addMonoidAlgebra

end MonoidAlgebra

namespace AddMonoidAlgebra

/-! #### Non-unital, non-associative algebra structure -/

section NonUnitalNonAssocAlgebra

variable (k) [Semiring k] [DistribSMul R k] [Add G] [NonUnitalNonAssocSemiring A]

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem nonUnitalAlgHom_ext' [DistribMulAction k A] {φ₁ φ₂ : k[G] →ₙₐ[k] A}
    (h : φ₁.toMulHom.comp (ofMagma k G) = φ₂.toMulHom.comp (ofMagma k G)) : φ₁ = φ₂ :=
  nonUnitalAlgHom_ext k <| DFunLike.congr_fun h

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

section lift

variable [CommSemiring k] [AddMonoid G] [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
def liftNCAlgHom (f : A →ₐ[k] B) (g : Multiplicative G →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    A[G] →ₐ[k] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

@[simp] lemma coe_liftNCAlgHom (f : A →ₐ[k] B) (g : Multiplicative G →* B) (h_comm) :
    ⇑(liftNCAlgHom f g h_comm) = liftNC f g := rfl

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem algHom_ext' ⦃φ₁ φ₂ : k[G] →ₐ[k] A⦄
    (h : (φ₁ : k[G] →* A).comp (of k G) = (φ₂ : k[G] →* A).comp (of k G)) :
    φ₁ = φ₂ :=
  algHom_ext <| DFunLike.congr_fun h

variable (k G A) in
/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
`k[G] →ₐ[k] A`. -/
def lift : (Multiplicative G →* A) ≃ (k[G] →ₐ[k] A) where
  toFun F := liftNCAlgHom (Algebra.ofId k A) F fun _ _ => Algebra.commutes _ _
  invFun f := (f : k[G] →* A).comp (of k G)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

theorem lift_apply' (F : Multiplicative G →* A) (f : k[G]) :
    lift k G A F f = f.sum fun a b => algebraMap k A b * F (Multiplicative.ofAdd a) :=
  rfl

theorem lift_apply (F : Multiplicative G →* A) (f : k[G]) :
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

/-- Decomposition of a `k`-algebra homomorphism from `k[G]` by
its values on `F (single a 1)`. -/
theorem lift_unique (F : k[G] →ₐ[k] A) (f : k[G]) :
    F f = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

lemma algHom_ext_iff {φ₁ φ₂ : k[G] →ₐ[k] A} : (∀ x, φ₁ (single x 1) = φ₂ (single x 1)) ↔ φ₁ = φ₂ :=
  ⟨fun h => algHom_ext h, by rintro rfl _; rfl⟩

end lift

end AddMonoidAlgebra

variable [CommSemiring R]

variable (k G) in
/-- The algebra equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative`. -/
def AddMonoidAlgebra.toMultiplicativeAlgEquiv [Semiring k] [Algebra R k] [AddMonoid G] :
    AddMonoidAlgebra k G ≃ₐ[R] MonoidAlgebra k (Multiplicative G) :=
  { AddMonoidAlgebra.toMultiplicative k G with
    commutes' := fun r => by simp [AddMonoidAlgebra.toMultiplicative] }

variable (k G) in
/-- The algebra equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of
`Additive`. -/
def MonoidAlgebra.toAdditiveAlgEquiv [Semiring k] [Algebra R k] [Monoid G] :
    MonoidAlgebra k G ≃ₐ[R] AddMonoidAlgebra k (Additive G) :=
  { MonoidAlgebra.toAdditive k G with commutes' := fun r => by simp [MonoidAlgebra.toAdditive] }
