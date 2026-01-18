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
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Algebra structure on monoid algebras

-/

@[expose] public noncomputable section

open Finset

open Finsupp hiding single mapDomain

variable {R S T A B C M N O : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

/-! #### Non-unital, non-associative algebra structure -/


section NonUnitalNonAssocAlgebra

variable (R) [Semiring R] [Mul M] [NonUnitalNonAssocSemiring A]

/-- A non-unital `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the monomials `single a 1`. -/
@[to_additive (dont_translate := R) /--
A non-unital `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the monomials `single a 1`. -/]
theorem nonUnitalAlgHom_ext [DistribMulAction R A] {φ₁ φ₂ : R[M] →ₙₐ[R] A}
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  NonUnitalAlgHom.to_distribMulActionHom_injective <|
    Finsupp.distribMulActionHom_ext' fun a => DistribMulActionHom.ext_ring (h a)

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem nonUnitalAlgHom_ext' [DistribMulAction R A] {φ₁ φ₂ : R[M] →ₙₐ[R] A}
    (h : φ₁.toMulHom.comp (ofMagma R M) = φ₂.toMulHom.comp (ofMagma R M)) : φ₁ = φ₂ :=
  nonUnitalAlgHom_ext R <| DFunLike.congr_fun h

/-- The functor `M ↦ R[M]`, from the category of magmas to the category of non-unital,
non-associative algebras over `R` is adjoint to the forgetful functor in the other direction. -/
@[simps apply_apply symm_apply]
def liftMagma [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    (M →ₙ* A) ≃ (R[M] →ₙₐ[R] A) where
  toFun f :=
    { liftAddHom fun x => (smulAddHom R A).flip (f x) with
      toFun := fun a => a.sum fun m t => t • f m
      map_smul' := fun t' a => by
        rw [Finsupp.smul_sum, sum_smul_index']
        · simp_rw [smul_assoc, MonoidHom.id_apply]
        · intro m
          exact zero_smul R (f m)
      map_mul' := fun a₁ a₂ => by
        let g : M → R → A := fun m t => t • f m
        have h₁ : ∀ m, g m 0 = 0 := by
          intro m
          exact zero_smul R (f m)
        have h₂ : ∀ (m) (t₁ t₂ : R), g m (t₁ + t₂) = g m t₁ + g m t₂ := by
          intros
          rw [← add_smul]
        -- Porting note: `reducible` cannot be `local` so proof gets long.
        simp_rw [Finsupp.mul_sum, Finsupp.sum_mul, smul_mul_smul_comm, ← f.map_mul, mul_def,
          sum_comm a₂ a₁]
        rw [sum_sum_index h₁ h₂]; congr; ext
        rw [sum_sum_index h₁ h₂]; congr; ext
        rw [sum_single_index (h₁ _)] }
  invFun F := F.toMulHom.comp (ofMagma R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

end NonUnitalNonAssocAlgebra

/-! #### Algebra structure -/

section Algebra
variable [CommSemiring R] [Semiring A] [Algebra R A] [Monoid M] [Monoid N]

/-- The instance `Algebra R A[M]` whenever we have `Algebra R A`.

In particular this provides the instance `Algebra R R[M]`. -/
@[to_additive (dont_translate := R A)
/-- The instance `Algebra R R[M]` whenever we have `Algebra R R`.

In particular this provides the instance `Algebra R R[M]`. -/]
instance algebra : Algebra R A[M] where
  algebraMap := singleOneRingHom.comp (algebraMap R A)
  smul_def' := fun r a => by
    ext
    dsimp
    rw [single_one_mul_apply, Algebra.smul_def]
  commutes' := fun r f => by
    ext
    dsimp
    rw [single_one_mul_apply, mul_single_one_apply, Algebra.commutes]

/-- `MonoidAlgebra.single 1` as an `AlgHom` -/
@[to_additive (dont_translate := R A) (attr := simps! apply)
/-- `AddMonoidAlgebra.single 0` as an `AlgHom` -/]
def singleOneAlgHom : A →ₐ[R] A[M] where
  __ := singleOneRingHom
  commutes' r := by ext; simp; rfl

@[to_additive (attr := simp)]
lemma coe_algebraMap : ⇑(algebraMap R A[M]) = single 1 ∘ algebraMap R A := rfl

lemma single_eq_algebraMap_mul_of (m : M) (r : R) :
    single m r = algebraMap R R[M] r * of R M m := by simp

theorem single_algebraMap_eq_algebraMap_mul_of (m : M) (r : R) :
    single m (algebraMap R A r) = algebraMap R A[M] r * of A M m := by simp

@[to_additive]
instance isLocalHom_singleOneAlgHom : IsLocalHom (singleOneAlgHom : A →ₐ[R] A[M]) where
  map_nonunit := isLocalHom_singleOneRingHom.map_nonunit

@[to_additive (dont_translate := R)]
instance isLocalHom_algebraMap [IsLocalHom (algebraMap R A)] :
    IsLocalHom (algebraMap R A[M]) where
  map_nonunit _ hx := .of_map _ _ <| isLocalHom_singleOneAlgHom (R := R).map_nonunit _ hx

variable (R M) in
/-- The trivial monoid algebra is the base ring. -/
@[to_additive (dont_translate := R A)
/-- The trivial monoid algebra is the base ring. -/]
def uniqueAlgEquiv [Unique M] : A[M] ≃ₐ[R] A where
  toRingEquiv := uniqueRingEquiv _
  commutes' r := by simp [Unique.eq_default]

variable [DecidableEq M]

variable (R) in
/-- A product monoid algebra is a nested monoid algebra. -/
@[to_additive (dont_translate := R A)
/-- A product monoid algebra is a nested monoid algebra. -/]
def curryAlgEquiv : A[M × N] ≃ₐ[R] A[N][M] where
  toRingEquiv := curryRingEquiv
  commutes' r := by
    ext
    simp [MonoidAlgebra, algebraMap, Algebra.algebraMap, singleOneRingHom, curryRingEquiv,
      EquivLike.toEquiv, singleAddHom, curryAddEquiv]

@[to_additive (attr := simp)]
lemma curryAlgEquiv_single (m : M) (n : N) (a : A) :
    curryAlgEquiv R (single (m, n) a) = single m (single n a) := by simp [curryAlgEquiv]

@[to_additive (attr := simp)]
lemma curryAlgEquiv_symm_single (m : M) (n : N) (a : A) :
    (curryAlgEquiv R).symm (single m <| single n a) = (single (m, n) a) := by
  classical exact Finsupp.uncurry_single ..

end Algebra

section lift
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
def liftNCAlgHom (f : A →ₐ[R] B) (g : M →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    A[M] →ₐ[R] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

@[simp] lemma coe_liftNCAlgHom (f : A →ₐ[R] B) (g : M →* B) (h_comm) :
    ⇑(liftNCAlgHom f g h_comm) = liftNC f g := rfl

/-- A `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the functions `single a 1`. -/
@[to_additive (dont_translate := R) /--
A `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the functions `single a 1`. -/]
theorem algHom_ext ⦃φ₁ φ₂ : R[M] →ₐ[R] A⦄ (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  AlgHom.toLinearMap_injective <| lhom_ext' fun a ↦ LinearMap.ext_ring (h a)

-- The priority must be `high`.
/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem algHom_ext' ⦃φ₁ φ₂ : R[M] →ₐ[R] A⦄
    (h : (φ₁ : R[M] →* A).comp (of R M) = (φ₂ : R[M] →* A).comp (of R M)) : φ₁ = φ₂ :=
  algHom_ext <| DFunLike.congr_fun h

variable (R A M) in
/-- Any monoid homomorphism `M →* A` can be lifted to an algebra homomorphism `R[M] →ₐ[R] A`. -/
def lift : (M →* A) ≃ (R[M] →ₐ[R] A) where
  toFun F := liftNCAlgHom (Algebra.ofId R A) F fun _ _ ↦ Algebra.commutes _ _
  invFun f := (f : R[M] →* A).comp (of R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

theorem lift_apply' (F : M →* A) (f : R[M]) :
    lift R A M F f = f.sum fun a b => algebraMap R A b * F a :=
  rfl

theorem lift_apply (F : M →* A) (f : R[M]) :
    lift R A M F f = f.sum fun a b => b • F a := by simp only [lift_apply', Algebra.smul_def]

theorem lift_def (F : M →* A) : ⇑(lift R A M F) = liftNC (algebraMap R A) F := rfl

@[simp]
theorem lift_symm_apply (F : R[M] →ₐ[R] A) (m : M) : (lift R A M).symm F m = F (single m 1) := rfl

@[simp]
theorem lift_single (F : M →* A) (a b) : lift R A M F (single a b) = b • F a := by
  rw [lift_def, liftNC_single, Algebra.smul_def, AddMonoidHom.coe_coe]

theorem lift_of (F : M →* A) (m : M) : lift R A M F (of R M m) = F m := by simp

theorem lift_unique' (F : R[M] →ₐ[R] A) : F = lift R A M ((F : R[M] →* A).comp (of R M)) :=
  ((lift R A M).apply_symm_apply F).symm

/-- Decomposition of a `R`-algebra homomorphism from `R[M]` by
its values on `F (single a 1)`. -/
theorem lift_unique (F : R[M] →ₐ[R] A) (f : R[M]) :
    F f = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

theorem lift_mapRangeRingHom_algebraMap [CommSemiring S] [Algebra S A]
    [Algebra R S] [IsScalarTower R S A]
    (f : M →* A) (x : R[M]) :
    lift _ _ _ f (mapRangeRingHom _ (algebraMap R S) x) = lift _ _ _ f x := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

/-- If `f : M → N` is a homomorphism between two magmas, then `MonoidAlgebra.mapDomain f`
is a non-unital algebra homomorphism between their magma algebras. -/
@[to_additive (dont_translate := R A) (attr := simps apply)
/-- If `f : M → N` is a homomorphism between two additive magmas,
then `AddMonoidAlgebra.mapDomain f` is a non-unital algebra homomorphism
between their additive magma algebras. -/]
def mapDomainNonUnitalAlgHom (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    [Mul M] [Mul N] (f : M →ₙ* N) : A[M] →ₙₐ[R] A[N] where
  __ := mapDomainNonUnitalRingHom A f
  map_mul' := mapDomain_mul f
  map_smul' _ _ := mapDomain_smul ..

variable (A) in
@[to_additive]
theorem mapDomain_algebraMap {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) (r : R) :
    mapDomain f (algebraMap R A[M] r) = algebraMap R A[N] r := by
  simp only [coe_algebraMap, mapDomain_single, map_one, (· ∘ ·)]

variable (R A) in
/-- If `f : M → N` is a monoid homomorphism, then `MonoidAlgebra.mapDomain f` is an algebra
homomorphism between their monoid algebras. -/
@[to_additive (dont_translate := R A) (attr := simps! apply)
/-- If `f : M → N` is an additive monoid homomorphism, then `MonoidAlgebra.mapDomain f` is an
algebra homomorphism between their additive monoid algebras. -/]
def mapDomainAlgHom (f : M →* N) : A[M] →ₐ[R] A[N] where
  toRingHom := mapDomainRingHom A f
  commutes' := by simp

@[to_additive (attr := simp)]
lemma mapDomainAlgHom_id : mapDomainAlgHom R A (.id M) = .id R A[M] := by
  ext; simp [MonoidHom.id, ← Function.id_def]

@[to_additive (attr := simp)]
lemma mapDomainAlgHom_comp (f : M →* N) (g : N →* O) :
    mapDomainAlgHom R A (g.comp f) = (mapDomainAlgHom R A g).comp (mapDomainAlgHom R A f) := by
  ext; simp [mapDomain_comp]

variable (R A) in
/-- If `e : M ≃* N` is a multiplicative equivalence between two monoids, then
`MonoidAlgebra.domCongr e` is an algebra equivalence between their monoid algebras. -/
@[to_additive (dont_translate := A)
/-- If `e : M ≃+ N` is an additive equivalence between two additive monoids, then
`AddMonoidAlgebra.domCongr e` is an algebra equivalence between their additive monoid algebras. -/]
def domCongr (e : M ≃* N) : A[M] ≃ₐ[R] A[N] where
  toRingEquiv := mapDomainRingEquiv A e
  commutes' _ := by ext; simp

@[to_additive (attr := simp)]
lemma domCongr_apply (e : M ≃* N) (x : A[M]) (n : N) : domCongr R A e x n = x (e.symm n) := by
  simp [domCongr]

@[to_additive]
theorem domCongr_toAlgHom (e : M ≃* N) : (domCongr R A e).toAlgHom = mapDomainAlgHom R A e := rfl

@[to_additive (attr := simp)]
lemma domCongr_support (e : M ≃* N) (f : A[M]) : (domCongr R A e f).support = f.support.map e := by
  ext; simp

@[to_additive (attr := simp)]
theorem domCongr_single (e : M ≃* N) (m : M) (a : A) :
    domCongr R A e (single m a) = single (e m) a := by simp [domCongr]

@[to_additive (attr := simp)]
lemma domCongr_comp_lsingle (e : M ≃* N) (m : M) :
    (domCongr R A e).toLinearMap ∘ₗ lsingle m = lsingle (e m) := by ext; simp

@[to_additive (attr := simp)]
theorem domCongr_refl : domCongr R A (.refl M) = .refl := by ext; simp

@[to_additive (attr := simp)]
theorem domCongr_symm (e : M ≃* N) : (domCongr R A e).symm = domCongr R A e.symm := rfl

variable [DecidableEq M] [DecidableEq N]

variable (R) in
/-- Nested monoid algebras can be taken in an arbitrary order. -/
@[to_additive (dont_translate := R)
/-- Nested monoid algebras can be taken in an arbitrary order. -/]
def commAlgEquiv : A[M][N] ≃ₐ[R] A[N][M] :=
  (curryAlgEquiv _).symm.trans <| .trans (domCongr _ _ <| .prodComm ..) (curryAlgEquiv _)

@[to_additive (attr := simp)]
lemma symm_commAlgEquiv : (commAlgEquiv R : A[M][N] ≃ₐ[R] A[N][M]).symm = commAlgEquiv R := rfl

@[to_additive (attr := simp)]
lemma commAlgEquiv_single_single (m : M) (n : N) (a : A) :
    commAlgEquiv R (single m <| single n a) = single n (single m a) :=
  commRingEquiv_single_single ..

end lift

section mapRange
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Monoid M] [Monoid N]

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

@[to_additive (attr := simp)]
lemma symm_mapRangeAlgEquiv (e : A ≃ₐ[R] B) :
    (mapRangeAlgEquiv R M e).symm = mapRangeAlgEquiv R M e.symm := rfl

@[to_additive (attr := simp)]
lemma mapRangeAlgEquiv_trans (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C) :
    mapRangeAlgEquiv R M (e₁.trans e₂) =
      (mapRangeAlgEquiv R M e₁).trans (mapRangeAlgEquiv R M e₂) := by ext; simp

end mapRange

section

variable (R) in
/-- When `V` is a `R[M]`-module, multiplication by a group element `g` is a `R`-linear map. -/
def GroupSMul.linearMap [Monoid M] [CommSemiring R] (V : Type*) [AddCommMonoid V] [Module R V]
    [Module R[M] V] [IsScalarTower R R[M] V] (g : M) : V →ₗ[R] V where
  toFun v := single g (1 : R) • v
  map_add' x y := smul_add (single g (1 : R)) x y
  map_smul' _c _x := smul_algebra_smul_comm _ _ _

variable (R) in
@[simp]
theorem GroupSMul.linearMap_apply [Monoid M] [CommSemiring R] (V : Type*) [AddCommMonoid V]
    [Module R V] [Module R[M] V] [IsScalarTower R R[M] V] (g : M) (v : V) :
    (GroupSMul.linearMap R V g) v = single g (1 : R) • v :=
  rfl

variable [Monoid M] [CommSemiring R] {V W : Type*} [AddCommMonoid V] [Module R V]
  [Module R[M] V] [IsScalarTower R R[M] V] [AddCommMonoid W]
  [Module R W] [Module R[M] W] [IsScalarTower R R[M] W]
  (f : V →ₗ[R] W)

/-- Build a `R[M]`-linear map from a `R`-linear map and evidence that it is `M`-equivariant. -/
def equivariantOfLinearOfComm
    (h : ∀ (g : M) (v : V), f (single g (1 : R) • v) = single g (1 : R) • f v) :
    V →ₗ[R[M]] W where
  toFun := f
  map_add' v v' := by simp
  map_smul' c v := by
    refine Finsupp.induction c ?_ ?_
    · simp
    · intro g r c' _nm _nz w
      dsimp at *
      simp only [add_smul, f.map_add, w, single_eq_algebraMap_mul_of, ← smul_smul]
      rw [algebraMap_smul, algebraMap_smul, f.map_smul, of_apply, h g v]

variable (h : ∀ (g : M) (v : V), f (single g (1 : R) • v) = single g (1 : R) • f v)

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

variable (R) [Semiring R] [Add M] [NonUnitalNonAssocSemiring A]

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem nonUnitalAlgHom_ext' [DistribMulAction R A] {φ₁ φ₂ : R[M] →ₙₐ[R] A}
    (h : φ₁.toMulHom.comp (ofMagma R M) = φ₂.toMulHom.comp (ofMagma R M)) : φ₁ = φ₂ :=
  nonUnitalAlgHom_ext R <| DFunLike.congr_fun h

/-- The functor `M ↦ R[M]`, from the category of magmas to the category of
non-unital, non-associative algebras over `R` is adjoint to the forgetful functor in the other
direction. -/
@[simps apply_apply symm_apply]
def liftMagma [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    (Multiplicative M →ₙ* A) ≃ (R[M] →ₙₐ[R] A) :=
  { (MonoidAlgebra.liftMagma R : (Multiplicative M →ₙ* A) ≃ (_ →ₙₐ[R] A)) with
    toFun f :=
      { (MonoidAlgebra.liftMagma R f :) with
        toFun := fun a => sum a fun m t => t • f (Multiplicative.ofAdd m) }
    invFun f := f.toMulHom.comp (ofMagma R M) }

end NonUnitalNonAssocAlgebra

/-! #### Algebra structure -/

section lift

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
def liftNCAlgHom (f : A →ₐ[R] B) (g : Multiplicative M →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    A[M] →ₐ[R] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

@[simp] lemma coe_liftNCAlgHom (f : A →ₐ[R] B) (g : Multiplicative M →* B) (h_comm) :
    ⇑(liftNCAlgHom f g h_comm) = liftNC f g := rfl

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem algHom_ext' ⦃φ₁ φ₂ : R[M] →ₐ[R] A⦄
    (h : (φ₁ : R[M] →* A).comp (of R M) = (φ₂ : R[M] →* A).comp (of R M)) :
    φ₁ = φ₂ :=
  algHom_ext <| DFunLike.congr_fun h

variable (R M A) in
/-- Any monoid homomorphism `M →* A` can be lifted to an algebra homomorphism
`R[M] →ₐ[R] A`. -/
def lift : (Multiplicative M →* A) ≃ (R[M] →ₐ[R] A) where
  toFun F := liftNCAlgHom (Algebra.ofId R A) F fun _ _ => Algebra.commutes _ _
  invFun f := (f : R[M] →* A).comp (of R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

theorem lift_apply' (F : Multiplicative M →* A) (f : R[M]) :
    lift R A M F f = f.sum fun a b => algebraMap R A b * F (Multiplicative.ofAdd a) :=
  rfl

theorem lift_apply (F : Multiplicative M →* A) (f : R[M]) :
    lift R A M F f = f.sum fun a b => b • F (Multiplicative.ofAdd a) := by
  simp only [lift_apply', Algebra.smul_def]

theorem lift_def (F : Multiplicative M →* A) :
    ⇑(lift R A M F) = liftNC ((algebraMap R A : R →+* A) : R →+ A) F :=
  rfl

@[simp]
theorem lift_symm_apply (F : R[M] →ₐ[R] A) (x : Multiplicative M) :
    (lift R A M).symm F x = F (single x.toAdd 1) :=
  rfl

theorem lift_of (F : Multiplicative M →* A) (x : Multiplicative M) :
    lift R A M F (of R M x) = F x := MonoidAlgebra.lift_of F x

@[simp]
theorem lift_single (F : Multiplicative M →* A) (a b) :
    lift R A M F (single a b) = b • F (Multiplicative.ofAdd a) :=
  MonoidAlgebra.lift_single F (.ofAdd a) b

lemma lift_of' (F : Multiplicative M →* A) (x : M) :
    lift R A M F (of' R M x) = F (Multiplicative.ofAdd x) :=
  lift_of F x

theorem lift_unique' (F : R[M] →ₐ[R] A) :
    F = lift R A M ((F : R[M] →* A).comp (of R M)) :=
  ((lift R A M).apply_symm_apply F).symm

/-- Decomposition of a `R`-algebra homomorphism from `R[M]` by
its values on `F (single a 1)`. -/
theorem lift_unique (F : R[M] →ₐ[R] A) (f : R[M]) :
    F f = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

theorem lift_mapRangeRingHom_algebraMap [CommSemiring S] [Algebra S A]
    [Algebra R S] [IsScalarTower R S A]
    (f : Multiplicative M →* A) (x : R[M]) :
    lift _ _ _ f (mapRangeRingHom _ (algebraMap R S) x) = lift _ _ _ f x := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

lemma algHom_ext_iff {φ₁ φ₂ : R[M] →ₐ[R] A} : (∀ x, φ₁ (single x 1) = φ₂ (single x 1)) ↔ φ₁ = φ₂ :=
  ⟨fun h => algHom_ext h, by rintro rfl _; rfl⟩

end lift

end AddMonoidAlgebra

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable (A M) in
/-- The algebra equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative`. -/
def AddMonoidAlgebra.toMultiplicativeAlgEquiv [AddMonoid M] :
    AddMonoidAlgebra A M ≃ₐ[R] MonoidAlgebra A (Multiplicative M) where
  toRingEquiv := AddMonoidAlgebra.toMultiplicative A M
  commutes' r := by simp [AddMonoidAlgebra.toMultiplicative]

variable (A M) in
/-- The algebra equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of
`Additive`. -/
def MonoidAlgebra.toAdditiveAlgEquiv [Monoid M] :
    MonoidAlgebra A M ≃ₐ[R] AddMonoidAlgebra A (Additive M) where
  toRingEquiv := MonoidAlgebra.toAdditive A M
  commutes' r := by simp [MonoidAlgebra.toAdditive]
