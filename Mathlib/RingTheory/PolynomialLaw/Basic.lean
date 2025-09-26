/-
Copyright (c) 2025 Antoine Chambert-Loir & María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir & María-Inés de Frutos-Fernández
-/
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # Polynomial laws on modules

Let `M` and `N` be a modules over a commutative ring `R`.
A polynomial law `f : PolynomialLaw R M N`, with notation `f : M →ₚₗₗ[R] N`,
is a “law” that assigns a natural map `PolynomialLaw.toFun' f S : S ⊗[R] M → S ⊗[R] N`
for every `R`-algebra `S`.

For type-theoretic reasons, if `R : Type u`, then the definition of the polynomial map `f`
is restricted to `R`-algebras `S` such that `S : Type u`.
Using the fact that a module is the direct limit of its finitely generated submodules, that a
finitely generated subalgebra is a quotient of a polynomial ring in the universe `u`, plus
the commutation of tensor products with direct limits, we will extend the functor
to all `R`-algebras (TODO).

## Main definitions/lemmas

* Instance : `Module R (M →ₚₗ[R] N)` shows that polynomial laws form a `R`-module.

* `PolynomialLaw.ground f` is the map `M → N` corresponding to `PolynomialLaw.toFun' f R` under
  the isomorphisms `R ⊗[R] M ≃ₗ[R] M`, and similarly for `N`.

In further works, we construct the coefficients of a polynomial law and show the relation with
polynomials (when the module `M` is free and finite).

## Implementation notes

In the literature, the theory is written for commutative rings, but this implementation
only assumes `R` is a commutative semiring.

## References

* [Roby, Norbert. 1963. « Lois polynomes et lois formelles en théorie des modules ».
Annales scientifiques de l’École Normale Supérieure 80 (3): 213‑348](Roby-1963)

-/

universe u

noncomputable section PolynomialLaw

open scoped TensorProduct

open LinearMap TensorProduct AlgHom

/-- A polynomial law `M →ₚₗ[R] N` between `R`-modules is a functorial family of maps
`S ⊗[R] M → S ⊗[R] N`, for all `R`-algebras `S`.

For universe reasons, `S` has to be restricted to the same universe as `R`. -/
@[ext]
structure PolynomialLaw (R : Type u) [CommSemiring R]
    (M : Type*) [AddCommMonoid M] [Module R M] (N : Type*) [AddCommMonoid N] [Module R N] where
  /-- The functions `S ⊗[R] M → S ⊗[R] N` underlying a polynomial law -/
  toFun' (S : Type u) [CommSemiring S] [Algebra R S] : S ⊗[R] M → S ⊗[R] N
  /-- The compatibility relations between the functions underlying a polynomial law -/
  isCompat' {S : Type u} [CommSemiring S] [Algebra R S]
    {S' : Type u} [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') :
    φ.toLinearMap.rTensor N ∘ toFun' S = toFun' S' ∘ φ.toLinearMap.rTensor M := by aesop

/-- `M →ₚₗ[R] N` is the type of `R`-polynomial laws from `M` to `N`. -/
notation:25 M " →ₚₗ[" R:25 "] " N:0 => PolynomialLaw R M N

@[local simp]
theorem PolynomialLaw.isCompat_apply'
    {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N] {f : M →ₚₗ[R] N}
    {S : Type u} [CommSemiring S] [Algebra R S] {S' : Type u} [CommSemiring S'] [Algebra R S']
    (φ : S →ₐ[R] S') (x : S ⊗[R] M) :
    (φ.toLinearMap.rTensor N) ((f.toFun' S) x) = (f.toFun' S') (φ.toLinearMap.rTensor M x) := by
  simpa only using congr_fun (f.isCompat' φ) x

attribute [local simp] PolynomialLaw.isCompat_apply'

namespace PolynomialLaw

section Module

section CommSemiring

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N] (r a b : R) (f g : M →ₚₗ[R] N)

instance : Zero (M →ₚₗ[R] N) := ⟨{ toFun' _ := 0 }⟩

@[simp]
theorem zero_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (0 : PolynomialLaw R M N).toFun' S = 0 := rfl

instance : Inhabited (PolynomialLaw R M N) := ⟨Zero.zero⟩

/-- The identity as a polynomial law -/
def id : M →ₚₗ[R] M where
  toFun' S _ _ := _root_.id

theorem id_apply' {S : Type u} [CommSemiring S] [Algebra R S] :
    (id : M →ₚₗ[R] M).toFun' S = _root_.id := rfl

/-- The sum of two polynomial laws -/
noncomputable def add : M →ₚₗ[R] N where
  toFun' S _ _ := f.toFun' S + g.toFun' S

instance : Add (PolynomialLaw R M N) := ⟨add⟩

@[simp]
theorem add_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (f + g).toFun' S = f.toFun' S + g.toFun' S := rfl

theorem add_def_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (f + g).toFun' S m = f.toFun' S m + g.toFun' S m := rfl

/-- External multiplication of a `f : M →ₚₗ[R] N` by `r : R` -/
def smul : M →ₚₗ[R] N where
  toFun' S _ _ := r • f.toFun' S

instance : SMul R (M →ₚₗ[R] N) := ⟨smul⟩

@[simp]
theorem smul_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (r • f).toFun' S = r • f.toFun' S := rfl

theorem smul_def_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (r • f).toFun' S m = r • f.toFun' S m := rfl

theorem add_smul : (a + b) • f = a • f + b • f := by
  ext; simp only [add_def, smul_def, _root_.add_smul]

theorem zero_smul : (0 : R) • f = 0 := by
  ext S; simp only [smul_def, _root_.zero_smul, zero_def, Pi.zero_apply]

theorem one_smul : (1 : R) • f = f := by
  ext S; simp only [smul_def, Pi.smul_apply, _root_.one_smul]

instance : MulAction R (M →ₚₗ[R] N) where
  one_smul := one_smul
  mul_smul a b f := by ext; simp only [smul_def, mul_smul]

instance : AddCommMonoid (M →ₚₗ[R] N) where
  add_assoc f g h := by ext; simp only [add_def, add_assoc]
  zero_add f := by ext; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext; simp only [add_def, add_zero, zero_def]
  nsmul n f := (n : R) • f
  nsmul_zero f := by simp only [Nat.cast_zero, zero_smul f]
  nsmul_succ n f := by simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  add_comm f g := by ext; simp only [add_def, add_comm]

instance : Module R (M →ₚₗ[R] N) where
  smul_zero a := rfl
  smul_add a f g := by ext; simp only [smul_def, add_def, smul_add]
  add_smul := add_smul
  zero_smul := zero_smul

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]
  (f : M →ₚₗ[R] N)

/-- The opposite of a polynomial law -/
noncomputable def neg : M →ₚₗ[R] N where
  toFun' S _ _ := (-1 : R) • f.toFun' S

instance : Neg (M →ₚₗ[R] N) := ⟨neg⟩

@[simp]
theorem neg_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (-f).toFun' S = (-1 : R) • f.toFun' S := rfl

instance : AddCommGroup (M →ₚₗ[R] N) where
  zsmul n f := (n : R) • f
  zsmul_zero' f := by simp only [Int.cast_zero, zero_smul]
  zsmul_succ' n f := by simp only [Nat.cast_succ, Int.cast_add, Int.cast_natCast,
    Int.cast_one, add_smul, _root_.one_smul]
  zsmul_neg' n f := by
    ext S _ _ m
    rw [neg_def]
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, _root_.add_smul,
      add_def_apply, smul_def_apply, Nat.succ_eq_add_one, Int.cast_add, Int.cast_natCast,
      Int.cast_one, _root_.one_smul, add_def, smul_def, Pi.smul_apply, Pi.add_apply, smul_add,
      smul_smul, neg_mul, one_mul]
    rw [add_comm]
  neg_add_cancel f := by
    ext S _ _ m
    simp only [add_def_apply, neg_def, Pi.smul_apply, zero_def, Pi.zero_apply]
    nth_rewrite 2 [← _root_.one_smul (M := R) (b := f.toFun' S m)]
    rw [← _root_.add_smul]
    simp only [neg_add_cancel, _root_.zero_smul]
  add_comm f g := by ext; simp only [add_def, add_comm]

end CommRing

end Module

section ground

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
variable (f : M →ₚₗ[R] N)

/-- The map `M → N` associated with a `f : M →ₚₗ[R] N` (essentially, `f.toFun' R`) -/
def ground : M → N := (TensorProduct.lid R N) ∘ (f.toFun' R) ∘ (TensorProduct.lid R M).symm

theorem ground_apply (m : M) : f.ground m = TensorProduct.lid R N (f.toFun' R (1 ⊗ₜ[R] m)) := rfl

instance : CoeFun (M →ₚₗ[R] N) (fun _ ↦ M → N) where
  coe := ground

theorem one_tmul_ground_apply' {S : Type u} [CommSemiring S] [Algebra R S] (x : M) :
    1 ⊗ₜ (f.ground x) = (f.toFun' S) (1 ⊗ₜ x) := by
  rw [ground_apply]
  convert f.isCompat_apply' (Algebra.algHom R R S) (1 ⊗ₜ[R] x)
  · simp only [includeRight_lid]
  · rw [rTensor_tmul, toLinearMap_apply, map_one]

/-- The map ground assigning a function `M → N` to a polynomial map `f : M →ₚₗ[R] N` as a
  linear map. -/
def lground : (M →ₚₗ[R] N) →ₗ[R] (M → N) where
  toFun := ground
  map_add' x y := by ext m; simp [ground]
  map_smul' r x := by ext m; simp [ground]

theorem ground_id : (id : M →ₚₗ[R] M).ground = _root_.id := by
  ext; simp [ground_apply, id_apply']

theorem ground_id_apply (m : M) : (id : M →ₚₗ[R] M).ground m = m := by
  rw [ground_id, id_eq]

end ground

section Composition

variable {R : Type u} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {P : Type*} [AddCommMonoid P] [Module R P]
variable {Q : Type*} [AddCommMonoid Q] [Module R Q]
variable (f : M →ₚₗ[R] N) (g : N →ₚₗ[R] P) (h : P →ₚₗ[R] Q)

/-- Composition of polynomial maps. -/
def comp (g : N →ₚₗ[R] P) (f : M →ₚₗ[R] N) : M →ₚₗ[R] P where
  toFun' S _ _ := (g.toFun' S).comp (f.toFun' S)
  isCompat' φ := by ext; simp only [Function.comp_apply, isCompat_apply']

theorem comp_toFun' (S : Type u) [CommSemiring S] [Algebra R S] :
    (g.comp f).toFun' S = (g.toFun' S).comp (f.toFun' S) := rfl

theorem comp_assoc : h.comp (g.comp f) = (h.comp g).comp f := rfl

theorem comp_id : g.comp id = g := by ext; rfl

theorem id_comp : id.comp f = f := by ext; rfl

end Composition

end PolynomialLaw
