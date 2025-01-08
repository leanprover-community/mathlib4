/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Abelian

/-!
# Extensions of Lie algebras

Copy group extension API from GroupTheory.GroupExtension.Defs

We use a type alias for the product, so that we can produce instances depending on the
cocycle. We should add reducible equivalences.

Also, need a `make an abelian Lie algebra` class?

-/
variable (R N L M : Type*)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

/-- `IsLieExtension R N L M inl rightHom` is the statement that the sequence of Lie algebra
homomorphisms
`0 → N → L → M → 0`. -/
structure IsLieExtension (inl : N →ₗ⁅R⁆ L) (rightHom : L →ₗ⁅R⁆ M) where
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map. -/
  range_inl_eq_ker_rightHom : LinearMap.range inl.toLinearMap = LinearMap.ker rightHom.toLinearMap
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom

/-- `LieExtension N E G` is a short exact sequence of Lie algebra homomorphisms
`0 → N → L → M → 0`. -/
structure LieExtension where
  /-- The inclusion homomorphism `N →ₗ⁅R⁆ L` -/
  inl : N →ₗ⁅R⁆ L
  /-- The projection homomorphism `L →ₗ⁅R⁆ M` -/
  rightHom : L →ₗ⁅R⁆ M
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map. -/
  range_inl_eq_ker_rightHom : LinearMap.range inl.toLinearMap = LinearMap.ker rightHom.toLinearMap
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom

namespace LieExtension

variable {R L M N V : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M] (S : LieExtension R N L M)

/-- Construct an extension from a surjective Lie algebra homomorphism. -/
@[simps!]
def ofSurjective (f : L →ₗ⁅R⁆ M) (hf : Function.Surjective f) :
    LieExtension R (LieHom.ker f) L M where
  inl := f.ker.incl
  rightHom := f
  inl_injective := LieIdeal.incl_injective f.ker
  range_inl_eq_ker_rightHom := by aesop
  rightHom_surjective := hf

/-- An extension is central if the image of the left map commutes with the whole Lie algebra. -/
def IsCentral : Prop :=
  LieModule.IsTrivial L S.rightHom.ker

/-- `LieExtension`s are equivalent iff there is a homomorphism making a commuting diagram. -/
structure Equiv {L' : Type*} [LieRing L'] [LieAlgebra R L'] (S' : LieExtension R N L' M) where
  /-- The homomorphism -/
  toLieHom : L →ₗ⁅R⁆ L'
  /-- The left-hand side of the diagram commutes. -/
  inl_comm : toLieHom.comp S.inl = S'.inl
  /-- The right-hand side of the diagram commutes. -/
  rightHom_comm : S'.rightHom.comp toLieHom = S.rightHom

/-- `Splitting` of a Lie extension is a section homomorphism. -/
structure Splitting where
  /-- A section homomorphism -/
  sectionHom : M →ₗ⁅R⁆ L
  /-- The section is a left inverse of the projection map. -/
  rightHom_comp_sectionHom : S.rightHom.comp sectionHom = LieHom.id

instance : FunLike S.Splitting M L where
  coe s := s.sectionHom
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass S.Splitting R M L where
  map_add f := f.sectionHom.map_add'
  map_smulₛₗ f := f.sectionHom.map_smul'

section TwoCocycleTriv

/-- A Lie algebra 2-cocycle with coefficients in a module with trivial action. -/
structure twoCocycleTriv (R L V) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup V]
    [Module R V] where
  /-- The underlying linear function. -/
  toFun : L →ₗ[R] L →ₗ[R] V
  map_eq_zero_of_eq' x : toFun x x = 0
  cocycle x y z : toFun x ⁅y, z⁆ = toFun ⁅x, y⁆ z + toFun y ⁅x, z⁆

variable [AddCommGroup V] [Module R V] (c : twoCocycleTriv R L V)

set_option linter.unusedVariables false in
/-- We introduce a type alias for `L × V` in order to avoid typeclass inference problems with
central extensions. -/
@[nolint unusedArguments]
def ofTwoCocycleTrivModule (c : twoCocycleTriv R L V) := L × V

/-- The casting function to the type synonym. -/
--@[reducible] -- this makes a mess
def ofProd : L × V ≃ ofTwoCocycleTrivModule c := Equiv.refl _

instance : AddCommGroup (ofTwoCocycleTrivModule c) :=
  inferInstanceAs <| AddCommGroup (L × V)

instance : Module R (ofTwoCocycleTrivModule c) :=
  inferInstanceAs <| Module R (L × V)

@[simp] theorem of_zero : ofProd c (0 : L × V) = 0 := rfl
@[simp] theorem of_add (x y : L × V) : ofProd c (x + y) = ofProd c x + ofProd c y := rfl

@[simp] theorem of_symm_zero : (ofProd c).symm (0 : ofTwoCocycleTrivModule c) = 0 := rfl
@[simp] theorem of_symm_add (x y : ofTwoCocycleTrivModule c) :
  (ofProd c).symm (x + y) = (ofProd c).symm x + (ofProd c).symm y := rfl

@[simp] theorem of_nsmul (n : ℕ) (x : L × V) :
  (ofProd c) (n • x) = n • (ofProd c) x := rfl
@[simp] theorem of_symm_nsmul (n : ℕ) (x : ofTwoCocycleTrivModule c) :
  (ofProd c).symm (n • x) = n • (ofProd c).symm x := rfl

instance : LieRing (ofTwoCocycleTrivModule c) where
  bracket x y := (⁅x.1, y.1⁆, c.toFun x.1 y.1)
  add_lie x y z := by simp [ofTwoCocycleTrivModule]
  lie_add x y z := by simp [ofTwoCocycleTrivModule]
  lie_self x := by simp [c.map_eq_zero_of_eq']
  leibniz_lie x y z := by simp [ofTwoCocycleTrivModule, c.cocycle x.1 y.1 z.1]

@[simp]
lemma bracket_ofTwoCocycleTriv {c : twoCocycleTriv R L V}
    (x y : ofTwoCocycleTrivModule c) : ⁅x, y⁆ = (⁅x.1, y.1⁆, c.toFun x.1 y.1) :=
  rfl

instance : LieAlgebra R (ofTwoCocycleTrivModule c) where
  lie_smul r x y := by
    simp only [bracket_ofTwoCocycleTriv]
    rw [show (r • y).1 = r • (y.1) by rfl, lie_smul r x.1 y.1, map_smul (c.toFun x.1) r y.1,
      Prod.smul_mk]

/-- The Lie algebra map from a central extension. -/
def rightHomTwoCocycleTriv : (ofTwoCocycleTrivModule c) →ₗ⁅R⁆ L where
  toLinearMap := LinearMap.fst R L V
  map_lie' {x y} := by
    simp only [ofTwoCocycleTrivModule, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      LinearMap.fst_apply]
    exact rfl

lemma surjection_of_cocycle : Function.Surjective (rightHomTwoCocycleTriv c) := by
  intro x
  use (x, 0)
  exact rfl

/-- A Lie extension from a trivial 2-cocycle -/
def ofTwoCocycleTriv :
    LieExtension R (LieHom.ker (rightHomTwoCocycleTriv c)) (ofTwoCocycleTrivModule c) L :=
  ofSurjective (rightHomTwoCocycleTriv c) (surjection_of_cocycle c)

lemma isCentral_ofTwoCocycleTriv : IsCentral (ofTwoCocycleTriv c) := by
  dsimp only [IsCentral]
  rw [LieModule.trivial_iff_le_maximal_trivial]
  intro x hx
  simp_all only [LieHom.mem_ker, LieModule.mem_maxTrivSubmodule, bracket_ofTwoCocycleTriv]
  intro y
  simp [show x.1 = (ofTwoCocycleTriv c).rightHom x by rfl, hx]

end TwoCocycleTriv

end LieExtension
