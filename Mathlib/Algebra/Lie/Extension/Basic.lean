/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Abelian

/-!
# Extensions of Lie algebras

Copy group extension API from GroupTheory.GroupExtension.Defs

Problem: If I want to build a central extension from a cocycle, I need to make the Lie ring
structure, and the Lie algebra structure, and the extension structure.  Perhaps it is better to
assume the structure pre-exists, and make a prop "comes from the 2-cocycle `c`" for the Lie
structure on `L × V`.  Then, we don't need to `letI` the typeclasses.

Also, need a `make an abelian Lie algebra` class?

-/
variable (R N L M : Type*)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

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

/-- A Lie extension is a surjective Lie algebra homomorphism. Delete? -/
def IsLieExtension (f : L →ₗ⁅R⁆ M) : Prop :=
  Function.Surjective f

namespace LieExtension

variable {R L M N V : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M] (S : LieExtension R N L M)

/-- Construct an extension from a surjective Lie algebra homomorphism. -/
@[simps!]
def ofSurjection (f : L →ₗ⁅R⁆ M) (hf : Function.Surjective f) :
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

/-- A Lie algebra 2-cocycle with coefficients in a module with trivial action. -/
structure twoCocycleTriv (R L V) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup V]
    [Module R V] where
  /-- The underlying linear function. -/
  toFun : L →ₗ[R] L →ₗ[R] V
  map_eq_zero_of_eq' x : toFun x x = 0
  cocycle x y z : toFun x ⁅y, z⁆ = toFun ⁅x, y⁆ z + toFun y ⁅x, z⁆

/-- The condition that a the bracket on the product comes from a 2-cocycle. -/
def IsLieRingOfTwoCocycleTriv [AddCommGroup V] [Module R V] [LieRing (L × V)]
    (c : twoCocycleTriv R L V) : Prop :=
  ∀ x y : L × V, ⁅x, y⁆ = (⁅x.1, y.1⁆, c.toFun x.1 y.1)


/-!
def inl_of_TwoCocycle [LieRing V] [LieAlgebra R V] [LieRing (L × V)]
    [LieAlgebra R (L × V)] (c : twoCocycleTriv R L V) : V →ₗ⁅R⁆ L × V where
-- synthesized type class instance is not definitionally equal to
-- expression inferred by typing rules,
-- synthesized Prod.instAddCommMonoid
-- inferred AddCommGroup.toAddCommMonoid
-/

/-- The Lie ring attached to a 2-cocycle with coefficients in a module with trivial action. -/
def _root_.LieRing.ofTwoCocycleTriv [AddCommGroup V] [Module R V]
   (c : twoCocycleTriv R L V) : LieRing (L × V) where
  toAddCommGroup := Prod.instAddCommGroup
  bracket x y := (⁅x.1, y.1⁆, c.toFun x.1 y.1)
  add_lie x y z := by simp
  lie_add x y z := by simp
  lie_self x := by simp [c.map_eq_zero_of_eq']
  leibniz_lie x y z := by simp [c.cocycle x.1 y.1 z.1]

/-- The Lie algebra structure of the Lie ring attached to a 2-cocycle -/
def _root_.LieAlgebra.ofTwoCocycleTriv [AddCommGroup V] [Module R V] (c : twoCocycleTriv R L V) :
    letI : LieRing (L × V) := LieRing.ofTwoCocycleTriv c
    LieAlgebra R (L × V) := by
  letI : LieRing (L × V) := LieRing.ofTwoCocycleTriv c
  exact LieAlgebra.mk fun r x y => by simp [LieRing.ofTwoCocycleTriv]

/-- The Lie algebra map from a central extension. -/
def mapFromTwoCocycleTriv [AddCommGroup V] [Module R V] (c : twoCocycleTriv R L V) :
    letI : LieRing (L × V) := LieRing.ofTwoCocycleTriv c
    letI : LieAlgebra R (L × V) := LieAlgebra.ofTwoCocycleTriv c
    L × V →ₗ⁅R⁆ L := by
  letI : LieRing (L × V) := LieRing.ofTwoCocycleTriv c
  letI : LieAlgebra R (L × V) := LieAlgebra.ofTwoCocycleTriv c
  refine { toLinearMap := LinearMap.fst R L V, map_lie' := ?_ }
  intro x y
  exact rfl

lemma surjection_of_cocycle [AddCommGroup V] [Module R V] (c : twoCocycleTriv R L V) :
    Function.Surjective (mapFromTwoCocycleTriv c) := by
  intro x
  use (x, 0)
  exact rfl

/-!
/-- A Lie extension from a trivial 2-cocycle -/
def ofTwoCocycleTriv [LieRing V] [Module R V] [LieAlgebra R V]
    (c : twoCocycleTriv R L V) :
    letI : LieRing (L × V) := LieRing.ofTwoCocycleTriv c
    letI : LieAlgebra R (L × V) := LieAlgebra.ofTwoCocycleTriv c
    LieExtension R V (L × V) L :=
    letI : LieRing (L × V) := LieRing.ofTwoCocycleTriv c
    letI : LieAlgebra R (L × V) := LieAlgebra.ofTwoCocycleTriv c
    ofSurjection (mapFromTwoCocycleTriv c) (surjection_of_cocycle c)

lemma isCentral_ofTwoCocycleTriv [LieRing V] [LieAlgebra R V] [LieRing (L × V)]
    [LieAlgebra R (L × V)]  (c : twoCocycleTriv R L V) (h : IsLieRingOfTwoCocycleTriv c) :
    IsCentral (ofTwoCocycleTriv c h) := by

  sorry
-/

end LieExtension
