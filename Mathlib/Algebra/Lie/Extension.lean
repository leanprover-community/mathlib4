/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Ideal

/-!
# Extensions of Lie algebras
This file defines extensions of Lie algebras, given by short exact sequences of Lie algebra
homomorphisms. They are implemented in two ways: `IsExtension` is a `Prop`-valued class taking two
homomorphisms as parameters, and `Extension` is a structure that includes the middle Lie algebra.

## Main definitions
* `LieAlgebra.IsExtension`: A `Prop`-valued class characterizing an extension of Lie algebras.
* `LieAlgebra.Extension`: A bundled structure giving an extension of Lie algebras.
* `LieAlgebra.IsExtension.extension`: A function that builds the bundled structure from the class.

## TODO
* `IsCentral` - central extensions
* `Equiv` - equivalence of extensions
* `ofTwoCocycle` - construction of extensions from 2-cocycles

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

-/

namespace LieAlgebra

variable {R N L M V : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

/-- A sequence of two Lie algebra homomorphisms is an extension if it is short exact. -/
class IsExtension (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) : Prop where
  ker_eq_bot : i.ker = ⊥
  range_eq_top : p.range = ⊤
  exact : i.range = p.ker

variable (R N M) in
/-- The type of all Lie extensions of `M` by `N`.  That is, short exact sequences of `R`-Lie algebra
homomorphisms `0 → N → L → M → 0` where `R`, `M`, and `N` are fixed. -/
structure Extension where
  /-- The middle object in the sequence. -/
  L : Type*
  /-- `L` is a Lie ring. -/
  instLieRing : LieRing L
  /-- `L` is a Lie algebra over `R`. -/
  instLieAlgebra : LieAlgebra R L
  /-- The inclusion homomorphism `N →ₗ⁅R⁆ L` -/
  incl : N →ₗ⁅R⁆ L
  /-- The projection homomorphism `L →ₗ⁅R⁆ M` -/
  proj : L →ₗ⁅R⁆ M
  IsExtension : IsExtension incl proj

/-- The bundled `LieAlgebra.Extension` corresponding to `LieAlgebra.IsExtension` -/
@[simps] def IsExtension.extension {i : N →ₗ⁅R⁆ L} {p : L →ₗ⁅R⁆ M} (h : IsExtension i p) :
    Extension R N M :=
  ⟨L, _, _, i, p, h⟩

/-- A surjective Lie algebra homomorphism yields an extension. -/
theorem isExtension_of_surjective (f : L →ₗ⁅R⁆ M) (hf : Function.Surjective f) :
    IsExtension f.ker.incl f where
  ker_eq_bot := LieIdeal.ker_incl f.ker
  range_eq_top := (LieHom.range_eq_top f).mpr hf
  exact := LieIdeal.incl_range f.ker

section TwoCocycleTriv

/-- A Lie algebra 2-cocycle with coefficients in a module with trivial action. We do not define the
trivial action of `L` on `V`. -/
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
@[simp] theorem of_smul (r : R) (x : L × V) : (ofProd c) (r • x) = r • ofProd c x := rfl

@[simp] theorem of_symm_zero : (ofProd c).symm (0 : ofTwoCocycleTrivModule c) = 0 := rfl
@[simp] theorem of_symm_add (x y : ofTwoCocycleTrivModule c) :
  (ofProd c).symm (x + y) = (ofProd c).symm x + (ofProd c).symm y := rfl
@[simp] theorem of_symm_smul (r : R) (x : ofTwoCocycleTrivModule c) :
  (ofProd c).symm (r • x) = r • (ofProd c).symm x := rfl

@[simp] theorem of_nsmul (n : ℕ) (x : L × V) :
  (ofProd c) (n • x) = n • (ofProd c) x := rfl
@[simp] theorem of_symm_nsmul (n : ℕ) (x : ofTwoCocycleTrivModule c) :
  (ofProd c).symm (n • x) = n • (ofProd c).symm x := rfl

instance : LieRing (ofTwoCocycleTrivModule c) where
  bracket x y := (⁅x.1, y.1⁆, c.toFun x.1 y.1)
  add_lie x y z := by simp [ofTwoCocycleTrivModule]
  lie_add x y z := by simp [ofTwoCocycleTrivModule]
  lie_self x := by simp [c.map_eq_zero_of_eq', Prod.mk_zero_zero]
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
def twoCocycleTrivProj : (ofTwoCocycleTrivModule c) →ₗ⁅R⁆ L where
  toLinearMap := LinearMap.fst R L V
  map_lie' {x y} := by
    simp only [ofTwoCocycleTrivModule, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      LinearMap.fst_apply]
    exact rfl

lemma surjective_of_cocycle : Function.Surjective (twoCocycleTrivProj c) :=
  fun x ↦ Exists.intro (x, 0) rfl

lemma isExtension_twoCocycleTriv :
    IsExtension (twoCocycleTrivProj c).ker.incl (twoCocycleTrivProj c) :=
  isExtension_of_surjective (twoCocycleTrivProj c) (surjective_of_cocycle c)

/-- A Lie extension from a trivial 2-cocycle -/
def Extension.ofTwoCocycleTriv :
    Extension R (twoCocycleTrivProj c).ker L :=
  IsExtension.extension (isExtension_twoCocycleTriv c)

end TwoCocycleTriv

end LieAlgebra
