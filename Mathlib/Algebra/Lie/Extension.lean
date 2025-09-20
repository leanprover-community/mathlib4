/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Ideal
import Mathlib.Algebra.Lie.CochainTrivial

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
theorem isExtension.of_surjective (f : L →ₗ⁅R⁆ M) (hf : Function.Surjective f) :
    IsExtension f.ker.incl f where
  ker_eq_bot := LieIdeal.ker_incl f.ker
  range_eq_top := (LieHom.range_eq_top f).mpr hf
  exact := LieIdeal.incl_range f.ker

variable (E : Extension R N M)

instance : LieRing E.L := E.instLieRing

instance : LieAlgebra R E.L := E.instLieAlgebra

namespace Extension

/-- `Extension`s are equivalent iff there is a homomorphism making a commuting diagram. -/
@[ext] structure Equiv (E' : Extension R N M) where
  /-- The homomorphism -/
  toLieEquiv : E.L ≃ₗ⁅R⁆ E'.L
  /-- The left-hand side of the diagram commutes. -/
  incl_comm : toLieEquiv.comp E.incl = E'.incl
  /-- The right-hand side of the diagram commutes. -/
  proj_comm : E'.proj.comp toLieEquiv = E.proj

instance : Mul (E.Equiv E) where
  mul x y := {
    toLieEquiv := x.toLieEquiv.trans y.toLieEquiv
    incl_comm := by
      ext z
      rw [LieHom.comp_apply, LieEquiv.trans, LieHom.comp_apply, ← LieHom.comp_apply _ _ z,
        x.incl_comm, ← LieHom.comp_apply, y.incl_comm]
    proj_comm := by
      ext z
      rw [LieHom.comp_apply, LieEquiv.trans, LieHom.comp_apply,
        ← LieHom.comp_apply _ _ (x.toLieEquiv.toLieHom z), y.proj_comm, ← LieHom.comp_apply,
        x.proj_comm] }

@[simp]
lemma Equiv.mul_eq (x y : E.Equiv E) : (x * y).toLieEquiv = x.toLieEquiv.trans y.toLieEquiv :=
  rfl

instance : One (E.Equiv E) where
  one := {
    toLieEquiv := LieEquiv.refl
    incl_comm := by ext; simp
    proj_comm := by ext; simp }

@[simp] lemma Equiv.one_eq : (1 : E.Equiv E).toLieEquiv = LieEquiv.refl := rfl

instance : Inv (E.Equiv E) where
  inv x := {
    toLieEquiv := x.toLieEquiv.symm
    incl_comm := by
      ext y
      simp only [LieHom.coe_comp, LieEquiv.coe_coe, Function.comp_apply]
      nth_rw 2 [show E.incl y = x.toLieEquiv.symm (x.toLieEquiv (E.incl y)) by simp]
      have : (x.toLieEquiv (E.incl y)) = (x.toLieEquiv.comp E.incl) y := by
        rw [LieHom.comp_apply, LieEquiv.coe_toLieHom]
      rw [this, x.incl_comm]
    proj_comm := by
      ext y
      simp only [LieHom.coe_comp, LieEquiv.coe_coe, Function.comp_apply]
      rw [show E.proj y = E.proj.comp x.toLieEquiv (x.toLieEquiv.symm y) by simp, x.proj_comm]
  }

@[simp] lemma Equiv.inv_eq (x : E.Equiv E) : x⁻¹.toLieEquiv = x.toLieEquiv.symm := rfl

instance : Group (E.Equiv E) where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel x := by ext; simp

/-- `Splitting` of a Lie extension is a section homomorphism. -/
structure Splitting where
  /-- A section homomorphism -/
  sectionHom : M →ₗ⁅R⁆ E.L
  /-- The section is a left inverse of the projection map. -/
  leftInv : Function.LeftInverse E.proj sectionHom

instance : FunLike (Splitting E) M E.L where
  coe s := s.sectionHom
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (Splitting E) R M E.L where
  map_add f := f.sectionHom.map_add'
  map_smulₛₗ f := f.sectionHom.map_smul'

section TwoCocycleTriv

/-- A Lie algebra 2-cocycle with coefficients in a module with trivial action. We do not define the
trivial action of `L` on `V`. -/
structure twoCocycleTriv (R L V) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup V]
    [Module R V] where
  /-- The underlying bilinear map. -/
  toFun : L →ₗ[R] L →ₗ[R] V
  map_eq_zero_of_eq' x : toFun x x = 0
  cocycle x y z : toFun x ⁅y, z⁆ = toFun ⁅x, y⁆ z + toFun y ⁅x, z⁆

/-- The canonical injection from cocycles to cochains. -/
def toCochain [AddCommGroup V] [Module R V] : (twoCocycleTriv R L V) → (twoCochain R L V) :=
  fun ⟨a, h, _⟩ ↦ ⟨a, h⟩

theorem toCochain_toBilin [AddCommGroup V] [Module R V] (a : twoCocycleTriv R L V) :
    (toCochain a).toBilin = a.toFun :=
  rfl

theorem image_eq_kernel [AddCommGroup V] [Module R V] (a : twoCochain R L V) :
    a ∈ (Set.range toCochain) ↔ a ∈ twoCocycle R L V := by
  rw [mem_twoCocycle_iff, Set.mem_range]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h
    ext x y z
    simp only [d₂₃_apply_apply, LinearMap.zero_apply, Pi.zero_apply]
    have := b.cocycle x y z
    rw [← toCochain_toBilin, hb, ← twoCochain_skew R L V _ z, ← lie_skew x z,
      LinearMap.map_neg] at this
    simp [this]
  · intro h
    have := (mem_twoCocycle_iff_Jacobi_like R L V a).mp h
    use ⟨a.toBilin, a.alt, this⟩
    simp [toCochain]

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

lemma isExtensionTwoCocycleTriv :
    LieAlgebra.IsExtension (twoCocycleTrivProj c).ker.incl (twoCocycleTrivProj c) :=
  isExtension.of_surjective (twoCocycleTrivProj c) (surjective_of_cocycle c)

/-- A Lie extension from a trivial 2-cocycle -/
def ofTwoCocycleTriv :
    Extension R (twoCocycleTrivProj c).ker L :=
  IsExtension.extension (isExtensionTwoCocycleTriv c)

end TwoCocycleTriv

end Extension

end LieAlgebra
