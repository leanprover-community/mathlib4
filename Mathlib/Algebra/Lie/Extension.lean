/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.CochainTrivial
import Mathlib.Algebra.Lie.Ideal
import Mathlib.Algebra.Module.TransferInstance

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
* `ofTwoCocycleAlg` - construction of extensions from 2-cocycles

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

-/

namespace LieAlgebra

variable {R N L M V : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

/-- A sequence of two Lie algebra homomorphisms is an extension if it is short exact. -/
structure IsExtension (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) : Prop where
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
  extension : IsExtension incl proj

/-- A surjective Lie algebra homomorphism yields an extension. -/
lemma isExtension.of_surjective (f : L →ₗ⁅R⁆ M) (hf : Function.Surjective f) :
    IsExtension f.ker.incl f where
  ker_eq_bot := LieIdeal.ker_incl f.ker
  range_eq_top := (LieHom.range_eq_top f).mpr hf
  exact := LieIdeal.incl_range f.ker

namespace Extension

/-- The bundled `LieAlgebra.Extension` corresponding to `LieAlgebra.IsExtension` -/
@[simps] def ofIsExtension {i : N →ₗ⁅R⁆ L} {p : L →ₗ⁅R⁆ M} (h : IsExtension i p) :
    Extension R N M :=
  ⟨L, _, _, i, p, h⟩

variable (E : Extension R N M)

instance : LieRing E.L := E.instLieRing

instance : LieAlgebra R E.L := E.instLieAlgebra

lemma incl_injective (E : Extension R N M) : Function.Injective E.incl :=
  (LieHom.ker_eq_bot E.incl).mp (IsExtension.ker_eq_bot E.extension)

lemma proj_surjective (E : Extension R N M) : Function.Surjective E.proj :=
  (LieHom.range_eq_top E.proj).mp (IsExtension.range_eq_top E.extension)

lemma exact (E : Extension R N M) : E.incl.range = E.proj.ker :=
  IsExtension.exact E.extension

lemma proj_incl (E : Extension R N M) (x : N) : E.proj (E.incl x) = 0 :=
  LieHom.mem_ker.mp <| LieHom.mem_ker.mpr <| le_of_eq (exact E) <| LieHom.mem_range_self E.incl x

/-- `Extension`s are equivalent iff there is a homomorphism making a commuting diagram. -/
@[ext] structure Equiv (E' : Extension R N M) where
  /-- The homomorphism -/
  toLieEquiv : E.L ≃ₗ⁅R⁆ E'.L
  /-- The left-hand side of the diagram commutes. -/
  incl_comm : toLieEquiv.comp E.incl = E'.incl
  /-- The right-hand side of the diagram commutes. -/
  proj_comm : E'.proj.comp toLieEquiv = E.proj

namespace Equiv

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
lemma mul_eq (x y : E.Equiv E) : (x * y).toLieEquiv = x.toLieEquiv.trans y.toLieEquiv :=
  rfl

instance : One (E.Equiv E) where
  one := {
    toLieEquiv := LieEquiv.refl
    incl_comm := by ext; simp
    proj_comm := by ext; simp }

@[simp] lemma one_eq : (1 : E.Equiv E).toLieEquiv = LieEquiv.refl := rfl

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

@[simp] lemma inv_eq (x : E.Equiv E) : x⁻¹.toLieEquiv = x.toLieEquiv.symm := rfl

instance : Group (E.Equiv E) where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel x := by ext; simp

end Equiv

/-- A one-field structure giving a type synonym for a direct product. We use this to describe an
alternative Lie algebra structure on the product, where the bracket is shifted by a 2-cocycle. -/
structure ofTwoCocycleAlg {R L V} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup V]
    [Module R V] (c : twoCocycle R L V) where
  /-- The underlying type. -/
  carrier : L × V

variable [AddCommGroup V] [Module R V] (c : twoCocycle R L V)

/-- An equivalence between the direct product and the corresponding one-field structure. This is
used to transfer the additive and scalar-multiple structure on the direct product to the type
synonym. -/
@[reducible]
def ofProd : L × V ≃ ofTwoCocycleAlg c where
  toFun a := ⟨ a ⟩
  invFun a := a.carrier

-- transport instances along equivalence!
instance : AddCommGroup (ofTwoCocycleAlg c) := (ofProd c).symm.addCommGroup

instance : Module R (ofTwoCocycleAlg c) := (ofProd c).symm.module R

@[simp] lemma of_zero : ofProd c (0 : L × V) = 0 := rfl
@[simp] lemma of_add (x y : L × V) : ofProd c (x + y) = ofProd c x + ofProd c y := rfl
@[simp] lemma of_smul (r : R) (x : L × V) : (ofProd c) (r • x) = r • ofProd c x := rfl

@[simp] lemma of_symm_zero : (ofProd c).symm (0 : ofTwoCocycleAlg c) = 0 := rfl
@[simp] lemma of_symm_add (x y : ofTwoCocycleAlg c) :
  (ofProd c).symm (x + y) = (ofProd c).symm x + (ofProd c).symm y := rfl
@[simp] lemma of_symm_smul (r : R) (x : ofTwoCocycleAlg c) :
  (ofProd c).symm (r • x) = r • (ofProd c).symm x := rfl

@[simp] lemma of_nsmul (n : ℕ) (x : L × V) :
  (ofProd c) (n • x) = n • (ofProd c) x := rfl
@[simp] lemma of_symm_nsmul (n : ℕ) (x : ofTwoCocycleAlg c) :
  (ofProd c).symm (n • x) = n • (ofProd c).symm x := rfl

instance : LieRing (ofTwoCocycleAlg c) where
  bracket x y := ofProd c (⁅((ofProd c).symm x).1, ((ofProd c).symm y).1⁆,
    c.1.val ((ofProd c).symm x).1 ((ofProd c).symm y).1)
  add_lie x y z := by
    rw [← of_add]
    exact Equiv.congr_arg (by simp)
  lie_add x y z := by
    rw [← of_add]
    exact Equiv.congr_arg (by simp)
  lie_self x := by
    rw [← of_zero, c.1.2]
    exact Equiv.congr_arg (by simp)
  leibniz_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, lie_lie, Prod.mk_add_mk, sub_add_cancel,
      Prod.mk.injEq, true_and]
    rw [(mem_twoCocycle_iff_Jacobi_like R L V c.1).mp c.2]

lemma bracket_ofTwoCocycleAlg {c : twoCocycle R L V} (x y : ofTwoCocycleAlg c) :
    ⁅x, y⁆ = ofProd c (⁅((ofProd c).symm x).1, ((ofProd c).symm y).1⁆,
      c.1.val ((ofProd c).symm x).1 ((ofProd c).symm y).1) :=
  rfl

instance : LieAlgebra R (ofTwoCocycleAlg c) where
  lie_smul r x y := by
    simp only [bracket_ofTwoCocycleAlg]
    exact Equiv.congr_arg (by simp)

/-- The Lie algebra map from a central extension derived from a 2-cocycle. -/
@[simps]
def twoCocycleProj : (ofTwoCocycleAlg c) →ₗ⁅R⁆ L where
  toLinearMap := {
    toFun x := ((ofProd c).symm x).1
    map_add' _ _ := by simp
    map_smul' _ _ := by simp }
  map_lie' {x y} := by simp [bracket_ofTwoCocycleAlg]

lemma surjective_of_cocycle : Function.Surjective (twoCocycleProj c) :=
  fun x ↦ Exists.intro ((ofProd c) (x, 0)) rfl

/-- An equivalence of extended Lie algebras induced by translation by a coboundary. -/
@[simps]
def LieEquiv.ofCoboundary (c' : twoCocycle R L V) (x : oneCochain R L V)
    (h : c' = c + d₁₂ R L V x) :
    LieEquiv R (ofTwoCocycleAlg c) (ofTwoCocycleAlg c') where
  toFun y := ofProd c' (((ofProd c).symm y).1, ((ofProd c).symm y).2 + x ((ofProd c).symm y).1)
  map_add' _ _ := by
    simp only [← of_add]
    exact Equiv.congr_arg (by simp; abel)
  map_smul' _ _ := by
    simp only [← of_smul]
    simp
  map_lie' {a b} := by
    refine (Equiv.apply_eq_iff_eq_symm_apply (ofProd c')).mpr ?_
    simp [bracket_ofTwoCocycleAlg, h]
  invFun z := ofProd c (((ofProd c').symm z).1, ((ofProd c').symm z).2 - x ((ofProd c').symm z).1)
  left_inv y := by simp
  right_inv z := by simp

end Extension

end LieAlgebra
