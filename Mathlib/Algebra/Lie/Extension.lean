/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Lie.Cochain
import Mathlib.Algebra.Module.TransferInstance

/-!
# Extensions of Lie algebras
This file defines extensions of Lie algebras, given by short exact sequences of Lie algebra
homomorphisms. They are implemented in two ways: `IsExtension` is a `Prop`-valued class taking two
homomorphisms as parameters, and `Extension` is a structure that includes the middle Lie algebra.

Because our sign convention for differentials is opposite that of Chevalley-Eilenberg, there is a
change of signs in the "action" part of the Lie bracket.

## Main definitions
* `LieAlgebra.IsExtension`: A `Prop`-valued class characterizing an extension of Lie algebras.
* `LieAlgebra.Extension`: A bundled structure giving an extension of Lie algebras.
* `LieAlgebra.IsExtension.extension`: A function that builds the bundled structure from the class.
* `LieAlgebra.ofTwoCocycle`: A Lie algebra built from a direct product, but whose bracket product is
  sheared by a 2-cocycle.
* `LieAlgebra.Extension.ofTwoCocycle` - A Lie algebra extension constructed from a 2-cocycle

## TODO
* `IsCentral` - central extensions
* `Equiv` - equivalence of extensions
* The 2-cocycle given by a linear splitting of an extension.
* The 2-coboundary from two linear splittings of an extension.

## References
* [Chevalley, Eilenberg, *Cohomology Theory of Lie Groups and Lie
  Algebras*](chevalley_eilenberg_1948)
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

-/

namespace LieAlgebra

variable {R N L M : Type*}

section IsExtension

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

/-- A sequence of two Lie algebra homomorphisms is an extension if it is short exact. -/
class IsExtension (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) : Prop where
  ker_eq_bot : i.ker = ⊥
  range_eq_top : p.range = ⊤
  exact : i.range = p.ker

lemma _root_.LieHom.range_eq_ker_iff (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) :
    i.range = p.ker ↔ Function.Exact i p :=
  ⟨fun h x ↦ by simp [← LieHom.coe_range, h], fun h ↦ (p.ker.toLieSubalgebra.ext i.range h).symm⟩

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

end IsExtension

section Algebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]

open LieModule.Cohomology

/-- A one-field structure giving a type synonym for a direct product. We use this to describe an
alternative Lie algebra structure on the product, where the bracket is shifted by a 2-cocycle. -/
structure ofTwoCocycle {R L M} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M]
    [Module R M] [LieRingModule L M] [LieModule R L M]
    (c : twoCocycle R L M) where
  /-- The underlying type. -/
  carrier : L × M

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
(c : twoCocycle R L M)

/-- An equivalence between the direct product and the corresponding one-field structure. This is
used to transfer the additive and scalar-multiple structure on the direct product to the type
synonym. -/
def ofProd : L × M ≃ ofTwoCocycle c where
  toFun a := ⟨ a ⟩
  invFun a := a.carrier

-- transport instances along equivalence!
instance : AddCommGroup (ofTwoCocycle c) := (ofProd c).symm.addCommGroup

instance : Module R (ofTwoCocycle c) := (ofProd c).symm.module R

@[simp] lemma of_zero : ofProd c (0 : L × M) = 0 := rfl
@[simp] lemma of_add (x y : L × M) : ofProd c (x + y) = ofProd c x + ofProd c y := rfl
@[simp] lemma of_smul (r : R) (x : L × M) : (ofProd c) (r • x) = r • ofProd c x := rfl

@[simp] lemma of_symm_zero : (ofProd c).symm (0 : ofTwoCocycle c) = 0 := rfl
@[simp] lemma of_symm_add (x y : ofTwoCocycle c) :
  (ofProd c).symm (x + y) = (ofProd c).symm x + (ofProd c).symm y := rfl
@[simp] lemma of_symm_smul (r : R) (x : ofTwoCocycle c) :
  (ofProd c).symm (r • x) = r • (ofProd c).symm x := rfl

@[simp] lemma of_nsmul (n : ℕ) (x : L × M) : (ofProd c) (n • x) = n • (ofProd c) x := rfl
@[simp] lemma of_symm_nsmul (n : ℕ) (x : ofTwoCocycle c) :
  (ofProd c).symm (n • x) = n • (ofProd c).symm x := rfl

instance : LieRing (ofTwoCocycle c) where
  bracket x y := ofProd c (⁅((ofProd c).symm x).1, ((ofProd c).symm y).1⁆,
    c.1.val ((ofProd c).symm x).1 ((ofProd c).symm y).1 +
    ⁅((ofProd c).symm x).1, ((ofProd c).symm y).2⁆ - ⁅((ofProd c).symm y).1, ((ofProd c).symm x).2⁆)
  add_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [of_symm_add, Prod.fst_add, add_lie, twoCochain_val_apply, map_add,
      LinearMap.add_apply, Prod.snd_add, lie_add, Prod.mk_add_mk, Prod.mk.injEq, true_and]
    abel
  lie_add x y z := by
    rw [← of_add]
    exact Equiv.congr_arg (by simp; abel)
  lie_self x := by
    rw [← of_zero, c.1.2]
    exact Equiv.congr_arg (by simp)
  leibniz_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [twoCochain_val_apply, Equiv.symm_apply_apply, lie_lie, Prod.mk_add_mk,
      sub_add_cancel, Prod.mk.injEq, true_and, lie_add, lie_sub]
    have hc := c.2
    rw [mem_twoCocycle_iff] at hc
    have := d₂₃_apply R L M c ((ofProd c).symm x).1 ((ofProd c).symm y).1 ((ofProd c).symm z).1
    simp only [hc, LinearMap.zero_apply] at this
    rw [← twoCochain_skew _ _ ⁅((ofProd c).symm x).1, ((ofProd c).symm z).1⁆,
      ← twoCochain_skew _ _ ⁅((ofProd c).symm y).1, ((ofProd c).symm z).1⁆, eq_sub_iff_add_eq,
      zero_add, neg_eq_iff_eq_neg] at this
    rw [this]
    abel

lemma bracket_ofTwoCocycle {c : twoCocycle R L M} (x y : ofTwoCocycle c) :
    ⁅x, y⁆ = ofProd c (⁅((ofProd c).symm x).1, ((ofProd c).symm y).1⁆,
      c.1.val ((ofProd c).symm x).1 ((ofProd c).symm y).1 +
      ⁅((ofProd c).symm x).1, ((ofProd c).symm y).2⁆ -
      ⁅((ofProd c).symm y).1, ((ofProd c).symm x).2⁆) :=
  rfl

instance : LieAlgebra R (ofTwoCocycle c) where
  lie_smul r x y := by
    simp only [bracket_ofTwoCocycle]
    exact Equiv.congr_arg (by simp [← smul_add, smul_sub])

end Algebra

namespace Extension

open LieModule.Cohomology

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M] [IsLieAbelian M]
  [LieRingModule L M] [LieModule R L M] (c : twoCocycle R L M)

/-- An extension of Lie algebras defined by a 2-cocycle. -/
def ofTwoCocycle : Extension R M L where
  L := LieAlgebra.ofTwoCocycle c
  instLieRing := inferInstance
  instLieAlgebra := inferInstance
  incl :=
    { toFun x := ofProd c (0, x)
      map_add' _ _ := by simp [← of_add]
      map_smul' _ _ := by simp [← of_smul]
      map_lie' {_ _} := by simp [bracket_ofTwoCocycle] }
  proj :=
    { toFun x := ((ofProd c).symm x).1
      map_add' _ _ := by simp
      map_smul' _ _ := by simp
      map_lie' {_ _} := by simp [bracket_ofTwoCocycle] }
  IsExtension :=
    { ker_eq_bot := by
        rw [LieHom.ker_eq_bot]
        intro x y
        simp
      range_eq_top := by
        rw [LieHom.range_eq_top]
        intro x
        use (ofProd c (x, 0))
        simp
      exact := by
        ext x
        constructor
        · intro hx
          obtain ⟨n, h⟩ := hx
          rw [← h]
          rfl
        · intro hx
          have : ((ofProd c).symm x).1 = 0 := hx
          simp only [LieHom.mem_range, LieHom.coe_mk]
          use ((ofProd c).symm x).2
          nth_rw 2 [← Equiv.apply_symm_apply (ofProd c) x]
          rw [← this] }

instance : LieRing (ofTwoCocycle c).L := (ofTwoCocycle c).instLieRing
instance : LieAlgebra R (ofTwoCocycle c).L := (ofTwoCocycle c).instLieAlgebra

/-- The Lie algebra isomorphism given by the type synonym. -/
def ofAlg : LieAlgebra.ofTwoCocycle c ≃ₗ⁅R⁆ (ofTwoCocycle c).L := LieEquiv.refl

lemma bracket (x y : (ofTwoCocycle c).L) :
    ⁅x, y⁆ = ofAlg c ⁅(ofAlg c).symm x, (ofAlg c).symm y⁆ := rfl

end Extension

end LieAlgebra
