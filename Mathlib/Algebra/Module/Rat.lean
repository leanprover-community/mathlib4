/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Field.Rat

/-!
# Basic results about modules over the rationals.
-/

universe u v

variable {M M₂ : Type*}

theorem map_nnratCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionSemiring R] [DivisionSemiring S]
    [Module R M] [Module S M₂] (c : ℚ≥0) (x : M) :
    f ((c : R) • x) = (c : S) • f x := by
  rw [NNRat.cast_def, NNRat.cast_def, div_eq_mul_inv, div_eq_mul_inv, mul_smul, mul_smul,
    map_natCast_smul f R S, map_inv_natCast_smul f R S]

theorem map_ratCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M]
    [Module S M₂] (c : ℚ) (x : M) :
    f ((c : R) • x) = (c : S) • f x := by
  rw [Rat.cast_def, Rat.cast_def, div_eq_mul_inv, div_eq_mul_inv, mul_smul, mul_smul,
    map_intCast_smul f R S, map_inv_natCast_smul f R S]

theorem map_nnrat_smul [AddCommMonoid M] [AddCommMonoid M₂]
    [_instM : Module ℚ≥0 M] [_instM₂ : Module ℚ≥0 M₂]
    {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂]
    (f : F) (c : ℚ≥0) (x : M) : f (c • x) = c • f x :=
  map_nnratCast_smul f ℚ≥0 ℚ≥0 c x

theorem map_rat_smul [AddCommGroup M] [AddCommGroup M₂]
    [_instM : Module ℚ M] [_instM₂ : Module ℚ M₂]
    {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂]
    (f : F) (c : ℚ) (x : M) : f (c • x) = c • f x :=
  map_ratCast_smul f ℚ ℚ c x

/-- There can be at most one `Module ℚ≥0 E` structure on an additive commutative monoid. -/
instance subsingleton_nnrat_module (E : Type*) [AddCommMonoid E] : Subsingleton (Module ℚ≥0 E) :=
  ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_nnrat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩

/-- There can be at most one `Module ℚ E` structure on an additive commutative group. -/
instance subsingleton_rat_module (E : Type*) [AddCommGroup E] : Subsingleton (Module ℚ E) :=
  ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_rat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩

/-- If `E` is a vector space over two division semirings `R` and `S`, then scalar multiplications
agree on non-negative rational numbers in `R` and `S`. -/
theorem nnratCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [DivisionSemiring S] [Module R E] [Module S E] (r : ℚ≥0) (x : E) : (r : R) • x = (r : S) • x :=
  map_nnratCast_smul (AddMonoidHom.id E) R S r x

/-- If `E` is a vector space over two division rings `R` and `S`, then scalar multiplications
agree on rational numbers in `R` and `S`. -/
theorem ratCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (r : ℚ) (x : E) : (r : R) • x = (r : S) • x :=
  map_ratCast_smul (AddMonoidHom.id E) R S r x

instance IsScalarTower.nnrat {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    [Module ℚ≥0 R] [Module ℚ≥0 M] : IsScalarTower ℚ≥0 R M where
  smul_assoc r x y := map_nnrat_smul ((smulAddHom R M).flip y) r x

instance IsScalarTower.rat {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    [Module ℚ R] [Module ℚ M] : IsScalarTower ℚ R M where
  smul_assoc r x y := map_rat_smul ((smulAddHom R M).flip y) r x

/-- `nnqsmul` is equal to any other module structure via a cast. -/
lemma NNRat.cast_smul_eq_nnqsmul (R : Type*) [DivisionSemiring R]
    [MulAction R M] [MulAction ℚ≥0 M] [IsScalarTower ℚ≥0 R M]
    (q : ℚ≥0) (x : M) : (q : R) • x = q • x := by
  rw [← one_smul R x, ← smul_assoc, ← smul_assoc]; simp

/-- `qsmul` is equal to any other module structure via a cast. -/
lemma Rat.cast_smul_eq_qsmul (R : Type*) [DivisionRing R]
    [MulAction R M] [MulAction ℚ M] [IsScalarTower ℚ R M]
    (q : ℚ) (x : M) : (q : R) • x = q • x := by
  rw [← one_smul R x, ← smul_assoc, ← smul_assoc]; simp

section
variable {α : Type u} {M : Type v}

instance SMulCommClass.nnrat [Monoid α] [AddCommMonoid M] [DistribMulAction α M] [Module ℚ≥0 M] :
    SMulCommClass ℚ≥0 α M where
  smul_comm r x y := (map_nnrat_smul (DistribMulAction.toAddMonoidHom M x) r y).symm

instance SMulCommClass.rat [Monoid α] [AddCommGroup M] [DistribMulAction α M] [Module ℚ M] :
    SMulCommClass ℚ α M where
  smul_comm r x y := (map_rat_smul (DistribMulAction.toAddMonoidHom M x) r y).symm

instance SMulCommClass.nnrat' [Monoid α] [AddCommMonoid M] [DistribMulAction α M] [Module ℚ≥0 M] :
    SMulCommClass α ℚ≥0 M :=
  SMulCommClass.symm _ _ _

instance SMulCommClass.rat' [Monoid α] [AddCommGroup M] [DistribMulAction α M] [Module ℚ M] :
    SMulCommClass α ℚ M :=
  SMulCommClass.symm _ _ _

end

variable (M) in
/-- A `ℚ≥0`-module is torsion-free as a group.

This instance will fire for any monoid `M`, so is local unless needed elsewhere. -/
lemma IsAddTorsionFree.of_module_nnrat [AddCommMonoid M] [Module ℚ≥0 M] : IsAddTorsionFree M where
  nsmul_right_injective n hn x y hxy := by
    simpa [← Nat.cast_smul_eq_nsmul ℚ≥0 n, *] using congr((n⁻¹ : ℚ≥0) • $hxy)

variable (M) in
/-- A `ℚ≥0`-module is torsion-free as a group.

This instance will fire for any monoid `M`, so is local unless needed elsewhere. -/
lemma IsAddTorsionFree.of_module_rat [AddCommGroup M] [Module ℚ M] : IsAddTorsionFree M where
  nsmul_right_injective n hn x y hxy := by
    simpa [← Nat.cast_smul_eq_nsmul ℚ n, *] using congr((n⁻¹ : ℚ) • $hxy)
