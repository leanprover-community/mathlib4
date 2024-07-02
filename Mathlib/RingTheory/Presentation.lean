/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Generators
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!

# Presentations of algebras

A presentation of an `R`-algebra `S` is a distinguished family of generators and relations.

## Main definition

- `Algebra.Presentation`: A presentation of an `R`-algebra `S` is a family of
  generators with
  1. `rels`: The type of relations.
  2. `relation : relations → MvPolynomial vars R`: The assignment of
     each relation to a polynomial in the generators.
- `Algebra.Presentation.IsFinite`: A presentation is called finite, if both variables and relations
  are finite.
- `Algebra.Presentation.dimension`: The dimension of a presentation is the number of generators
  minus the number of relations.

We also give constructors for localization and base change.

## TODO

- Define composition of presentations.
- Define `Hom`s of presentations.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

universe t w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/--
A presentation of an `R`-algebra `S` is a family of
generators with
1. `rels`: The type of relations.
2. `relation : relations → MvPolynomial vars R`: The assignment of
each relation to a polynomial in the generators.
-/
@[nolint checkUnivs]
structure Algebra.Presentation extends Algebra.Generators.{w} R S where
  /-- The type of relations.  -/
  rels : Type t
  /-- The assignment of each relation to a polynomial in the generators. -/
  relation : rels → toGenerators.Ring
  /-- The relations span the kernel of the canonical map. -/
  span_range_relation_eq_ker :
    Ideal.span (Set.range relation) = toGenerators.ker

namespace Algebra.Presentation

variable {R S}
variable (P : Presentation.{t, w} R S)

@[simp]
lemma aeval_val_relation (i) : aeval P.val (P.relation i) = 0 := by
  rw [← RingHom.mem_ker, ← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The polynomial algebra wrt a family of generators modulo a family of relations. -/
protected abbrev Quotient : Type (max w u) := P.Ring ⧸ P.ker

/-- `P.Quotient` is `P.Ring`-isomorphic to `S` and in particular `R`-isomorphic to `S`. -/
def quotientEquiv : P.Quotient ≃ₐ[P.Ring] S :=
  Ideal.quotientKerAlgEquivOfRightInverse (f := Algebra.ofId P.Ring S) P.aeval_val_σ

@[simp]
lemma quotientEquiv_mk (p : P.Ring) : P.quotientEquiv p = algebraMap P.Ring S p :=
  rfl

@[simp]
lemma quotientEquiv_symm (x : S) : P.quotientEquiv.symm x = P.σ x :=
  rfl

/--
Dimension of a presentation defined as the cardinality of the generators
minus the cardinality of the relations.

Note: this definition is completely non-sensical for non-finite presentations and
even then for this to make sense, you should assume that the presentation
is a complete intersection.
-/
noncomputable def dimension : ℕ :=
  Nat.card P.vars - Nat.card P.rels

/-- A presentation is finite if there are only finitely-many
relations and finitely-many relations. -/
class IsFinite (P : Presentation.{t, w} R S) : Prop where
  finite_vars : Finite P.vars
  finite_rels : Finite P.rels

attribute [instance] IsFinite.finite_vars IsFinite.finite_rels

lemma ideal_fg_of_isFinite [P.IsFinite] : P.ker.FG := by
  use (Set.finite_range P.relation).toFinset
  simp [span_range_relation_eq_ker]

/-- If a presentation is finite, the corresponding quotient is
of finite presentation. -/
instance [P.IsFinite] : FinitePresentation R P.Quotient :=
  FinitePresentation.quotient P.ideal_fg_of_isFinite

lemma finitePresentation_of_isFinite [P.IsFinite] :
    FinitePresentation R S :=
  FinitePresentation.equiv (P.quotientEquiv.restrictScalars R)

section Construction

section Localization

variable (r : R) [IsLocalization.Away r S]

open IsLocalization.Away

private lemma span_range_relation_eq_ker_localizationAway :
    Ideal.span { C r * X () - 1 } =
      RingHom.ker (aeval (S₁ := S) (Generators.localizationAway r).val) := by
  have : aeval (S₁ := S) (Generators.localizationAway r).val =
      (mvPolynomialQuotientEquiv S r).toAlgHom.comp
        (Ideal.Quotient.mkₐ R (Ideal.span {C r * X () - 1})) := by
    ext x
    simp only [Generators.localizationAway_vars, aeval_X, Generators.localizationAway_val,
      AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, Ideal.Quotient.mkₐ_eq_mk,
      Function.comp_apply]
    rw [IsLocalization.Away.mvPolynomialQuotientEquiv_apply, aeval_X]
  rw [this]
  erw [← RingHom.comap_ker]
  simp only [Generators.localizationAway_vars, AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe,
    AlgEquiv.toAlgHom_toRingHom]
  show Ideal.span {C r * X () - 1} = Ideal.comap _ (RingHom.ker (mvPolynomialQuotientEquiv S r))
  simp [RingHom.ker_equiv, ← RingHom.ker_eq_comap_bot]

/-- If `S` is the localization of `R` away from `r`, we can construct a natural
presentation of `S` as `R`-algebra with a single generator `X` and the relation `r * X - 1 = 0`. -/
@[simps relation, simps (config := .lemmasOnly) rels]
noncomputable def localizationAway : Presentation R S where
  toGenerators := Generators.localizationAway r
  rels := Unit
  relation _ := C r * X () - 1
  span_range_relation_eq_ker := by
    simp only [Generators.localizationAway_vars, Set.range_const]
    apply span_range_relation_eq_ker_localizationAway r

instance localizationAway_isFinite : (localizationAway r (S := S)).IsFinite where
  finite_vars := inferInstanceAs <| Finite Unit
  finite_rels := inferInstanceAs <| Finite Unit

@[simp]
lemma localizationAway_dimension_zero : (localizationAway r (S := S)).dimension = 0 := by
  simp [Presentation.dimension, localizationAway, Generators.localizationAway_vars]

end Localization

variable {T} [CommRing T] [Algebra R T] (P : Presentation R S)

private lemma span_range_relation_eq_ker_baseChange :
    Ideal.span (Set.range fun i ↦ (MvPolynomial.map (algebraMap R T)) (P.relation i)) =
      RingHom.ker (aeval (R := T) (S₁ := T ⊗[R] S) P.baseChange.val) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x ⟨y, hy⟩
    have Z := aeval_val_relation P y
    apply_fun TensorProduct.includeRight (R := R) (A := T) at Z
    rw [map_zero] at Z
    simp only [SetLike.mem_coe, RingHom.mem_ker, ← Z, ← hy, algebraMap_apply,
      TensorProduct.includeRight_apply]
    erw [aeval_map_algebraMap]
    show _ = TensorProduct.includeRight _
    erw [map_aeval, TensorProduct.includeRight.comp_algebraMap]
    rfl
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have H := Algebra.TensorProduct.lTensor_ker (A := T) (IsScalarTower.toAlgHom R P.Ring S)
      P.algebraMap_surjective
    let e := MvPolynomial.algebraTensorAlgEquiv (R := R) (σ := P.vars) (A := T)
    have H' : e.symm x ∈ RingHom.ker (TensorProduct.map (AlgHom.id R T)
        (IsScalarTower.toAlgHom R P.Ring S)) := by
      rw [RingHom.mem_ker, ← hx]
      clear hx
      induction x using MvPolynomial.induction_on with
      | h_C a =>
        simp only [Generators.algebraMap_apply, algHom_C, TensorProduct.algebraMap_apply,
          id.map_eq_id, RingHom.id_apply, e]
        erw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
        simp only [TensorProduct.algebraMap_apply, id.map_eq_id, RingHom.id_apply,
          TensorProduct.map_tmul, AlgHom.coe_id, id_eq, _root_.map_one, algebraMap_eq]
        erw [aeval_C]
        simp
      | h_add p q hp hq => simp only [map_add, hp, hq]
      | h_X p i hp =>
        simp only [_root_.map_mul, algebraTensorAlgEquiv_symm_X, hp, TensorProduct.map_tmul,
          _root_.map_one, IsScalarTower.coe_toAlgHom', Generators.algebraMap_apply, aeval_X, e]
        congr
        erw [aeval_X]
        rw [Generators.baseChange_val]
    erw [H] at H'
    replace H' : e.symm x ∈ Ideal.map TensorProduct.includeRight P.ker := H'
    erw [← P.span_range_relation_eq_ker, ← Ideal.mem_comap, Ideal.comap_symm,
      Ideal.map_map, Ideal.map_span, ← Set.range_comp] at H'
    convert H'
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      TensorProduct.includeRight_apply, TensorProduct.lift_tmul, _root_.map_one, mapAlgHom_apply,
      one_mul]
    rfl

/-- If `P` is a presentation of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural presentation of `T ⊗[R] S` over `T`. -/
@[simps relation, simps (config := .lemmasOnly) rels]
noncomputable
def baseChange : Presentation T (T ⊗[R] S) where
  __ := Generators.baseChange P.toGenerators
  rels := P.rels
  relation i := MvPolynomial.map (algebraMap R T) (P.relation i)
  span_range_relation_eq_ker := P.span_range_relation_eq_ker_baseChange

end Construction
