/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Generators
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.RingHom.Surjective
/-!

# Presentations of algebras

## Main definition

- `Algebra.Presentation`: A presentation of a `R`-algebra `S` is a family of
  generators with
  1. `relations`: The type of relations.
  2. `relation : relations → MvPolynomial vars R`: The assignment of
     each relation to a polynomial in the generators.

## TODO

- define `Hom`s of presentations

-/

universe t w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/--
A presentation of a `R`-algebra `S` is a family of
generators with
1. `relations`: The type of relations.
2. `relation : relations → MvPolynomial vars R`: The assignment of
each relation to a polynomial in the generators.
-/
structure Algebra.Presentation extends Algebra.Generators.{w} R S where
  /-- The type of relations.  -/
  relations : Type t
  /-- The assignment of each relation to a polynomial in the generators. -/
  relation : relations → MvPolynomial vars R
  /-- The relations span the kernel of the canonical map. -/
  ker_algebraMap_eq_span_range_relation :
    RingHom.ker (algebraMap (MvPolynomial vars R) S) = Ideal.span (Set.range <| relation)

namespace Algebra.Presentation

variable {R S}
variable (P : Presentation.{t, w} R S)

protected abbrev Ideal : Ideal P.Ring := RingHom.ker <| algebraMap P.Ring S

lemma ideal_eq_span_range_relation : P.Ideal = Ideal.span (Set.range <| P.relation) :=
  P.ker_algebraMap_eq_span_range_relation

lemma algebraMap_relation (i) : algebraMap (MvPolynomial P.vars R) S (P.relation i) = 0 := by
  rw [← RingHom.mem_ker, ker_algebraMap_eq_span_range_relation]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The polynomial algebra wrt a family of generators module a family of relations. -/
protected abbrev Quotient : Type (max w u) := P.Ring ⧸ P.Ideal

/-- `P.Quotient` is `P.Ring`-isomorphic to `S` and in particular `R`-isomorphic to `S`. -/
def quotientEquiv : P.Quotient ≃ₐ[P.Ring] S :=
  Ideal.quotientKerAlgEquivOfRightInverse (f := Algebra.ofId P.Ring S) P.aeval_val_σ

@[simp]
lemma quotientEquiv_mk (p : P.Ring) : P.quotientEquiv p = algebraMap P.Ring S p :=
  rfl

@[simp]
lemma quotientEquiv_symm (x : S) : P.quotientEquiv.symm x = P.σ x :=
  rfl

/-- A presentation is called finite if there are only finitely-many
relations and finitely-many relations. -/
class IsFinite (P : Presentation.{t, w} R S) : Prop where
  finite_vars : Finite P.vars
  finite_relations : Finite P.relations

attribute [instance] IsFinite.finite_vars IsFinite.finite_relations

lemma ideal_fg_of_isFinite [P.IsFinite] : P.Ideal.FG := by
  use (Set.finite_range P.relation).toFinset
  simp [ideal_eq_span_range_relation]

/-- If a presentation is finite, the corresponding quotient is
of finite presentation. -/
instance [P.IsFinite] : FinitePresentation R P.Quotient :=
  FinitePresentation.quotient P.ideal_fg_of_isFinite

lemma finitePresentation_of_presentation_of_isFinite [P.IsFinite] :
    FinitePresentation R S :=
  FinitePresentation.equiv (P.quotientEquiv.restrictScalars R)

section Construction

/-
TODO: add constructor for `Presentation` with `Presentation.IsFinite` for
a finitely-presented algebra.
-/

variable {T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : Presentation S T) (P : Presentation R S)

/-- Given presentations of `T` over `S` and of `S` over `R`,
we may construct a presentation of `T` over `R`. -/
@[simps relations, simps (config := .lemmasOnly) relation]
noncomputable def comp : Presentation R T where
  toGenerators := Q.toGenerators.comp P.toGenerators
  relations := Q.relations ⊕ P.relations
  relation := Sum.elim
    (fun rq ↦ Finsupp.sum (Q.relation rq)
      (fun x j ↦ (MvPolynomial.rename Sum.inr <| P.σ j) * monomial (x.mapDomain Sum.inl) 1))
    (fun rp ↦ MvPolynomial.rename Sum.inr <| P.relation rp)
  ker_algebraMap_eq_span_range_relation := by
    ext p
    sorry
    /-
    refine MvPolynomial.induction_on' p ?_ ?_
    · intro u a
      constructor
      intro hua
      simp [RingHom.mem_ker] at hua
    · intro p q hp hq
      constructor
      · intro hl
    -/

lemma comp_relation_map (r : Q.relations) :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val)) ((Q.comp P).relation (Sum.inl r)) = Q.relation r := by
  simp only [comp_relation, Generators.comp_vars, Sum.elim_inl]
  rw [map_finsupp_sum]
  simp only [_root_.map_mul]
  simp_rw [aeval_rename]
  simp_rw [aeval_monomial]
  simp only [Sum.elim_comp_inr, _root_.map_one, one_mul]
  nth_rw 2 [← Finsupp.sum_single (Q.relation r)]
  congr
  ext u s m
  congr
  show _ = monomial u s
  simp only [aeval, AlgHom.coe_mk, coe_eval₂Hom]
  rw [monomial_eq, IsScalarTower.algebraMap_eq R S]
  simp only [algebraMap_eq]
  rw [← eval₂_comp_left, ← aeval_def, P.aeval_val_σ]
  congr
  rw [Finsupp.prod_mapDomain_index_inj]
  simp only [Sum.elim_inl]
  exact Sum.inl_injective

instance comp_isFinite [P.IsFinite] [Q.IsFinite] : (Q.comp P).IsFinite where
  finite_vars := inferInstanceAs <| Finite (Q.vars ⊕ P.vars)
  finite_relations := inferInstanceAs <| Finite (Q.relations ⊕ P.relations)

end Construction

/--
Dimension of a presentation defined as the cardinality of the generators
minus the cardinality of the relations.

Note: this definition is completely non-sensical for non-finite presentations and
even then for this to make sense, you should assume that the presentation
is standard smooth.
-/
noncomputable def dimension : ℕ :=
  Nat.card P.vars - Nat.card P.relations

open TensorProduct

noncomputable
def foo {R S T} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (P : Generators R S) : Generators T (T ⊗[R] S) := by
  --apply surjective_stableUnderBaseChange
  apply Generators.ofSurjective (fun x ↦ 1 ⊗ₜ[R] P.val x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
    let X := P.σ b
    use a • MvPolynomial.map (algebraMap R T) X
    simp [X]
    rw [aeval_map_algebraMap]
    have : ∀ y : P.Ring,
      aeval (fun x ↦ (1 ⊗ₜ[R] P.val x : T ⊗[R] S)) y = 1 ⊗ₜ aeval (fun x ↦ P.val x) y := by
      intro y
      induction y using MvPolynomial.induction_on with
      | h_C a =>
        rw [aeval_C, aeval_C]
        show algebraMap R T a ⊗ₜ 1 = _
        rw [algebraMap_eq_smul_one, smul_tmul, algebraMap_eq_smul_one]
      | h_add p q hp hq =>
        simp [tmul_add]
        rw [hp, hq]
      | h_X p i hp =>
        rw[_root_.map_mul, hp]
        rw[aeval_X]
        rw[_root_.map_mul, aeval_X]
        simp
    rw[this, P.aeval_val_σ, smul_tmul', smul_eq_mul, mul_one]
  | add x y ex ey =>
    obtain ⟨a, ha⟩ := ex
    obtain ⟨b, hb⟩ := ey
    use (a + b)
    rw[map_add, ha, hb]

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 10000000000
noncomputable
def foo2 {R S T} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (P : Presentation R S) : Presentation T (T ⊗[R] S) where
  __ := foo P.toGenerators
  relations := P.relations
  relation := fun i ↦ MvPolynomial.map (algebraMap R T) (P.relation i)
  ker_algebraMap_eq_span_range_relation := by
    dsimp
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      have H := Algebra.TensorProduct.lTensor_ker (A := T) (IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective

      let e := MvPolynomial.algebraTensorAlgEquiv (R := R) (σ := P.vars) (A := T)
      have H' : e.symm x ∈ RingHom.ker (TensorProduct.map (AlgHom.id R T) (IsScalarTower.toAlgHom R P.Ring S)) := by
        rw [RingHom.mem_ker, ← hx]
        clear hx
        induction x using MvPolynomial.induction_on with
        | h_C a =>
          simp only [Generators.algebraMap_apply, algHom_C, TensorProduct.algebraMap_apply,
            id.map_eq_id, RingHom.id_apply, e]
          erw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
          simp
        | h_add p q hp hq =>
          simp only [map_add]
          rw[hp, hq]


        | h_X p i hp =>
          repeat rw[_root_.map_mul]
          rw[hp]
          simp [e]
          rfl
        -- have Z : ∀ x : MvPolynomial (P.vars) (T), (algebraMap (MvPolynomial (foo P.toGenerators).vars T) x =
      erw [H, ker_algebraMap_eq_span_range_relation] at H'
      erw [← Ideal.mem_comap, Ideal.comap_symm, Ideal.map_map, Ideal.map_span, ← Set.range_comp] at H'
      convert H'
      simp
      rfl
    · rw [Ideal.span_le]
      intro x hx
      obtain ⟨y, hy⟩ := hx
      have Z := algebraMap_relation (P) y
      apply_fun TensorProduct.includeRight (R := R) (A := T) at Z
      rw [map_zero] at Z
      show algebraMap _ _ x = 0
      convert Z
      rw [← hy]
      simp
      rw [aeval_map_algebraMap]
      show _ = includeRight _
      erw [map_aeval]
      erw [includeRight.comp_algebraMap]
      rfl
