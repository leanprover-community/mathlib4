/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
import Mathlib.RingTheory.Presentation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.FinitePresentation
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Standard smooth algebras

In this file we define standard smooth presentations for algebras. This notion
is introduced for `SubmersivePresentations`, which is a `Presentation`
that has less relations than generators. More precisely there exists
an injective map from `P.relations` to `P.vars`.

-/

universe t t' w w' u v

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S]

open TensorProduct

namespace Algebra

/--
A `SubmersivePresentation` of an `R`-algebra `S` is a `Presentation`
with finitely-many relations equipped with an injective `map : relations → vars`.
-/
structure SubmersivePresentation extends Algebra.Presentation.{t, w} R S where
  /- A map from the relations type to the variables type. -/
  map : relations → vars
  map_inj : Function.Injective map
  relations_finite : Finite relations

namespace SubmersivePresentation

attribute [instance] relations_finite

variable {R S}
variable (P : SubmersivePresentation R S)

lemma card_relations_le_card_vars_of_isFinite [P.IsFinite] : 
    Nat.card P.relations ≤ Nat.card P.vars :=
  Nat.card_le_card_of_injective P.map P.map_inj

noncomputable abbrev basis : Basis P.relations P.Ring (P.relations → P.Ring) :=
  Pi.basisFun P.Ring P.relations

/--
A `SubmersivePresentation` induces a `P.Ring`-linear map on
`P.relations → P.Ring`.

More precisely, the `j`-th standard basis
vector, corresponding to the `j`-th relation of `P` is mapped
to the vector of partial derivatives of `P.relation j` with respect
to the coordinates `P.map i` for all `i : P.relations`.

The determinant of this map is used to define when a `SubmersivePresentation`
is standard smooth. See `SubmersivePresentation.det`.
-/
noncomputable def linearMap : (P.relations → P.Ring) →ₗ[P.Ring] (P.relations → P.Ring) :=
  Basis.constr P.basis P.Ring
    (fun j i : P.relations ↦ MvPolynomial.pderiv (P.map i) (P.relation j))

/-- The determinant of a `P : SubmersivePresentation` is the determinant
of `P.linearMap` viewed as element of `S`. -/
noncomputable def det : S :=
  algebraMap P.Ring S <| LinearMap.det P.linearMap

section Constructors

variable {T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : SubmersivePresentation S T) (P : SubmersivePresentation R S)

@[simps map]
noncomputable def comp :
    SubmersivePresentation R T where
  toPresentation := Q.toPresentation.comp P.toPresentation
  map := Sum.elim (fun rq ↦ Sum.inl <| Q.map rq) (fun rp ↦ Sum.inr <| P.map rp)
  map_inj a b hab := by match a, b with
    | Sum.inl a, Sum.inl b =>
        simp only [Sum.elim_inl] at hab
        apply Sum.inl_injective at hab
        apply Q.map_inj at hab
        rw [hab]
    | Sum.inr a, Sum.inr b =>
        simp only [Sum.elim_inr] at hab
        apply Sum.inr_injective at hab
        apply P.map_inj at hab
        rw [hab]
  relations_finite := inferInstanceAs <| Finite (Q.relations ⊕ P.relations)

/-- The dimension of the composition of two finite submersive presentations is
the sum of the dimensions. -/
lemma dimension_comp_eq_dimension_add_dimension [Q.IsFinite] [P.IsFinite] :
    (Q.comp P).dimension = Q.dimension + P.dimension := by
  simp only [Presentation.dimension]
  erw [Presentation.comp_relations, Generators.comp_vars]
  have : Nat.card P.relations ≤ Nat.card P.vars :=
    card_relations_le_card_vars_of_isFinite P
  have : Nat.card Q.relations ≤ Nat.card Q.vars :=
    card_relations_le_card_vars_of_isFinite Q
  simp only [Nat.card_sum]
  omega

lemma pderiv_rename {σ τ : Type*} (f : σ → τ) (x : σ) (p : MvPolynomial σ R)
    (hf : Function.Injective f) :
    MvPolynomial.pderiv (f x) (MvPolynomial.rename f p) =
      MvPolynomial.rename f (MvPolynomial.pderiv x p) := by
  classical
  induction' p using MvPolynomial.induction_on with a p q hp hq p a h
  · simp
  · simp [hp, hq]
  · simp [h, Pi.single_apply, hf.eq_iff]
    split_ifs
    rfl
    simp

lemma linearMap_comp_basis_P_inl (i : P.relations) (j : Q.relations) :
    (Q.comp P).linearMap ((Q.comp P).basis (Sum.inr i))
      (Sum.inl j) = 0 := by
  simp [linearMap]
  apply MvPolynomial.pderiv_eq_zero_of_not_mem_vars
  erw [Presentation.comp_relation]
  simp
  intro hmem
  apply MvPolynomial.vars_rename at hmem
  classical
  erw [Finset.mem_image] at hmem
  simp at hmem

lemma linearMap_comp_basis_P_inr (i : P.relations) (j : P.relations) :
    (Q.comp P).linearMap ((Q.comp P).basis (Sum.inr i)) (Sum.inr j) =
      MvPolynomial.rename Sum.inr (P.linearMap (P.basis i) j) := by
  simp [linearMap]
  erw [Presentation.comp_relation]
  simp
  erw [pderiv_rename Sum.inr]
  exact Sum.inr_injective

open MvPolynomial

lemma linearMap_comp_basis_Q_inr (i : Q.relations) (j : Q.relations) :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val))
      ((Q.comp P).linearMap ((Q.comp P).basis (Sum.inl i)) (Sum.inl j)) =
        Q.linearMap (Q.basis i) j := by
  simp [linearMap]
  rw [← Presentation.comp_relation_map Q.toPresentation P.toPresentation]
  change (aeval (Sum.elim X (C ∘ P.val))) ((pderiv (Sum.inl (Q.map j))) ((Q.comp P).relation (Sum.inl i))) =
    (pderiv (Q.map j)) ((aeval (Sum.elim X (C ∘ P.val))) ((Q.comp P).relation (Sum.inl i)))
  induction' (Q.comp P).relation (Sum.inl i) using MvPolynomial.induction_on with a p q hp hq p q h
  · erw [pderiv_C]
    simp only [map_zero]
    erw [aeval_C]
    simp
  · simp [hp, hq]
  · simp only [Derivation.leibniz, smul_eq_mul, map_add, _root_.map_mul, aeval_X, h, add_left_inj]
    congr
    classical
    rw [pderiv_X]
    rw [Pi.single_apply]
    match q with
    | Sum.inl q =>
        simp only [Sum.inl.injEq, RingHom.map_ite_one_zero, Sum.elim_inl, pderiv_X]
        rw [Pi.single_apply]
    | Sum.inr q => simp

open Classical

lemma foo [Fintype Q.relations] [Fintype P.relations] :
    letI : Fintype (Q.comp P).relations := inferInstanceAs <| Fintype (Q.relations ⊕ P.relations)
    (aeval (Q.comp P).val)
      (((LinearMap.toMatrix (Q.comp P).basis (Q.comp P).basis) (Q.comp P).linearMap).toBlocks₁₁).det = Q.det := by
    letI : Fintype (Q.comp P).relations := inferInstanceAs <| Fintype (Q.relations ⊕ P.relations)
    unfold SubmersivePresentation.det
    rw [AlgHom.map_det (aeval (Q.comp P).val)]
    rw [← LinearMap.det_toMatrix Q.basis]
    rw [RingHom.map_det]
    congr
    ext i j : 1
    simp
    unfold Matrix.toBlocks₁₁
    simp
    rw [LinearMap.toMatrix_apply]
    simp only [Pi.basisFun_repr]
    rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, ← linearMap_comp_basis_Q_inr Q P]
    induction' ((Q.comp P).linearMap ((Q.comp P).basis (Sum.inl j)) (Sum.inl i))
      using MvPolynomial.induction_on with r p q hp hq p i h
    · simp
      erw [aeval_C (Sum.elim X (⇑C ∘ P.val))]
      simp
      rw [← IsScalarTower.algebraMap_apply]
    · simp [hp, hq]
    · simp [h]
      match i with
      | Sum.inl i => simp; rfl
      | Sum.inr i => simp; rfl

lemma det_comp_eq_det_smul_det : (Q.comp P).det = P.det • Q.det := by
  simp [det]
  cases nonempty_fintype Q.relations
  cases nonempty_fintype P.relations
  letI : Fintype (Q.comp P).relations := inferInstanceAs <| Fintype (Q.relations ⊕ P.relations)
  classical
  rw [← LinearMap.det_toMatrix (Q.comp P).basis]
  rw [← Matrix.fromBlocks_toBlocks ((LinearMap.toMatrix (Q.comp P).basis (Q.comp P).basis) (Q.comp P).linearMap)]
  have :
    ((LinearMap.toMatrix (Q.comp P).basis (Q.comp P).basis) (Q.comp P).linearMap).toBlocks₁₂ = 0 := by
      ext i j : 1
      simp
      unfold Matrix.toBlocks₁₂
      simp
      rw [LinearMap.toMatrix_apply]
      simp only [Pi.basisFun_repr]
      exact linearMap_comp_basis_P_inl Q P j i
  rw [this]
  have := Matrix.det_fromBlocks_zero₁₂
    (((LinearMap.toMatrix (Q.comp P).basis (Q.comp P).basis) (Q.comp P).linearMap).toBlocks₁₁)
    (((LinearMap.toMatrix (Q.comp P).basis (Q.comp P).basis) (Q.comp P).linearMap).toBlocks₂₁)
    (((LinearMap.toMatrix (Q.comp P).basis (Q.comp P).basis) (Q.comp P).linearMap).toBlocks₂₂)
  apply_fun (aeval (Q.comp P).val) at this
  convert this
  simp
  have : (aeval (Q.comp P).val)
      (((LinearMap.toMatrix (Q.comp P).basis (Q.comp P).basis) (Q.comp P).linearMap).toBlocks₁₁).det = Q.det :=
    foo Q P
  rw [this]
  have : (aeval (Q.comp P).val)
      ((LinearMap.toMatrix (Q.comp P).basis (Q.comp P).basis) (Q.comp P).linearMap).toBlocks₂₂.det =
      algebraMap S T P.det := by
    unfold SubmersivePresentation.det
    rw [AlgHom.map_det (aeval (Q.comp P).val)]
    rw [← LinearMap.det_toMatrix P.basis]
    rw [RingHom.map_det, RingHom.map_det]
    congr
    ext i j : 1
    simp
    unfold Matrix.toBlocks₂₂
    simp
    rw [LinearMap.toMatrix_apply]
    simp only [Pi.basisFun_repr]
    rw [linearMap_comp_basis_P_inr]
    erw [aeval_rename]
    rw [LinearMap.toMatrix_apply]
    simp only [Pi.basisFun_repr]
    rw [aeval_def]
    rw [← IsScalarTower.algebraMap_eq]
    rfl
  rw [this]
  rw [mul_comm]
  rw [Algebra.smul_def]
  rfl

end Constructors

/-
Note: the definition of `IsStandardSmooth` does not necessarily need
`presentation_finite`.

Should we generalize this and call it `IsWeaklyStandardSmooth`
and have `IsStandardSmooth` additionally?
-/

/-- A `SubmersivePresentation` is standard smooth if its determinant is a unit
and the presentation is finite. -/
class IsStandardSmooth (P : SubmersivePresentation R S) : Prop where
  det_isUnit : IsUnit P.det
  presentation_finite : P.IsFinite := by infer_instance

attribute [instance] IsStandardSmooth.presentation_finite

section Comp

variable {T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : SubmersivePresentation S T) (P : SubmersivePresentation R S)

instance comp_isStandardSmooth [P.IsStandardSmooth] [Q.IsStandardSmooth] : (Q.comp P).IsStandardSmooth where
  det_isUnit := by
    rw [det_comp_eq_det_smul_det, Algebra.smul_def, IsUnit.mul_iff]
    constructor
    · apply RingHom.isUnit_map
      exact IsStandardSmooth.det_isUnit
    · exact IsStandardSmooth.det_isUnit
  presentation_finite :=
    Presentation.comp_isFinite Q.toPresentation P.toPresentation

end Comp

/--
A `SubmersivePresentation` is standard smooth of relative dimension `n` if it is
standard smooth and the presentation is of dimension `n`.
-/
class IsStandardSmoothOfRelativeDimension (P : SubmersivePresentation R S) (n : ℕ) : Prop where
  isStandardSmooth : P.IsStandardSmooth := by infer_instance
  dimension_eq' : P.dimension = n

lemma dimension_eq {n : ℕ} [P.IsStandardSmoothOfRelativeDimension n] : P.dimension = n :=
  IsStandardSmoothOfRelativeDimension.dimension_eq'

section Comp

variable {T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : SubmersivePresentation S T) (P : SubmersivePresentation R S)

instance {n m : ℕ} [P.IsStandardSmoothOfRelativeDimension n]
    [Q.IsStandardSmoothOfRelativeDimension m] :
    (Q.comp P).IsStandardSmoothOfRelativeDimension (n + m) where
  isStandardSmooth :=
    have : Q.IsStandardSmooth := IsStandardSmoothOfRelativeDimension.isStandardSmooth m
    have : P.IsStandardSmooth := IsStandardSmoothOfRelativeDimension.isStandardSmooth n
    comp_isStandardSmooth Q P
  dimension_eq' := by
    rw [← dimension_eq (n := m) Q, ← dimension_eq (n := n) P, add_comm]
    have : Q.IsStandardSmooth := IsStandardSmoothOfRelativeDimension.isStandardSmooth m
    have : P.IsStandardSmooth := IsStandardSmoothOfRelativeDimension.isStandardSmooth n
    exact dimension_comp_eq_dimension_add_dimension Q P

end Comp

section BaseChange

noncomputable
def baseChange {R S T} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (P : SubmersivePresentation R S) : SubmersivePresentation T (T ⊗[R] S) where
  __ := P.toPresentation.baseChange
  map := P.map
  map_inj := P.map_inj
  relations_finite := P.relations_finite

theorem baseChange_isStandardSmooth {R S T} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (P : SubmersivePresentation R S) (hP : P.IsStandardSmooth) :
      (baseChange P (T := T)).IsStandardSmooth := by
  classical
  constructor
  let P' := baseChange P (T := T)
  cases nonempty_fintype P.relations
  obtain ⟨a⟩ := nonempty_fintype P'.relations
  have : LinearMap.toMatrix (Pi.basisFun _ _) (Pi.basisFun _ _) P'.linearMap =
    (MvPolynomial.map (algebraMap R T)).mapMatrix
      (LinearMap.toMatrix (Pi.basisFun _ _) (Pi.basisFun _ _) P.linearMap) := by
    ext i j : 1
    simp [LinearMap.toMatrix, SubmersivePresentation.linearMap, P', baseChange, Presentation.baseChange]
    induction' P.relation j using MvPolynomial.induction_on
    · simp
      erw [MvPolynomial.map_C]
      simp
    · simp[*]
    · simp[*, Pi.single_apply]
      split <;> rfl
  apply_fun Matrix.det at this
  erw [← RingHom.map_det] at this
  simp only [LinearMap.det_toMatrix] at this
  erw [SubmersivePresentation.det, this]
  have := hP.1.map (Algebra.TensorProduct.includeRight (R := R) (A := T))
  convert this
  erw [LinearMap.det_toMatrix]
  simp
  erw [MvPolynomial.aeval_map_algebraMap]
  show _ = Algebra.TensorProduct.includeRight (MvPolynomial.aeval _ _)
  erw [MvPolynomial.map_aeval]
  erw [(Algebra.TensorProduct.includeRight).comp_algebraMap]
  rfl
  exact ⟨hP.2.1, hP.2.2⟩

end BaseChange

end SubmersivePresentation

/--
An `R`-algebra `S` is called standard smooth, if there
exists a standard smooth submersive presentation.
-/
class IsStandardSmooth : Prop where
  out : ∃ (P : SubmersivePresentation.{t, w} R S), P.IsStandardSmooth

namespace IsStandardSmooth

section Comp

variable {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

lemma comp [IsStandardSmooth.{t, w} R S] [IsStandardSmooth.{t', w'} S T] :
    IsStandardSmooth.{max t t', max w w'} R T where
  out := by
    obtain ⟨P, hP⟩ := ‹IsStandardSmooth R S›
    obtain ⟨Q, hQ⟩ := ‹IsStandardSmooth S T›
    use Q.comp P
    infer_instance

end Comp

end IsStandardSmooth

/--
An `R`-algebra `S` is called standard smooth of relative dimension `n`, if there
exists a standard smooth submersive presentation.
-/
class IsStandardSmoothOfRelativeDimension (n : ℕ) : Prop where
  out : ∃ (P : SubmersivePresentation.{t, w} R S), P.IsStandardSmoothOfRelativeDimension n

end Algebra
