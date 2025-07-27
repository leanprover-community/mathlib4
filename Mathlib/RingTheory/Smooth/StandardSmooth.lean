/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Standard smooth algebras

In this file we define standard smooth algebras. For this we introduce
the notion of a `PreSubmersivePresentation`. This is a presentation `P` that has
fewer relations than generators. More precisely there exists an injective map from `σ`
to `ι`. To such a presentation we may associate a jacobian. `P` is then a submersive
presentation, if its jacobian is invertible.

Finally, a standard smooth algebra is an algebra that admits a submersive presentation.

While every standard smooth algebra is smooth, the converse does not hold. But if `S` is `R`-smooth,
then `S` is `R`-standard smooth locally on `S`, i.e. there exists a set `{ t }` of `S` that
generates the unit ideal, such that `Sₜ` is `R`-standard smooth for every `t` (TODO, see below).

## Main definitions

All of these are in the `Algebra` namespace. Let `S` be an `R`-algebra.

- `PreSubmersivePresentation`: A `Presentation` of `S` as `R`-algebra, equipped with an injective
  map `P.map` from `σ` to `ι`. This map is used to define the differential of a
  presubmersive presentation.

For a presubmersive presentation `P` of `S` over `R` we make the following definitions:

- `PreSubmersivePresentation.differential`: A linear endomorphism of `σ → P.Ring` sending
  the `j`-th standard basis vector, corresponding to the `j`-th relation, to the vector
  of partial derivatives of `P.relation j` with respect to the coordinates `P.map i` for
  `i : σ`.
- `PreSubmersivePresentation.jacobian`: The determinant of `P.differential`.
- `PreSubmersivePresentation.jacobiMatrix`: If `σ` has a `Fintype` instance, we may form
  the matrix corresponding to `P.differential`. Its determinant is `P.jacobian`.
- `SubmersivePresentation`: A submersive presentation is a finite, presubmersive presentation `P`
  with in `S` invertible jacobian.

Furthermore, for algebras we define:

- `Algebra.IsStandardSmooth`: `S` is `R`-standard smooth if `S` admits a submersive
  `R`-presentation.
- `Algebra.IsStandardSmooth.relativeDimension`: If `S` is `R`-standard smooth this is the dimension
  of an arbitrary submersive `R`-presentation of `S`. This is independent of the choice
  of the presentation (TODO, see below).
- `Algebra.IsStandardSmoothOfRelativeDimension n`: `S` is `R`-standard smooth of relative dimension
  `n` if it admits a submersive `R`-presentation of dimension `n`.

Finally, for ring homomorphisms we define:

- `RingHom.IsStandardSmooth`: A ring homomorphism `R →+* S` is standard smooth if `S` is standard
  smooth as `R`-algebra.
- `RingHom.IsStandardSmoothOfRelativeDimension n`: A ring homomorphism `R →+* S` is standard
  smooth of relative dimension `n` if `S` is standard smooth of relative dimension `n` as
  `R`-algebra.

## TODO

- Show that the module of Kaehler differentials of a standard smooth `R`-algebra `S` of relative
  dimension `n` is `S`-free of rank `n`. In particular this shows that the relative dimension
  is independent of the choice of the standard smooth presentation.
- Show that standard smooth algebras are smooth. This relies on the computation of the module of
  Kaehler differentials.
- Show that locally on the target, smooth algebras are standard smooth.

## Implementation details

Standard smooth algebras and ring homomorphisms feature 4 universe levels: The universe levels of
the rings involved and the universe levels of the types of the variables and relations.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

universe t t' w w' u v

open TensorProduct Module MvPolynomial

variable (n m : ℕ)

namespace Algebra

variable (R : Type u) (S : Type v) (ι : Type w) (σ : Type t) [CommRing R] [CommRing S] [Algebra R S]

/--
A `PreSubmersivePresentation` of an `R`-algebra `S` is a `Presentation`
with relations equipped with an injective `map : relations → vars`.

This map determines how the differential of `P` is constructed. See
`PreSubmersivePresentation.differential` for details.
-/
@[nolint checkUnivs]
structure PreSubmersivePresentation extends Algebra.Presentation R S ι σ where
  /-- A map from the relations type to the variables type. Used to compute the differential. -/
  map : σ → ι
  map_inj : Function.Injective map

namespace PreSubmersivePresentation

variable {R S ι σ}
variable (P : PreSubmersivePresentation R S ι σ)

include P in
lemma card_relations_le_card_vars_of_isFinite [Finite ι] :
    Nat.card σ ≤ Nat.card ι :=
  Nat.card_le_card_of_injective P.map P.map_inj

section

variable [Finite σ]

/-- The standard basis of `σ → P.ring`. -/
noncomputable abbrev basis : Basis σ P.Ring (σ → P.Ring) :=
  Pi.basisFun P.Ring σ

/--
The differential of a `P : PreSubmersivePresentation` is a `P.Ring`-linear map on
`σ → P.Ring`:

The `j`-th standard basis vector, corresponding to the `j`-th relation of `P`, is mapped
to the vector of partial derivatives of `P.relation j` with respect
to the coordinates `P.map i` for all `i : σ`.

The determinant of this map is the jacobian of `P` used to define when a `PreSubmersivePresentation`
is submersive. See `PreSubmersivePresentation.jacobian`.
-/
noncomputable def differential : (σ → P.Ring) →ₗ[P.Ring] (σ → P.Ring) :=
  Basis.constr P.basis P.Ring
    (fun j i : σ ↦ MvPolynomial.pderiv (P.map i) (P.relation j))

/-- `PreSubmersivePresentation.differential` pushed forward to `S` via `aeval P.val`. -/
noncomputable def aevalDifferential : (σ → S) →ₗ[S] (σ → S) :=
  (Pi.basisFun S σ).constr S
    (fun j i : σ ↦ aeval P.val <| pderiv (P.map i) (P.relation j))

@[simp]
lemma aevalDifferential_single [DecidableEq σ] (i j : σ) :
    P.aevalDifferential (Pi.single i 1) j = aeval P.val (pderiv (P.map j) (P.relation i)) := by
  dsimp only [aevalDifferential]
  rw [← Pi.basisFun_apply, Basis.constr_basis]

/-- The jacobian of a `P : PreSubmersivePresentation` is the determinant
of `P.differential` viewed as element of `S`. -/
noncomputable def jacobian : S :=
  algebraMap P.Ring S <| LinearMap.det P.differential

end

section Matrix

variable [Fintype σ] [DecidableEq σ]

/--
If `σ` has a `Fintype` and `DecidableEq` instance, the differential of `P`
can be expressed in matrix form.
-/
noncomputable def jacobiMatrix : Matrix σ σ P.Ring :=
  LinearMap.toMatrix P.basis P.basis P.differential

lemma jacobian_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det := by
  simp [jacobiMatrix, jacobian]

lemma jacobiMatrix_apply (i j : σ) :
    P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j) := by
  simp [jacobiMatrix, LinearMap.toMatrix, differential, basis]

lemma aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix :
    P.aevalDifferential.toMatrix' = (aeval P.val).mapMatrix P.jacobiMatrix := by
  ext i j : 1
  rw [← LinearMap.toMatrix_eq_toMatrix']
  rw [LinearMap.toMatrix_apply]
  simp [jacobiMatrix_apply]

end Matrix

section Constructions

/-- If `algebraMap R S` is bijective, the empty generators are a pre-submersive
presentation with no relations. -/
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    PreSubmersivePresentation R S PEmpty.{w + 1} PEmpty.{t + 1} where
  toPresentation := Presentation.ofBijectiveAlgebraMap.{t, w} h
  map := PEmpty.elim
  map_inj (a b : PEmpty) h := by contradiction

@[simp]
lemma ofBijectiveAlgebraMap_jacobian (h : Function.Bijective (algebraMap R S)) :
    (ofBijectiveAlgebraMap h).jacobian = 1 := by
  classical
  have : (algebraMap (ofBijectiveAlgebraMap h).Ring S).mapMatrix
      (ofBijectiveAlgebraMap h).jacobiMatrix = 1 := by
    ext (i j : PEmpty)
    contradiction
  rw [jacobian_eq_jacobiMatrix_det, RingHom.map_det, this, Matrix.det_one]

section Localization

variable (r : R) [IsLocalization.Away r S]

variable (S) in
/-- If `S` is the localization of `R` at `r`, this is the canonical submersive presentation
of `S` as `R`-algebra. -/
@[simps map]
noncomputable def localizationAway : PreSubmersivePresentation R S Unit Unit where
  __ := Presentation.localizationAway S r
  map _ := ()
  map_inj _ _ h := h

@[simp]
lemma localizationAway_jacobiMatrix :
    (localizationAway S r).jacobiMatrix = Matrix.diagonal (fun () ↦ MvPolynomial.C r) := by
  have h : (pderiv ()) (C r * X () - 1) = C r := by simp
  ext (i : Unit) (j : Unit) : 1
  rwa [jacobiMatrix_apply]

@[simp]
lemma localizationAway_jacobian : (localizationAway S r).jacobian = algebraMap R S r := by
  rw [jacobian_eq_jacobiMatrix_det, localizationAway_jacobiMatrix]
  simp [show Fintype.card (localizationAway r (S := S)).rels = 1 from rfl]

end Localization

section Composition

variable {ι' σ' T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : PreSubmersivePresentation S T ι' σ') (P : PreSubmersivePresentation R S ι σ)

/-- Given an `R`-algebra `S` and an `S`-algebra `T` with pre-submersive presentations,
this is the canonical pre-submersive presentation of `T` as an `R`-algebra. -/
@[simps map]
noncomputable def comp : PreSubmersivePresentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
  __ := Q.toPresentation.comp P.toPresentation
  map := Sum.elim (fun rq ↦ Sum.inl <| Q.map rq) (fun rp ↦ Sum.inr <| P.map rp)
  map_inj := Function.Injective.sumElim ((Sum.inl_injective).comp (Q.map_inj))
    ((Sum.inr_injective).comp (P.map_inj)) <| by simp

lemma toPresentation_comp : (Q.comp P).toPresentation = Q.toPresentation.comp P.toPresentation :=
  rfl

lemma toGenerators_comp : (Q.comp P).toGenerators = Q.toGenerators.comp P.toGenerators := rfl

/-- The dimension of the composition of two finite submersive presentations is
the sum of the dimensions. -/
lemma dimension_comp_eq_dimension_add_dimension [Finite ι] [Finite ι'] [Finite σ] [Finite σ'] :
    (Q.comp P).dimension = Q.dimension + P.dimension := by
  simp only [Presentation.dimension]
  have : Nat.card σ ≤ Nat.card ι :=
    card_relations_le_card_vars_of_isFinite P
  have : Nat.card σ' ≤ Nat.card ι' :=
    card_relations_le_card_vars_of_isFinite Q
  simp only [Nat.card_sum]
  omega

section

/-!
### Jacobian of composition

Let `S` be an `R`-algebra and `T` be an `S`-algebra with presentations `P` and `Q` respectively.
In this section we compute the jacobian of the composition of `Q` and `P` to be
the product of the jacobians. For this we use a block decomposition of the jacobi matrix and show
that the upper-right block vanishes, the upper-left block has determinant jacobian of `Q` and
the lower-right block has determinant jacobian of `P`.

-/

variable [Fintype σ] [Fintype σ']

open scoped Classical in
private lemma jacobiMatrix_comp_inl_inr (i : σ') (j : σ) :
    (Q.comp P).jacobiMatrix (Sum.inl i) (Sum.inr j) = 0 := by
  classical
  rw [jacobiMatrix_apply]
  refine MvPolynomial.pderiv_eq_zero_of_notMem_vars (fun hmem ↦ ?_)
  apply MvPolynomial.vars_rename at hmem
  simp at hmem

open scoped Classical in
private lemma jacobiMatrix_comp_₁₂ : (Q.comp P).jacobiMatrix.toBlocks₁₂ = 0 := by
  ext i j : 1
  simp [Matrix.toBlocks₁₂, jacobiMatrix_comp_inl_inr]

section Q

open scoped Classical in
private lemma jacobiMatrix_comp_inl_inl (i j : σ') :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val))
      ((Q.comp P).jacobiMatrix (Sum.inl j) (Sum.inl i)) = Q.jacobiMatrix j i := by
  rw [jacobiMatrix_apply, jacobiMatrix_apply, comp_map, Sum.elim_inl,
    ← Q.comp_aeval_relation_inl P.toPresentation]
  apply aeval_sumElim_pderiv_inl

open scoped Classical in
private lemma jacobiMatrix_comp_₁₁_det :
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det = Q.jacobian := by
  rw [jacobian_eq_jacobiMatrix_det, AlgHom.map_det (aeval (Q.comp P).val), RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, ← Q.jacobiMatrix_comp_inl_inl P,
    Q.algebraMap_apply]
  apply aeval_sumElim

end Q

section P

open scoped Classical in
private lemma jacobiMatrix_comp_inr_inr (i j : σ) :
    (Q.comp P).jacobiMatrix (Sum.inr i) (Sum.inr j) =
      MvPolynomial.rename Sum.inr (P.jacobiMatrix i j) := by
  rw [jacobiMatrix_apply, jacobiMatrix_apply]
  simp only [comp_map, Sum.elim_inr]
  apply pderiv_rename Sum.inr_injective

open scoped Classical in
private lemma jacobiMatrix_comp_₂₂_det :
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = algebraMap S T P.jacobian := by
  rw [jacobian_eq_jacobiMatrix_det]
  rw [AlgHom.map_det (aeval (Q.comp P).val), RingHom.map_det, RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.toBlocks₂₂, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    RingHom.mapMatrix_apply, Generators.algebraMap_apply, map_aeval, coe_eval₂Hom]
  rw [jacobiMatrix_comp_inr_inr, ← IsScalarTower.algebraMap_eq]
  simp only [aeval, AlgHom.coe_mk, coe_eval₂Hom]
  generalize P.jacobiMatrix i j = p
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [algHom_C, algebraMap_eq, eval₂_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, eval₂_mul, hp]
    simp [Presentation.toGenerators_comp, toPresentation_comp]

end P

end

/-- The jacobian of the composition of presentations is the product of the jacobians. -/
@[simp]
lemma comp_jacobian_eq_jacobian_smul_jacobian [Finite σ] [Finite σ'] :
    (Q.comp P).jacobian = P.jacobian • Q.jacobian := by
  classical
  cases nonempty_fintype σ'
  cases nonempty_fintype σ
  rw [jacobian_eq_jacobiMatrix_det, ← Matrix.fromBlocks_toBlocks ((Q.comp P).jacobiMatrix),
    jacobiMatrix_comp_₁₂]
  convert_to
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det *
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = P.jacobian • Q.jacobian
  · simp only [Generators.algebraMap_apply, ← map_mul]
    congr
    convert Matrix.det_fromBlocks_zero₁₂ (Q.comp P).jacobiMatrix.toBlocks₁₁
      (Q.comp P).jacobiMatrix.toBlocks₂₁ (Q.comp P).jacobiMatrix.toBlocks₂₂
  · rw [jacobiMatrix_comp_₁₁_det, jacobiMatrix_comp_₂₂_det, mul_comm, Algebra.smul_def]

end Composition

section BaseChange

variable (T : Type*) [CommRing T] [Algebra R T] (P : PreSubmersivePresentation R S ι σ)

/-- If `P` is a pre-submersive presentation of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural pre-submersive presentation of `T ⊗[R] S` over `T`. -/
noncomputable def baseChange : PreSubmersivePresentation T (T ⊗[R] S) ι σ where
  __ := P.toPresentation.baseChange T
  map := P.map
  map_inj := P.map_inj

lemma baseChange_toPresentation :
    (P.baseChange R).toPresentation = P.toPresentation.baseChange R :=
  rfl

lemma baseChange_ring : (P.baseChange R).Ring = P.Ring := rfl

@[simp]
lemma baseChange_jacobian [Finite σ] : (P.baseChange T).jacobian = 1 ⊗ₜ P.jacobian := by
  classical
  cases nonempty_fintype σ
  simp_rw [jacobian_eq_jacobiMatrix_det]
  have h : (baseChange T P).jacobiMatrix =
      (MvPolynomial.map (algebraMap R T)).mapMatrix P.jacobiMatrix := by
    ext i j : 1
    simp only [baseChange, jacobiMatrix_apply, Presentation.baseChange_relation,
      RingHom.mapMatrix_apply, Matrix.map_apply,
      Presentation.baseChange_toGenerators, MvPolynomial.pderiv_map]
  rw [h]
  erw [← RingHom.map_det, aeval_map_algebraMap]
  rw [P.algebraMap_apply]
  apply aeval_one_tmul

end BaseChange

/-- Given a pre-submersive presentation `P` and equivalences `ι' ≃ ι` and
`σ' ≃ σ`, this is the induced pre-sumbersive presentation with variables indexed
by `ι` and relations indexed by `κ -/
@[simps toPresentation, simps -isSimp map]
noncomputable def reindex (P : PreSubmersivePresentation R S ι σ)
    {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) :
    PreSubmersivePresentation R S ι' σ' where
  __ := P.toPresentation.reindex e f
  map := e.symm ∘ P.map ∘ f
  map_inj := by
    rw [Function.Injective.of_comp_iff e.symm.injective, Function.Injective.of_comp_iff P.map_inj]
    exact f.injective

lemma jacobiMatrix_reindex {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ)
    [Fintype σ'] [DecidableEq σ'] [Fintype σ] [DecidableEq σ] :
    (P.reindex e f).jacobiMatrix =
      (P.jacobiMatrix.reindex f.symm f.symm).map (MvPolynomial.rename e.symm) := by
  ext i j : 1
  simp [jacobiMatrix_apply,
    MvPolynomial.pderiv_rename e.symm.injective, reindex, Presentation.reindex]

@[simp]
lemma jacobian_reindex (P : PreSubmersivePresentation R S ι σ)
    {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) [Finite σ] [Finite σ'] :
    (P.reindex e f).jacobian = P.jacobian := by
  classical
  cases nonempty_fintype σ
  cases nonempty_fintype σ'
  simp_rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  simp only [reindex_toPresentation, Presentation.reindex_toGenerators, jacobiMatrix_reindex,
    Matrix.reindex_apply, Equiv.symm_symm, Generators.algebraMap_apply, Generators.reindex_val]
  simp_rw [← MvPolynomial.aeval_rename,
    ← AlgHom.mapMatrix_apply, ← Matrix.det_submatrix_equiv_self f, AlgHom.map_det,
    AlgHom.mapMatrix_apply, Matrix.map_map]
  simp [← AlgHom.coe_comp, rename_comp_rename, rename_id]

section

variable {v : ι → MvPolynomial σ R} (a : ι → σ) (ha : Function.Injective a)
  (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R :=
    Function.surjInv Ideal.Quotient.mk_surjective)
  (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x := by apply Function.surjInv_eq)

/--
The naive pre-submersive presentation of a quotient `R[Xᵢ] ⧸ (vⱼ)`.
If the definitional equality of the section matters, it can be explicitly provided.

To construct the associated submersive presentation, use
`PreSubmersivePresentation.jacobiMatrix_naive`.
-/
@[simps! toPresentation]
noncomputable
def naive {v : ι → MvPolynomial σ R} (a : ι → σ) (ha : Function.Injective a)
    (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R :=
      Function.surjInv Ideal.Quotient.mk_surjective)
    (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x := by apply Function.surjInv_eq) :
    PreSubmersivePresentation R (MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) σ ι where
  __ := Presentation.naive s hs
  map := a
  map_inj := ha

@[simp] lemma jacobiMatrix_naive [Fintype ι] [DecidableEq ι] (i j : ι) :
    (naive a ha s hs).jacobiMatrix i j = (v j).pderiv (a i) :=
  jacobiMatrix_apply _ _ _

end

end Constructions

end PreSubmersivePresentation

variable [Finite σ]

/--
A `PreSubmersivePresentation` is submersive if its jacobian is a unit in `S`
and the presentation is finite.
-/
@[nolint checkUnivs]
structure SubmersivePresentation extends PreSubmersivePresentation.{t, w} R S ι σ where
  jacobian_isUnit : IsUnit toPreSubmersivePresentation.jacobian

namespace SubmersivePresentation

open PreSubmersivePresentation

section Constructions

variable {R S} in
/-- If `algebraMap R S` is bijective, the empty generators are a submersive
presentation with no relations. -/
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    SubmersivePresentation R S PEmpty.{w + 1} PEmpty.{t + 1} where
  __ := PreSubmersivePresentation.ofBijectiveAlgebraMap.{t, w} h
  jacobian_isUnit := by
    rw [ofBijectiveAlgebraMap_jacobian]
    exact isUnit_one

/-- The canonical submersive `R`-presentation of `R` with no generators and no relations. -/
noncomputable def id : SubmersivePresentation R R PEmpty.{w + 1} PEmpty.{t + 1} :=
  ofBijectiveAlgebraMap Function.bijective_id

section Composition
variable {R S ι σ}
variable {T ι' σ' : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [Finite σ'] (Q : SubmersivePresentation S T ι' σ') (P : SubmersivePresentation R S ι σ)

/-- Given an `R`-algebra `S` and an `S`-algebra `T` with submersive presentations,
this is the canonical submersive presentation of `T` as an `R`-algebra. -/
noncomputable def comp : SubmersivePresentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
  __ := Q.toPreSubmersivePresentation.comp P.toPreSubmersivePresentation
  jacobian_isUnit := by
    rw [comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def, IsUnit.mul_iff]
    exact ⟨RingHom.isUnit_map _ <| P.jacobian_isUnit, Q.jacobian_isUnit⟩

end Composition

section Localization

variable {R} (r : R) [IsLocalization.Away r S]

/-- If `S` is the localization of `R` at `r`, this is the canonical submersive presentation
of `S` as `R`-algebra. -/
noncomputable def localizationAway : SubmersivePresentation R S Unit Unit where
  __ := PreSubmersivePresentation.localizationAway S r
  jacobian_isUnit := by
    rw [localizationAway_jacobian]
    apply IsLocalization.map_units' (⟨r, 1, by simp⟩ : Submonoid.powers r)

end Localization

section BaseChange

variable (T) [CommRing T] [Algebra R T] (P : SubmersivePresentation R S ι σ)

variable {R S ι σ} in
/-- If `P` is a submersive presentation of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural submersive presentation of `T ⊗[R] S` over `T`. -/
noncomputable def baseChange : SubmersivePresentation T (T ⊗[R] S) ι σ where
  toPreSubmersivePresentation := P.toPreSubmersivePresentation.baseChange T
  jacobian_isUnit :=
    P.baseChange_jacobian T ▸ P.jacobian_isUnit.map TensorProduct.includeRight

end BaseChange

variable {R S ι σ} in
/-- Given a submersive presentation `P` and equivalences `ι' ≃ ι` and
`σ' ≃ σ`, this is the induced sumbersive presentation with variables indexed
by `ι'` and relations indexed by `σ'` -/
@[simps toPreSubmersivePresentation]
noncomputable def reindex (P : SubmersivePresentation R S ι σ)
    {ι' σ' : Type*} [Finite σ'] (e : ι' ≃ ι) (f : σ' ≃ σ) : SubmersivePresentation R S ι' σ' where
  __ := P.toPreSubmersivePresentation.reindex e f
  jacobian_isUnit := by simp [P.jacobian_isUnit]

end Constructions

variable {R S ι σ}

open Classical in
/-- If `P` is submersive, `PreSubmersivePresentation.aevalDifferential` is an isomorphism. -/
noncomputable def aevalDifferentialEquiv (P : SubmersivePresentation R S ι σ) :
    (σ → S) ≃ₗ[S] (σ → S) :=
  haveI : Fintype σ := Fintype.ofFinite σ
  have :
      IsUnit (LinearMap.toMatrix (Pi.basisFun S σ) (Pi.basisFun S σ) P.aevalDifferential).det := by
    convert P.jacobian_isUnit
    rw [LinearMap.toMatrix_eq_toMatrix', jacobian_eq_jacobiMatrix_det,
      aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix, P.algebraMap_eq]
    simp [RingHom.map_det]
  LinearEquiv.ofIsUnitDet this

variable (P : SubmersivePresentation R S ι σ)

@[simp]
lemma aevalDifferentialEquiv_apply [Finite σ] (x : σ → S) :
    P.aevalDifferentialEquiv x = P.aevalDifferential x :=
  rfl

/-- If `P` is a submersive presentation, the partial derivatives of `P.relation i` by
`P.map j` form a basis of `σ → S`. -/
noncomputable def basisDeriv (P : SubmersivePresentation R S ι σ) : Basis σ S (σ → S) :=
  Basis.map (Pi.basisFun S σ) P.aevalDifferentialEquiv

@[simp]
lemma basisDeriv_apply (i j : σ) :
    P.basisDeriv i j = (aeval P.val) (pderiv (P.map j) (P.relation i)) := by
  classical
  simp [basisDeriv]

lemma linearIndependent_aeval_val_pderiv_relation :
    LinearIndependent S (fun i j ↦ (aeval P.val) (pderiv (P.map j) (P.relation i))) := by
  simp_rw [← SubmersivePresentation.basisDeriv_apply]
  exact P.basisDeriv.linearIndependent

end SubmersivePresentation

attribute [local instance] Fintype.ofFinite

/--
An `R`-algebra `S` is called standard smooth, if there
exists a submersive presentation.
-/
class IsStandardSmooth : Prop where
  out : ∃ (ι σ : Type) (_ : Finite σ), Finite ι ∧ Nonempty (SubmersivePresentation R S ι σ)

lemma SubmersivePresentation.isStandardSmooth [Finite ι] (P : SubmersivePresentation R S ι σ) :
    IsStandardSmooth R S := by
  exact ⟨_, _, _, inferInstance, ⟨P.reindex (Fintype.equivFin _).symm (Fintype.equivFin _).symm⟩⟩

/--
The relative dimension of a standard smooth `R`-algebra `S` is
the dimension of an arbitrarily chosen submersive `R`-presentation of `S`.

Note: If `S` is non-trivial, this number is independent of the choice of the presentation as it is
equal to the `S`-rank of `Ω[S/R]`
(see `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`).
-/
noncomputable def IsStandardSmooth.relativeDimension [IsStandardSmooth R S] : ℕ :=
  letI := ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose
  ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose_spec.2.some.dimension

/--
An `R`-algebra `S` is called standard smooth of relative dimension `n`, if there exists
a submersive presentation of dimension `n`.
-/
class IsStandardSmoothOfRelativeDimension : Prop where
  out : ∃ (ι σ : Type) (_ : Finite σ) (_ : Finite ι) (P : SubmersivePresentation R S ι σ),
    P.dimension = n

lemma SubmersivePresentation.isStandardSmoothOfRelativeDimension [Finite ι]
    (P : SubmersivePresentation R S ι σ) (hP : P.dimension = n) :
    IsStandardSmoothOfRelativeDimension n R S := by
  refine ⟨⟨_, _, _, inferInstance,
    P.reindex (Fintype.equivFin _).symm (Fintype.equivFin σ).symm, ?_⟩⟩
  simp [hP]

variable {R} {S}

lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth
    [H : IsStandardSmoothOfRelativeDimension n R S] : IsStandardSmooth R S :=
  ⟨_, _, _, H.out.choose_spec.choose_spec.choose_spec.choose,
    H.out.choose_spec.choose_spec.choose_spec.choose_spec.nonempty⟩

lemma IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective
    (h : Function.Bijective (algebraMap R S)) :
    IsStandardSmoothOfRelativeDimension 0 R S :=
  ⟨_, _, _, inferInstance,
    SubmersivePresentation.ofBijectiveAlgebraMap h, Presentation.ofBijectiveAlgebraMap_dimension h⟩

variable (R) in
instance IsStandardSmoothOfRelativeDimension.id :
    IsStandardSmoothOfRelativeDimension 0 R R :=
  IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective Function.bijective_id

instance (priority := 100) IsStandardSmooth.finitePresentation [IsStandardSmooth R S] :
    FinitePresentation R S := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.finitePresentation_of_isFinite

section Composition

variable (R S T) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

lemma IsStandardSmooth.trans [IsStandardSmooth R S] [IsStandardSmooth S T] :
    IsStandardSmooth R T where
  out := by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
    obtain ⟨_, _, _, _, ⟨Q⟩⟩ := ‹IsStandardSmooth S T›
    exact ⟨_, _, _, inferInstance, ⟨Q.comp P⟩⟩

lemma IsStandardSmoothOfRelativeDimension.trans [IsStandardSmoothOfRelativeDimension n R S]
    [IsStandardSmoothOfRelativeDimension m S T] :
    IsStandardSmoothOfRelativeDimension (m + n) R T where
  out := by
    obtain ⟨_, _, _, _, P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    obtain ⟨_, _, _, _, Q, hQ⟩ := ‹IsStandardSmoothOfRelativeDimension m S T›
    refine ⟨_, _, _, inferInstance, Q.comp P, hP ▸ hQ ▸ ?_⟩
    apply PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension

end Composition

lemma IsStandardSmooth.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmooth R S where
  out := ⟨_, _, _, inferInstance, ⟨SubmersivePresentation.localizationAway S r⟩⟩

lemma IsStandardSmoothOfRelativeDimension.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmoothOfRelativeDimension 0 R S where
  out := ⟨_, _, _, inferInstance, SubmersivePresentation.localizationAway S r,
    Presentation.localizationAway_dimension_zero r⟩

section BaseChange

variable (T) [CommRing T] [Algebra R T]

instance IsStandardSmooth.baseChange [IsStandardSmooth R S] :
    IsStandardSmooth T (T ⊗[R] S) where
  out := by
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
    exact ⟨ι, σ, _, inferInstance, ⟨P.baseChange T⟩⟩

instance IsStandardSmoothOfRelativeDimension.baseChange
    [IsStandardSmoothOfRelativeDimension n R S] :
    IsStandardSmoothOfRelativeDimension n T (T ⊗[R] S) where
  out := by
    obtain ⟨_, _, _, _, P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    exact ⟨_, _, _, inferInstance, P.baseChange T, hP⟩

end BaseChange

end Algebra
