/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Presentation
import Mathlib.RingTheory.Kaehler.CotangentComplex

/-!
# Standard smooth algebras

In this file we define standard smooth algebras. For this we introduce
the notion of a `PreSubmersivePresentation`. This is a presentation `P` that has
fewer relations than generators. More precisely there exists an injective map from `P.rels`
to `P.vars`. To such a presentation we may associate a jacobian. `P` is then a submersive
presentation, if its jacobian is invertible.

Finally, a standard smooth algebra is an algebra that admits a submersive presentation.

While every standard smooth algebra is smooth, the converse does not hold. But if `S` is `R`-smooth,
then `S` is `R`-standard smooth locally on `S`, i.e. there exists a set `{ t }` of `S` that
generates the unit ideal, such that `Sₜ` is `R`-standard smooth for every `t` (TODO, see below).

## Main definitions

All of these are in the `Algebra` namespace. Let `S` be an `R`-algebra.

- `PreSubmersivePresentation`: A `Presentation` of `S` as `R`-algebra, equipped with an injective
  map `P.map` from `P.rels` to `P.vars`. This map is used to define the differential of a
  presubmersive presentation.

For a presubmersive presentation `P` of `S` over `R` we make the following definitions:

- `PreSubmersivePresentation.differential`: A linear endomorphism of `P.rels → P.Ring` sending
  the `j`-th standard basis vector, corresponding to the `j`-th relation, to the vector
  of partial derivatives of `P.relation j` with respect to the coordinates `P.map i` for
  `i : P.rels`.
- `PreSubmersivePresentation.jacobian`: The determinant of `P.differential`.
- `PreSubmersivePresentation.jacobiMatrix`: If `P.rels` has a `Fintype` instance, we may form
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

open TensorProduct MvPolynomial Classical

variable (n m : ℕ)

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/--
A `PreSubmersivePresentation` of an `R`-algebra `S` is a `Presentation`
with finitely-many relations equipped with an injective `map : relations → vars`.

This map determines how the differential of `P` is constructed. See
`PreSubmersivePresentation.differential` for details.
-/
@[nolint checkUnivs]
structure PreSubmersivePresentation extends Algebra.Presentation.{t, w} R S where
  /-- A map from the relations type to the variables type. Used to compute the differential. -/
  map : rels → vars
  map_inj : Function.Injective map
  relations_finite : Finite rels

namespace PreSubmersivePresentation

attribute [instance] relations_finite

variable {R S}
variable (P : PreSubmersivePresentation R S)

lemma card_relations_le_card_vars_of_isFinite [P.IsFinite] :
    Nat.card P.rels ≤ Nat.card P.vars :=
  Nat.card_le_card_of_injective P.map P.map_inj

/-- The standard basis of `P.rels → P.ring`. -/
noncomputable abbrev basis : Basis P.rels P.Ring (P.rels → P.Ring) :=
  Pi.basisFun P.Ring P.rels

/--
The differential of a `P : PreSubmersivePresentation` is a `P.Ring`-linear map on
`P.rels → P.Ring`:

The `j`-th standard basis vector, corresponding to the `j`-th relation of `P`, is mapped
to the vector of partial derivatives of `P.relation j` with respect
to the coordinates `P.map i` for all `i : P.rels`.

The determinant of this map is the jacobian of `P` used to define when a `PreSubmersivePresentation`
is submersive. See `PreSubmersivePresentation.jacobian`.
-/
noncomputable def differential : (P.rels → P.Ring) →ₗ[P.Ring] (P.rels → P.Ring) :=
  Basis.constr P.basis P.Ring
    (fun j i : P.rels ↦ MvPolynomial.pderiv (P.map i) (P.relation j))

/-- The jacobian of a `P : PreSubmersivePresentation` is the determinant
of `P.differential` viewed as element of `S`. -/
noncomputable def jacobian : S :=
  algebraMap P.Ring S <| LinearMap.det P.differential

section Matrix

variable [Fintype P.rels] [DecidableEq P.rels]

/--
If `P.rels` has a `Fintype` and `DecidableEq` instance, the differential of `P`
can be expressed in matrix form.
-/
noncomputable def jacobiMatrix : Matrix P.rels P.rels P.Ring :=
  LinearMap.toMatrix P.basis P.basis P.differential

lemma jacobian_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det := by
   simp [jacobiMatrix, jacobian]

lemma jacobiMatrix_apply (i j : P.rels) :
    P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j) := by
  simp [jacobiMatrix, LinearMap.toMatrix, differential, basis]

end Matrix

section Constructions

/-- If `algebraMap R S` is bijective, the empty generators are a pre-submersive
presentation with no relations. -/
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    PreSubmersivePresentation.{t, w} R S where
  toPresentation := Presentation.ofBijectiveAlgebraMap.{t, w} h
  map := PEmpty.elim
  map_inj (a b : PEmpty) h := by contradiction
  relations_finite := inferInstanceAs (Finite PEmpty.{t + 1})

instance (h : Function.Bijective (algebraMap R S)) : Fintype (ofBijectiveAlgebraMap h).vars :=
  inferInstanceAs (Fintype PEmpty)

instance (h : Function.Bijective (algebraMap R S)) : Fintype (ofBijectiveAlgebraMap h).rels :=
  inferInstanceAs (Fintype PEmpty)

@[simp]
lemma ofBijectiveAlgebraMap_jacobian (h : Function.Bijective (algebraMap R S)) :
    (ofBijectiveAlgebraMap h).jacobian = 1 := by
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
noncomputable def localizationAway : PreSubmersivePresentation R S where
  __ := Presentation.localizationAway S r
  map _ := ()
  map_inj _ _ h := h
  relations_finite := inferInstanceAs <| Finite Unit

instance : Fintype (localizationAway S r).rels :=
  inferInstanceAs (Fintype Unit)

instance : DecidableEq (localizationAway S r).rels :=
  inferInstanceAs (DecidableEq Unit)

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

variable {T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : PreSubmersivePresentation S T) (P : PreSubmersivePresentation R S)

/-- Given an `R`-algebra `S` and an `S`-algebra `T` with pre-submersive presentations,
this is the canonical pre-submersive presentation of `T` as an `R`-algebra. -/
@[simps map]
noncomputable def comp : PreSubmersivePresentation R T where
  __ := Q.toPresentation.comp P.toPresentation
  map := Sum.elim (fun rq ↦ Sum.inl <| Q.map rq) (fun rp ↦ Sum.inr <| P.map rp)
  map_inj := Function.Injective.sum_elim ((Sum.inl_injective).comp (Q.map_inj))
    ((Sum.inr_injective).comp (P.map_inj)) <| by simp
  relations_finite := inferInstanceAs <| Finite (Q.rels ⊕ P.rels)

/-- The dimension of the composition of two finite submersive presentations is
the sum of the dimensions. -/
lemma dimension_comp_eq_dimension_add_dimension [Q.IsFinite] [P.IsFinite] :
    (Q.comp P).dimension = Q.dimension + P.dimension := by
  simp only [Presentation.dimension]
  erw [Presentation.comp_rels, Generators.comp_vars]
  have : Nat.card P.rels ≤ Nat.card P.vars :=
    card_relations_le_card_vars_of_isFinite P
  have : Nat.card Q.rels ≤ Nat.card Q.vars :=
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

variable [Fintype (Q.comp P).rels]

private lemma jacobiMatrix_comp_inl_inr (i : Q.rels) (j : P.rels) :
    (Q.comp P).jacobiMatrix (Sum.inl i) (Sum.inr j) = 0 := by
  rw [jacobiMatrix_apply]
  refine MvPolynomial.pderiv_eq_zero_of_not_mem_vars (fun hmem ↦ ?_)
  apply MvPolynomial.vars_rename at hmem
  simp at hmem

private lemma jacobiMatrix_comp_₁₂ : (Q.comp P).jacobiMatrix.toBlocks₁₂ = 0 := by
  ext i j : 1
  simp [Matrix.toBlocks₁₂, jacobiMatrix_comp_inl_inr]

section Q

variable [Fintype Q.rels]

private lemma jacobiMatrix_comp_inl_inl (i j : Q.rels) :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val))
      ((Q.comp P).jacobiMatrix (Sum.inl j) (Sum.inl i)) = Q.jacobiMatrix j i := by
  rw [jacobiMatrix_apply, jacobiMatrix_apply, comp_map, Sum.elim_inl,
    ← Q.comp_aeval_relation_inl P.toPresentation]
  apply aeval_sum_elim_pderiv_inl

private lemma jacobiMatrix_comp_₁₁_det :
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det = Q.jacobian := by
  rw [jacobian_eq_jacobiMatrix_det, AlgHom.map_det (aeval (Q.comp P).val), RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, ← Q.jacobiMatrix_comp_inl_inl P]
  apply aeval_sum_elim

end Q

section P

variable [Fintype P.rels]

private lemma jacobiMatrix_comp_inr_inr (i j : P.rels) :
    (Q.comp P).jacobiMatrix (Sum.inr i) (Sum.inr j) =
      MvPolynomial.rename Sum.inr (P.jacobiMatrix i j) := by
  rw [jacobiMatrix_apply, jacobiMatrix_apply]
  simp only [comp_map, Sum.elim_inr]
  apply pderiv_rename Sum.inr_injective

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
  induction' p using MvPolynomial.induction_on with a p q hp hq p i hp
  · simp only [algHom_C, algebraMap_eq, eval₂_C]
    erw [MvPolynomial.eval₂_C]
  · simp [hp, hq]
  · simp only [map_mul, rename_X, eval₂_mul, hp, eval₂_X]
    erw [Generators.comp_val]
    simp

end P

end

/-- The jacobian of the composition of presentations is the product of the jacobians. -/
@[simp]
lemma comp_jacobian_eq_jacobian_smul_jacobian : (Q.comp P).jacobian = P.jacobian • Q.jacobian := by
  cases nonempty_fintype Q.rels
  cases nonempty_fintype P.rels
  letI : Fintype (Q.comp P).rels := inferInstanceAs <| Fintype (Q.rels ⊕ P.rels)
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

variable (T) [CommRing T] [Algebra R T] (P : PreSubmersivePresentation R S)

/-- If `P` is a pre-submersive presentation of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural pre-submersive presentation of `T ⊗[R] S` over `T`. -/
noncomputable def baseChange : PreSubmersivePresentation T (T ⊗[R] S) where
  __ := P.toPresentation.baseChange T
  map := P.map
  map_inj := P.map_inj
  relations_finite := P.relations_finite

@[simp]
lemma baseChange_jacobian : (P.baseChange T).jacobian = 1 ⊗ₜ P.jacobian := by
  classical
  cases nonempty_fintype P.rels
  letI : Fintype (P.baseChange T).rels := inferInstanceAs <| Fintype P.rels
  simp_rw [jacobian_eq_jacobiMatrix_det]
  have h : (baseChange T P).jacobiMatrix =
      (MvPolynomial.map (algebraMap R T)).mapMatrix P.jacobiMatrix := by
    ext i j : 1
    simp only [baseChange, jacobiMatrix_apply, Presentation.baseChange_relation,
      RingHom.mapMatrix_apply, Matrix.map_apply]
    erw [MvPolynomial.pderiv_map]
    rfl
  rw [h]
  erw [← RingHom.map_det, aeval_map_algebraMap]
  apply aeval_one_tmul

end BaseChange

end Constructions

end PreSubmersivePresentation

/--
A `PreSubmersivePresentation` is submersive if its jacobian is a unit in `S`
and the presentation is finite.
-/
@[nolint checkUnivs]
structure SubmersivePresentation extends PreSubmersivePresentation.{t, w} R S where
  jacobian_isUnit : IsUnit toPreSubmersivePresentation.jacobian
  isFinite : toPreSubmersivePresentation.IsFinite := by infer_instance

attribute [instance] SubmersivePresentation.isFinite

namespace SubmersivePresentation

open PreSubmersivePresentation

section Constructions

variable {R S} in
/-- If `algebraMap R S` is bijective, the empty generators are a submersive
presentation with no relations. -/
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    SubmersivePresentation.{t, w} R S where
  __ := PreSubmersivePresentation.ofBijectiveAlgebraMap.{t, w} h
  jacobian_isUnit := by
    rw [ofBijectiveAlgebraMap_jacobian]
    exact isUnit_one
  isFinite := Presentation.ofBijectiveAlgebraMap_isFinite h

/-- The canonical submersive `R`-presentation of `R` with no generators and no relations. -/
noncomputable def id : SubmersivePresentation.{t, w} R R :=
  ofBijectiveAlgebraMap Function.bijective_id

section Composition

variable {R S T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : SubmersivePresentation S T) (P : SubmersivePresentation R S)

/-- Given an `R`-algebra `S` and an `S`-algebra `T` with submersive presentations,
this is the canonical submersive presentation of `T` as an `R`-algebra. -/
noncomputable def comp : SubmersivePresentation R T where
  __ := Q.toPreSubmersivePresentation.comp P.toPreSubmersivePresentation
  jacobian_isUnit := by
    rw [comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def, IsUnit.mul_iff]
    exact ⟨RingHom.isUnit_map _ <| P.jacobian_isUnit, Q.jacobian_isUnit⟩
  isFinite := Presentation.comp_isFinite Q.toPresentation P.toPresentation

end Composition

section Localization

variable {R} (r : R) [IsLocalization.Away r S]

/-- If `S` is the localization of `R` at `r`, this is the canonical submersive presentation
of `S` as `R`-algebra. -/
noncomputable def localizationAway : SubmersivePresentation R S where
  __ := PreSubmersivePresentation.localizationAway S r
  jacobian_isUnit := by
    rw [localizationAway_jacobian]
    apply IsLocalization.map_units' (⟨r, 1, by simp⟩ : Submonoid.powers r)
  isFinite := Presentation.localizationAway_isFinite r

end Localization

section BaseChange

variable (T) [CommRing T] [Algebra R T] (P : SubmersivePresentation R S)

/-- If `P` is a submersive presentation of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural submersive presentation of `T ⊗[R] S` over `T`. -/
noncomputable def baseChange : SubmersivePresentation T (T ⊗[R] S) where
  toPreSubmersivePresentation := P.toPreSubmersivePresentation.baseChange T
  jacobian_isUnit := P.baseChange_jacobian T ▸ P.jacobian_isUnit.map TensorProduct.includeRight
  isFinite := Presentation.baseChange_isFinite T P.toPresentation

end BaseChange

end Constructions

end SubmersivePresentation

/--
An `R`-algebra `S` is called standard smooth, if there
exists a submersive presentation.
-/
class IsStandardSmooth : Prop where
  out : Nonempty (SubmersivePresentation.{t, w} R S)

/--
The relative dimension of a standard smooth `R`-algebra `S` is
the dimension of an arbitrarily chosen submersive `R`-presentation of `S`.

Note: If `S` is non-trivial, this number is independent of the choice of the presentation as it is
equal to the `S`-rank of `Ω[S/R]` (TODO).
-/
noncomputable def IsStandardSmooth.relativeDimension [IsStandardSmooth R S] : ℕ :=
  ‹IsStandardSmooth R S›.out.some.dimension

/--
An `R`-algebra `S` is called standard smooth of relative dimension `n`, if there exists
a submersive presentation of dimension `n`.
-/
class IsStandardSmoothOfRelativeDimension : Prop where
  out : ∃ P : SubmersivePresentation.{t, w} R S, P.dimension = n

variable {R} {S}

lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth
    [IsStandardSmoothOfRelativeDimension.{t, w} n R S] :
    IsStandardSmooth.{t, w} R S :=
  ⟨‹IsStandardSmoothOfRelativeDimension n R S›.out.nonempty⟩

lemma IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective
    (h : Function.Bijective (algebraMap R S)) :
    IsStandardSmoothOfRelativeDimension.{t, w} 0 R S :=
  ⟨SubmersivePresentation.ofBijectiveAlgebraMap h, Presentation.ofBijectiveAlgebraMap_dimension h⟩

variable (R) in
instance IsStandardSmoothOfRelativeDimension.id :
    IsStandardSmoothOfRelativeDimension.{t, w} 0 R R :=
  IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective Function.bijective_id

section Composition

variable (R S T) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

lemma IsStandardSmooth.trans [IsStandardSmooth.{t, w} R S] [IsStandardSmooth.{t', w'} S T] :
    IsStandardSmooth.{max t t', max w w'} R T where
  out := by
    obtain ⟨⟨P⟩⟩ := ‹IsStandardSmooth R S›
    obtain ⟨⟨Q⟩⟩ := ‹IsStandardSmooth S T›
    exact ⟨Q.comp P⟩

lemma IsStandardSmoothOfRelativeDimension.trans [IsStandardSmoothOfRelativeDimension.{t, w} n R S]
    [IsStandardSmoothOfRelativeDimension.{t', w'} m S T] :
    IsStandardSmoothOfRelativeDimension.{max t t', max w w'} (m + n) R T where
  out := by
    obtain ⟨P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    obtain ⟨Q, hQ⟩ := ‹IsStandardSmoothOfRelativeDimension m S T›
    refine ⟨Q.comp P, hP ▸ hQ ▸ ?_⟩
    apply PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension

end Composition

lemma IsStandardSmooth.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmooth.{0, 0} R S where
  out := ⟨SubmersivePresentation.localizationAway S r⟩

lemma IsStandardSmoothOfRelativeDimension.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmoothOfRelativeDimension.{0, 0} 0 R S where
  out := ⟨SubmersivePresentation.localizationAway S r,
    Presentation.localizationAway_dimension_zero r⟩

section BaseChange

variable (T) [CommRing T] [Algebra R T]

instance IsStandardSmooth.baseChange [IsStandardSmooth.{t, w} R S] :
    IsStandardSmooth.{t, w} T (T ⊗[R] S) where
  out := by
    obtain ⟨⟨P⟩⟩ := ‹IsStandardSmooth R S›
    exact ⟨P.baseChange R S T⟩

instance IsStandardSmoothOfRelativeDimension.baseChange
    [IsStandardSmoothOfRelativeDimension.{t, w} n R S] :
    IsStandardSmoothOfRelativeDimension.{t, w} n T (T ⊗[R] S) where
  out := by
    obtain ⟨P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    exact ⟨P.baseChange R S T, hP⟩

end BaseChange

section

variable (P : SubmersivePresentation R S)

open Extension

lemma Generators.Cotangent.mk_mem_ker_cotangentComplex_iff {P : Generators R S} (x : P.ker) :
    Cotangent.mk x ∈ LinearMap.ker P.toExtension.cotangentComplex ↔
        ∀ i : P.vars, (aeval P.val) (pderiv i x.val) = 0 := by
  simp only [Generators.toExtension_Ring, Generators.toExtension_commRing,
    Generators.toExtension_algebra₂, LinearMap.mem_ker]
  let e := P.cotangentSpaceBasis.repr
  rw [← LinearMap.map_eq_zero_iff _ P.cotangentSpaceBasis.repr.injective]
  rw [Finsupp.ext_iff]
  simp only [Generators.toExtension_Ring, Generators.toExtension_commRing,
    Generators.toExtension_algebra₂, LinearEquiv.coe_coe, Finsupp.coe_zero, Pi.zero_apply]
  erw [Extension.cotangentComplex_mk]
  simp_rw [P.cotangentSpaceBasis_repr_one_tmul]

lemma Presentation.Cotangent.mk_mem_ker_cotangentComplex_iff {P : Presentation R S} (x : P.ker) :
    Cotangent.mk x ∈ LinearMap.ker P.toExtension.cotangentComplex ↔
        ∀ i : P.vars, (pderiv i x.val) ∈ Ideal.span (Set.range P.relation) := by
  rw [Generators.Cotangent.mk_mem_ker_cotangentComplex_iff]
  simp_rw [← RingHom.mem_ker, P.span_range_relation_eq_ker]
  rfl

@[simps apply]
noncomputable def Finsupp.comapDomain.linearMap {α β R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {f : α → β} (hf : Function.Injective f) :
    (β →₀ M) →ₗ[R] α →₀ M where
  __ := Finsupp.comapDomain.addMonoidHom hf
  map_smul' m x := by ext; simp

@[simps! apply_toFun]
noncomputable def PreSubmersivePresentation.restrict (P : PreSubmersivePresentation R S) :
    (P.vars →₀ S) →ₗ[S] P.rels →₀ S :=
  Finsupp.comapDomain.linearMap P.map_inj

noncomputable def aux (P : PreSubmersivePresentation R S) :
    P.toExtension.Cotangent →ₗ[S] P.rels →₀ S :=
  P.restrict ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ P.toExtension.cotangentComplex

@[simp]
lemma aux_apply (P : PreSubmersivePresentation R S) (x : P.ker) (i : P.rels) :
    (aux P) (Cotangent.mk x) i = (aeval P.val) (pderiv (P.map i) x.val) := by
  dsimp only [aux, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    cotangentComplex_mk, PreSubmersivePresentation.restrict_apply_toFun]
  rw [Generators.cotangentSpaceBasis_repr_one_tmul]

lemma aux_zero_iff {P : PreSubmersivePresentation R S} (x : P.ker) :
    (aux P) (Cotangent.mk x) = 0 ↔
      ∀ i : P.rels, (aeval P.val) (pderiv (P.map i) x.val) = 0 := by
  rw [Finsupp.ext_iff]
  simp_rw [aux_apply, Finsupp.coe_zero, Pi.zero_apply]

lemma Extension.Cotangent.mk_eq_zero_iff {P : Extension R S} (x : P.ker) :
    Cotangent.mk x = 0 ↔ x.val ∈ P.ker ^ 2 := by
  simp [Cotangent.ext_iff, Ideal.toCotangent_eq_zero]

lemma _root_.Matrix.mulVec_injective_of_isUnit {R m : Type*} [Semiring R] [Fintype m]
    {A : Matrix m m R} (ha : IsUnit A) : Function.Injective A.mulVec := by
  obtain ⟨B, hBl, hBr⟩ := isUnit_iff_exists.mp ha
  intro x y hxy
  simpa [hBr] using congrArg B.mulVec hxy

lemma _root_.Matrix.vecMul_injective_of_isUnit {R m : Type*} [Semiring R] [Fintype m]
    {A : Matrix m m R}
    (ha : IsUnit A) : Function.Injective A.vecMul := by
  obtain ⟨B, hBl, hBr⟩ := isUnit_iff_exists.mp ha
  intro x y hxy
  simpa [hBl] using congrArg B.vecMul hxy

lemma _root_.Matrix.linearIndependent_rows_of_isUnit {m : Type*} [Fintype m] {A : Matrix m m R}
    (ha : IsUnit A) : LinearIndependent R (fun i ↦ A i) := by
  rw [← Matrix.vecMul_injective_iff]
  exact Matrix.vecMul_injective_of_isUnit ha

lemma _root_.Matrix.linearIndependent_cols_of_isUnit {m : Type*} [Fintype m] {A : Matrix m m R}
    (ha : IsUnit A) : LinearIndependent R (fun i ↦ A.transpose i) := by
  rw [← Matrix.mulVec_injective_iff]
  exact Matrix.mulVec_injective_of_isUnit ha

lemma SubmersivePresentation.linearIndependent_aeval_val_pderiv_relation :
    LinearIndependent S (fun i j ↦ (aeval P.val) (pderiv (P.map j) (P.relation i))) := by
  have : Fintype P.rels := Fintype.ofFinite P.rels
  have := P.jacobian_isUnit
  rw [P.jacobian_eq_jacobiMatrix_det, RingHom.map_det, ← Matrix.isUnit_iff_isUnit_det] at this
  have heq (i j : P.rels) : (aeval P.val) ((pderiv (P.map i)) (P.relation j)) =
      (P.jacobiMatrix.map (algebraMap P.Ring S)) i j := by
    simp [P.jacobiMatrix_apply]
  simp_rw [heq]
  apply Matrix.linearIndependent_cols_of_isUnit this

lemma Presentation.relation_mem_ker {P : Presentation R S} (i : P.rels) :
    P.relation i ∈ P.ker := by
  rw [← P.span_range_relation_eq_ker]
  apply Ideal.subset_span
  use i

lemma aux_injective : Function.Injective (aux P.toPreSubmersivePresentation) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨(x : P.ker), rfl⟩ := Cotangent.mk_surjective x
  simp only [Submodule.mem_bot]
  rw [Cotangent.mk_eq_zero_iff]
  simp at hx
  erw [aux_zero_iff] at hx
  have : x.val ∈ Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker]
    exact x.property
  rw [Finsupp.mem_ideal_span_range_iff_exists_finsupp] at this
  obtain ⟨c, hc⟩ := this
  have heq (i : P.rels) :
      (aeval P.val) (pderiv (P.map i) <| c.sum fun i a ↦ a * P.relation i) = 0 := by
    rw [hc]
    apply hx
  simp [Finsupp.sum] at heq
  have heq2 : ∑ i ∈ c.support,
      (aeval P.val) (c i) • (fun j ↦ (aeval P.val) (pderiv (P.map j) (P.relation i))) = 0 := by
    ext j
    simp
    apply heq
  have (i : P.rels) : (aeval P.val) (c i) = 0 := by
    have := P.linearIndependent_aeval_val_pderiv_relation
    rw [linearIndependent_iff''] at this
    have := this c.support (fun i ↦ (aeval P.val) (c i))
      (by intro i; simp; intro h; simp [h]) (heq2)
    simp at this
    exact this i
  show _ ∈ P.ker ^ 2
  rw [← hc]
  apply Ideal.sum_mem
  intro i hi
  simp
  rw [pow_two]
  apply Ideal.mul_mem_mul
  · rw [P.ker_eq_ker_aeval_val]
    simpa using this i
  · exact P.relation_mem_ker i

lemma cotangentComplex_injective : Function.Injective P.toExtension.cotangentComplex := by
  have := aux_injective P
  simp only [aux, LinearMap.coe_comp, LinearEquiv.coe_coe] at this
  exact Function.Injective.of_comp (Function.Injective.of_comp this)

lemma subsingleton_h1Cotangent : Subsingleton P.toExtension.H1Cotangent := by
  rw [Algebra.Extension.subsingleton_h1Cotangent]
  exact cotangentComplex_injective P

@[simp]
lemma Finsupp.linearEquivFunOnFinite_symm_apply (R M α : Type*) [Finite α] [AddCommMonoid M]
    [Semiring R] [Module R M] (f : α →₀ M) (a : α) :
    (Finsupp.linearEquivFunOnFinite R M α).symm f a = f a := rfl

noncomputable def SubmersivePresentation.basisCotangent : Basis P.rels S P.toExtension.Cotangent :=
  letI e : (P.rels → S) ≃ₗ[S] P.rels →₀ S :=
    (Finsupp.linearEquivFunOnFinite S S P.rels).symm
  have h : aux P.toPreSubmersivePresentation ∘
      (fun i ↦ Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩) =
      e ∘ (fun i j ↦ (aeval P.val) ((pderiv (P.map j)) (P.relation i))) := by
    ext i j
    simp only [Function.comp_apply, e, aux_apply]
    rfl
  have hli : LinearIndependent S
      (fun i ↦ Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩) := by
    apply LinearIndependent.of_comp (aux P.toPreSubmersivePresentation)
    rw [h]
    apply P.linearIndependent_aeval_val_pderiv_relation.map' e.toLinearMap e.ker
  have hsp : ⊤ ≤ Submodule.span S
      (Set.range fun i ↦ Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩) :=
    sorry
  Basis.mk hli hsp

instance : Module.Free S P.toExtension.Cotangent :=
  Module.Free.of_basis P.basisCotangent

end

end Algebra
