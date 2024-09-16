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
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective

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

noncomputable def jacobiMatrix [Fintype P.relations] [DecidableEq P.relations] :
    Matrix P.relations P.relations P.Ring :=
  LinearMap.toMatrix P.basis P.basis P.linearMap

/-- The determinant of a `P : SubmersivePresentation` is the determinant
of `P.linearMap` viewed as element of `S`. -/
noncomputable def det : S :=
  algebraMap P.Ring S <| LinearMap.det P.linearMap

lemma det_eq_jacobiMatrix_det [Fintype P.relations] [DecidableEq P.relations] :
     P.det = algebraMap P.Ring S P.jacobiMatrix.det := by
   simp [jacobiMatrix, det]

lemma jacobiMatrix_apply [Fintype P.relations] [DecidableEq P.relations] (i j : P.relations) :
    P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j) := by
  simp [jacobiMatrix, LinearMap.toMatrix, linearMap]

section Constructors

section Localization

variable (r : R) [IsLocalization.Away r S]

@[simps map]
noncomputable def localizationAway : SubmersivePresentation R S where
  toPresentation := Presentation.localizationAway r
  map _ := ()
  map_inj _ _ h := h
  relations_finite := inferInstanceAs <| Finite Unit

end Localization

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

section Example

open MvPolynomial

variable (r : R) (P1 P2 : MvPolynomial (Fin 2) R)

abbrev ring : Type _ := MvPolynomial (Fin 2) R ⧸ Ideal.span {P1, X 0 * P2 - 1}
abbrev I : Ideal (MvPolynomial (Fin 2) R) := Ideal.span {P1, X 0 * P2 - 1}

lemma quotient_mk_comp_X_surjective :
    Function.Surjective (aeval (R := R) (Ideal.Quotient.mk (I P1 P2) ∘ X)) := by
  rw [show aeval (Ideal.Quotient.mk (I P1 P2) ∘ X) = Ideal.Quotient.mkₐ R (I P1 P2) by ext; simp]
  exact Ideal.Quotient.mkₐ_surjective R (I P1 P2)

noncomputable def pres : SubmersivePresentation R (ring P1 P2) where
  vars := Fin 2
  val i := match i with
    | 0 => Ideal.Quotient.mk (I P1 P2) (X 0)
    | 1 => Ideal.Quotient.mk (I P1 P2) (X 1)
  σ' x := (quotient_mk_comp_X_surjective P1 P2 x).choose
  aeval_val_σ' x := sorry--(quotient_mk_comp_X_surjective r x).choose_spec
  relations := Fin 2
  relation i := match i with
    | 0 => P1
    | 1 => P2
  ker_algebraMap_eq_span_range_relation := sorry
  map i := i
  map_inj i j h := h
  relations_finite := inferInstance

instance : Fintype (pres P1 P2).relations := inferInstanceAs <| Fintype (Fin 2)
instance : DecidableEq (pres P1 P2).relations := inferInstanceAs <| DecidableEq (Fin 2)

lemma aeval_val_pres (p : MvPolynomial (Fin 2) R) :
    aeval (pres P1 P2).val p = Ideal.Quotient.mk _ p := by
  induction p using MvPolynomial.induction_on with
  | h_C a => erw [aeval_C]; rfl
  | h_X p i h => simp [h]; match i with
      | 0 => rfl
      | 1 => rfl
  | h_add p q hp hq => simp [hp, hq]

lemma det_eq : (pres P1 P2).jacobiMatrix.det = P2 := sorry

example : (pres P1 P2).IsStandardSmooth where
  det_isUnit := by
    rw [det_eq_jacobiMatrix_det, det_eq]
    rw [isUnit_iff_exists_inv]
    simp only [Generators.algebraMap_apply]
    use (Ideal.Quotient.mk _ (X 0))
    rw [aeval_val_pres]
    rw [← _root_.map_mul]
    rw [← _root_.map_one (Ideal.Quotient.mk _)]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply Ideal.subset_span
    rw [mul_comm]
    simp
  presentation_finite := { finite_relations := inferInstance, finite_vars := inferInstanceAs <| Finite (Fin 2) }

example : IsUnit (algebraMap (gens r).Ring (ring r) (C r)) := by
  rw [isUnit_iff_exists_inv]
  use Ideal.Quotient.mk _ (X ())
  simp
  rw [← map_one (Ideal.Quotient.mk _)]
  apply Ideal.subset_span
  simp
  sorry
  sorry
  sorry


end Example

attribute [instance] IsStandardSmooth.presentation_finite

section Localization

variable (r : R) [IsLocalization.Away r S]

lemma localizationAway_det : (localizationAway r (S := S)).det = algebraMap R S r := by
  simp [det]
  classical
  letI : Fintype (localizationAway r (S := S)).relations := inferInstanceAs <| Fintype Unit
  rw [← LinearMap.det_toMatrix (localizationAway r (S := S)).basis]
  have : (LinearMap.toMatrix (localizationAway r (S := S)).basis (localizationAway r).basis)
      (localizationAway r).linearMap = Matrix.diagonal (fun () ↦ MvPolynomial.C r) := by
    ext (i : Unit) (j : Unit) : 1
    simp [linearMap, LinearMap.toMatrix]
    erw [Presentation.localizationAway_relation]
    rw [map_sub]
    erw [MvPolynomial.pderiv_C_mul]
    rw [MvPolynomial.pderiv_X]
    simp
  rw [this]
  rw [Matrix.det_diagonal]
  simp

instance isLocalizationAway_isStandardSmooth : (localizationAway r (S := S)).IsStandardSmooth where
  det_isUnit := by
    rw [localizationAway_det]
    apply IsLocalization.map_units' (⟨r, 1, by simp⟩ : Submonoid.powers r)
  presentation_finite := Presentation.localizationAway_isFinite r

end Localization

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

section Localization

variable (r : R) [IsLocalization.Away r S]

/-- If `S` is the localization away from `r`, then `S` is `R`-standard smooth. -/
lemma of_isLocalizationAway : IsStandardSmooth.{0, 0} R S where
  out := ⟨SubmersivePresentation.localizationAway (S := S) r, inferInstance⟩

end Localization

section Comp

variable {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- If `T` is a standard-smooth `S`-algebra and `S` is a standard-smooth `R`-algebra, then
`T` is a standard-smooth `R` algebra. -/
lemma trans [IsStandardSmooth.{t, w} R S] [IsStandardSmooth.{t', w'} S T] :
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

variable {R : Type} [CommRing R]
variable (W : WeierstrassCurve.Projective R)

open MvPolynomial

namespace WeierstrassCurve.Projective

noncomputable abbrev P1 : MvPolynomial (Fin 3) R :=
  X 2 ^ 2 + (C W.a₁ * X 0 + C W.a₃) * X 2 - X 0 ^ 3 - C W.a₂ * X 0 ^ 2 - C W.a₄ * X 0 - C W.a₆

noncomputable abbrev P2 : MvPolynomial (Fin 3) R :=
  X 1 * (pderiv 0 W.P1) - C 1

abbrev ring1 : Type := MvPolynomial (Fin 3) R ⧸ (Ideal.span {P1 W, P2 W})

noncomputable abbrev generators1 : Algebra.Generators R (ring1 W) :=
  Algebra.Generators.ofAlgHom (Ideal.Quotient.mkₐ R (Ideal.span {P1 W, P2 W}))
    (Ideal.Quotient.mkₐ_surjective _ _)

noncomputable def presentation1 : Algebra.SubmersivePresentation R (ring1 W) where
  vars := Fin 3
  val := W.generators1.val
  σ' := W.generators1.σ'
  aeval_val_σ' := W.generators1.aeval_val_σ'
  relations := Fin 2
  relation i := match i with
    | 0 => P1 W
    | 1 => P2 W
  map (i : Fin 2) := match i with
    | 0 => (0 : Fin 3)
    | 1 => (1 : Fin 3)
  relations_finite := inferInstance
  map_inj i j h := by
    match i, j with
    | 0, 0 => simp
    | 1, 1 => simp
    | 0, 1 => aesop
    | 1, 0 => aesop
  ker_algebraMap_eq_span_range_relation := by
    show RingHom.ker (algebraMap W.generators1.Ring W.ring1) = _
    simp only [Algebra.Generators.ofAlgHom_algebraMap, AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_ker]
    congr
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · intro hx
      cases hx
      · use 0
        symm
        simpa
      · use 1
        symm
        simpa
    · intro ⟨y, hy⟩
      match y with
      | 0 => simp at hy; exact Or.inl hy.symm
      | 1 => simp at hy; exact Or.inr hy.symm

example : W.presentation1.Ring = MvPolynomial (Fin 3) R := rfl

open Algebra.SubmersivePresentation

attribute [-simp] map_ofNat Fin.isValue

lemma ring1_id00 :
    (pderiv (W.presentation1.map (0 : Fin 2))) (W.presentation1.relation (0 : Fin 2)) =
      pderiv 0 W.P1 := by
  rfl

lemma ring1_id10 :
    (pderiv (W.presentation1.map (1 : Fin 2))) (W.presentation1.relation (0 : Fin 2)) = 0 := by
  simp [presentation1]

lemma ring1_id11 :
    (pderiv (W.presentation1.map (1 : Fin 2))) (W.presentation1.relation (1 : Fin 2)) =
      pderiv 0 W.P1 := by
  simp [presentation1]
  show -(X 0 ^ 2 * (pderiv 1) (C 3)) - C W.a₂ * (X 0 * (pderiv 1) (C 2)) = 0
  rw [pderiv_C]
  rw [pderiv_C]
  simp

instance : Fintype W.presentation1.relations := inferInstanceAs <| Fintype (Fin 2)
instance : DecidableEq W.presentation1.relations := inferInstanceAs <| Fintype (Fin 2)

lemma ring1_jac_det : W.presentation1.jacobiMatrix.det =
    (pderiv 0 W.P1) ^ 2 := by
  simp only [presentation1]
  sorry
  /-
  rw [Matrix.det_fin_two]
  rw [jacobiMatrix_apply, ring1_id00]
  rw [jacobiMatrix_apply, ring1_id11]
  nth_rw 2 [jacobiMatrix_apply]
  rw [ring1_id10]
  simp
  ring
  -/

lemma pres1_isUnit_pderv : IsUnit ((algebraMap W.presentation1.Ring W.ring1) ((pderiv 0) W.P1)) := by
  show IsUnit ((aeval (R := R) W.presentation1.val) ((pderiv 0) W.P1))
  rw [isUnit_iff_exists_inv]
  use (Ideal.Quotient.mk _ (X (1 : Fin 2)))
  have : (Ideal.Quotient.mk (Ideal.span {W.P1, W.P2})) 1 =
      Ideal.Quotient.mk _ (X (1 : Fin 3) * (pderiv 0 W.P1)) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    rw [← Ideal.neg_mem_iff]
    rw [neg_sub]
    apply Ideal.subset_span
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr rfl
  rw [← _root_.map_one (Ideal.Quotient.mk _)]
  rw [this]
  rw [_root_.map_mul]
  rw [mul_comm]
  sorry

/-- this is needed because of an instance diamond, see
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Diamond.20in.20.60Algebra.2EGenerators.60
-/
lemma alg_eq_alg : Ideal.Quotient.algebra (MvPolynomial (Fin 3) R) = W.presentation1.instRing_1 := by
  ext r x
  simp
  refine Quotient.inductionOn x (fun x ↦ ?_)
  conv_rhs => rw [@Algebra.smul_def _ _ _ _ (W.presentation1.instRing_1)]
  conv_lhs => rw [@Algebra.smul_def _ _ _ _ (Ideal.Quotient.algebra _)]
  show Ideal.Quotient.mk _ r * ⟦x⟧ = aeval W.presentation1.val r * ⟦x⟧
  congr
  ext p
  · simp; rfl
  · simp; rfl

lemma pres1_stdsmooth : (presentation1 W).IsStandardSmooth where
  det_isUnit := by
    rw [det_eq_jacobiMatrix_det]
    rw [ring1_jac_det]
    rw [map_pow]
    rw [isUnit_pow_iff (by omega)]
    rw [algebraMap_apply]
    --rw [← alg_eq_alg]
    exact W.pres1_isUnit_pderv
  presentation_finite := {
    finite_relations := inferInstanceAs <| Finite (Fin 2)
    finite_vars := inferInstanceAs <| Finite (Fin 3)
  }
