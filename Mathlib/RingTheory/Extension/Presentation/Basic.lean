/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.MvPolynomial.Localization

/-!

# Presentations of algebras

A presentation of an `R`-algebra `S` is a distinguished family of generators and relations.

## Main definition

- `Algebra.Presentation`: A presentation of an `R`-algebra `S` is a family of
  generators with
  1. `rels`: The type of relations.
  2. `relation : relations → MvPolynomial vars R`: The assignment of
     each relation to a polynomial in the generators.
- `Algebra.Presentation.IsFinite`: A presentation is called finite if both variables and relations
  are finite.
- `Algebra.Presentation.dimension`: The dimension of a presentation is the number of generators
  minus the number of relations.

We also give constructors for localization, base change and composition.

## TODO

- Define `Hom`s of presentations.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

@[expose] public section

universe t w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) (ι : Type w) (σ : Type t) [CommRing R] [CommRing S] [Algebra R S]

/--
A presentation of an `R`-algebra `S` is a family of
generators with `σ → MvPolynomial ι R`: The assignment of
each relation to a polynomial in the generators.
-/
@[nolint checkUnivs]
structure Algebra.Presentation extends Algebra.Generators R S ι where
  /-- The assignment of each relation to a polynomial in the generators. -/
  relation : σ → toGenerators.Ring
  /-- The relations span the kernel of the canonical map. -/
  span_range_relation_eq_ker :
    Ideal.span (Set.range relation) = toGenerators.ker

namespace Algebra.Presentation

variable {R S ι σ}
variable (P : Presentation R S ι σ)

@[simp]
lemma aeval_val_relation (i) : aeval P.val (P.relation i) = 0 := by
  rw [← RingHom.mem_ker, ← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
  exact Ideal.subset_span ⟨i, rfl⟩

lemma relation_mem_ker (i) : P.relation i ∈ P.ker := by
  rw [← P.span_range_relation_eq_ker]
  apply Ideal.subset_span
  use i

/-- The polynomial algebra w.r.t. a family of generators modulo a family of relations. -/
protected abbrev Quotient : Type (max w u) := P.Ring ⧸ P.ker

/-- `P.Quotient` is `P.Ring`-isomorphic to `S` and in particular `R`-isomorphic to `S`. -/
noncomputable def quotientEquiv : P.Quotient ≃ₐ[P.Ring] S :=
  Ideal.quotientKerAlgEquivOfRightInverse (f := Algebra.ofId P.Ring S) (g := P.σ) <| fun x ↦ by
    rw [Algebra.ofId_apply, P.algebraMap_apply, P.aeval_val_σ]

@[simp]
lemma quotientEquiv_mk (p : P.Ring) : P.quotientEquiv p = algebraMap P.Ring S p :=
  rfl

@[simp]
lemma quotientEquiv_symm (x : S) : P.quotientEquiv.symm x = P.σ x :=
  rfl

set_option linter.unusedVariables false in
/--
Dimension of a presentation defined as the cardinality of the generators
minus the cardinality of the relations.

Note: this definition is completely non-sensical for non-finite presentations and
even then for this to make sense, you should assume that the presentation
is a complete intersection.
-/
@[nolint unusedArguments]
noncomputable def dimension (P : Presentation R S ι σ) : ℕ :=
  Nat.card ι - Nat.card σ

lemma fg_ker [Finite σ] : P.ker.FG := by
  use (Set.finite_range P.relation).toFinset
  simp [span_range_relation_eq_ker]

/-- If a presentation is finite, the corresponding quotient is
of finite presentation. -/
instance [Finite σ] [Finite ι] : FinitePresentation R P.Quotient :=
  FinitePresentation.quotient P.fg_ker

lemma finitePresentation_of_isFinite [Finite σ] [Finite ι] (P : Presentation R S ι σ) :
    FinitePresentation R S :=
  FinitePresentation.equiv (P.quotientEquiv.restrictScalars R)

variable (R S) in
lemma exists_presentation_fin [FinitePresentation R S] :
    ∃ n m, Nonempty (Presentation R S (Fin n) (Fin m)) :=
  letI H := FinitePresentation.out (R := R) (A := S)
  letI n : ℕ := H.choose
  letI f : MvPolynomial (Fin n) R →ₐ[R] S := H.choose_spec.choose
  haveI hf : Function.Surjective f := H.choose_spec.choose_spec.1
  haveI hf' : (RingHom.ker f).FG := H.choose_spec.choose_spec.2
  letI H' := Submodule.fg_iff_exists_fin_generating_family.mp hf'
  let m : ℕ := H'.choose
  let v : Fin m → MvPolynomial (Fin n) R := H'.choose_spec.choose
  have hv : Ideal.span (Set.range v) = RingHom.ker f := H'.choose_spec.choose_spec
  ⟨n, m,
    ⟨{__ := Generators.ofSurjective (fun x ↦ f (.X x)) (by convert! hf; ext; simp)
      relation := v
      span_range_relation_eq_ker := hv.trans (by congr; ext; simp) }⟩⟩

variable (R S) in
/-- The index of generators to `ofFinitePresentation`. -/
noncomputable
def ofFinitePresentationVars [FinitePresentation R S] : ℕ :=
  (exists_presentation_fin R S).choose

variable (R S) in
/-- The index of relations to `ofFinitePresentation`. -/
noncomputable
def ofFinitePresentationRels [FinitePresentation R S] : ℕ :=
  (exists_presentation_fin R S).choose_spec.choose

variable (R S) in
/-- An arbitrary choice of a finite presentation of a finitely presented algebra. -/
noncomputable
def ofFinitePresentation [FinitePresentation R S] :
    Presentation R S (Fin (ofFinitePresentationVars R S)) (Fin (ofFinitePresentationRels R S)) :=
  (exists_presentation_fin R S).choose_spec.choose_spec.some

section Construction

/-- Transport a presentation along an algebra isomorphism. -/
@[simps toGenerators relation]
noncomputable def ofAlgEquiv (P : Presentation R S ι σ) {T : Type*} [CommRing T] [Algebra R T]
    (e : S ≃ₐ[R] T) :
    Presentation R T ι σ where
  __ := Generators.ofAlgEquiv P.toGenerators e
  relation i := P.relation i
  span_range_relation_eq_ker := by simp [P.span_range_relation_eq_ker]

@[simp]
lemma dimension_ofAlgEquiv (P : Presentation R S ι σ) {T : Type*} [CommRing T] [Algebra R T]
    (e : S ≃ₐ[R] T) : (P.ofAlgEquiv e).dimension = P.dimension :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- If `algebraMap R S` is bijective, the empty generators are a presentation with no relations. -/
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    Presentation R S PEmpty.{w + 1} PEmpty.{t + 1} where
  __ := Generators.ofSurjectiveAlgebraMap h.surjective
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    simp only [Set.range_eq_empty, Ideal.span_empty]
    symm
    rw [← RingHom.injective_iff_ker_eq_bot]
    change Function.Injective (aeval PEmpty.elim)
    rw [aeval_injective_iff_of_isEmpty]
    exact h.injective

lemma ofBijectiveAlgebraMap_dimension (h : Function.Bijective (algebraMap R S)) :
    (ofBijectiveAlgebraMap h).dimension = 0 := by
  simp [dimension]

variable (R) in
/-- The canonical `R`-presentation of `R` with no generators and no relations. -/
noncomputable def id : Presentation R R PEmpty.{w + 1} PEmpty.{t + 1} :=
  ofBijectiveAlgebraMap Function.bijective_id

lemma id_dimension : (Presentation.id R).dimension = 0 :=
  ofBijectiveAlgebraMap_dimension (R := R) Function.bijective_id

section Localization

variable (r : R) [IsLocalization.Away r S]

open IsLocalization.Away

lemma _root_.Algebra.Generators.ker_localizationAway :
    (Generators.localizationAway S r).ker = Ideal.span { C r * X () - 1 } := by
  have : aeval (S₁ := S) (Generators.localizationAway S r).val =
      (mvPolynomialQuotientEquiv S r).toAlgHom.comp
        (Ideal.Quotient.mkₐ R (Ideal.span {C r * X () - 1})) := by
    ext x
    simp only [aeval_X, Generators.localizationAway_val, AlgHom.coe_comp,
      AlgEquiv.coe_algHom, Ideal.Quotient.mkₐ_eq_mk, Function.comp_apply]
    rw [IsLocalization.Away.mvPolynomialQuotientEquiv_apply, aeval_X]
  rw [Generators.ker_eq_ker_aeval_val, this, ← RingHom.ker_coe_toRingHom, AlgHom.comp_toRingHom,
    ← RingHom.comap_ker]
  simp only [AlgEquiv.toAlgHom_toRingHom]
  change Ideal.comap _ (RingHom.ker (mvPolynomialQuotientEquiv S r)) = Ideal.span {C r * X () - 1}
  simp [RingHom.ker_equiv, ← RingHom.ker_eq_comap_bot]

variable (S) in
/-- If `S` is the localization of `R` away from `r`, we can construct a natural
presentation of `S` as `R`-algebra with a single generator `X` and the relation `r * X - 1 = 0`. -/
@[simps relation]
noncomputable def localizationAway : Presentation R S Unit Unit where
  toGenerators := Generators.localizationAway S r
  relation _ := C r * X () - 1
  span_range_relation_eq_ker := by
    simp only [Set.range_const]
    exact (Generators.ker_localizationAway r).symm

@[simp]
lemma localizationAway_dimension_zero : (localizationAway S r).dimension = 0 := by
  simp [Presentation.dimension]

lemma _root_.Algebra.Generators.C_mul_X_sub_one_mem_ker :
    C r * X () - 1 ∈ (Generators.localizationAway S r).ker :=
  (Presentation.localizationAway S r).relation_mem_ker ()

end Localization

section BaseChange

variable (T) [CommRing T] [Algebra R T] (P : Presentation R S ι σ)

lemma span_range_relation_eq_ker_baseChange :
    Ideal.span (Set.range fun i ↦ (MvPolynomial.map (algebraMap R T)) (P.relation i)) =
      RingHom.ker (aeval (S₁ := T ⊗[R] S) (P.baseChange T).val) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x ⟨y, hy⟩
    have Z := aeval_val_relation P y
    apply_fun TensorProduct.includeRight (R := R) (A := T) at Z
    rw [map_zero] at Z
    simp only [SetLike.mem_coe, RingHom.mem_ker, ← Z, ← hy,
      TensorProduct.includeRight_apply]
    rw [aeval_map_algebraMap T (P.baseChange T).val (P.relation y)]
    change _ = TensorProduct.includeRight.toRingHom _
    rw [map_aeval, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TensorProduct.includeRight.comp_algebraMap]
    rfl
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have H := Algebra.TensorProduct.lTensor_ker (A := T) (IsScalarTower.toAlgHom R P.Ring S)
      P.algebraMap_surjective
    let e := MvPolynomial.algebraTensorAlgEquiv (R := R) (σ := ι) (A := T)
    have H' : e.symm x ∈ RingHom.ker (TensorProduct.map (AlgHom.id R T)
        (IsScalarTower.toAlgHom R P.Ring S)) := by
      rw [RingHom.mem_ker, ← hx]
      clear hx
      induction x using MvPolynomial.induction_on with
      | C a =>
        simp only [algHom_C, TensorProduct.algebraMap_apply,
          algebraMap_self, RingHom.id_apply, e]
        rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
        simp only [TensorProduct.algebraMap_apply, algebraMap_self, RingHom.id_apply,
          TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p i hp => simp [hp, e]
    rw [H] at H'
    replace H' : e.symm x ∈ Ideal.map TensorProduct.includeRight P.ker := H'
    rw [← P.span_range_relation_eq_ker, ← Ideal.mem_comap, ← Ideal.comap_coe,
      ← AlgEquiv.toRingEquiv_toRingHom, Ideal.comap_coe, AlgEquiv.symm_toRingEquiv,
      Ideal.comap_symm, ← Ideal.map_coe, ← Ideal.map_coe _ (Ideal.span _), Ideal.map_map,
      Ideal.map_span, ← Set.range_comp, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe] at H'
    convert! H'
    simp [e]

/-- If `P` is a presentation of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural presentation of `T ⊗[R] S` over `T`. -/
@[simps relation]
noncomputable
def baseChange : Presentation T (T ⊗[R] S) ι σ where
  __ := P.toGenerators.baseChange T
  relation i := MvPolynomial.map (algebraMap R T) (P.relation i)
  span_range_relation_eq_ker := P.span_range_relation_eq_ker_baseChange T

lemma baseChange_toGenerators : (P.baseChange T).toGenerators = P.toGenerators.baseChange T := rfl

end BaseChange

section Composition

/-!
### Composition of presentations

Let `S` be an `R`-algebra with presentation `P` and `T` be an `S`-algebra with
presentation `Q`. In this section we construct a presentation of `T` as an `R`-algebra.

For the underlying generators see `Algebra.Generators.comp`. The family of relations is
indexed by `σ' ⊕ σ`.

We have two canonical maps:
`MvPolynomial ι R →ₐ[R] MvPolynomial (ι' ⊕ ι) R` induced by `Sum.inr`
and `aux : MvPolynomial (ι' ⊕ ι) R →ₐ[R] MvPolynomial ι' S` induced by
the evaluation `MvPolynomial ι R →ₐ[R] S` (see below).

Now `i : σ` is mapped to the image of `P.relation i` under the first map and
`j : σ'` is mapped to a pre-image under `aux` of `Q.relation j` (see `comp_relation_aux`
for the construction of the pre-image and `comp_relation_aux_map` for a proof that it is indeed
a pre-image).

The evaluation map factors as:
`MvPolynomial (ι' ⊕ ι) R →ₐ[R] MvPolynomial ι' S →ₐ[R] T`, where
the first map is `aux`. The goal is to compute that the kernel of this composition
is spanned by the relations indexed by `σ' ⊕ σ` (`span_range_relation_eq_ker_comp`).
One easily sees that this kernel is the pre-image under `aux` of the kernel of the evaluation
of `Q`, where the latter is by assumption spanned by the relations `Q.relation j`.

Since `aux` is surjective (`aux_surjective`), the pre-image is the sum of the ideal spanned
by the constructed pre-images of the `Q.relation j` and the kernel of `aux`. It hence
remains to show that the kernel of `aux` is spanned by the image of the `P.relation i`
under the canonical map `MvPolynomial ι R →ₐ[R] MvPolynomial (ι' ⊕ ι) R`. By
assumption this span is the kernel of the evaluation map of `P`. For this, we use the isomorphism
`MvPolynomial (ι' ⊕ ι) R ≃ₐ[R] MvPolynomial ι' (MvPolynomial ι R)` and
`MvPolynomial.ker_map`.

-/

variable {ι' σ' T : Type*} [CommRing T] [Algebra S T]
variable (Q : Presentation S T ι' σ') (P : Presentation R S ι σ)

set_option linter.unusedVariables false in
/-- The evaluation map `MvPolynomial (ι' ⊕ ι) →ₐ[R] T` factors via this map. For more
details, see the module docstring at the beginning of the section. -/
private noncomputable def aux (Q : Presentation S T ι' σ') (P : Presentation R S ι σ) :
    MvPolynomial (ι' ⊕ ι) R →ₐ[R] MvPolynomial ι' S :=
  aeval (Sum.elim X (MvPolynomial.C ∘ P.val))

/-- A choice of pre-image of `Q.relation r` under the canonical
map `MvPolynomial (ι' ⊕ ι) R →ₐ[R] MvPolynomial ι' S` given by the evaluation of `P`. -/
noncomputable def compRelationAux (r : σ') : MvPolynomial (ι' ⊕ ι) R :=
  Finsupp.sum (Q.relation r)
    (fun x j ↦ (MvPolynomial.rename Sum.inr <| P.σ j) * monomial (x.mapDomain Sum.inl) 1)

@[simp]
private lemma aux_X (i : ι' ⊕ ι) : (Q.aux P) (X i) = Sum.elim X (C ∘ P.val) i :=
  aeval_X (Sum.elim X (C ∘ P.val)) i

/-- The pre-images constructed in `compRelationAux` are indeed pre-images under `aux`. -/
private lemma compRelationAux_map (r : σ') :
    (Q.aux P) (Q.compRelationAux P r) = Q.relation r := by
  simp only [aux, compRelationAux, map_finsuppSum]
  simp only [map_mul, aeval_rename, aeval_monomial, Sum.elim_comp_inr]
  conv_rhs => rw [← Finsupp.sum_single (Q.relation r)]
  congr
  ext u s m
  simp only [MvPolynomial.single_eq_monomial, aeval, AlgHom.coe_mk, coe_eval₂Hom]
  rw [monomial_eq, IsScalarTower.algebraMap_eq R S, algebraMap_eq, ← eval₂_comp_left, ← aeval_def]
  simp [Finsupp.prod_mapDomain_index_inj (Sum.inl_injective)]

private lemma aux_surjective : Function.Surjective (Q.aux P) := fun p ↦ by
  induction p using MvPolynomial.induction_on with
  | C a =>
    use rename Sum.inr <| P.σ a
    simp [aux, aeval_rename]
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | mul_X p i h =>
    obtain ⟨a, rfl⟩ := h
    exact ⟨(a * X (Sum.inl i)), by simp⟩

private lemma aux_image_relation :
    Q.aux P '' (Set.range (Algebra.Presentation.compRelationAux Q P)) = Set.range Q.relation := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (Q.compRelationAux_map P a).symm⟩
  · rintro ⟨y, rfl⟩
    use Q.compRelationAux P y
    simp only [Set.mem_range, exists_apply_eq_apply, true_and, compRelationAux_map]

private lemma aux_eq_comp : Q.aux P =
    (MvPolynomial.mapAlgHom (aeval P.val)).comp (sumAlgEquiv R ι' ι).toAlgHom := by
  ext i : 1
  cases i <;> simp

private lemma aux_ker :
    RingHom.ker (Q.aux P) = Ideal.map (rename Sum.inr) (RingHom.ker (aeval P.val)) := by
  rw [aux_eq_comp, ← AlgHom.comap_ker, MvPolynomial.ker_mapAlgHom]
  change Ideal.comap _ (Ideal.map (IsScalarTower.toAlgHom R (MvPolynomial ι R) _) _) = _
  rw [← sumAlgEquiv_comp_rename_inr, ← Ideal.map_mapₐ, Ideal.comap_map_of_bijective]
  simpa using AlgEquiv.bijective (sumAlgEquiv R ι' ι)

variable [Algebra R T] [IsScalarTower R S T]

private lemma aeval_comp_val_eq :
    (aeval (Q.comp P.toGenerators).val) =
      (aevalTower (IsScalarTower.toAlgHom R S T) Q.val).comp (Q.aux P) := by
  ext i
  simp only [AlgHom.coe_comp, Function.comp_apply]
  cases i <;> simp

lemma span_range_relation_eq_ker_comp : Ideal.span
    (Set.range (Sum.elim (Algebra.Presentation.compRelationAux Q P)
      fun rp ↦ (rename Sum.inr) (P.relation rp))) = (Q.comp P.toGenerators).ker := by
  rw [Generators.ker_eq_ker_aeval_val, Q.aeval_comp_val_eq, ← AlgHom.comap_ker]
  change _ = Ideal.comap _ (RingHom.ker (aeval Q.val))
  rw [← Q.ker_eq_ker_aeval_val, ← Q.span_range_relation_eq_ker, ← Q.aux_image_relation P,
    ← Ideal.map_span, Ideal.comap_map_of_surjective' _ (Q.aux_surjective P)]
  rw [Set.Sum.elim_range, Ideal.span_union, Q.aux_ker, ← P.ker_eq_ker_aeval_val,
    ← P.span_range_relation_eq_ker, Ideal.map_span]
  congr
  ext
  simp

/-- Given presentations of `T` over `S` and of `S` over `R`,
we may construct a presentation of `T` over `R`. -/
@[simps -isSimp relation]
noncomputable def comp : Presentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
  toGenerators := Q.toGenerators.comp P.toGenerators
  relation := Sum.elim (Q.compRelationAux P)
    (fun rp ↦ MvPolynomial.rename Sum.inr <| P.relation rp)
  span_range_relation_eq_ker := Q.span_range_relation_eq_ker_comp P

lemma toGenerators_comp : (Q.comp P).toGenerators = Q.toGenerators.comp P.toGenerators := rfl

@[simp]
lemma comp_relation_inr (r : σ) :
    (Q.comp P).relation (Sum.inr r) = rename Sum.inr (P.relation r) :=
  rfl

lemma comp_aeval_relation_inl (r : σ') :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val)) ((Q.comp P).relation (Sum.inl r)) =
      Q.relation r := by
  change (Q.aux P) _ = _
  simp [comp_relation, compRelationAux_map]

variable (g : S) [IsLocalization.Away g T] (P : Generators R S ι)

/-- The composition of a presentation `P` with a
localization away from an element has the form `R[Xᵢ, Y]/(fⱼ, (P.σ g) Y - 1)`,
if the chosen section of `P` preserves `-1` and `0`.
Note: If `S` is non-trivial, we can ensure this by only modifying `P.σ`. -/
lemma relation_comp_localizationAway_inl (P : Presentation R S ι σ)
    (h1 : P.σ (-1) = -1) (h0 : P.σ 0 = 0) (r : Unit) :
    ((Presentation.localizationAway T g).comp P).relation (Sum.inl r) =
      rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1 := by
  classical
  simp only [Presentation.comp, Sum.elim_inl, Presentation.compRelationAux,
    Presentation.localizationAway_relation, sub_eq_add_neg, C_mul_X_eq_monomial,
    ← map_one C, ← map_neg C]
  refine (Finsupp.sum_single_add_single (Finsupp.single () 1) 0 g (-1 : S) _ ?_ ?_).trans ?_
  · simp
  · simp [h0]
  · simp [h1, ← X_pow_eq_monomial]

end Composition

/-- Given a presentation `P` and equivalences `ι' ≃ ι` and
`σ' ≃ σ`, this is the induced presentation with variables indexed
by `ι'` and relations indexed by `σ'` -/
@[simps toGenerators]
noncomputable def reindex (P : Presentation R S ι σ)
    {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) :
    Presentation R S ι' σ' where
  __ := P.toGenerators.reindex e
  relation := rename e.symm ∘ P.relation ∘ f
  span_range_relation_eq_ker := by
    rw [Generators.ker_eq_ker_aeval_val, Generators.reindex_val, ← aeval_comp_rename,
      ← AlgHom.comap_ker, ← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker,
      Set.range_comp, Set.range_comp, Equiv.range_eq_univ, Set.image_univ,
      ← Ideal.map_span (rename ⇑e.symm)]
    have hf : Function.Bijective (MvPolynomial.rename e.symm) := (renameEquiv R e.symm).bijective
    apply Ideal.comap_injective_of_surjective _ hf.2
    simp_rw [Ideal.comap_comapₐ, rename_comp_rename, Equiv.self_comp_symm]
    simp [Ideal.comap_map_of_bijective _ hf, rename_id]

@[simp]
lemma dimension_reindex (P : Presentation R S ι σ) {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) :
    (P.reindex e f).dimension = P.dimension := by
  simp [dimension, Nat.card_congr e, Nat.card_congr f]

section

variable {v : ι → MvPolynomial σ R}
  (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R)
  (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x)

/--
The naive presentation of a quotient `R[Xᵢ] ⧸ (vⱼ)`.
If the definitional equality of the section matters, it can be explicitly provided.
-/
@[simps! toGenerators]
noncomputable
def naive {v : ι → MvPolynomial σ R}
    (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R :=
      Function.surjInv Ideal.Quotient.mk_surjective)
    (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x := by apply Function.surjInv_eq) :
    Presentation R (MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) σ ι where
  __ := Generators.naive s hs
  relation := v
  span_range_relation_eq_ker := (Generators.ker_naive s hs).symm

lemma naive_relation : (naive s hs).relation = v := by rfl

@[simp] lemma naive_relation_apply (i : ι) : (naive s hs).relation i = v i := rfl

lemma mem_ker_naive (i : ι) : v i ∈ (naive s hs).ker := relation_mem_ker _ i

end

end Construction

end Presentation

lemma Generators.fg_ker_of_finitePresentation [Algebra.FinitePresentation R S] {α : Type*}
    (P : Generators R S α) [Finite α] : P.ker.FG := by
  rw [Generators.ker_eq_ker_aeval_val]
  exact Algebra.FinitePresentation.ker_fG_of_surjective _ P.aeval_val_surjective

end Algebra
