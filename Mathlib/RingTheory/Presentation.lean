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

We also give constructors for localization, base change and composition.

## TODO

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
  /-- The type of relations. -/
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

lemma relation_mem_ker (i : P.rels) : P.relation i ∈ P.ker := by
  rw [← P.span_range_relation_eq_ker]
  apply Ideal.subset_span
  use i

/-- The polynomial algebra wrt a family of generators modulo a family of relations. -/
protected abbrev Quotient : Type (max w u) := P.Ring ⧸ P.ker

/-- `P.Quotient` is `P.Ring`-isomorphic to `S` and in particular `R`-isomorphic to `S`. -/
def quotientEquiv : P.Quotient ≃ₐ[P.Ring] S :=
  Ideal.quotientKerAlgEquivOfRightInverse (f := Algebra.ofId P.Ring S) (g := P.σ) <| fun x ↦ by
    rw [Algebra.ofId_apply, P.algebraMap_apply, P.aeval_val_σ]

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

variable (R S) in
/-- An arbitrary choice of a finite presentation of a finitely presented algebra. -/
noncomputable
def ofFinitePresentation [FinitePresentation R S] : Presentation.{0, 0} R S :=
  letI H := FinitePresentation.out (R := R) (A := S)
  letI n : ℕ := H.choose
  letI f : MvPolynomial (Fin n) R →ₐ[R] S := H.choose_spec.choose
  haveI hf : Function.Surjective f := H.choose_spec.choose_spec.1
  haveI hf' : (RingHom.ker f).FG := H.choose_spec.choose_spec.2
  letI H' := Submodule.fg_iff_exists_fin_generating_family.mp hf'
  let m : ℕ := H'.choose
  let v : Fin m → MvPolynomial (Fin n) R := H'.choose_spec.choose
  let hv : Ideal.span (Set.range v) = RingHom.ker f := H'.choose_spec.choose_spec
  { __ := Generators.ofSurjective (fun x ↦ f (.X x)) (by convert hf; ext; simp)
    rels := Fin m
    relation := v
    span_range_relation_eq_ker := hv.trans (by congr; ext; simp) }

instance [FinitePresentation R S] : (ofFinitePresentation R S).IsFinite where
  finite_vars := Finite.of_fintype (Fin _)
  finite_rels := Finite.of_fintype (Fin _)

section Construction

/-- If `algebraMap R S` is bijective, the empty generators are a presentation with no relations. -/
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    Presentation.{t, w} R S where
  __ := Generators.ofSurjectiveAlgebraMap h.surjective
  rels := PEmpty
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    simp only [Set.range_eq_empty, Ideal.span_empty]
    symm
    rw [← RingHom.injective_iff_ker_eq_bot]
    show Function.Injective (aeval PEmpty.elim)
    rw [aeval_injective_iff_of_isEmpty]
    exact h.injective

instance ofBijectiveAlgebraMap_isFinite (h : Function.Bijective (algebraMap R S)) :
    (ofBijectiveAlgebraMap.{t, w} h).IsFinite where
  finite_vars := inferInstanceAs (Finite PEmpty.{w + 1})
  finite_rels := inferInstanceAs (Finite PEmpty.{t + 1})

lemma ofBijectiveAlgebraMap_dimension (h : Function.Bijective (algebraMap R S)) :
    (ofBijectiveAlgebraMap h).dimension = 0 := by
  simp_rw [dimension, ofBijectiveAlgebraMap, Generators.ofSurjectiveAlgebraMap,
    Generators.ofSurjective, Nat.card_eq_fintype_card, Fintype.card_ofIsEmpty]

variable (R) in
/-- The canonical `R`-presentation of `R` with no generators and no relations. -/
noncomputable def id : Presentation.{t, w} R R := ofBijectiveAlgebraMap Function.bijective_id

instance : (id R).IsFinite := ofBijectiveAlgebraMap_isFinite (R := R) Function.bijective_id

lemma id_dimension : (Presentation.id R).dimension = 0 :=
  ofBijectiveAlgebraMap_dimension (R := R) Function.bijective_id

section Localization

variable (r : R) [IsLocalization.Away r S]

open IsLocalization.Away

lemma _root_.Algebra.Generators.ker_localizationAway :
    (Generators.localizationAway (S := S) r).ker = Ideal.span { C r * X () - 1 } := by
  have : aeval (S₁ := S) (Generators.localizationAway r).val =
      (mvPolynomialQuotientEquiv S r).toAlgHom.comp
        (Ideal.Quotient.mkₐ R (Ideal.span {C r * X () - 1})) := by
    ext x
    simp only [Generators.localizationAway_vars, aeval_X, Generators.localizationAway_val,
      AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, Ideal.Quotient.mkₐ_eq_mk,
      Function.comp_apply]
    rw [IsLocalization.Away.mvPolynomialQuotientEquiv_apply, aeval_X]
  rw [Generators.ker_eq_ker_aeval_val, this, AlgEquiv.toAlgHom_eq_coe, ← RingHom.ker_coe_toRingHom,
    AlgHom.comp_toRingHom, ← RingHom.comap_ker]
  simp only [Generators.localizationAway_vars, AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe,
    AlgEquiv.toAlgHom_toRingHom]
  show Ideal.comap _ (RingHom.ker (mvPolynomialQuotientEquiv S r)) = Ideal.span {C r * X () - 1}
  simp [RingHom.ker_equiv, ← RingHom.ker_eq_comap_bot]

variable (S) in
/-- If `S` is the localization of `R` away from `r`, we can construct a natural
presentation of `S` as `R`-algebra with a single generator `X` and the relation `r * X - 1 = 0`. -/
@[simps relation, simps -isSimp rels]
noncomputable def localizationAway : Presentation R S where
  toGenerators := Generators.localizationAway r
  rels := Unit
  relation _ := C r * X () - 1
  span_range_relation_eq_ker := by
    simp only [Generators.localizationAway_vars, Set.range_const]
    exact (Generators.ker_localizationAway r).symm

instance localizationAway_isFinite : (localizationAway S r).IsFinite where
  finite_vars := inferInstanceAs <| Finite Unit
  finite_rels := inferInstanceAs <| Finite Unit

instance : Fintype (localizationAway S r).rels :=
  inferInstanceAs (Fintype Unit)

@[simp]
lemma localizationAway_dimension_zero : (localizationAway S r).dimension = 0 := by
  simp [Presentation.dimension, localizationAway, Generators.localizationAway_vars]

end Localization

section BaseChange

variable (T) [CommRing T] [Algebra R T] (P : Presentation R S)

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
    erw [aeval_map_algebraMap T P.baseChange.val (P.relation y)]
    show _ = TensorProduct.includeRight.toRingHom _
    rw [map_aeval, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TensorProduct.includeRight.comp_algebraMap]
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
      | C a =>
        simp only [Generators.algebraMap_apply, algHom_C, TensorProduct.algebraMap_apply,
          id.map_eq_id, RingHom.id_apply, e]
        rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
        simp only [TensorProduct.algebraMap_apply, id.map_eq_id, RingHom.id_apply,
          TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one, algebraMap_eq]
        erw [aeval_C]
        simp
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p i hp =>
        simp only [map_mul, algebraTensorAlgEquiv_symm_X, hp, TensorProduct.map_tmul, map_one,
          IsScalarTower.coe_toAlgHom', Generators.algebraMap_apply, aeval_X, e]
        congr
        erw [aeval_X]
        rw [Generators.baseChange_val]
    rw [H] at H'
    replace H' : e.symm x ∈ Ideal.map TensorProduct.includeRight P.ker := H'
    rw [← P.span_range_relation_eq_ker, ← Ideal.mem_comap, ← Ideal.comap_coe,
      ← AlgEquiv.toRingEquiv_toRingHom, Ideal.comap_coe, AlgEquiv.symm_toRingEquiv,
      Ideal.comap_symm, ← Ideal.map_coe, ← Ideal.map_coe _ (Ideal.span _), Ideal.map_map,
      Ideal.map_span, ← Set.range_comp, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe] at H'
    convert H'
    simp [e]

/-- If `P` is a presentation of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural presentation of `T ⊗[R] S` over `T`. -/
@[simps relation, simps -isSimp rels]
noncomputable
def baseChange : Presentation T (T ⊗[R] S) where
  __ := Generators.baseChange P.toGenerators
  rels := P.rels
  relation i := MvPolynomial.map (algebraMap R T) (P.relation i)
  span_range_relation_eq_ker := P.span_range_relation_eq_ker_baseChange T

lemma baseChange_toGenerators : (P.baseChange T).toGenerators = P.toGenerators.baseChange := rfl

instance baseChange_isFinite [P.IsFinite] : (P.baseChange T).IsFinite where
  finite_vars := inferInstanceAs <| Finite (P.vars)
  finite_rels := inferInstanceAs <| Finite (P.rels)

end BaseChange

section Composition

/-!
### Composition of presentations

Let `S` be an `R`-algebra with presentation `P` and `T` be an `S`-algebra with
presentation `Q`. In this section we construct a presentation of `T` as an `R`-algebra.

For the underlying generators see `Algebra.Generators.comp`. The family of relations is
indexed by `Q.rels ⊕ P.rels`.

We have two canonical maps:
`MvPolynomial P.vars R →ₐ[R] MvPolynomial (Q.vars ⊕ P.vars) R` induced by `Sum.inr`
and `aux : MvPolynomial (Q.vars ⊕ P.vars) R →ₐ[R] MvPolynomial Q.vars S` induced by
the evaluation `MvPolynomial P.vars R →ₐ[R] S` (see below).

Now `i : P.rels` is mapped to the image of `P.relation i` under the first map and
`j : Q.rels` is mapped to a pre-image under `aux` of `Q.relation j` (see `comp_relation_aux`
for the construction of the pre-image and `comp_relation_aux_map` for a proof that it is indeed
a pre-image).

The evaluation map factors as:
`MvPolynomial (Q.vars ⊕ P.vars) R →ₐ[R] MvPolynomial Q.vars S →ₐ[R] T`, where
the first map is `aux`. The goal is to compute that the kernel of this composition
is spanned by the relations indexed by `Q.rels ⊕ P.rels` (`span_range_relation_eq_ker_comp`).
One easily sees that this kernel is the pre-image under `aux` of the kernel of the evaluation
of `Q`, where the latter is by assumption spanned by the relations `Q.relation j`.

Since `aux` is surjective (`aux_surjective`), the pre-image is the sum of the ideal spanned
by the constructed pre-images of the `Q.relation j` and the kernel of `aux`. It hence
remains to show that the kernel of `aux` is spanned by the image of the `P.relation i`
under the canonical map `MvPolynomial P.vars R →ₐ[R] MvPolynomial (Q.vars ⊕ P.vars) R`. By
assumption this span is the kernel of the evaluation map of `P`. For this, we use the isomorphism
`MvPolynomial (Q.vars ⊕ P.vars) R ≃ₐ[R] MvPolynomial Q.vars (MvPolynomial P.vars R)` and
`MvPolynomial.ker_map`.

-/

variable {T} [CommRing T] [Algebra S T]
variable (Q : Presentation S T) (P : Presentation R S)

/-- The evaluation map `MvPolynomial (Q.vars ⊕ P.vars) →ₐ[R] T` factors via this map. For more
details, see the module docstring at the beginning of the section. -/
private noncomputable def aux : MvPolynomial (Q.vars ⊕ P.vars) R →ₐ[R] MvPolynomial Q.vars S :=
  aeval (Sum.elim X (MvPolynomial.C ∘ P.val))

/-- A choice of pre-image of `Q.relation r` under `aux`. -/
private noncomputable def comp_relation_aux (r : Q.rels) : MvPolynomial (Q.vars ⊕ P.vars) R :=
  Finsupp.sum (Q.relation r)
    (fun x j ↦ (MvPolynomial.rename Sum.inr <| P.σ j) * monomial (x.mapDomain Sum.inl) 1)

@[simp]
private lemma aux_X (i : Q.vars ⊕ P.vars) : (Q.aux P) (X i) = Sum.elim X (C ∘ P.val) i :=
  aeval_X (Sum.elim X (C ∘ P.val)) i

/-- The pre-images constructed in `comp_relation_aux` are indeed pre-images under `aux`. -/
private lemma comp_relation_aux_map (r : Q.rels) :
    (Q.aux P) (Q.comp_relation_aux P r) = Q.relation r := by
  simp only [aux, comp_relation_aux, Generators.comp_vars, Sum.elim_inl, map_finsupp_sum]
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
    simp only [aux, aeval_rename, Sum.elim_comp_inr]
    have (p : MvPolynomial P.vars R) :
        aeval (C ∘ P.val) p = (C (aeval P.val p) : MvPolynomial Q.vars S) := by
      induction p using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp [hp, hq]
      | mul_X p i h => simp [h]
    simp [this]
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | mul_X p i h =>
    obtain ⟨a, rfl⟩ := h
    exact ⟨(a * X (Sum.inl i)), by simp⟩

private lemma aux_image_relation :
    Q.aux P '' (Set.range (Algebra.Presentation.comp_relation_aux Q P)) = Set.range Q.relation := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (Q.comp_relation_aux_map P a).symm⟩
  · rintro ⟨y, rfl⟩
    use Q.comp_relation_aux P y
    simp only [Set.mem_range, exists_apply_eq_apply, true_and, comp_relation_aux_map]

private lemma aux_eq_comp : Q.aux P =
    (MvPolynomial.mapAlgHom (aeval P.val)).comp (sumAlgEquiv R Q.vars P.vars).toAlgHom := by
  ext i : 1
  cases i <;> simp

private lemma aux_ker :
    RingHom.ker (Q.aux P) = Ideal.map (rename Sum.inr) (RingHom.ker (aeval P.val)) := by
  rw [aux_eq_comp, ← AlgHom.comap_ker, MvPolynomial.ker_mapAlgHom]
  show Ideal.comap _ (Ideal.map (IsScalarTower.toAlgHom R (MvPolynomial P.vars R) _) _) = _
  rw [← sumAlgEquiv_comp_rename_inr, ← Ideal.map_mapₐ, Ideal.comap_map_of_bijective]
  simpa using AlgEquiv.bijective (sumAlgEquiv R Q.vars P.vars)

variable [Algebra R T] [IsScalarTower R S T]

private lemma aeval_comp_val_eq :
    (aeval (Q.comp P.toGenerators).val) =
      (aevalTower (IsScalarTower.toAlgHom R S T) Q.val).comp (Q.aux P) := by
  ext i
  simp only [AlgHom.coe_comp, Function.comp_apply]
  erw [Q.aux_X P i]
  cases i <;> simp

private lemma span_range_relation_eq_ker_comp : Ideal.span
    (Set.range (Sum.elim (Algebra.Presentation.comp_relation_aux Q P)
      fun rp ↦ (rename Sum.inr) (P.relation rp))) = (Q.comp P.toGenerators).ker := by
  rw [Generators.ker_eq_ker_aeval_val, Q.aeval_comp_val_eq, ← AlgHom.comap_ker]
  show _ = Ideal.comap _ (RingHom.ker (aeval Q.val))
  rw [← Q.ker_eq_ker_aeval_val, ← Q.span_range_relation_eq_ker, ← Q.aux_image_relation P,
    ← Ideal.map_span, Ideal.comap_map_of_surjective' _ (Q.aux_surjective P)]
  rw [Set.Sum.elim_range, Ideal.span_union, Q.aux_ker, ← P.ker_eq_ker_aeval_val,
    ← P.span_range_relation_eq_ker, Ideal.map_span]
  congr
  ext
  simp

/-- Given presentations of `T` over `S` and of `S` over `R`,
we may construct a presentation of `T` over `R`. -/
@[simps rels, simps -isSimp relation]
noncomputable def comp : Presentation R T where
  toGenerators := Q.toGenerators.comp P.toGenerators
  rels := Q.rels ⊕ P.rels
  relation := Sum.elim (Q.comp_relation_aux P)
    (fun rp ↦ MvPolynomial.rename Sum.inr <| P.relation rp)
  span_range_relation_eq_ker := Q.span_range_relation_eq_ker_comp P

lemma toGenerators_comp : (Q.comp P).toGenerators = Q.toGenerators.comp P.toGenerators := rfl

@[simp]
lemma comp_relation_inr (r : P.rels) :
    (Q.comp P).relation (Sum.inr r) = rename Sum.inr (P.relation r) :=
  rfl

lemma comp_aeval_relation_inl (r : Q.rels) :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val)) ((Q.comp P).relation (Sum.inl r)) =
      Q.relation r := by
  show (Q.aux P) _ = _
  simp [comp_relation, comp_relation_aux_map]

instance comp_isFinite [P.IsFinite] [Q.IsFinite] : (Q.comp P).IsFinite where
  finite_vars := inferInstanceAs <| Finite (Q.vars ⊕ P.vars)
  finite_rels := inferInstanceAs <| Finite (Q.rels ⊕ P.rels)

end Composition

/-- Given a presentation `P` and equivalences `ι ≃ P.vars` and
`κ ≃ P.rels`, this is the induced presentation with variables indexed
by `ι` and relations indexed by `κ -/
@[simps toGenerators, simps -isSimp relation rels]
noncomputable def reindex (P : Presentation.{w, t} R S)
    {ι κ : Type*} (e : ι ≃ P.vars) (f : κ ≃ P.rels) :
    Presentation R S where
  __ := P.toGenerators.reindex e
  rels := κ
  relation := rename e.symm ∘ P.relation ∘ f
  span_range_relation_eq_ker := by
    rw [Generators.ker_eq_ker_aeval_val, Generators.reindex_val, ← aeval_comp_rename,
      ← AlgHom.comap_ker, ← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker,
      Set.range_comp, Set.range_comp, Equiv.range_eq_univ, Set.image_univ,
      ← Ideal.map_span (rename ⇑e.symm)]
    have hf : Function.Bijective (MvPolynomial.rename e.symm) := (renameEquiv R e.symm).bijective
    apply Ideal.comap_injective_of_surjective _ hf.2
    simp_rw [Ideal.comap_comapₐ, rename_comp_rename, Generators.reindex_vars, Equiv.self_comp_symm]
    simp [Ideal.comap_map_of_bijective _ hf, rename_id]

@[simp]
lemma isFinite_reindex_iff {ι κ : Type*} (e : ι ≃ P.vars) (f : κ ≃ P.rels) :
    (P.reindex e f).IsFinite ↔ P.IsFinite :=
  ⟨fun h ↦ ⟨e.finite_iff.mp h.1, f.finite_iff.mp h.2⟩,
    fun h ↦ ⟨e.finite_iff.mpr h.1, f.finite_iff.mpr h.2⟩⟩

alias ⟨_, IsFinite.reindex⟩ := isFinite_reindex_iff

@[simp]
lemma dimension_reindex (P : Presentation.{w, t} R S) {ι κ : Type*} (e : ι ≃ P.vars)
    (f : κ ≃ P.rels) :
    (P.reindex e f).dimension = P.dimension := by
  simp [dimension, Generators.reindex_vars, reindex_rels, Nat.card_congr e, Nat.card_congr f]

end Construction

end Presentation

end Algebra
