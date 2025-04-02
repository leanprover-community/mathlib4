/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.LinearAlgebra.Basis.Exact
import Mathlib.RingTheory.Kaehler.CotangentComplex
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Etale.Basic

/-!
# Cotangent complex of a submersive presentation

Let `P` be a submersive presentation of `S` as an `R`-algebra and
denote by `I` the kernel `R[X] → S`. We show

- `SubmersivePresentation.free_cotangent`: `I ⧸ I ^ 2` is `S`-free on the classes of `P.relation i`.
- `SubmersivePresentation.subsingleton_h1Cotangent`: `H¹(L_{S/R}) = 0`.
- `SubmersivePresentation.free_kaehlerDifferential`: `Ω[S⁄R]` is `S`-free on the images of `dxᵢ`
  where `i ∉ Set.range P.map`.
- `SubmersivePresentation.rank_kaehlerDifferential`: If `S` is non-trivial, the rank of
  `Ω[S⁄R]` is the dimension of `P`.

We also provide the corresponding instances for standard smooth algebras as corollaries.

We keep the notation `I = ker(R[X] → S)` in all docstrings of this file.
-/

universe u

namespace Algebra

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

open Extension MvPolynomial

namespace PreSubmersivePresentation

/--
Given a pre-submersive presentation, this is the composition
`I ⧸ I ^ 2 → ⊕ S dxᵢ → ⊕ S dxᵢ` where the second direct sum runs over
all `i : P.rels` induced by the injection `P.map : P.rels → P.vars`.

If `P` is submersive, this is an isomorphism. See `SubmersivePresentation.cotangentEquiv`.
-/
noncomputable def cotangentComplexAux (P : PreSubmersivePresentation R S) :
    P.toExtension.Cotangent →ₗ[S] P.rels → S :=
  Finsupp.linearEquivFunOnFinite S S P.rels ∘ₗ Finsupp.lcomapDomain _ P.map_inj ∘ₗ
    P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ P.toExtension.cotangentComplex

lemma cotangentComplexAux_apply (P : PreSubmersivePresentation R S) (x : P.ker) (i : P.rels) :
    P.cotangentComplexAux (Cotangent.mk x) i = (aeval P.val) (pderiv (P.map i) x.val) := by
  dsimp only [cotangentComplexAux, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    cotangentComplex_mk]
  simp only [Generators.toExtension_Ring, Finsupp.lcomapDomain_apply,
    Finsupp.linearEquivFunOnFinite_apply, Finsupp.comapDomain_apply,
    Generators.cotangentSpaceBasis_repr_tmul, one_mul]

lemma cotangentComplexAux_zero_iff {P : PreSubmersivePresentation R S} (x : P.ker) :
    P.cotangentComplexAux (Cotangent.mk x) = 0 ↔
      ∀ i : P.rels, (aeval P.val) (pderiv (P.map i) x.val) = 0 := by
  rw [funext_iff]
  simp_rw [cotangentComplexAux_apply, Pi.zero_apply]

end PreSubmersivePresentation

namespace SubmersivePresentation

variable (P : SubmersivePresentation R S)

lemma cotangentComplexAux_injective : Function.Injective P.cotangentComplexAux := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨(x : P.ker), rfl⟩ := Cotangent.mk_surjective x
  rw [Submodule.mem_bot, Cotangent.mk_eq_zero_iff]
  rw [LinearMap.mem_ker, P.cotangentComplexAux_zero_iff] at hx
  have : x.val ∈ Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker]
    exact x.property
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp this
  have heq (i : P.rels) :
      aeval P.val (pderiv (P.map i) <| c.sum fun i a ↦ a * P.relation i) = 0 := by
    rw [hc]
    apply hx
  simp only [Finsupp.sum, map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    Presentation.aeval_val_relation, zero_mul, add_zero] at heq
  have heq2 : ∑ i ∈ c.support,
      aeval P.val (c i) • (fun j ↦ aeval P.val (pderiv (P.map j) (P.relation i))) = 0 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    apply heq
  have (i : P.rels) : aeval P.val (c i) = 0 := by
    have := P.linearIndependent_aeval_val_pderiv_relation
    rw [linearIndependent_iff''] at this
    have := this c.support (fun i ↦ aeval P.val (c i))
      (by intro i; simp only [Finsupp.mem_support_iff, ne_eq, not_not]; intro h; simp [h]) heq2
    exact this i
  show _ ∈ P.ker ^ 2
  rw [← hc]
  apply Ideal.sum_mem
  intro i hi
  rw [pow_two]
  apply Ideal.mul_mem_mul
  · rw [P.ker_eq_ker_aeval_val]
    simpa using this i
  · exact P.relation_mem_ker i

lemma cotangentComplexAux_surjective : Function.Surjective P.cotangentComplexAux := by
  rw [← LinearMap.range_eq_top, _root_.eq_top_iff, ← P.basisDeriv.span_eq, Submodule.span_le]
  rintro - ⟨i, rfl⟩
  use Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩
  ext j
  rw [P.cotangentComplexAux_apply]
  simp

/-- The isomorphism of `S`-modules between `I ⧸ I ^ 2` and `P.rels → S` given
by `P.relation i ↦ ∂ⱼ (P.relation i)`. -/
@[simps! apply]
noncomputable def cotangentEquiv : P.toExtension.Cotangent ≃ₗ[S] P.rels → S :=
  LinearEquiv.ofBijective _ ⟨P.cotangentComplexAux_injective, P.cotangentComplexAux_surjective⟩

lemma cotangentComplex_injective : Function.Injective P.toExtension.cotangentComplex := by
  have := P.cotangentComplexAux_injective
  simp only [PreSubmersivePresentation.cotangentComplexAux, LinearMap.coe_comp,
    LinearEquiv.coe_coe] at this
  exact Function.Injective.of_comp (Function.Injective.of_comp <| Function.Injective.of_comp this)

/-- If `P` is a submersive presentation, `H¹` of the associated cotangent complex vanishes. -/
instance subsingleton_h1Cotangent : Subsingleton P.toExtension.H1Cotangent := by
  rw [Algebra.Extension.subsingleton_h1Cotangent]
  exact cotangentComplex_injective P

/-- The classes of `P.relation i` form a basis of `I ⧸ I ^ 2`. -/
@[stacks 00T7 "(3)"]
noncomputable def basisCotangent : Basis P.rels S P.toExtension.Cotangent :=
  ⟨cotangentEquiv P ≪≫ₗ (Finsupp.linearEquivFunOnFinite S S P.rels).symm⟩

@[stacks 00T7 "(3)"]
instance free_cotangent : Module.Free S P.toExtension.Cotangent :=
  Module.Free.of_basis P.basisCotangent

/--
If `P` is a submersive presentation, this is the section of the map
`I ⧸ I ^ 2 → ⊕ S dxᵢ` given by projecting to the summands indexed by `P.rels` and composing with the
inverse of `P.cotangentEquiv`.

By `SubmersivePresentation.sectionCotangent_comp` this is indeed a section.
-/
noncomputable def sectionCotangent : P.toExtension.CotangentSpace →ₗ[S] P.toExtension.Cotangent :=
  (cotangentEquiv P).symm ∘ₗ (Finsupp.linearEquivFunOnFinite S S P.rels).toLinearMap ∘ₗ
    Finsupp.lcomapDomain _ P.map_inj ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap

lemma sectionCotangent_eq_iff (x : P.toExtension.CotangentSpace) (y : P.toExtension.Cotangent) :
    sectionCotangent P x = y ↔
      ∀ i : P.rels, P.cotangentSpaceBasis.repr x (P.map i) = (P.cotangentComplexAux y) i := by
  simp only [sectionCotangent, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← (cotangentEquiv P).injective.eq_iff, funext_iff, LinearEquiv.apply_symm_apply]
  simp

lemma sectionCotangent_comp :
    sectionCotangent P ∘ₗ P.toExtension.cotangentComplex = LinearMap.id := by
  ext : 1
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [sectionCotangent_eq_iff]
  intro i
  rfl

lemma sectionCotangent_zero_of_not_mem_range (i : P.vars) (hi : i ∉ Set.range P.map) :
    (sectionCotangent P) (P.cotangentSpaceBasis i) = 0 := by
  classical
  contrapose hi
  rw [sectionCotangent_eq_iff] at hi
  simp only [Basis.repr_self, map_zero, Pi.zero_apply, not_forall,
    Finsupp.single_apply, ite_eq_right_iff, Classical.not_imp, exists_and_right] at hi
  obtain ⟨j, hij, _⟩ := hi
  simp only [Set.mem_range, not_exists, not_forall, not_not]
  use j
  exact hij.symm

/--
Given a submersive presentation of `S` as `R`-algebra, any indexing type `κ` complementary to
the `P.rels` in `P.vars` indexes a basis of `Ω[S⁄R]`.
See `SubmersivePresentation.basisKaehler` for the special case `κ = (Set.range P.map)ᶜ`.
-/
noncomputable def basisKaehlerOfIsCompl {κ : Type*} {f : κ → P.vars}
    (hf : Function.Injective f) (hcompl : IsCompl (Set.range f) (Set.range P.map)) :
    Basis κ S (Ω[S⁄R]) := by
  apply P.cotangentSpaceBasis.ofSplitExact (sectionCotangent_comp P)
    Extension.exact_cotangentComplex_toKaehler Extension.toKaehler_surjective hf (b := P.map)
  · intro i
    apply sectionCotangent_zero_of_not_mem_range _ _
    simp [← hcompl.compl_eq]
  · simp only [sectionCotangent, LinearMap.coe_comp, Function.comp_assoc, LinearEquiv.coe_coe]
    apply LinearIndependent.map' _ _ P.cotangentEquiv.symm.ker
    convert (Pi.basisFun S P.rels).linearIndependent
    classical
    ext i j
    simp only [Function.comp_apply, Basis.repr_self, Finsupp.linearEquivFunOnFinite_apply,
      Pi.basisFun_apply, Finsupp.single_apply_left P.map_inj, Finsupp.single_eq_pi_single]
    simp [Finsupp.single_eq_pi_single]
  · exact hcompl.2

/-- Given a submersive presentation of `S` as `R`-algebra, the images of `dxᵢ`
for `i` in the complement of `P.rels` in `P.vars` form a basis of `Ω[S⁄R]`. -/
@[stacks 00T7 "(2)"]
noncomputable def basisKaehler :
    Basis ((Set.range P.map)ᶜ : Set _) S (Ω[S⁄R]) :=
  P.basisKaehlerOfIsCompl Subtype.val_injective <| by
    rw [Subtype.range_coe_subtype]
    exact IsCompl.symm isCompl_compl

/-- If `P` is a submersive presentation of `S` as an `R`-algebra, `Ω[S⁄R]` is free. -/
@[stacks 00T7 "(2)"]
theorem free_kaehlerDifferential (P : SubmersivePresentation R S) :
    Module.Free S (Ω[S⁄R]) :=
  Module.Free.of_basis P.basisKaehler

attribute [local instance] Fintype.ofFinite in
/-- If `P` is a submersive presentation of `S` as an `R`-algebra and `S` is nontrivial,
`Ω[S⁄R]` is free of rank the dimension of `P`, i.e. the number of generators minus the number
of relations. -/
theorem rank_kaehlerDifferential [Nontrivial S]
    (P : SubmersivePresentation R S) : Module.rank S (Ω[S⁄R]) = P.dimension := by
  simp only [rank_eq_card_basis P.basisKaehler, Nat.cast_inj, Fintype.card_compl_set,
    Presentation.dimension, Nat.card_eq_fintype_card, Set.card_range_of_injective P.map_inj]

end SubmersivePresentation

/-- If `S` is `R`-standard smooth, `Ω[S⁄R]` is a free `S`-module. -/
instance IsStandardSmooth.free_kaehlerDifferential [IsStandardSmooth R S] :
    Module.Free S (Ω[S⁄R]) := by
  obtain ⟨⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.free_kaehlerDifferential

instance IsStandardSmooth.subsingleton_h1Cotangent [IsStandardSmooth R S] :
    Subsingleton (H1Cotangent R S) := by
  obtain ⟨⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.equivH1Cotangent.symm.toEquiv.subsingleton

/-- If `S` is non-trivial and `R`-standard smooth of relative dimension, `Ω[S⁄R]` is a free
`S`-module of rank `n`. -/
theorem IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential [Nontrivial S] (n : ℕ)
    [IsStandardSmoothOfRelativeDimension n R S] :
    Module.rank S (Ω[S⁄R]) = n := by
  obtain ⟨⟨P, hP⟩⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
  rw [P.rank_kaehlerDifferential, hP]

instance IsStandardSmoothOfRelationDimension.subsingleton_kaehlerDifferential
    [IsStandardSmoothOfRelativeDimension 0 R S] : Subsingleton (Ω[S⁄R]) := by
  cases subsingleton_or_nontrivial S
  · exact Module.subsingleton S _
  haveI : IsStandardSmooth R S := IsStandardSmoothOfRelativeDimension.isStandardSmooth 0
  exact Module.subsingleton_of_rank_zero
    (IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 0)

end

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

instance (priority := 900) [IsStandardSmooth R S] : Smooth R S where
  formallySmooth := by
    rw [Algebra.FormallySmooth.iff_subsingleton_and_projective]
    exact ⟨inferInstance, inferInstance⟩

/-- If `S` is `R`-standard smooth of relative dimension zero, it is étale. -/
instance (priority := 900) [IsStandardSmoothOfRelativeDimension 0 R S] : Etale R S where
  finitePresentation := (IsStandardSmoothOfRelativeDimension.isStandardSmooth 0).finitePresentation
  formallyEtale :=
    have : IsStandardSmooth R S := IsStandardSmoothOfRelativeDimension.isStandardSmooth 0
    have : FormallyUnramified R S := ⟨inferInstance⟩
    Algebra.FormallyEtale.of_unramified_and_smooth

end Algebra
