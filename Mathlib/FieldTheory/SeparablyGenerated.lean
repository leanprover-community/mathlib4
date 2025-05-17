import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Algebra.GroupWithZero.Action.Faithful
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Polynomial.GaussLemma


noncomputable section

section InOtherPR

lemma IsTranscendenceBasis.comp_equiv {ι ι' R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : ι → A} (H : IsTranscendenceBasis R x) (e : ι' ≃ ι) :
    IsTranscendenceBasis R (x ∘ e) :=
  ⟨H.1.comp _ e.injective, by simpa using H.2⟩

lemma IsTranscendenceBasis.of_comp {ι R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (x : ι → A) (f : A →ₐ[R] B) (h : Function.Injective f)
    (H : IsTranscendenceBasis R (f ∘ x)) :
    IsTranscendenceBasis R x := by
  refine ⟨(AlgHom.algebraicIndependent_iff f h).mp H.1, ?_⟩
  intro s hs hs'
  have := (algebraicIndependent_image h.injOn).mp ((AlgHom.algebraicIndependent_iff f h).mpr hs)
  have := H.2 (f '' s)
    ((algebraicIndependent_image h.injOn).mp ((AlgHom.algebraicIndependent_iff f h).mpr hs))
    (by rw [Set.range_comp]; exact Set.image_mono hs')
  rwa [Set.range_comp, (Set.image_injective.mpr h).eq_iff] at this

lemma IsTranscendenceBasis.comp {ι R A : Type*} (B : Type*) [CommRing R]
    [Nontrivial R] [CommRing A] [NoZeroDivisors A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.IsAlgebraic A B]
    [FaithfulSMul A B]
    {x : ι → A} (hx : IsTranscendenceBasis R x) : IsTranscendenceBasis R (algebraMap A B ∘ x) := by
  refine (hx.1.map (f := IsScalarTower.toAlgHom _ _ _)
    (FaithfulSMul.algebraMap_injective A B).injOn).isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  rw [Set.range_comp, ← AlgHom.map_adjoin]
  set S := Algebra.adjoin R (Set.range x)
  let e := S.equivMapOfInjective (IsScalarTower.toAlgHom R A B)
    (FaithfulSMul.algebraMap_injective A B)
  letI := e.toRingHom.toAlgebra
  haveI : IsScalarTower S (S.map (IsScalarTower.toAlgHom R A B)) B := .of_algebraMap_eq fun x ↦ rfl
  have : Algebra.IsAlgebraic S A := hx.isAlgebraic
  have : Algebra.IsAlgebraic S B := .trans _ A _
  exact .extendScalars e.injective

lemma IsTranscendenceBasis.image {ι R A : Type*} [CommRing R] [Nontrivial R] [CommRing A]
    [Algebra R A] {x : ι → A} (hx : IsTranscendenceBasis R x) :
    IsTranscendenceBasis R ((↑) : Set.range x → A) := by
  exact to_subtype_range hx

lemma Field.finInsepDegree_mul_finInsepDegree_of_finite (F E K : Type*)
    [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] [Module.Finite F K] :
    finInsepDegree F E * finInsepDegree E K = finInsepDegree F K := by
  have : Module.Finite E K := .of_restrictScalars_finite F _ _
  apply mul_right_injective₀ (NeZero.ne (finSepDegree F K))
  dsimp only
  rw [Field.finSepDegree_mul_finInsepDegree,
    ← Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F E K,
    mul_mul_mul_comm, Field.finSepDegree_mul_finInsepDegree, Field.finSepDegree_mul_finInsepDegree,
    Module.finrank_mul_finrank]

lemma Field.finInsepDegree_le_of_left_le {F K : Type*}
    [Field F] [Field K] [Algebra F K] {E₁ E₂ : IntermediateField F K} (H : E₁ ≤ E₂)
    [Module.Finite E₁ K] :
    finInsepDegree E₂ K ≤ finInsepDegree E₁ K := by
  letI inst := (IntermediateField.inclusion H).toAlgebra
  letI := inst.toModule
  have : IsScalarTower E₁ E₂ K := .of_algebraMap_eq' rfl
  have : Module.Finite E₁ E₂ := .of_injective (IsScalarTower.toAlgHom E₁ E₂ K).toLinearMap
    (algebraMap E₂ K).injective
  rw [← Field.finInsepDegree_mul_finInsepDegree_of_finite E₁ E₂ K]
  refine Nat.le_mul_of_pos_left (finInsepDegree (↥E₂) K) ?_
  exact Nat.pos_iff_ne_zero.mpr ((NeZero.ne _))

lemma IntermediateField.finrank_eq_one_iff_eq_top {R M : Type*}
    [Field R] [Field M] [Algebra R M] {N : IntermediateField R M} :
    Module.finrank N M = 1 ↔ N = ⊤ := by
  refine ⟨?_, (· ▸ IntermediateField.finrank_top)⟩
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one, ← top_le_iff, ← top_le_iff]
  intro H x _
  obtain ⟨x, rfl⟩ := @H x trivial
  exact x.2

lemma Field.finInsepDegree_eq_one_iff_isSeparable {F K : Type*}
    [Field F] [Field K] [Algebra F K] :
    Field.finInsepDegree F K = 1 ↔ Algebra.IsSeparable F K := by
  rw [← separableClosure.eq_top_iff, ← IntermediateField.finrank_eq_one_iff_eq_top, finInsepDegree]

lemma IsSeparable.map {F K L : Type*} [CommRing F] [Ring K] [Ring L] [Algebra F K] [Algebra F L]
    {x : K} (f : K →ₐ[F] L) (H : IsSeparable F x) (hf : Function.Injective f) :
    IsSeparable F (f x) := by
  rwa [IsSeparable, minpoly.algHom_eq _ hf]

lemma Algebra.finite_of_intermediateFieldFG_of_isAlgebraic
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (h : IntermediateField.FG (⊤ : IntermediateField k K)) [Algebra.IsAlgebraic k K] :
    Module.Finite k K := by
  obtain ⟨s, hs⟩ := h
  have : Algebra.FiniteType k K := by
    use s
    rw [← IntermediateField.adjoin_algebraic_toSubalgebra
      (fun x hx ↦ Algebra.IsAlgebraic.isAlgebraic x)]
    simpa [← IntermediateField.toSubalgebra_inj] using hs
  exact Algebra.IsIntegral.finite

lemma Finset.mul_sup {ι : Type*} (s : Finset ι) (f : ι → ℕ) (a : ℕ) :
    a * s.sup f = s.sup (a * f ·) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ IH => simp only [Finset.sup_insert, ← IH, Nat.mul_max_mul_left]

lemma IsTranscendenceBasis.isAlgebraic_iff {R S T : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [CommRing T] [IsDomain T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T]
    {ι : Type*} {v : ι → T} (hv : IsTranscendenceBasis R v) :
    Algebra.IsAlgebraic S T ↔ ∀ i, IsAlgebraic S (v i) := by
  have := (algebraMap R S).domain_nontrivial
  refine ⟨fun _ ↦ fun i ↦ Algebra.IsAlgebraic.isAlgebraic (v i), fun H ↦ ?_⟩
  have : Algebra.IsAlgebraic S (Algebra.adjoin S (Set.range v)) := by
    simpa [← Subalgebra.isAlgebraic_iff, Algebra.isAlgebraic_adjoin_iff]
  letI : Algebra (Algebra.adjoin R (Set.range v)) (Algebra.adjoin S (Set.range v)) :=
    (Subalgebra.inclusion (T := (Algebra.adjoin S (Set.range v)).restrictScalars R)
    (by rw [Algebra.Subalgebra.restrictScalars_adjoin]; exact le_sup_right)).toAlgebra
  have : IsScalarTower (Algebra.adjoin R (Set.range v)) (Algebra.adjoin S (Set.range v)) T :=
    .of_algebraMap_eq fun x ↦ rfl
  have := hv.isAlgebraic
  have : Algebra.IsAlgebraic (Algebra.adjoin S (Set.range v)) T :=
    .extendScalars (R := Algebra.adjoin R (Set.range v)) (Subalgebra.inclusion_injective _)
  refine .trans _ (Algebra.adjoin S (Set.range v)) _

@[simp]
lemma Finsupp.some_embDomain_some {α M : Type*} [Zero M] (f : α →₀ M) :
    (f.embDomain .some).some = f := by
  ext; rw [some_apply]; exact embDomain_apply _ _ _

@[simp]
lemma Finsupp.embDomain_some_none {α M : Type*} [Zero M] (f : α →₀ M) :
    f.embDomain .some .none = 0 :=
  embDomain_notin_range _ _ _ (by simp)

lemma MvPolynomial.natDegree_optionEquivLeft {R S₁ : Type*} [CommSemiring R]
    (p : MvPolynomial (Option S₁) R) :
    (optionEquivLeft R S₁ p).natDegree = p.degreeOf .none := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    ext σ
    trans p.coeff (σ.embDomain .some + .single .none N)
    · simpa [-optionEquivLeft_apply] using
        optionEquivLeft_coeff_coeff R S₁ (σ.embDomain .some + .single .none N) p
    simp only [coeff_zero, ← not_mem_support_iff]
    intro H
    simpa using (degreeOf_lt_iff ((zero_le _).trans_lt hN)).mp hN _ H
  · rw [degreeOf_le_iff]
    intro σ hσ
    refine Polynomial.le_natDegree_of_ne_zero fun H ↦ ?_
    have := optionEquivLeft_coeff_coeff R S₁ σ p
    rw [H, coeff_zero, eq_comm, ← not_mem_support_iff] at this
    exact this hσ

lemma MvPolynomial.totalDegree_coeff_optionEquivLeft_add_le {R S₁ : Type*} [CommSemiring R]
    (p : MvPolynomial (Option S₁) R) (i : ℕ) (hi : i ≤ p.totalDegree) :
    ((optionEquivLeft R S₁ p).coeff i).totalDegree + i ≤ p.totalDegree := by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simpa
  rw [totalDegree, add_comm, Finset.add_sup (by simpa only [support_nonempty]), Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain, add_comm i]
  · simpa [-optionEquivLeft_apply, mem_support_iff, ← optionEquivLeft_coeff_coeff R S₁] using hσ

lemma MvPolynomial.totalDegree_coeff_optionEquivLeft_le {R S₁ : Type*} [CommSemiring R]
    (p : MvPolynomial (Option S₁) R) (i : ℕ) :
    ((optionEquivLeft R S₁ p).coeff i).totalDegree ≤ p.totalDegree := by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simp
  rw [totalDegree, Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain, add_comm i]
  · simpa [-optionEquivLeft_apply, mem_support_iff, ← optionEquivLeft_coeff_coeff R S₁] using hσ

lemma MvPolynomial.totalDegree_renameEquiv {σ τ : Type*} (R : Type*) [CommSemiring R] (f : σ ≃ τ)
    (p : MvPolynomial σ R) : (renameEquiv R f p).totalDegree = p.totalDegree :=
  (totalDegree_rename_le f p).antisymm (le_trans (by simp) (totalDegree_rename_le f.symm _))

theorem MvPolynomial.isUnit_iff_of_isDomain {σ R : Type*} [CommRing R] [IsDomain R]
    {P : MvPolynomial σ R} :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → P.coeff i = 0) := by
  classical
  refine ⟨fun H ↦ ⟨H.map constantCoeff, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · intros n hn
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by simpa [Finsupp.ext_iff] using hn
    let e := (optionEquivLeft _ _).symm.trans (renameEquiv R (Equiv.optionSubtypeNe i))
    have H := (Polynomial.coeff_isUnit_isNilpotent_of_isUnit (H.map e.symm)).2 (n i) hi
    simp only [ne_eq, isNilpotent_iff_eq_zero] at H
    have : coeff _ ((e.symm P).coeff _) = _ :=
      optionEquivLeft_coeff_coeff _ _ (n.equivMapDomain (Equiv.optionSubtypeNe i).symm)
        (renameEquiv R (Equiv.optionSubtypeNe i).symm P)
    simp only [ne_eq, Finsupp.equivMapDomain_apply, Equiv.symm_symm, Equiv.optionSubtypeNe_apply,
      Option.casesOn'_none, renameEquiv_apply, H, coeff_zero] at this
    rwa [Finsupp.equivMapDomain_eq_mapDomain,
      coeff_rename_mapDomain _ (Equiv.optionSubtypeNe i).symm.injective, eq_comm] at this
  · convert h₁.map C
    ext m
    rw [coeff_C]
    split_ifs with h
    · rw [h]
    · exact h₂ _ (.symm h)

theorem MvPolynomial.isUnit_iff_totalDegree_of_isDomain {σ R : Type*} [CommRing R] [IsDomain R]
    {P : MvPolynomial σ R} :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ P.totalDegree = 0 := by
  convert isUnit_iff_of_isDomain (P := P)
  rw [totalDegree_eq_zero_iff]
  simp [not_imp_comm (a := _ = (0 : R)), Finsupp.ext_iff]

lemma monotone_prod_iff' {α β γ : Type*} [Preorder α] [Preorder β] [Preorder γ] {f : α → β × γ} :
    Monotone f ↔ Monotone (Prod.fst ∘ f) ∧ Monotone (Prod.snd ∘ f) :=
  ⟨fun h ↦ ⟨monotone_fst.comp h, monotone_snd.comp h⟩, fun ⟨h₁, h₂⟩ _ _ e ↦ ⟨h₁ e, h₂ e⟩⟩

/-- The order on `σ →₀ ℕ` defined by comparing `∑ f` first, and then the lexicographical order,
as a `MonomialOrder`. Also see `MonomialOrder.totalLex_le_def` -/
noncomputable def MonomialOrder.totalLex (σ : Type*) [LinearOrder σ] [WellFoundedGT σ] :
    MonomialOrder σ :=
  let emb : (σ →₀ ℕ) →+ Lex (ℕ × Lex ((σ →₀ ℕ))) :=
      (Finsupp.lsum (R := ℕ) ℕ (fun _ ↦ .id)).toAddMonoidHom.prod (.id _)
  { syn := AddMonoidHom.mrange emb
    toSyn :=
    { __ := emb.mrangeRestrict
      invFun s := s.1.2
      left_inv x := rfl
      right_inv | ⟨_, x, rfl⟩ => by ext; rfl }
    toSyn_monotone := by
      refine Prod.Lex.toLex_mono.comp (monotone_prod_iff'.mpr ⟨?_, Finsupp.toLex_monotone⟩)
      intro f₁ f₂ e
      dsimp [Function.comp_def]
      exact Finsupp.sum_le_sum_index e (fun _ _ ↦ monotone_id) (fun _ _ ↦ rfl) }

open scoped MonomialOrder in
lemma MonomialOrder.totalLex_le_def {σ : Type*} [LinearOrder σ] [WellFoundedGT σ] {f g : σ →₀ ℕ} :
    f ≼[totalLex σ] g ↔ ((f.sum fun _ ↦ id) ≤ g.sum fun _ ↦ id) ∧
      (((f.sum fun _ ↦ id) = g.sum fun _ ↦ id) → toLex f ≤ toLex g) := Prod.Lex.le_iff'

lemma MonomialOrder.degree_mem_support {σ R : Type*}
    [CommRing R] (m : MonomialOrder σ) {p : MvPolynomial σ R} (hp : p ≠ 0) :
    m.degree p ∈ p.support := by
  rwa [MvPolynomial.mem_support_iff, coeff_degree_ne_zero_iff]

lemma MonomialOrder.sum_degree_totalLex {σ R : Type*}
    [CommRing R] [LinearOrder σ] [WellFoundedGT σ] (p : MvPolynomial σ R) :
    (((totalLex σ).degree (R := R) p).sum fun _ ↦ id) = p.totalDegree := by
  by_cases hp : p = 0
  · simp [hp]
  apply le_antisymm
  · exact MvPolynomial.le_totalDegree ((totalLex σ).degree_mem_support hp)
  · rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    intro s hs
    exact (totalLex_le_def.mp ((totalLex σ).le_degree hs)).1

theorem MvPolynomial.totalDegree_mul_of_isDomain {σ R : Type*} [CommRing R] [IsDomain R]
    {P Q : MvPolynomial σ R} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    totalDegree (P * Q) = totalDegree P + totalDegree Q := by
  let inst : LinearOrder σ := IsWellOrder.linearOrder WellOrderingRel
  have : WellFoundedLT σ := ⟨WellOrderingRel.isWellOrder.wf⟩
  simp_rw [← MonomialOrder.sum_degree_totalLex (σ := σᵒᵈ), MonomialOrder.degree_mul hP hQ]
  simp [Finsupp.sum_add_index]

theorem Irreducible.isPrimitive
    {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    {p : Polynomial R} (hp : Irreducible p) (hp' : p.natDegree ≠ 0) :
    p.IsPrimitive := by
  rintro r ⟨q, hq⟩
  suffices ¬IsUnit q by simpa using ((hp.2 hq).resolve_right this).map Polynomial.constantCoeff
  intro H
  have hr : r ≠ 0 := by rintro rfl; simp_all
  obtain ⟨s, hs, rfl⟩ := Polynomial.isUnit_iff.mp H
  simp [hq, Polynomial.natDegree_C_mul hr] at hp'

theorem Polynomial.leadingCoeff_scaleRoots {R : Type*} [Semiring R] (p : Polynomial R) (r : R) :
    (p.scaleRoots r).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]

theorem Polynomial.mapAlgEquiv_toAlgHom {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (f : A ≃ₐ[R] B) :
    (mapAlgEquiv f : Polynomial A →ₐ[R] Polynomial B) = mapAlgHom f := rfl

lemma Polynomial.mapAlgHom_comp' {R A B C : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [Semiring C] [Algebra R C]
    (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    (mapAlgHom f).comp (mapAlgHom g) = mapAlgHom (f.comp g) := by
  apply AlgHom.ext
  intro x
  simp [AlgHom.comp_algebraMap, map_map]
  congr

end InOtherPR

namespace Algebra

universe u

section

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (p : ℕ) [ExpChar k p] (hp : p.Prime)
variable {n : ℕ} (a : Fin (n + 1) → K) (ha : IntermediateField.adjoin k (Set.range a) = ⊤)
variable (ha' : IsTranscendenceBasis k (a ∘ Fin.castSucc))
variable (H : ∀ s : Finset K,
  LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (· ^ p) (s : Set K))

attribute [local instance 2000] Polynomial.isScalarTower Algebra.toSMul IsScalarTower.right in
open MvPolynomial in
open scoped IntermediateField in
include hp ha ha' H in
/--
Suppose `k` has chararcteristic `p` and `K/k` is generated by `a₁,...,aₙ₊₁`,
where `a₁,...aₙ` forms a transcendental basis.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then some subset of `a₁,...,aₙ₊₁` forms a separable transcedental basis.
-/
@[stacks 0H71]
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top :
    ∃ i : Fin (n + 1), IsTranscendenceBasis k (a ∘ Fin.succAbove i) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (Set.range (a ∘ Fin.succAbove i))) K := by
  classical
  -- Since `a₁,...aₙ` forms a transcendental basis,
  -- there exists a non-zero polynomial relation `F(a₁,...,aₙ₊₁) = 0`.
  have HF : ∃ F : MvPolynomial (Fin (n + 1)) k, F ≠ 0 ∧ MvPolynomial.aeval a F = 0 := by
    obtain ⟨p, hp, hpa⟩ := ha'.isAlgebraic.1 (a (.last n))
    obtain ⟨p, rfl⟩ := (((MvPolynomial.renameEquiv k finSuccEquivLast).trans
      (MvPolynomial.optionEquivLeft k (Fin n))).trans
        (Polynomial.mapAlgEquiv ha'.1.aevalEquiv)).surjective p
    refine ⟨p, by simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using hp, ?_⟩
    letI : Algebra (adjoin k (Set.range (a ∘ Fin.castSucc)))
      (Polynomial (adjoin k (Set.range (a ∘ Fin.castSucc)))) := inferInstance
    have : IsScalarTower k (adjoin k (Set.range (a ∘ Fin.castSucc)))
      (Polynomial (adjoin k (Set.range (a ∘ Fin.castSucc)))) := Polynomial.isScalarTower
    rw [← hpa, ← AlgEquiv.coe_algHom, ← AlgHom.restrictScalars_apply k (Polynomial.aeval _),
      ← AlgHom.comp_apply]
    congr 1
    ext i
    obtain ⟨_ | i, rfl⟩ := finSuccEquivLast.symm.surjective i <;>
      simp [Subalgebra.algebraMap_eq]
  replace HF : ∃ m, ∃ F : MvPolynomial (Fin (n + 1)) k, F.totalDegree = m ∧ F ≠ 0 ∧
      MvPolynomial.aeval a F = 0 :=
    have ⟨F, hF, h⟩ := HF; ⟨F.totalDegree, F, rfl, hF, h⟩
  -- We choose the one with the least total degree `m`.
  let m := Nat.find HF
  obtain ⟨F, hm : _ = m, hF, h⟩ := Nat.find_spec HF
  replace H (ι : Type) (_ : Fintype ι) (v : ι → K) (hv : LinearIndependent k v) :
      LinearIndependent k (v · ^ p) := by
    have := H (Finset.univ.image v) (by simpa using hv.linearIndepOn_id)
    rwa [Finset.coe_image, Finset.coe_univ, Set.image_univ,
      linearIndepOn_range_iff hv.injective] at this
  -- By the minimality of total degree, `F` is irreducible.
  have hFirr : Irreducible F := by
    refine ⟨fun h' ↦ (h'.map (aeval a)).ne_zero h, fun q₁ q₂ e ↦ ?_⟩
    · by_contra! hq₁q₂
      wlog hq₁ : aeval a q₁ = 0 generalizing q₁ q₂
      · have e' := congr(aeval a $e)
        rw [map_mul, eq_comm, h, mul_eq_zero, or_iff_right hq₁] at e'
        exact this q₂ q₁ (e.trans (mul_comm _ _)) hq₁q₂.symm e'
      subst e
      simp only [ne_eq, mul_eq_zero, not_or] at hF
      have : m ≤ _ := Nat.find_min' HF ⟨q₁, rfl, hF.1, hq₁⟩
      rw [← hm, MvPolynomial.totalDegree_mul_of_isDomain hF.1 hF.2,
        add_le_iff_nonpos_right, nonpos_iff_eq_zero] at this
      apply hF.2
      rw [totalDegree_eq_zero_iff_eq_C.mp this]
      convert C.map_zero
      simpa [this] using isUnit_iff_totalDegree_of_isDomain.not.mp hq₁q₂.2
  -- By the minimality of total degree and the linearly independent condition,
  -- there exists some `Xᵢᵈ` with `p ∤ d` appearing in `F`.
  obtain ⟨i, hi⟩ : ∃ i, ∃ σ ∈ F.support, ¬ p ∣ σ i := by
    by_contra!
    have : ∀ σ ∈ F.support, ∃ σ', σ = p • σ' := by
      intro σ hσ
      choose σ' hσ' using (this · σ hσ)
      exact ⟨⟨σ.support, σ', by simp [hσ', hp.ne_zero]⟩, Finsupp.ext hσ'⟩
    choose! σ' hσ' using this
    have := mt (H F.support inferInstance (fun s ↦ aeval a (monomial (σ' s) (1 : k)))) (by
      convert_to ¬LinearIndependent k fun s : F.support ↦ aeval a ((monomial s) (1 : k))
      · simp_rw [← map_pow, monomial_pow, one_pow]
        congr! with ⟨s, hs⟩
        exact (hσ' s hs).symm
      · rw [not_linearIndependent_iff]
        refine ⟨.univ, (F.coeff ·), ?_, by simpa [MvPolynomial.eq_zero_iff] using hF⟩
        simp only [← map_smul, ← map_sum, Finset.univ_eq_attach, smul_eq_mul, mul_one]
        rw [F.support.sum_attach (fun i ↦ monomial i (F.coeff i)),
          support_sum_monomial_coeff, h])
    simp only [LinearIndependent, injective_iff_map_eq_zero, not_forall] at this
    obtain ⟨F', hF', hF'0⟩ := this
    let F'' : MvPolynomial (Fin (n + 1)) k := F'.mapDomain fun s ↦ σ' s.1
    have hF''0 : F'' ≠ 0 := by
      refine ne_of_ne_of_eq ((Finsupp.mapDomain_injective ?_).ne_iff.mpr hF'0) (by simp)
      rintro s t (hst : σ' s = σ' t)
      ext i
      rw [hσ' _ s.2, hσ' _ t.2, hst]
    have hF'' : aeval a F'' = 0 := by
      simp only [← hF', F'']
      clear * - F'
      induction F' using Finsupp.induction_linear with
      | zero => simp only [map_zero, Finsupp.mapDomain_zero]
      | add f g _ _ => simp only [Finsupp.mapDomain_add, map_add, *]
      | single a b =>
        simp only [Finsupp.mapDomain_single, Finsupp.linearCombination_single, ← map_smul,
          smul_eq_mul, mul_one]
        rfl
    have : m ≤ _ := Nat.find_min' HF ⟨F'', rfl, hF''0, hF''⟩
    suffices hpm : p * F''.totalDegree ≤ m by
      have hF''0' : F''.totalDegree ≠ 0 := by
        contrapose! hF''0
        rw [totalDegree_eq_zero_iff_eq_C.mp hF''0, aeval_C, map_eq_zero] at hF''
        rw [totalDegree_eq_zero_iff_eq_C.mp hF''0, hF'', map_zero]
      replace this := hpm.trans (this.trans_eq (one_mul _).symm)
      exact hp.one_lt.not_le ((mul_le_mul_iff_of_pos_right hF''0'.bot_lt).mp this)
    rw [totalDegree, Finset.mul_sup, Finset.sup_le_iff, ← hm]
    intro σ hσ
    obtain ⟨σ, hσ₂, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hσ)
    refine le_trans ?_ (Finset.le_sup σ.2)
    conv_rhs => rw [hσ' _ σ.2, Finsupp.sum_smul_index (fun _ ↦ rfl), ← Finsupp.mul_sum]
  -- Now we view `F` as a polynomial in one variable `Xᵢ`.
  let Fi := optionEquivLeft k (Fin n) (renameEquiv k (finSuccEquiv' i) F)
  let F' : Polynomial (adjoin k (Set.range (a ∘ i.succAbove))) :=
    Polynomial.mapAlgHom (aeval fun j ↦ ⟨a (i.succAbove j), subset_adjoin ⟨j, rfl⟩⟩) Fi
  have hF' : Polynomial.aeval (a i) F' = 0 := by
    simp only [← h, F', ← AlgEquiv.coe_algHom, ← AlgHom.comp_apply, Fi,
      ← AlgHom.restrictScalars_apply k (S := adjoin _ _) (Polynomial.aeval _)]
    congr 1
    ext j
    obtain ⟨_ | i, rfl⟩ := (finSuccEquiv' i).symm.surjective j <;> simp [Subalgebra.algebraMap_eq]
  -- We show that the `Xᵢᵈ` with `p ∤ d` is still present in `F` after mapping into `K`,
  -- or else there is a non-trivial algebraic relation, contradicting the minimality of `F`.
  have hF'' : ∃ d, ¬ p ∣ d ∧ F'.coeff d ≠ 0 := by
    obtain ⟨σ, hσ, hi⟩ := hi
    refine ⟨σ i, hi, fun hF'i ↦ ?_⟩
    have H : m ≤ _ := Nat.find_min' HF ⟨rename i.succAbove (Fi.coeff (σ i)), rfl, ?_, ?_⟩
    · have hi' : σ i ≠ 0 := fun H ↦ hi (H ▸ dvd_zero p)
      have : (Fi.coeff _).totalDegree + _ ≤ _ :=
        totalDegree_coeff_optionEquivLeft_add_le (renameEquiv k (finSuccEquiv' i) F) (σ i) (by
          rw [totalDegree_renameEquiv]
          refine le_trans (Finset.single_le_sum (by simp) ?_) (le_totalDegree hσ)
          simpa only [Finsupp.mem_support_iff])
      rw [totalDegree_renameEquiv, hm] at this
      have := (this.trans H).trans (totalDegree_rename_le _ _)
      simp [hi'] at this
    · rw [← map_zero (rename i.succAbove), (rename_injective _ i.succAbove_right_injective).ne_iff]
      intro H
      have : coeff _ (Fi.coeff _) = _ :=
        optionEquivLeft_coeff_coeff _ _ (σ.equivMapDomain (finSuccEquiv' i))
          (renameEquiv k (finSuccEquiv' i) F)
      rw [renameEquiv_apply, Finsupp.equivMapDomain_eq_mapDomain,
        coeff_rename_mapDomain _ (finSuccEquiv' i).injective,
        Finsupp.mapDomain_equiv_apply, finSuccEquiv'_symm_none, H, coeff_zero, eq_comm,
        ← not_mem_support_iff] at this
      exact this hσ
    · trans algebraMap _ _ (F'.coeff (σ i)); swap; · simp only [hF'i, map_zero]
      simp only [aeval_rename, Polynomial.coe_mapAlgHom, Polynomial.coeff_map,
        RingHom.coe_coe, ← aeval_algebraMap_apply, F']
      rfl
  have hFi : Fi.natDegree ≠ 0 := by
    intro e
    obtain ⟨d, hpd, hF'd⟩ := hF''
    obtain rfl : d = 0 := by
      rw [← le_zero_iff, ← e]
      exact (Polynomial.le_natDegree_of_ne_zero hF'd).trans Polynomial.natDegree_map_le
    exact hpd (dvd_zero _)
  -- This verifies that `xᵢ` is algebraic over `k(x₁,...,xᵢ₋₁, xᵢ₊₁,...,xₙ₊₁)`,
  -- which implies that the latter set is a transcendental basis.
  have : Algebra.IsAlgebraic (adjoin k (Set.range (a ∘ i.succAbove))) K := by
    refine ha'.isAlgebraic_iff.mpr fun j ↦ ?_
    by_cases hij : i = j
    · exact ⟨F', fun e ↦ by simp [e] at hF'', by simpa [hij] using hF'⟩
    refine isAlgebraic_algebraMap (R := Algebra.adjoin k _) ⟨_, Algebra.subset_adjoin ?_⟩
    rw [Set.range_comp, Fin.range_succAbove]
    exact ⟨_, Ne.symm hij, by simp⟩
  have Hi : IsTranscendenceBasis k (a ∘ i.succAbove) :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite k _
      (by rw [ha'.lift_cardinalMk_eq_trdeg])
  refine ⟨i, Hi, ?_⟩
  set k' := IntermediateField.adjoin k (Set.range (a ∘ i.succAbove))
  have hk' : k'⟮a i⟯ = ⊤ := by
    apply IntermediateField.restrictScalars_injective k
    rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top,
      ← ha, Set.range_comp, Fin.range_succAbove, ← Set.image_singleton, ← Set.image_union,
      Set.compl_union_self, Set.image_univ]
  rw [← AlgEquiv.Algebra.isSeparable_iff IntermediateField.topEquiv, ← hk',
    IntermediateField.isSeparable_adjoin_simple_iff_isSeparable]
  have hk'' : Algebra.adjoin k (Set.range (a ∘ i.succAbove)) ≤ k'.toSubalgebra :=
    IntermediateField.algebra_adjoin_le_adjoin _ _
  let F'' : Polynomial k' := F'.mapAlgHom (B := k') (Subalgebra.inclusion hk'')
  -- By gauss' lemma, `F` is still irrreducible over `k(x₁,...,xᵢ₋₁, xᵢ₊₁,...,xₙ₊₁)`.
  have hF''irr : Irreducible F'' := by
    have : Irreducible Fi :=
      (hFirr.map (renameEquiv k (finSuccEquiv' i))).map (optionEquivLeft k (Fin n))
    have inst : NormalizedGCDMonoid (MvPolynomial (Fin n) k) := Nonempty.some inferInstance
    have : Irreducible (Fi.mapAlgHom (IsScalarTower.toAlgHom k _ _)) :=
      (this.isPrimitive hFi).irreducible_iff_irreducible_map_fraction_map
        (K := FractionRing (MvPolynomial (Fin n) k)).mp this
    convert this.map (Polynomial.mapAlgEquiv Hi.1.aevalEquivField)
    simp only [F', Polynomial.mapAlgHom_comp', ← AlgEquiv.coe_algHom, AlgEquiv.toAlgHom_eq_coe,
      ← AlgHom.comp_apply, Polynomial.mapAlgEquiv_toAlgHom, F'']
    congr
    ext j : 3
    simp only [AlgHom.coe_comp, Function.comp_apply, aeval_X, IsScalarTower.toAlgHom_apply]
    show a _ = Hi.1.aevalEquivField (algebraMap _ _ _)
    rw [Hi.1.aevalEquivField_algebraMap_apply_coe, aeval_X, Function.comp_apply]
  have hF''ai : Polynomial.aeval (a i) F'' = 0 := by
    simpa only [Polynomial.coe_mapAlgHom, Polynomial.aeval_def, Polynomial.eval₂_map, F''] using hF'
  have hF''0 : F'' ≠ 0 := by
    intro e
    simp_rw [F'', ← map_zero (Polynomial.mapAlgHom (Subalgebra.inclusion hk'')),
      Polynomial.coe_mapAlgHom] at e
    rw [(Polynomial.map_injective _ (by exact Subalgebra.inclusion_injective hk'')).eq_iff] at e
    simp [e] at hF''
  -- And by the existence of `Xᵢᵈ` with `p ∤ d`, it is separable.
  by_contra Hsep
  have instExpChar : ExpChar k' p := expChar_of_injective_algebraMap (algebraMap k k').injective _
  have : CharP k' p := by
    cases instExpChar
    · cases hp.ne_one rfl
    · assumption
  obtain ⟨g, hg, e⟩ := (((minpoly k' (a i)).separable_or p (minpoly.irreducible
    (isAlgebraic_iff_isIntegral.mp ⟨F'', hF''0, hF''ai⟩))).resolve_left Hsep).2
  obtain ⟨d, hpd, hF'd⟩ := hF''
  replace e := congr(Polynomial.coeff $e d)
  rw [← minpoly.eq_of_irreducible hF''irr hF''ai, Polynomial.coeff_mul_C,
    Polynomial.coeff_expand hp.pos, if_neg hpd, eq_mul_inv_iff_mul_eq₀ (by simpa using hF''0),
    zero_mul, eq_comm] at e
  exact (Subalgebra.inclusion_injective hk'').ne_iff.mpr hF'd (by simpa [F''] using e)

lemma Fin.range_snoc {n : ℕ} {α} (f : Fin n → α) (x : α) :
    Set.range (Fin.snoc f x) = insert x (Set.range f) := by
  ext; simp [Fin.exists_fin_succ', or_comm, eq_comm]

lemma IsAlgebraic.of_surjective_algebraMap {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra R S] (H : Function.Surjective (algebraMap R S)) : Algebra.IsAlgebraic R S := by
  by_cases h : Function.Injective (algebraMap R S)
  · exact (AlgEquiv.ofBijective (Algebra.ofId R S) ⟨h, H⟩).isAlgebraic
  · exact isAlgebraic_of_not_injective h

lemma _root_.IntermediateField.restrictScalars_le_iff (K : Type*) {L E : Type*} [Field K] [Field L]
    [Field E] [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    {E₁ E₂ : IntermediateField L E} : E₁.restrictScalars K ≤ E₂.restrictScalars K ↔ E₁ ≤ E₂ := .rfl

lemma _root_.IntermediateField.FG.of_restrictScalars {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    {E' : IntermediateField L E} (H : (E'.restrictScalars K).FG) : E'.FG := by
  obtain ⟨s, hs⟩ := H
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rw [IntermediateField.adjoin_le_iff]
    exact (IntermediateField.subset_adjoin K _).trans_eq congr(($hs : Set E))
  · rw [← IntermediateField.restrictScalars_le_iff K, ← hs, IntermediateField.adjoin_le_iff]
    exact IntermediateField.subset_adjoin L _

attribute [local instance 2000] Algebra.toSMul Algebra.toModule in
open IntermediateField in
include hp H in
/--
Suppose `k` has chararcteristic `p` and `K/k` is finitely generated.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then `K/k` is finite separably generated.

TODO: show that this is an if and only if.
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
    (Hfg : IntermediateField.FG (F := k) (E := K) ⊤) :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  classical
  -- We find a transcedence basis `t` such that `[K : k(t)]ᵢ` is minimal
  have Hexists : ∃ n : ℕ, ∃ t : Finset K, IsTranscendenceBasis k ((↑) : t → K) ∧
      Field.finInsepDegree (IntermediateField.adjoin k (t : Set K)) K = n := by
    obtain ⟨s, hs⟩ := Hfg
    have : Algebra.IsAlgebraic (adjoin k (s : Set K)) K := by
      rw [← isAlgebraic_adjoin_iff_top, hs]
      refine .of_surjective_algebraMap topEquiv.surjective
    obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) (s : Set K)
    have ht' : t.Finite := s.finite_toSet.subset hts
    refine ⟨_, ht'.toFinset, (by convert ht <;> ext <;> simp), rfl⟩
  let N := Nat.find Hexists
  obtain ⟨t, ht, htN : _ = N⟩ := Nat.find_spec Hexists
  have : Module.Finite (IntermediateField.adjoin k (t : Set K)) K := by
    apply (config := { allowSynthFailures := true })
      Algebra.finite_of_intermediateFieldFG_of_isAlgebraic
    · exact .of_restrictScalars (K := k) (by rwa [restrictScalars_top])
    · convert IsTranscendenceBasis.isAlgebraic_field ht <;> simp
  refine ⟨t, ht, ?_⟩
  -- Suppose `[K : k(t)]ᵢ ≠ 1`, i.e. `K : k(t)` is not separable
  rw [Algebra.isSeparable_def]
  by_contra!
  obtain ⟨x, hx⟩ := this
  have inst : ExpChar K p := expChar_of_injective_ringHom (algebraMap k K).injective p
  let K' := IntermediateField.adjoin k (insert x ↑t : Set K)
  let tx : Fin (t.card + 1) → K' :=
    Fin.snoc (fun i ↦ ⟨(t.equivFin.symm i).1, IntermediateField.subset_adjoin _ _ (by simp)⟩)
      ⟨x, IntermediateField.subset_adjoin _ _ (by simp)⟩
  have : IntermediateField.adjoin k (t : Set K) ≤ K' :=
    IntermediateField.adjoin.mono _ _ _ (Set.subset_insert _ _)
  letI inst := (IntermediateField.inclusion this).toAlgebra
  have : IsScalarTower (IntermediateField.adjoin k (t : Set K)) K' K :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite K' K :=
    .of_restrictScalars_finite (IntermediateField.adjoin k (t : Set K)) K' K
  have : Module.Finite (IntermediateField.adjoin k (t : Set K)) K' :=
    .of_injective (IsScalarTower.toAlgHom _ K' K).toLinearMap
    (algebraMap K' K).injective
  have htx : K'.val '' Set.range tx = insert x ↑t := by
    rw [Fin.range_snoc, Set.image_insert_eq, ← Set.range_comp]
    simp only [val_mk, coe_val, Set.union_singleton, K', tx]
    congr
    show Set.range (Subtype.val ∘ t.equivFin.symm) = _
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Subtype.range_val]
    rfl
  -- By `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top`,
  -- we can find an intermediate field that is "less inseparable" and we get a contradiction.
  obtain ⟨i, hi₁, hi₂⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top
      (k := k) (K := K') p hp tx
      (by
        apply IntermediateField.map_injective (IntermediateField.val _)
        rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, fieldRange_val, htx])
      (by
        apply IsTranscendenceBasis.of_comp _ (IntermediateField.val _) Subtype.val_injective
        convert ht.comp_equiv t.equivFin.symm using 1
        ext
        simp [K', tx])
      (by
        intro s
        have := H (s.image (IntermediateField.val _))
        simp only [coe_val, Finset.coe_image] at this
        rw [← linearIndepOn_iff_image Subtype.val_injective.injOn] at this
        rw [linearIndepOn_iff_image (f := (· ^ p)) (frobenius_inj K p).injOn,
          ← Set.image_comp, ← linearIndepOn_iff_image (f := (· ^ p) ∘ Subtype.val)
            ((frobenius_inj K p).comp Subtype.val_injective).injOn] at this
        rw [← LinearMap.linearIndepOn_iff_of_injOn K'.val.toLinearMap Subtype.val_injective.injOn,
          ← LinearMap.linearIndepOn_iff_of_injOn K'.val.toLinearMap Subtype.val_injective.injOn]
        exact this)
  let K'' := IntermediateField.adjoin k
    (Finset.univ.image (algebraMap K' K ∘ tx ∘ i.succAbove) : Set K)
  have hK''K' : K'' ≤ K' := by
    apply IntermediateField.adjoin.mono
    simp only [Fin.coe_eq_castSucc, Finset.coe_image, Function.comp_apply,
      IntermediateField.algebraMap_apply, Finset.coe_univ, Set.image_univ, Set.union_singleton]
    rw [← htx]
    simp [Set.subset_def]
  letI := (IntermediateField.inclusion hK''K').toAlgebra
  have : IsScalarTower K'' K' K := .of_algebraMap_eq fun _ ↦ rfl
  let K''₂ := IntermediateField.adjoin k (Set.range (tx ∘ i.succAbove))
  let e : K''₂ ≃ₐ[k] K'' :=
    (K''₂.equivMap K'.val).trans (IntermediateField.equivOfEq
      (by simp [IntermediateField.adjoin_map, K'', K''₂, ← Set.range_comp]; rfl))
  letI inst := e.toRingHom.toAlgebra
  have : IsScalarTower K''₂ K'' K' := .of_algebraMap_eq fun _ ↦ Subtype.ext rfl
  have : Algebra.IsSeparable K'' K' := Algebra.isSeparable_tower_top_of_isSeparable K''₂ K'' K'
  have : Algebra.IsAlgebraic K''₂ K' := hi₁.isAlgebraic_field
  have : Algebra.IsAlgebraic K'' K' := .tower_top (K := K''₂) _
  have : Algebra.IsAlgebraic K' K := .of_finite _ _
  have : Algebra.IsAlgebraic K'' K := .trans _ K' _
  have : Module.Finite K'' K := by
    apply Algebra.finite_of_intermediateFieldFG_of_isAlgebraic
    exact .of_restrictScalars (K := k) (by rwa [restrictScalars_top])
  refine Nat.find_min Hexists ?_ ⟨Finset.univ.image ((algebraMap (↥K') K) ∘ tx ∘ i.succAbove),
    (by convert (hi₁.comp K).to_subtype_range <;> ext <;> simp), rfl⟩
  show _ < N
  rw [← htN]
  refine lt_of_le_of_lt (b := Field.finInsepDegree K' K) ?_ ?_
  · have : Algebra.IsSeparable K'' K' := Algebra.isSeparable_tower_top_of_isSeparable K''₂ K'' K'
    rw [← Field.finInsepDegree_mul_finInsepDegree_of_finite K'' K' K,
      Algebra.IsSeparable.finInsepDegree_eq, one_mul]
  · rw [← Field.finInsepDegree_mul_finInsepDegree_of_finite
      (IntermediateField.adjoin k (t : Set K)) K' K, Nat.lt_mul_iff_one_lt_left (NeZero.pos _)]
    by_contra! hcontra
    have := hcontra.antisymm (Nat.one_le_iff_ne_zero.mpr (NeZero.ne _))
    rw [Field.finInsepDegree_eq_one_iff_isSeparable] at this
    have := (Algebra.IsSeparable.isSeparable (IntermediateField.adjoin k
      (t : Set K)) (⟨x, IntermediateField.subset_adjoin _ _ (by simp)⟩ : K')).map
      (IsScalarTower.toAlgHom _ K' K) Subtype.val_injective
    exact hx this

lemma sum_pow_expChar {R : Type*} [CommSemiring R] (p : ℕ) [ExpChar R p]
    {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ x ∈ s, f x) ^ p = ∑ x ∈ s, f x ^ p :=
  map_sum (frobenius R p) ..

lemma exists_isTranscendenceBasis_and_isSeparable_of_perfectField
    [PerfectField k] (Hfg : (⊤ : IntermediateField k K).FG) :
    ∃ (s : Finset K),
      IsTranscendenceBasis k (Subtype.val : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  let p := ringExpChar k
  have : ExpChar K p := expChar_of_injective_ringHom (algebraMap k K).injective p
  obtain (hp|h) := expChar_is_prime_or_one k p
  · refine Algebra.exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
      p hp (fun s hs ↦ ?_) Hfg
    simp only [LinearIndepOn, Finset.coe_sort_coe, Fintype.linearIndependent_iff]
    intro g hg
    have (x : s) : ∃ (a : k), a ^ p = g x := surjective_frobenius k p (g x)
    choose a ha using this
    simp_rw [← ha, Algebra.smul_def, map_pow, ← mul_pow, ← sum_pow_expChar, ← frobenius_def,
      ← Algebra.smul_def] at hg
    have := frobenius_inj K p
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero] at this
    rw [LinearIndepOn, Fintype.linearIndependent_iff] at hs
    simp_rw [← ha, hs _ (this _ hg)]
    intro i
    simp
    exact Nat.Prime.ne_zero hp
  · have : ExpChar k 1 := ringExpChar.of_eq h
    have : CharZero k := charZero_of_expChar_one' k
    obtain ⟨s, hs⟩ := Hfg
    have : Algebra.IsAlgebraic (adjoin k (s : Set K)) K := by
      rw [← IntermediateField.isAlgebraic_adjoin_iff_top, hs]
      refine .of_surjective_algebraMap IntermediateField.topEquiv.surjective
    obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) (s : Set K)
    have hfin : t.Finite := s.finite_toSet.subset hts
    refine ⟨hfin.toFinset, ?_, ?_⟩
    · convert ht <;> ext <;> simp
    · have : Algebra.IsAlgebraic (IntermediateField.adjoin k (hfin.toFinset : Set K)) K := by
        convert ht.isAlgebraic_field <;> simp
      infer_instance

end

end Algebra
