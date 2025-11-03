/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.Algebra.Algebra.Subalgebra.IsSimpleOrder
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Adjoin.Dimension
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Adjoining Elements to Fields

This file contains many results about adjoining elements to fields.
-/

open Module Polynomial

namespace IntermediateField

section

lemma restrictScalars_le_iff (K : Type*) {L E : Type*} [Field K] [Field L]
    [Field E] [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    {E₁ E₂ : IntermediateField L E} : E₁.restrictScalars K ≤ E₂.restrictScalars K ↔ E₁ ≤ E₂ := .rfl

lemma FG.of_restrictScalars {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    {E' : IntermediateField L E} (H : (E'.restrictScalars K).FG) : E'.FG := by
  obtain ⟨s, hs⟩ := H
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rw [adjoin_le_iff]
    exact (subset_adjoin K _).trans_eq congr(($hs : Set E))
  · rw [← restrictScalars_le_iff K, ← hs, adjoin_le_iff]
    exact subset_adjoin L _

end

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {S : Set E}

theorem mem_adjoin_range_iff {ι : Type*} (i : ι → E) (x : E) :
    x ∈ adjoin F (Set.range i) ↔ ∃ r s : MvPolynomial ι F,
      x = MvPolynomial.aeval i r / MvPolynomial.aeval i s := by
  simp_rw [mem_adjoin_iff_div, Algebra.adjoin_range_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]

theorem mem_adjoin_iff (x : E) :
    x ∈ adjoin F S ↔ ∃ r s : MvPolynomial S F,
      x = MvPolynomial.aeval Subtype.val r / MvPolynomial.aeval Subtype.val s := by
  rw [← mem_adjoin_range_iff, Subtype.range_coe]

theorem mem_adjoin_simple_iff {α : E} (x : E) :
    x ∈ adjoin F {α} ↔ ∃ r s : F[X], x = aeval α r / aeval α s := by
  simp only [mem_adjoin_iff_div, Algebra.adjoin_singleton_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]

variable {F}

section Supremum

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)

instance finiteDimensional_sup [FiniteDimensional K E1] [FiniteDimensional K E2] :
    FiniteDimensional K (E1 ⊔ E2 : IntermediateField K L) := by
  let g := Algebra.TensorProduct.productMap E1.val E2.val
  suffices g.range = (E1 ⊔ E2).toSubalgebra by
    have h : FiniteDimensional K (Subalgebra.toSubmodule g.range) :=
      g.toLinearMap.finiteDimensional_range
    rwa [this] at h
  rw [Algebra.TensorProduct.productMap_range, E1.range_val, E2.range_val, sup_toSubalgebra_of_left]

/-- If `E1` and `E2` are intermediate fields, and at least one them are algebraic, then the rank of
the compositum of `E1` and `E2` is less than or equal to the product of that of `E1` and `E2`.
Note that this result is also true without algebraic assumption,
but the proof becomes very complicated. -/
theorem rank_sup_le_of_isAlgebraic
    (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2) :
    Module.rank K ↥(E1 ⊔ E2) ≤ Module.rank K E1 * Module.rank K E2 := by
  have := E1.toSubalgebra.rank_sup_le_of_free E2.toSubalgebra
  rwa [← sup_toSubalgebra_of_isAlgebraic E1 E2 halg] at this

/-- If `E1` and `E2` are intermediate fields, then the `Module.finrank` of
the compositum of `E1` and `E2` is less than or equal to the product of that of `E1` and `E2`. -/
theorem finrank_sup_le :
    finrank K ↥(E1 ⊔ E2) ≤ finrank K E1 * finrank K E2 := by
  by_cases h : FiniteDimensional K E1
  · have := E1.toSubalgebra.finrank_sup_le_of_free E2.toSubalgebra
    change _ ≤ finrank K E1 * finrank K E2 at this
    rwa [← sup_toSubalgebra_of_left] at this
  rw [FiniteDimensional, ← rank_lt_aleph0_iff, not_lt] at h
  have := LinearMap.rank_le_of_injective _ <| Submodule.inclusion_injective <|
    show Subalgebra.toSubmodule E1.toSubalgebra ≤ Subalgebra.toSubmodule (E1 ⊔ E2).toSubalgebra by
      simp
  rw [show finrank K E1 = 0 from Cardinal.toNat_apply_of_aleph0_le h,
    show finrank K ↥(E1 ⊔ E2) = 0 from Cardinal.toNat_apply_of_aleph0_le (h.trans this), zero_mul]

variable {ι : Type*} {t : ι → IntermediateField K L}

theorem coe_iSup_of_directed [Nonempty ι] (dir : Directed (· ≤ ·) t) :
    ↑(iSup t) = ⋃ i, (t i : Set L) :=
  let M : IntermediateField K L :=
    { __ := Subalgebra.copy _ _ (Subalgebra.coe_iSup_of_directed dir).symm
      inv_mem' := fun _ hx ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (t i).inv_mem hi⟩ }
  have : iSup t = M := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (t i : Set L)) i) (Set.iUnion_subset fun _ ↦ le_iSup t _)
  this.symm ▸ rfl

theorem toSubalgebra_iSup_of_directed (dir : Directed (· ≤ ·) t) :
    (iSup t).toSubalgebra = ⨆ i, (t i).toSubalgebra := by
  cases isEmpty_or_nonempty ι
  · simp_rw [iSup_of_empty, bot_toSubalgebra]
  · exact SetLike.ext' ((coe_iSup_of_directed dir).trans (Subalgebra.coe_iSup_of_directed dir).symm)

instance finiteDimensional_iSup_of_finite [h : Finite ι] [∀ i, FiniteDimensional K (t i)] :
    FiniteDimensional K (⨆ i, t i : IntermediateField K L) := by
  rw [← iSup_univ]
  induction Set.univ, Set.finite_univ (α := ι) using Set.Finite.induction_on with
  | empty =>
    rw [iSup_emptyset]
    exact (botEquiv K L).symm.toLinearEquiv.finiteDimensional
  | insert s hs =>
    rw [iSup_insert]
    exact IntermediateField.finiteDimensional_sup _ _

/-- See `finiteDimensional_iSup_of_finset'` for a stronger version,
that was the one used in mathlib3. -/
instance finiteDimensional_iSup_of_finset
    {s : Finset ι} [∀ i, FiniteDimensional K (t i)] :
    FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L) :=
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

theorem finiteDimensional_iSup_of_finset'
    {s : Finset ι} (h : ∀ i ∈ s, FiniteDimensional K (t i)) :
    FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L) :=
  have := Subtype.forall'.mp h
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

/-- A compositum of splitting fields is a splitting field -/
theorem isSplittingField_iSup {p : ι → K[X]}
    {s : Finset ι} (h0 : ∏ i ∈ s, p i ≠ 0) (h : ∀ i ∈ s, (p i).IsSplittingField K (t i)) :
    (∏ i ∈ s, p i).IsSplittingField K (⨆ i ∈ s, t i : IntermediateField K L) := by
  let F : IntermediateField K L := ⨆ i ∈ s, t i
  have hF : ∀ i ∈ s, t i ≤ F := fun i hi ↦ le_iSup_of_le i (le_iSup (fun _ ↦ t i) hi)
  simp only [isSplittingField_iff] at h ⊢
  refine
    ⟨splits_prod (algebraMap K F) fun i hi ↦
        splits_comp_of_splits (algebraMap K (t i)) (inclusion (hF i hi)).toRingHom
          (h i hi).1,
      ?_⟩
  simp only [rootSet_prod p s h0, ← Set.iSup_eq_iUnion, (@gc K _ L _ _).l_iSup₂]
  exact iSup_congr fun i ↦ iSup_congr fun hi ↦ (h i hi).2

end Supremum

section Tower

variable (E)
variable {K : Type*} [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

/-- If `K / E / F` is a field extension tower, `L` is an intermediate field of `K / F`, such that
either `E / F` or `L / F` is algebraic, then `[E(L) : E] ≤ [L : F]`. A corollary of
`Subalgebra.adjoin_rank_le` since in this case `E(L) = E[L]`. -/
theorem adjoin_rank_le_of_isAlgebraic (L : IntermediateField F K)
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L := by
  have h : (adjoin E (L.toSubalgebra : Set K)).toSubalgebra =
      Algebra.adjoin E (L.toSubalgebra : Set K) :=
    L.adjoin_toSubalgebra_of_isAlgebraic E halg
  have := L.toSubalgebra.adjoin_rank_le E
  rwa [(Subalgebra.equivOfEq _ _ h).symm.toLinearEquiv.rank_eq] at this

theorem adjoin_rank_le_of_isAlgebraic_left (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F E] :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L :=
  adjoin_rank_le_of_isAlgebraic E L (Or.inl halg)

theorem adjoin_rank_le_of_isAlgebraic_right (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F L] :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L :=
  adjoin_rank_le_of_isAlgebraic E L (Or.inr halg)

end Tower

open Set CompleteLattice

/-- Adjoining a single element is compact in the lattice of intermediate fields. -/
theorem adjoin_simple_isCompactElement (x : E) : IsCompactElement F⟮x⟯ := by
  simp_rw [isCompactElement_iff_le_of_directed_sSup_le,
    adjoin_simple_le_iff, sSup_eq_iSup', ← exists_prop]
  intro s hne hs hx
  have := hne.to_subtype
  rwa [← SetLike.mem_coe, coe_iSup_of_directed hs.directed_val, mem_iUnion, Subtype.exists] at hx

/-- Adjoining a finite subset is compact in the lattice of intermediate fields. -/
theorem adjoin_finset_isCompactElement (S : Finset E) :
    IsCompactElement (adjoin F S : IntermediateField F E) := by
  rw [← biSup_adjoin_simple]
  simp_rw [Finset.mem_coe, ← Finset.sup_eq_iSup]
  exact isCompactElement_finsetSup S fun x _ => adjoin_simple_isCompactElement x

/-- Adjoining a finite subset is compact in the lattice of intermediate fields. -/
theorem adjoin_finite_isCompactElement {S : Set E} (h : S.Finite) : IsCompactElement (adjoin F S) :=
  Finite.coe_toFinset h ▸ adjoin_finset_isCompactElement h.toFinset

/-- The lattice of intermediate fields is compactly generated. -/
instance : IsCompactlyGenerated (IntermediateField F E) :=
  ⟨fun s =>
    ⟨(fun x => F⟮x⟯) '' s,
      ⟨by rintro t ⟨x, _, rfl⟩; exact adjoin_simple_isCompactElement x,
        sSup_image.trans <| (biSup_adjoin_simple _).trans <|
          le_antisymm (adjoin_le_iff.mpr le_rfl) <| subset_adjoin F (s : Set E)⟩⟩⟩

theorem exists_finset_of_mem_iSup {ι : Type*} {f : ι → IntermediateField F E} {x : E}
    (hx : x ∈ ⨆ i, f i) : ∃ s : Finset ι, x ∈ ⨆ i ∈ s, f i := by
  have := (adjoin_simple_isCompactElement x).exists_finset_of_le_iSup (IntermediateField F E) f
  simp only [adjoin_simple_le_iff] at this
  exact this hx

theorem exists_finset_of_mem_supr' {ι : Type*} {f : ι → IntermediateField F E} {x : E}
    (hx : x ∈ ⨆ i, f i) : ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, F⟮(i.2 : E)⟯ := by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le fun i x h ↦ ?_) hx)
  exact SetLike.le_def.mp (le_iSup_of_le ⟨i, x, h⟩ (by simp)) (mem_adjoin_simple_self F x)

theorem exists_finset_of_mem_supr'' {ι : Type*} {f : ι → IntermediateField F E}
    (h : ∀ i, Algebra.IsAlgebraic F (f i)) {x : E} (hx : x ∈ ⨆ i, f i) :
    ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, adjoin F ((minpoly F (i.2 :)).rootSet E) := by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i x1 hx1 => ?_)) hx)
  refine SetLike.le_def.mp (le_iSup_of_le ⟨i, x1, hx1⟩ ?_)
    (subset_adjoin F (rootSet (minpoly F x1) E) ?_)
  · rw [IntermediateField.minpoly_eq, Subtype.coe_mk]
  · rw [mem_rootSet_of_ne, minpoly.aeval]
    exact minpoly.ne_zero (isIntegral_iff.mp (Algebra.IsIntegral.isIntegral (⟨x1, hx1⟩ : f i)))

theorem exists_finset_of_mem_adjoin {S : Set E} {x : E} (hx : x ∈ adjoin F S) :
    ∃ T : Finset E, (T : Set E) ⊆ S ∧ x ∈ adjoin F (T : Set E) := by
  simp_rw [← biSup_adjoin_simple S, ← iSup_subtype''] at hx
  obtain ⟨s, hx'⟩ := exists_finset_of_mem_iSup hx
  classical
  refine ⟨s.image Subtype.val, by simp, SetLike.le_def.mp ?_ hx'⟩
  simp_rw [Finset.coe_image, iSup_le_iff, adjoin_le_iff]
  rintro _ h _ rfl
  exact subset_adjoin F _ ⟨_, h, rfl⟩

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {α : E} {S : Set E}

section AdjoinRank

open Module Module

variable {K L : IntermediateField F E}

@[simp]
theorem rank_eq_one_iff : Module.rank F K = 1 ↔ K = ⊥ := by
  rw [← toSubalgebra_inj, ← rank_eq_rank_subalgebra, Subalgebra.rank_eq_one_iff,
    bot_toSubalgebra]

@[simp]
theorem finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥ := by
  rw [← toSubalgebra_inj, ← finrank_eq_finrank_subalgebra, Subalgebra.finrank_eq_one_iff,
    bot_toSubalgebra]

@[simp]
protected theorem rank_bot : Module.rank F (⊥ : IntermediateField F E) = 1 := by
  rw [rank_eq_one_iff]

@[simp]
protected theorem finrank_bot : finrank F (⊥ : IntermediateField F E) = 1 := by
  rw [finrank_eq_one_iff]

@[simp] theorem rank_bot' : Module.rank (⊥ : IntermediateField F E) E = Module.rank F E := by
  rw [← rank_mul_rank F (⊥ : IntermediateField F E) E, IntermediateField.rank_bot, one_mul]

@[simp] theorem finrank_bot' : finrank (⊥ : IntermediateField F E) E = finrank F E :=
  congr(Cardinal.toNat $(rank_bot'))

@[simp] protected theorem rank_top : Module.rank (⊤ : IntermediateField F E) E = 1 :=
  Subalgebra.bot_eq_top_iff_rank_eq_one.mp <| top_le_iff.mp fun x _ ↦ ⟨⟨x, trivial⟩, rfl⟩

@[simp] protected theorem finrank_top : finrank (⊤ : IntermediateField F E) E = 1 :=
  rank_eq_one_iff_finrank_eq_one.mp IntermediateField.rank_top

@[simp] theorem rank_top' : Module.rank F (⊤ : IntermediateField F E) = Module.rank F E :=
  rank_top F E

@[simp] theorem finrank_top' : finrank F (⊤ : IntermediateField F E) = finrank F E :=
  finrank_top F E

lemma finrank_eq_one_iff_eq_top {K : IntermediateField F E} :
    Module.finrank K E = 1 ↔ K = ⊤ := by
  refine ⟨?_, (· ▸ IntermediateField.finrank_top)⟩
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one, ← top_le_iff, ← top_le_iff]
  intro H x _
  obtain ⟨x, rfl⟩ := @H x IntermediateField.mem_top
  exact x.2

theorem bot_eq_top_iff_finrank_eq_one :
    (⊥ : IntermediateField F E) = ⊤ ↔ Module.finrank F E = 1 := by
  rw [← IntermediateField.finrank_bot', ← finrank_eq_one_iff_eq_top]

variable (F E) in
theorem isSimpleOrder_of_finrank_prime (hp : Nat.Prime (Module.finrank F E)) :
    IsSimpleOrder (IntermediateField F E) := by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · exact ⟨⊥, ⊤, fun h ↦ Nat.prime_one_false (bot_eq_top_iff_finrank_eq_one.mp h ▸ hp)⟩
  · intro K
    simpa [← toSubalgebra_strictMono.apply_eq_bot_iff, ← toSubalgebra_strictMono.apply_eq_top_iff]
      using (Subalgebra.isSimpleOrder_of_finrank_prime _ _ hp).eq_bot_or_eq_top K.toSubalgebra

theorem rank_adjoin_eq_one_iff : Module.rank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans rank_eq_one_iff adjoin_eq_bot_iff

theorem rank_adjoin_simple_eq_one_iff :
    Module.rank F F⟮α⟯ = 1 ↔ α ∈ (⊥ : IntermediateField F E) := by
  rw [rank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff

theorem finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans finrank_eq_one_iff adjoin_eq_bot_iff

theorem finrank_adjoin_simple_eq_one_iff :
    finrank F F⟮α⟯ = 1 ↔ α ∈ (⊥ : IntermediateField F E) := by
  rw [finrank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff

/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_rank_adjoin_eq_one (h : ∀ x : E, Module.rank F F⟮x⟯ = 1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact rank_adjoin_simple_eq_one_iff.mp (h y)

theorem bot_eq_top_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮x⟯ = 1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact finrank_adjoin_simple_eq_one_iff.mp (h y)

theorem subsingleton_of_rank_adjoin_eq_one (h : ∀ x : E, Module.rank F F⟮x⟯ = 1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_rank_adjoin_eq_one h)

theorem subsingleton_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮x⟯ = 1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_eq_one h)

/-- If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_finrank_adjoin_le_one [FiniteDimensional F E]
    (h : ∀ x : E, finrank F F⟮x⟯ ≤ 1) : (⊥ : IntermediateField F E) = ⊤ := by
  apply bot_eq_top_of_finrank_adjoin_eq_one
  exact fun x => by linarith [h x, show 0 < finrank F F⟮x⟯ from finrank_pos]

theorem subsingleton_of_finrank_adjoin_le_one [FiniteDimensional F E]
    (h : ∀ x : E, finrank F F⟮x⟯ ≤ 1) : Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_le_one h)

end AdjoinRank

end AdjoinIntermediateFieldLattice

section AdjoinIntegralElement

universe u

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {α : E}
variable {K : Type u} [Field K] [Algebra F K]

theorem minpoly_gen (α : E) :
    minpoly F (AdjoinSimple.gen F α) = minpoly F α := by
  rw [← minpoly.algebraMap_eq (algebraMap F⟮α⟯ E).injective, AdjoinSimple.algebraMap_gen]

theorem aeval_gen_minpoly (α : E) : aeval (AdjoinSimple.gen F α) (minpoly F α) = 0 := by
  ext
  convert minpoly.aeval F α
  conv in aeval α => rw [← AdjoinSimple.algebraMap_gen F α]
  exact (aeval_algebraMap_apply E (AdjoinSimple.gen F α) _).symm

/-- algebra isomorphism between `AdjoinRoot` and `F⟮α⟯` -/
@[stacks 09G1 "Algebraic case"]
noncomputable def adjoinRootEquivAdjoin (h : IsIntegral F α) :
    AdjoinRoot (minpoly F α) ≃ₐ[F] F⟮α⟯ :=
  AlgEquiv.ofBijective
    (AdjoinRoot.liftAlgHom (minpoly F α) _ (AdjoinSimple.gen F α) (aeval_gen_minpoly F α))
    (by
      set f := AdjoinRoot.lift _ _ (aeval_gen_minpoly F α :)
      haveI := Fact.mk (minpoly.irreducible h)
      constructor
      · exact RingHom.injective f
      · suffices F⟮α⟯.toSubfield ≤ RingHom.fieldRange (F⟮α⟯.toSubfield.subtype.comp f) by
          intro x
          obtain ⟨y, hy⟩ := this (Subtype.mem x)
          exact ⟨y, Subtype.ext hy⟩
        refine Subfield.closure_le.mpr (Set.union_subset (fun x hx => ?_) ?_)
        · obtain ⟨y, hy⟩ := hx
          refine ⟨y, ?_⟩
          rw [RingHom.comp_apply]
          dsimp only [coe_type_toSubfield]
          rw [AdjoinRoot.lift_of (aeval_gen_minpoly F α)]
          exact hy
        · refine Set.singleton_subset_iff.mpr ⟨AdjoinRoot.root (minpoly F α), ?_⟩
          rw [RingHom.comp_apply]
          dsimp only [coe_type_toSubfield]
          rw [AdjoinRoot.lift_root (aeval_gen_minpoly F α)]
          rfl)

theorem adjoinRootEquivAdjoin_apply_root (h : IsIntegral F α) :
    adjoinRootEquivAdjoin F h (AdjoinRoot.root (minpoly F α)) = AdjoinSimple.gen F α :=
  AdjoinRoot.lift_root (aeval_gen_minpoly F α)

@[simp]
theorem adjoinRootEquivAdjoin_symm_apply_gen (h : IsIntegral F α) :
    (adjoinRootEquivAdjoin F h).symm (AdjoinSimple.gen F α) = AdjoinRoot.root (minpoly F α) := by
  rw [AlgEquiv.symm_apply_eq, adjoinRootEquivAdjoin_apply_root]

theorem adjoin_root_eq_top (p : K[X]) [Fact (Irreducible p)] : K⟮AdjoinRoot.root p⟯ = ⊤ :=
  (eq_adjoin_of_eq_algebra_adjoin K _ ⊤ (AdjoinRoot.adjoinRoot_eq_top (f := p)).symm).symm

section PowerBasis

variable {L : Type*} [Field L] [Algebra K L]

/-- The elements `1, x, ..., x ^ (d - 1)` form a basis for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def powerBasisAux {x : L} (hx : IsIntegral K x) :
    Basis (Fin (minpoly K x).natDegree) K K⟮x⟯ :=
  (AdjoinRoot.powerBasis (minpoly.ne_zero hx)).basis
    |>.map (adjoinRootEquivAdjoin K hx).toLinearEquiv
    |>.reindex (finCongr rfl)

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
@[simps]
noncomputable def adjoin.powerBasis {x : L} (hx : IsIntegral K x) : PowerBasis K K⟮x⟯ where
  gen := AdjoinSimple.gen K x
  dim := (minpoly K x).natDegree
  basis := powerBasisAux hx
  basis_eq_pow i := by
    rw [powerBasisAux, Basis.reindex_apply, Basis.map_apply, PowerBasis.basis_eq_pow,
      finCongr_symm, finCongr_apply, Fin.cast_eq_self, AlgEquiv.toLinearEquiv_apply,
      map_pow, AdjoinRoot.powerBasis_gen, adjoinRootEquivAdjoin_apply_root]

theorem adjoin.finiteDimensional {x : L} (hx : IsIntegral K x) : FiniteDimensional K K⟮x⟯ :=
  (adjoin.powerBasis hx).finite

theorem isAlgebraic_adjoin_simple {x : L} (hx : IsIntegral K x) : Algebra.IsAlgebraic K K⟮x⟯ :=
  have := adjoin.finiteDimensional hx; Algebra.IsAlgebraic.of_finite K K⟮x⟯

/-- If `x` is an algebraic element of field `K`, then its minimal polynomial has degree
`[K(x) : K]`. -/
@[stacks 09GN]
theorem adjoin.finrank {x : L} (hx : IsIntegral K x) :
    Module.finrank K K⟮x⟯ = (minpoly K x).natDegree := by
  rw [PowerBasis.finrank (adjoin.powerBasis hx :)]
  rfl

/-- If `K / E / F` is a field extension tower, `S ⊂ K` is such that `F(S) = K`,
then `E(S) = K`. -/
theorem adjoin_eq_top_of_adjoin_eq_top [Algebra E K] [IsScalarTower F E K]
    {S : Set K} (hprim : adjoin F S = ⊤) : adjoin E S = ⊤ :=
  restrictScalars_injective F <| by
    rw [restrictScalars_top, ← top_le_iff, ← hprim, adjoin_le_iff,
      coe_restrictScalars, ← adjoin_le_iff]

/-- If `E / F` is a finite extension such that `E = F(α)`, then for any intermediate field `K`, the
`F` adjoin the coefficients of `minpoly K α` is equal to `K` itself. -/
theorem adjoin_minpoly_coeff_of_exists_primitive_element
    [FiniteDimensional F E] (hprim : adjoin F {α} = ⊤) (K : IntermediateField F E) :
    adjoin F ((minpoly K α).map (algebraMap K E)).coeffs = K := by
  set g := (minpoly K α).map (algebraMap K E)
  set K' : IntermediateField F E := adjoin F g.coeffs
  have hsub : K' ≤ K := by
    refine adjoin_le_iff.mpr fun x ↦ ?_
    rw [Finset.mem_coe, mem_coeffs_iff]
    rintro ⟨n, -, rfl⟩
    rw [coeff_map]
    apply Subtype.mem
  have dvd_g : minpoly K' α ∣ g.toSubring K'.toSubring (subset_adjoin F _) := by
    apply minpoly.dvd
    rw [aeval_def, eval₂_eq_eval_map]
    erw [g.map_toSubring K'.toSubring]
    rw [eval_map, ← aeval_def]
    exact minpoly.aeval K α
  have finrank_eq : ∀ K : IntermediateField F E, finrank K E = natDegree (minpoly K α) := by
    intro K
    have := adjoin.finrank (.of_finite K α)
    rw [adjoin_eq_top_of_adjoin_eq_top F hprim] at this
    simp_all
  refine eq_of_le_of_finrank_le' hsub ?_
  simp_rw [finrank_eq]
  convert natDegree_le_of_dvd dvd_g
    ((g.monic_toSubring _ _).mpr <| (minpoly.monic <| .of_finite K α).map _).ne_zero using 1
  rw [natDegree_toSubring, natDegree_map]

instance : Module.Finite F (⊥ : IntermediateField F E) := Subalgebra.finite_bot

variable {F} in
/-- If `E / F` is an infinite algebraic extension, then there exists an intermediate field
`L / F` with arbitrarily large finite extension degree. -/
theorem exists_lt_finrank_of_infinite_dimensional
    [Algebra.IsAlgebraic F E] (hnfd : ¬ FiniteDimensional F E) (n : ℕ) :
    ∃ L : IntermediateField F E, FiniteDimensional F L ∧ n < finrank F L := by
  induction n with
  | zero => exact ⟨⊥, Subalgebra.finite_bot, finrank_pos⟩
  | succ n ih =>
    obtain ⟨L, fin, hn⟩ := ih
    obtain ⟨x, hx⟩ : ∃ x : E, x ∉ L := by
      contrapose! hnfd
      rw [show L = ⊤ from eq_top_iff.2 fun x _ ↦ hnfd x] at fin
      exact topEquiv.toLinearEquiv.finiteDimensional
    let L' := L ⊔ F⟮x⟯
    haveI := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
    refine ⟨L', inferInstance, by_contra fun h ↦ ?_⟩
    have h1 : L = L' := eq_of_le_of_finrank_le le_sup_left ((not_lt.1 h).trans hn)
    have h2 : F⟮x⟯ ≤ L' := le_sup_right
    exact hx <| (h1.symm ▸ h2) <| mem_adjoin_simple_self F x

theorem _root_.minpoly.natDegree_le (x : L) [FiniteDimensional K L] :
    (minpoly K x).natDegree ≤ finrank K L :=
  le_of_eq_of_le (IntermediateField.adjoin.finrank (.of_finite _ _)).symm
    K⟮x⟯.toSubmodule.finrank_le

theorem _root_.minpoly.degree_le (x : L) [FiniteDimensional K L] :
    (minpoly K x).degree ≤ finrank K L :=
  degree_le_of_natDegree_le (minpoly.natDegree_le x)

/-- If `x : L` is an integral element in a field extension `L` over `K`, then the degree of the
  minimal polynomial of `x` over `K` divides `[L : K]`. -/
theorem _root_.minpoly.degree_dvd {x : L} (hx : IsIntegral K x) :
    (minpoly K x).natDegree ∣ finrank K L := by
  rw [dvd_iff_exists_eq_mul_left, ← IntermediateField.adjoin.finrank hx]
  use finrank K⟮x⟯ L
  rw [mul_comm, finrank_mul_finrank]

-- TODO: generalize to `Sort`
/-- A compositum of algebraic extensions is algebraic -/
theorem isAlgebraic_iSup {ι : Type*} {t : ι → IntermediateField K L}
    (h : ∀ i, Algebra.IsAlgebraic K (t i)) :
    Algebra.IsAlgebraic K (⨆ i, t i : IntermediateField K L) := by
  constructor
  rintro ⟨x, hx⟩
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr' hx
  rw [isAlgebraic_iff, Subtype.coe_mk, ← Subtype.coe_mk (p := (· ∈ _)) x hx, ← isAlgebraic_iff]
  haveI : ∀ i : Σ i, t i, FiniteDimensional K K⟮(i.2 : L)⟯ := fun ⟨i, x⟩ ↦
    adjoin.finiteDimensional (isIntegral_iff.1 (Algebra.IsIntegral.isIntegral x))
  apply IsAlgebraic.of_finite

theorem isAlgebraic_adjoin {S : Set L} (hS : ∀ x ∈ S, IsIntegral K x) :
    Algebra.IsAlgebraic K (adjoin K S) := by
  rw [← biSup_adjoin_simple, ← iSup_subtype'']
  exact isAlgebraic_iSup fun x ↦ isAlgebraic_adjoin_simple (hS x x.2)

/-- If `L / K` is a field extension, `S` is a finite subset of `L`, such that every element of `S`
is integral (= algebraic) over `K`, then `K(S) / K` is a finite extension.
A direct corollary of `finiteDimensional_iSup_of_finite`. -/
theorem finiteDimensional_adjoin {S : Set L} [Finite S] (hS : ∀ x ∈ S, IsIntegral K x) :
    FiniteDimensional K (adjoin K S) := by
  rw [← biSup_adjoin_simple, ← iSup_subtype'']
  haveI (x : S) := adjoin.finiteDimensional (hS x.1 x.2)
  exact finiteDimensional_iSup_of_finite

end PowerBasis

/-- Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minpoly α` in `K`. -/
noncomputable def algHomAdjoinIntegralEquiv (h : IsIntegral F α) :
    (F⟮α⟯ →ₐ[F] K) ≃ { x // x ∈ (minpoly F α).aroots K } :=
  (adjoin.powerBasis h).liftEquiv'.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [adjoin.powerBasis_gen, minpoly_gen, Equiv.refl_apply])

lemma algHomAdjoinIntegralEquiv_symm_apply_gen (h : IsIntegral F α)
    (x : { x // x ∈ (minpoly F α).aroots K }) :
    (algHomAdjoinIntegralEquiv F h).symm x (AdjoinSimple.gen F α) = x :=
  (adjoin.powerBasis h).lift_gen x.val <| by
    rw [adjoin.powerBasis_gen, minpoly_gen]; exact (mem_aroots.mp x.2).2

/-- Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/
noncomputable def fintypeOfAlgHomAdjoinIntegral (h : IsIntegral F α) : Fintype (F⟮α⟯ →ₐ[F] K) :=
  PowerBasis.AlgHom.fintype (adjoin.powerBasis h)

theorem card_algHom_adjoin_integral (h : IsIntegral F α) (h_sep : IsSeparable F α)
    (h_splits : (minpoly F α).Splits (algebraMap F K)) :
    Nat.card (F⟮α⟯ →ₐ[F] K) = (minpoly F α).natDegree := by
  let _ : Fintype (F⟮α⟯ →ₐ[F] K) := fintypeOfAlgHomAdjoinIntegral F h
  rw [Nat.card_eq_fintype_card, AlgHom.card_of_powerBasis] <;>
    simp only [IsSeparable, adjoin.powerBasis_dim, adjoin.powerBasis_gen, minpoly_gen, h_splits]
  exact h_sep

-- Apparently `K⟮root f⟯ →+* K⟮root f⟯` is expensive to unify during instance synthesis.
open Module AdjoinRoot in
/-- Let `f, g` be monic polynomials over `K`. If `f` is irreducible, and `g(x) - α` is irreducible
in `K⟮α⟯` with `α` a root of `f`, then `f(g(x))` is irreducible. -/
theorem _root_.Polynomial.irreducible_comp {f g : K[X]} (hfm : f.Monic) (hgm : g.Monic)
    (hf : Irreducible f)
    (hg : ∀ (E : Type u) [Field E] [Algebra K E] (x : E) (_ : minpoly K x = f),
      Irreducible (g.map (algebraMap _ _) - C (AdjoinSimple.gen K x))) :
    Irreducible (f.comp g) := by
  have hf' : natDegree f ≠ 0 :=
    fun e ↦ not_irreducible_C (f.coeff 0) (eq_C_of_natDegree_eq_zero e ▸ hf)
  have hg' : natDegree g ≠ 0 := by
    have := Fact.mk hf
    intro e
    apply not_irreducible_C ((g.map (algebraMap _ _)).coeff 0 - AdjoinSimple.gen K (root f))
    -- Needed to specialize `map_sub` to avoid a timeout https://github.com/leanprover-community/mathlib4/pull/8386
    rw [RingHom.map_sub, coeff_map, ← map_C, ← eq_C_of_natDegree_eq_zero e]
    apply hg (AdjoinRoot f)
    rw [AdjoinRoot.minpoly_root hf.ne_zero, hfm, inv_one, map_one, mul_one]
  have H₁ : f.comp g ≠ 0 := fun h ↦ by simpa [hf', hg', natDegree_comp] using congr_arg natDegree h
  have H₂ : ¬ IsUnit (f.comp g) := fun h ↦
    by simpa [hf', hg', natDegree_comp] using natDegree_eq_zero_of_isUnit h
  have ⟨p, hp₁, hp₂⟩ := WfDvdMonoid.exists_irreducible_factor H₂ H₁
  suffices natDegree p = natDegree f * natDegree g from (associated_of_dvd_of_natDegree_le hp₂ H₁
    (this.trans natDegree_comp.symm).ge).irreducible hp₁
  have := Fact.mk hp₁
  let Kx := AdjoinRoot p
  letI := (AdjoinRoot.powerBasis hp₁.ne_zero).finite
  have key₁ : f = minpoly K (aeval (root p) g) := by
    refine minpoly.eq_of_irreducible_of_monic hf ?_ hfm
    rw [← aeval_comp]
    exact aeval_eq_zero_of_dvd_aeval_eq_zero hp₂ (AdjoinRoot.eval₂_root p)
  have key₁' : finrank K K⟮aeval (root p) g⟯ = natDegree f := by
    rw [adjoin.finrank, ← key₁]
    exact IsIntegral.of_finite _ _
  have key₂ : g.map (algebraMap _ _) - C (AdjoinSimple.gen K (aeval (root p) g)) =
      minpoly K⟮aeval (root p) g⟯ (root p) :=
    minpoly.eq_of_irreducible_of_monic (hg _ _ key₁.symm) (by simp [AdjoinSimple.gen])
      (Monic.sub_of_left (hgm.map _) (degree_lt_degree (by simpa [Nat.pos_iff_ne_zero] using hg')))
  have key₂' : finrank K⟮aeval (root p) g⟯ Kx = natDegree g := by
    trans natDegree (minpoly K⟮aeval (root p) g⟯ (root p))
    · have : K⟮aeval (root p) g⟯⟮root p⟯ = ⊤ := by
        apply restrictScalars_injective K
        rw [restrictScalars_top, adjoin_adjoin_left, Set.union_comm, ← adjoin_adjoin_left,
          adjoin_root_eq_top p, restrictScalars_adjoin]
        simp
      rw [← finrank_top', ← this, adjoin.finrank]
      exact IsIntegral.of_finite _ _
    · simp [← key₂]
  have := Module.finrank_mul_finrank K K⟮aeval (root p) g⟯ Kx
  rwa [key₁', key₂', (AdjoinRoot.powerBasis hp₁.ne_zero).finrank, powerBasis_dim, eq_comm] at this

end AdjoinIntegralElement

end IntermediateField

namespace minpoly
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open AlgEquiv IntermediateField

/-- If `y : L` is a root of `minpoly K x`, then `minpoly K y = minpoly K x`. -/
theorem eq_of_root {x y : L} (hx : IsAlgebraic K x)
    (h_ev : Polynomial.aeval y (minpoly K x) = 0) : minpoly K y = minpoly K x :=
  ((eq_iff_aeval_minpoly_eq_zero hx.isIntegral).mpr h_ev).symm

/-- The canonical `algEquiv` between `K⟮x⟯`and `K⟮y⟯`, sending `x` to `y`, where `x` and `y` have
  the same minimal polynomial over `K`. -/
noncomputable def algEquiv {x y : L} (hx : IsAlgebraic K x)
    (h_mp : minpoly K x = minpoly K y) : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
  exact AlgEquiv.trans (adjoinRootEquivAdjoin K hx.isIntegral).symm
    (AlgEquiv.trans (AdjoinRoot.algEquivOfEq _ _ h_mp)
      (adjoinRootEquivAdjoin K hy.isIntegral))

/-- `minpoly.algEquiv` sends the generator of `K⟮x⟯` to the generator of `K⟮y⟯`. -/
theorem algEquiv_apply {x y : L} (hx : IsAlgebraic K x) (h_mp : minpoly K x = minpoly K y) :
    algEquiv hx h_mp (AdjoinSimple.gen K x) = AdjoinSimple.gen K y := by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
  rw [algEquiv, trans_apply, ← adjoinRootEquivAdjoin_apply_root K hx.isIntegral,
    symm_apply_apply, trans_apply, AdjoinRoot.algEquivOfEq_root,
    adjoinRootEquivAdjoin_apply_root K hy.isIntegral]

end minpoly

namespace PowerBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open IntermediateField

/-- `pb.equivAdjoinSimple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/
noncomputable def equivAdjoinSimple (pb : PowerBasis K L) : K⟮pb.gen⟯ ≃ₐ[K] L :=
  (adjoin.powerBasis pb.isIntegral_gen).equivOfMinpoly pb <| by
    rw [adjoin.powerBasis_gen, minpoly_gen]

@[simp]
theorem equivAdjoinSimple_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple (aeval (AdjoinSimple.gen K pb.gen) f) = aeval pb.gen f :=
  equivOfMinpoly_aeval _ pb _ f

@[simp]
theorem equivAdjoinSimple_gen (pb : PowerBasis K L) :
    pb.equivAdjoinSimple (AdjoinSimple.gen K pb.gen) = pb.gen :=
  equivOfMinpoly_gen _ pb _

@[simp]
theorem equivAdjoinSimple_symm_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple.symm (aeval pb.gen f) = aeval (AdjoinSimple.gen K pb.gen) f := by
  rw [equivAdjoinSimple, equivOfMinpoly_symm, equivOfMinpoly_aeval, adjoin.powerBasis_gen]

@[simp]
theorem equivAdjoinSimple_symm_gen (pb : PowerBasis K L) :
    pb.equivAdjoinSimple.symm pb.gen = AdjoinSimple.gen K pb.gen := by
  rw [equivAdjoinSimple, equivOfMinpoly_symm, equivOfMinpoly_gen, adjoin.powerBasis_gen]

end PowerBasis

namespace IntermediateField

universe u v

open Cardinal

variable (F : Type u) [Field F]

theorem lift_cardinalMk_adjoin_le {E : Type v} [Field E] [Algebra F E] (s : Set E) :
    Cardinal.lift.{u} #(adjoin F s) ≤ Cardinal.lift.{v} #F ⊔ Cardinal.lift.{u} #s ⊔ ℵ₀ := by
  rw [show ↥(adjoin F s) = (adjoin F s).toSubfield from rfl, adjoin_toSubfield]
  apply (Cardinal.lift_le.mpr (Subfield.cardinalMk_closure_le_max _)).trans
  rw [lift_max, sup_le_iff, lift_aleph0]
  refine ⟨(Cardinal.lift_le.mpr ((mk_union_le _ _).trans <| add_le_max _ _)).trans ?_, le_sup_right⟩
  simp_rw [lift_max, lift_aleph0]
  grw [mk_range_le_lift]

theorem cardinalMk_adjoin_le {E : Type u} [Field E] [Algebra F E] (s : Set E) :
    #(adjoin F s) ≤ #F ⊔ #s ⊔ ℵ₀ := by
  simpa using lift_cardinalMk_adjoin_le F s

section AdjoinPair

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {x y : L}

theorem isAlgebraic_adjoin_pair (hx : IsIntegral K x) (hy : IsIntegral K y) :
    Algebra.IsAlgebraic K K⟮x, y⟯ := by
  apply IntermediateField.isAlgebraic_adjoin
  simp [hx, hy]

theorem finiteDimensional_adjoin_pair (hx : IsIntegral K x) (hy : IsIntegral K y) :
    FiniteDimensional K K⟮x, y⟯ := by
  have := adjoin.finiteDimensional hx
  have := adjoin.finiteDimensional hy
  rw [← Set.singleton_union, adjoin_union]
  exact finiteDimensional_sup K⟮x⟯ K⟮y⟯

variable (K x y)

theorem mem_adjoin_pair_left : x ∈ K⟮x, y⟯ := subset_adjoin K {x, y} (Set.mem_insert x {y})

theorem mem_adjoin_pair_right : y ∈ K⟮x, y⟯ :=
  subset_adjoin K {x, y} (Set.mem_insert_of_mem x (Set.mem_singleton y))

/-- The first generator of an intermediate field of the form `K⟮x, y⟯`. -/
def AdjoinPair.gen₁ : K⟮x, y⟯ := ⟨x, mem_adjoin_pair_left K x y⟩

/-- The second generator of an intermediate field of the form `K⟮x, y⟯`. -/
def AdjoinPair.gen₂ : K⟮x, y⟯ := ⟨y, mem_adjoin_pair_right K x y⟩

theorem AdjoinPair.algebraMap_gen₁ : (algebraMap (↥K⟮x, y⟯) L) (gen₁ K x y) = x := rfl

theorem AdjoinPair.algebraMap_gen₂ : (algebraMap (↥K⟮x, y⟯) L) (gen₂ K x y) = y := rfl

end AdjoinPair

end IntermediateField
