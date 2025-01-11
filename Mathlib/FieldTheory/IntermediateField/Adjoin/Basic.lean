/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Adjoin.Dimension
import Mathlib.RingTheory.Finiteness.TensorProduct
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.SetTheory.Cardinal.Subfield
import Mathlib.LinearAlgebra.Dual

/-!
# Adjoining Elements to Fields

This file contains many results about adjoining elements to fields.
-/

open Module Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {S : Set E}

theorem mem_adjoin_range_iff {ι : Type*} (i : ι → E) (x : E) :
    x ∈ adjoin F (Set.range i) ↔ ∃ r s : MvPolynomial ι F,
      x = MvPolynomial.aeval i r / MvPolynomial.aeval i s := by
  simp_rw [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring,
    Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range, exists_exists_eq_and]
  tauto

theorem mem_adjoin_iff (x : E) :
    x ∈ adjoin F S ↔ ∃ r s : MvPolynomial S F,
      x = MvPolynomial.aeval Subtype.val r / MvPolynomial.aeval Subtype.val s := by
  rw [← mem_adjoin_range_iff, Subtype.range_coe]

theorem mem_adjoin_simple_iff {α : E} (x : E) :
    x ∈ adjoin F {α} ↔ ∃ r s : F[X], x = aeval α r / aeval α s := by
  simp only [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring,
    Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range, exists_exists_eq_and]
  tauto

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
  let P : Set ι → Prop := fun s => FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L)
  change P Set.univ
  apply Set.Finite.induction_on
  all_goals dsimp only [P]
  · exact Set.finite_univ
  · rw [iSup_emptyset]
    exact (botEquiv K L).symm.toLinearEquiv.finiteDimensional
  · intro _ s _ _ hs
    rw [iSup_insert]
    exact IntermediateField.finiteDimensional_sup _ _

instance finiteDimensional_iSup_of_finset
    /- Porting note: changed `h` from `∀ i ∈ s, FiniteDimensional K (t i)` because this caused an
      error. See `finiteDimensional_iSup_of_finset'` for a stronger version, that was the one
      used in mathlib3. -/
    {s : Finset ι} [∀ i, FiniteDimensional K (t i)] :
    FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L) :=
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

theorem finiteDimensional_iSup_of_finset'
    /- Porting note: this was the mathlib3 version. Using `[h : ...]`, as in mathlib3, causes the
    error "invalid parametric local instance". -/
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

-- Porting note: original proof times out.
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
-- Porting note: writing `fun i x h => ...` does not work.
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le fun i ↦ ?_) hx)
  exact fun x h ↦ SetLike.le_def.mp (le_iSup_of_le ⟨i, x, h⟩ (by simp)) (mem_adjoin_simple_self F x)

theorem exists_finset_of_mem_supr'' {ι : Type*} {f : ι → IntermediateField F E}
    (h : ∀ i, Algebra.IsAlgebraic F (f i)) {x : E} (hx : x ∈ ⨆ i, f i) :
    ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, adjoin F ((minpoly F (i.2 :)).rootSet E) := by
-- Porting note: writing `fun i x1 hx1 => ...` does not work.
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i => ?_)) hx)
  intro x1 hx1
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

-- Porting note: original proof used `Exists.cases_on`.
/-- algebra isomorphism between `AdjoinRoot` and `F⟮α⟯` -/
@[stacks 09G1 "Algebraic case"]
noncomputable def adjoinRootEquivAdjoin (h : IsIntegral F α) :
    AdjoinRoot (minpoly F α) ≃ₐ[F] F⟮α⟯ :=
  AlgEquiv.ofBijective
    (AdjoinRoot.liftHom (minpoly F α) (AdjoinSimple.gen F α) (aeval_gen_minpoly F α))
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
          -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
          erw [RingHom.comp_apply, AdjoinRoot.lift_of (aeval_gen_minpoly F α)]
          exact hy
        · refine Set.singleton_subset_iff.mpr ⟨AdjoinRoot.root (minpoly F α), ?_⟩
          -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
          erw [RingHom.comp_apply, AdjoinRoot.lift_root (aeval_gen_minpoly F α)]
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
  (AdjoinRoot.powerBasis (minpoly.ne_zero hx)).basis.map (adjoinRootEquivAdjoin K hx).toLinearEquiv

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
@[simps]
noncomputable def adjoin.powerBasis {x : L} (hx : IsIntegral K x) : PowerBasis K K⟮x⟯ where
  gen := AdjoinSimple.gen K x
  dim := (minpoly K x).natDegree
  basis := powerBasisAux hx
  basis_eq_pow i := by
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [powerBasisAux, Basis.map_apply, PowerBasis.basis_eq_pow, AlgEquiv.toLinearEquiv_apply,
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
    erw [aeval_def, eval₂_eq_eval_map, g.map_toSubring K'.toSubring, eval_map, ← aeval_def]
    exact minpoly.aeval K α
  have finrank_eq : ∀ K : IntermediateField F E, finrank K E = natDegree (minpoly K α) := by
    intro K
    have := adjoin.finrank (.of_finite K α)
    erw [adjoin_eq_top_of_adjoin_eq_top F hprim, finrank_top K E] at this
    exact this
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
  induction' n with n ih
  · exact ⟨⊥, Subalgebra.finite_bot, finrank_pos⟩
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
  minimal polynomial of `x` over `K` divides `[L : K]`.-/
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
    @Fintype.card (F⟮α⟯ →ₐ[F] K) (fintypeOfAlgHomAdjoinIntegral F h) = (minpoly F α).natDegree := by
  rw [AlgHom.card_of_powerBasis] <;>
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

section Minpoly

open AlgEquiv

variable {K L : Type _} [Field K] [Field L] [Algebra K L]
namespace AdjoinRoot

/-- The canonical algebraic homomorphism from `AdjoinRoot p` to `AdjoinRoot q`, where
  the polynomial `q : K[X]` divides `p`. -/
noncomputable def algHomOfDvd {p q : K[X]} (hpq : q ∣ p) :
    AdjoinRoot p →ₐ[K] AdjoinRoot q :=
  (liftHom p (root q) (by simp only [aeval_eq, mk_eq_zero, hpq]))

theorem coe_algHomOfDvd {p q : K[X]} (hpq : q ∣ p) :
    (algHomOfDvd hpq).toFun = liftHom p (root q) (by simp only [aeval_eq, mk_eq_zero, hpq]) :=
  rfl

/-- `algHomOfDvd` sends `AdjoinRoot.root p` to `AdjoinRoot.root q`. -/
theorem algHomOfDvd_apply_root {p q : K[X]} (hpq : q ∣ p) :
    algHomOfDvd hpq (root p) = root q := by
  rw [algHomOfDvd, liftHom_root]

/-- The canonical algebraic equivalence between `AdjoinRoot p` and `AdjoinRoot q`, where
  the two polynomials `p q : K[X]` are equal. -/
noncomputable def algEquivOfEq {p q : K[X]} (hp : p ≠ 0) (h_eq : p = q) :
    AdjoinRoot p ≃ₐ[K] AdjoinRoot q :=
  ofAlgHom (algHomOfDvd (dvd_of_eq h_eq.symm)) (algHomOfDvd (dvd_of_eq h_eq))
    (PowerBasis.algHom_ext (powerBasis (h_eq ▸ hp))
      (by rw [algHomOfDvd, powerBasis_gen (h_eq ▸ hp), AlgHom.coe_comp, Function.comp_apply,
        algHomOfDvd, liftHom_root, liftHom_root, AlgHom.coe_id, id_eq]))
    (PowerBasis.algHom_ext (powerBasis hp)
      (by rw [algHomOfDvd, powerBasis_gen hp, AlgHom.coe_comp, Function.comp_apply, algHomOfDvd,
          liftHom_root, liftHom_root, AlgHom.coe_id, id_eq]))

theorem coe_algEquivOfEq {p q : K[X]} (hp : p ≠ 0) (h_eq : p = q) :
    (algEquivOfEq hp h_eq).toFun = liftHom p (root q) (by rw [h_eq, aeval_eq, mk_self]) :=
  rfl

theorem algEquivOfEq_toAlgHom {p q : K[X]} (hp : p ≠ 0) (h_eq : p = q) :
    (algEquivOfEq hp h_eq).toAlgHom = liftHom p (root q) (by rw [h_eq, aeval_eq, mk_self]) :=
  rfl

/-- `algEquivOfEq` sends `AdjoinRoot.root p` to `AdjoinRoot.root q`. -/
theorem algEquivOfEq_apply_root {p q : K[X]} (hp : p ≠ 0) (h_eq : p = q) :
    algEquivOfEq hp h_eq (root p) = root q := by
  rw [← coe_algHom, algEquivOfEq_toAlgHom, liftHom_root]

/-- The canonical algebraic equivalence between `AdjoinRoot p` and `AdjoinRoot q`,
where the two polynomials `p q : K[X]` are associated.-/
noncomputable def algEquivOfAssociated {p q : K[X]} (hp : p ≠ 0) (hpq : Associated p q) :
    AdjoinRoot p ≃ₐ[K] AdjoinRoot q :=
  ofAlgHom (liftHom p (root q) (by simp only [aeval_eq, mk_eq_zero, hpq.symm.dvd] ))
    (liftHom q (root p) (by simp only [aeval_eq, mk_eq_zero, hpq.dvd]))
    ( PowerBasis.algHom_ext (powerBasis (hpq.ne_zero_iff.mp hp))
        (by rw [powerBasis_gen (hpq.ne_zero_iff.mp hp), AlgHom.coe_comp, Function.comp_apply,
          liftHom_root, liftHom_root, AlgHom.coe_id, id_eq]))
    (PowerBasis.algHom_ext (powerBasis hp)
      (by rw [powerBasis_gen hp, AlgHom.coe_comp, Function.comp_apply, liftHom_root, liftHom_root,
          AlgHom.coe_id, id_eq]))

theorem coe_algEquivOfAssociated {p q : K[X]} (hp : p ≠ 0) (hpq : Associated p q) :
    (algEquivOfAssociated hp hpq).toFun =
      liftHom p (root q) (by simp only [aeval_eq, mk_eq_zero, hpq.symm.dvd]) :=
  rfl

theorem algEquivOfAssociated_toAlgHom {p q : K[X]} (hp : p ≠ 0) (hpq : Associated p q) :
    (algEquivOfAssociated hp hpq).toAlgHom =
      liftHom p (root q) (by simp only [aeval_eq, mk_eq_zero, hpq.symm.dvd]) :=
  rfl

/-- `algEquivOfAssociated` sends `AdjoinRoot.root p` to `AdjoinRoot.root q`. -/
theorem algEquivOfAssociated_apply_root {p q : K[X]} (hp : p ≠ 0) (hpq : Associated p q) :
    algEquivOfAssociated hp hpq (root p) = root q := by
  rw [← coe_algHom, algEquivOfAssociated_toAlgHom, liftHom_root]

end AdjoinRoot

namespace minpoly

open IntermediateField

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
    (AlgEquiv.trans (AdjoinRoot.algEquivOfEq (ne_zero hx.isIntegral) h_mp)
      (adjoinRootEquivAdjoin K hy.isIntegral))

/-- `minpoly.algEquiv` sends the generator of `K⟮x⟯` to the generator of `K⟮y⟯`. -/
theorem algEquiv_apply {x y : L} (hx : IsAlgebraic K x) (h_mp : minpoly K x = minpoly K y) :
    algEquiv hx h_mp (AdjoinSimple.gen K x) = AdjoinSimple.gen K y := by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
  rw [algEquiv, trans_apply, ← adjoinRootEquivAdjoin_apply_root K hx.isIntegral,
    symm_apply_apply, trans_apply, AdjoinRoot.algEquivOfEq_apply_root,
    adjoinRootEquivAdjoin_apply_root K hy.isIntegral]

end minpoly

end Minpoly

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
  simp_rw [lift_max, lift_aleph0, sup_assoc]
  exact sup_le_sup_right mk_range_le_lift _

theorem cardinalMk_adjoin_le {E : Type u} [Field E] [Algebra F E] (s : Set E) :
    #(adjoin F s) ≤ #F ⊔ #s ⊔ ℵ₀ := by
  simpa using lift_cardinalMk_adjoin_le F s

end IntermediateField
