/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Lean.Expr.ExtraRecognizers

/-!

# Linear independence

This file defines linear independence in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define `LinearIndependent R v` as `Function.Injective (Finsupp.linearCombination R v)`. Here
`Finsupp.linearCombination` is the linear map sending a function `f : ι →₀ R` with finite support to
the linear combination of vectors from `v` with these coefficients.

The goal of this file is to define linear independence and to prove that several other
statements are equivalent to this one, including `ker (Finsupp.linearCombination R v) = ⊥` and
some versions with explicitly written linear combinations.

## Main definitions
All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `LinearIndependent R v` states that the elements of the family `v` are linearly independent.

* `LinearIndepOn R v s` states that the elements of the family `v` indexed by the members
  of the set `s : Set ι` are linearly independent.

* `LinearIndependent.repr hv x` returns the linear combination representing `x : span R (range v)`
  on the linearly independent vectors `v`, given `hv : LinearIndependent R v`
  (using classical choice). `LinearIndependent.repr hv` is provided as a linear map.

* `LinearIndependent.Maximal` states that there exists no linear independent family that strictly
  includes the given one.

## Main results

* `Fintype.linearIndependent_iff`: if `ι` is a finite type, then any function `f : ι → R` has
  finite support, so we can reformulate the statement using `∑ i : ι, f i • v i` instead of a sum
  over an auxiliary `s : Finset ι`;

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent.

If you want to use sets, use the family `(fun x ↦ x : s → M)` given a set `s : Set M`. The lemmas
`LinearIndependent.to_subtype_range` and `LinearIndependent.of_subtype_range` connect those two
worlds.

## TODO

This file contains much more than definitions.

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

assert_not_exists Cardinal

noncomputable section

open Function Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}
variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring


variable {v : ι → M}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (R) (v)
/-- `LinearIndependent R v` states the family of vectors `v` is linearly independent over `R`. -/
def LinearIndependent : Prop :=
  Injective (Finsupp.linearCombination R v)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `LinearIndependent` that suggests pretty printing with type hints
in case the family of vectors is over a `Set`.

Type hints look like `LinearIndependent fun (v : ↑s) => ↑v` or `LinearIndependent (ι := ↑s) f`,
depending on whether the family is a lambda expression or not. -/
@[app_delab LinearIndependent]
def delabLinearIndependent : Delab :=
  whenPPOption getPPNotation <|
  whenNotPPOption getPPAnalysisSkip <|
  withOptionAtCurrPos `pp.analysis.skip true do
    let e ← getExpr
    guard <| e.isAppOfArity ``LinearIndependent 7
    let some _ := (e.getArg! 0).coeTypeSet? | failure
    let optionsPerPos ← if (e.getArg! 3).isLambda then
      withNaryArg 3 do return (← read).optionsPerPos.setBool (← getPos) pp.funBinderTypes.name true
    else
      withNaryArg 0 do return (← read).optionsPerPos.setBool (← getPos) `pp.analysis.namedArg true
    withTheReader Context ({· with optionsPerPos}) delab

/-- `LinearIndepOn R v s` states that the vectors in the family `v` that are indexed
by the elements of `s` are linearly independent over `R`. -/
def LinearIndepOn (s : Set ι) : Prop := LinearIndependent R (fun x : s ↦ v x)

variable {R v}

theorem LinearIndepOn.linearIndependent {s : Set ι} (h : LinearIndepOn R v s) :
    LinearIndependent R (fun x : s ↦ v x) := h

theorem linearIndependent_iff_injective_finsuppLinearCombination :
    LinearIndependent R v ↔ Injective (Finsupp.linearCombination R v) := Iff.rfl

@[deprecated (since := "2025-03-18")]
alias linearIndependent_iff_injective_linearCombination :=
  linearIndependent_iff_injective_finsuppLinearCombination

alias ⟨LinearIndependent.finsuppLinearCombination_injective, _⟩ :=
  linearIndependent_iff_injective_finsuppLinearCombination

@[deprecated (since := "2025-03-18")]
alias LinearIndependent.linearCombination_injective :=
  LinearIndependent.finsuppLinearCombination_injective

theorem linearIndependent_iff_injective_fintypeLinearCombination [Fintype ι] :
    LinearIndependent R v ↔ Injective (Fintype.linearCombination R v) := by
  simp [← Finsupp.linearCombination_eq_fintype_linearCombination, LinearIndependent]

@[deprecated (since := "2025-03-18")]
alias Fintype.linearIndependent_iff_injective :=
  linearIndependent_iff_injective_fintypeLinearCombination

alias ⟨LinearIndependent.fintypeLinearCombination_injective, _⟩ :=
  linearIndependent_iff_injective_fintypeLinearCombination

theorem LinearIndependent.injective [Nontrivial R] (hv : LinearIndependent R v) : Injective v := by
  simpa [comp_def]
    using Injective.comp hv (Finsupp.single_left_injective one_ne_zero)

theorem LinearIndepOn.injOn [Nontrivial R] (hv : LinearIndepOn R v s) : InjOn v s :=
  injOn_iff_injective.2 <| LinearIndependent.injective hv

theorem LinearIndependent.smul_left_injective (hv : LinearIndependent R v) (i : ι) :
    Injective fun r : R ↦ r • v i := by convert hv.comp (Finsupp.single_injective i); simp

theorem LinearIndependent.ne_zero [Nontrivial R] (i : ι) (hv : LinearIndependent R v) :
    v i ≠ 0 := by
  intro h
  have := @hv (Finsupp.single i 1 : ι →₀ R) 0 (by simpa using h)
  simp at this

theorem LinearIndepOn.ne_zero [Nontrivial R] {i : ι} (hv : LinearIndepOn R v s) (hi : i ∈ s) :
    v i ≠ 0 :=
  LinearIndependent.ne_zero ⟨i, hi⟩ hv

theorem LinearIndepOn.zero_notMem_image [Nontrivial R] (hs : LinearIndepOn R v s) : 0 ∉ v '' s :=
  fun ⟨_, hi, h0⟩ ↦ hs.ne_zero hi h0

@[deprecated (since := "2025-05-23")]
alias LinearIndepOn.zero_not_mem_image := LinearIndepOn.zero_notMem_image

theorem linearIndependent_empty_type [IsEmpty ι] : LinearIndependent R v :=
  injective_of_subsingleton _

@[simp]
theorem linearIndependent_zero_iff [Nontrivial R] : LinearIndependent R (0 : ι → M) ↔ IsEmpty ι :=
  ⟨fun h ↦ not_nonempty_iff.1 fun ⟨i⟩ ↦ (h.ne_zero i rfl).elim,
    fun _ ↦ linearIndependent_empty_type⟩

@[simp]
theorem linearIndepOn_zero_iff [Nontrivial R] : LinearIndepOn R (0 : ι → M) s ↔ s = ∅ :=
  linearIndependent_zero_iff.trans isEmpty_coe_sort

@[simp]
theorem linearIndependent_subsingleton_iff [Nontrivial R] [Subsingleton M] (f : ι → M) :
    LinearIndependent R f ↔ IsEmpty ι := by
  rw [Subsingleton.elim f 0, linearIndependent_zero_iff]

variable (R M) in
theorem linearIndependent_empty : LinearIndependent R (fun x => x : (∅ : Set M) → M) :=
  linearIndependent_empty_type

variable (R v) in
@[simp]
theorem linearIndepOn_empty : LinearIndepOn R v ∅ :=
  linearIndependent_empty_type ..

theorem linearIndependent_set_coe_iff :
    LinearIndependent R (fun x : s ↦ v x) ↔ LinearIndepOn R v s := Iff.rfl

@[deprecated (since := "2025-02-20")] alias
  linearIndependent_set_subtype := linearIndependent_set_coe_iff

theorem linearIndependent_subtype_iff {s : Set M} :
    LinearIndependent R (Subtype.val : s → M) ↔ LinearIndepOn R id s := Iff.rfl

theorem linearIndependent_comp_subtype_iff :
    LinearIndependent R (v ∘ Subtype.val : s → M) ↔ LinearIndepOn R v s := Iff.rfl

/-- A subfamily of a linearly independent family (i.e., a composition with an injective map) is a
linearly independent family. -/
theorem LinearIndependent.comp (h : LinearIndependent R v) (f : ι' → ι) (hf : Injective f) :
    LinearIndependent R (v ∘ f) := by
  simpa [comp_def] using Injective.comp h (Finsupp.mapDomain_injective hf)

lemma LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn R v s) (h : t ⊆ s) :
    LinearIndepOn R v t := hs.comp _ <| Set.inclusion_injective h

-- This version makes `l₁` and `l₂` explicit.
theorem linearIndependent_iffₛ :
    LinearIndependent R v ↔
      ∀ l₁ l₂, Finsupp.linearCombination R v l₁ = Finsupp.linearCombination R v l₂ → l₁ = l₂ :=
  Iff.rfl

open Finset in
theorem linearIndependent_iff'ₛ :
    LinearIndependent R v ↔
      ∀ s : Finset ι, ∀ f g : ι → R, ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i → ∀ i ∈ s, f i = g i :=
  linearIndependent_iffₛ.trans
    ⟨fun hv s f g eq i his ↦ by
      have h :=
        hv (∑ i ∈ s, Finsupp.single i (f i)) (∑ i ∈ s, Finsupp.single i (g i)) <| by
          simpa only [map_sum, Finsupp.linearCombination_single] using eq
      have (f : ι → R) : f i = (∑ j ∈ s, Finsupp.single j (f j)) i :=
        calc
          f i = (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single i (f i)) := by
            { rw [Finsupp.lapply_apply, Finsupp.single_eq_same] }
          _ = ∑ j ∈ s, (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single j (f j)) :=
            Eq.symm <|
              Finset.sum_eq_single i
                (fun j _hjs hji => by rw [Finsupp.lapply_apply, Finsupp.single_eq_of_ne hji])
                fun hnis => hnis.elim his
          _ = (∑ j ∈ s, Finsupp.single j (f j)) i := (map_sum ..).symm
      rw [this f, this g, h],
      fun hv f g hl ↦
      Finsupp.ext fun _ ↦ by
        classical
        refine _root_.by_contradiction fun hni ↦ hni <| hv (f.support ∪ g.support) f g ?_ _ ?_
        · rwa [← sum_subset subset_union_left, ← sum_subset subset_union_right] <;>
            rintro i - hi <;> rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
        · contrapose! hni
          simp_rw [notMem_union, Finsupp.notMem_support_iff] at hni
          rw [hni.1, hni.2]⟩

theorem linearIndependent_iff''ₛ :
    LinearIndependent R v ↔
      ∀ (s : Finset ι) (f g : ι → R), (∀ i ∉ s, f i = g i) →
        ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i → ∀ i, f i = g i := by
  classical
  exact linearIndependent_iff'ₛ.trans
    ⟨fun H s f g eq hv i ↦ if his : i ∈ s then H s f g hv i his else eq i his,
      fun H s f g eq i hi ↦ by
      convert
        H s (fun j ↦ if j ∈ s then f j else 0) (fun j ↦ if j ∈ s then g j else 0)
          (fun j hj ↦ (if_neg hj).trans (if_neg hj).symm)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, eq]) i <;>
      exact (if_pos hi).symm⟩

theorem not_linearIndependent_iffₛ :
    ¬LinearIndependent R v ↔ ∃ s : Finset ι,
      ∃ f g : ι → R, ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i ∧ ∃ i ∈ s, f i ≠ g i := by
  rw [linearIndependent_iff'ₛ]
  simp only [exists_prop, not_forall]

theorem Fintype.linearIndependent_iffₛ [Fintype ι] :
    LinearIndependent R v ↔ ∀ f g : ι → R, ∑ i, f i • v i = ∑ i, g i • v i → ∀ i, f i = g i := by
  simp_rw [linearIndependent_iff_injective_fintypeLinearCombination,
    Injective, Fintype.linearCombination_apply, funext_iff]

theorem Fintype.not_linearIndependent_iffₛ [Fintype ι] :
    ¬LinearIndependent R v ↔ ∃ f g : ι → R, ∑ i, f i • v i = ∑ i, g i • v i ∧ ∃ i, f i ≠ g i := by
  simpa using not_iff_not.2 Fintype.linearIndependent_iffₛ

lemma linearIndepOn_finset_iffₛ {s : Finset ι} :
    LinearIndepOn R v s ↔ ∀ f g : ι → R,
      ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i → ∀ i ∈ s, f i = g i := by
  classical
  simp_rw [LinearIndepOn, Fintype.linearIndependent_iffₛ]
  constructor
  · rintro hv f g hfg i hi
    simp_rw [← s.sum_attach] at hfg
    exact hv (f ∘ Subtype.val) (g ∘ Subtype.val) hfg ⟨i, hi⟩
  · rintro hv f g hfg i
    simpa using hv (fun j ↦ if hj : j ∈ s then f ⟨j, hj⟩ else 0)
      (fun j ↦ if hj : j ∈ s then g ⟨j, hj⟩ else 0) (by simpa +contextual [← s.sum_attach]) i

lemma not_linearIndepOn_finset_iffₛ {s : Finset ι} :
    ¬LinearIndepOn R v s ↔ ∃ f g : ι → R,
      ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i ∧ ∃ i ∈ s, f i ≠ g i := by
  simpa using linearIndepOn_finset_iffₛ.not

/-- A family is linearly independent if and only if all of its finite subfamily is
linearly independent. -/
theorem linearIndependent_iff_finset_linearIndependent :
    LinearIndependent R v ↔ ∀ (s : Finset ι), LinearIndependent R (v ∘ (Subtype.val : s → ι)) :=
  ⟨fun H _ ↦ H.comp _ Subtype.val_injective, fun H ↦ linearIndependent_iff'ₛ.2 fun s f g eq i hi ↦
    Fintype.linearIndependent_iffₛ.1 (H s) (f ∘ Subtype.val) (g ∘ Subtype.val)
      (by simpa only [← s.sum_coe_sort] using eq) ⟨i, hi⟩⟩

lemma linearIndepOn_iff_linearIndepOn_finset :
    LinearIndepOn R v s ↔ ∀ t : Finset ι, ↑t ⊆ s → LinearIndepOn R v t where
  mp hv t hts := hv.mono hts
  mpr hv := by
    rw [LinearIndepOn, linearIndependent_iff_finset_linearIndependent]
    exact fun t ↦ (hv (t.map <| .subtype _) (by simp)).comp (ι' := t)
      (fun x ↦ ⟨x, Finset.mem_map_of_mem _ x.2⟩) fun x ↦ by aesop

/-- If the image of a family of vectors under a linear map is linearly independent, then so is
the original family. -/
theorem LinearIndependent.of_comp (f : M →ₗ[R] M') (hfv : LinearIndependent R (f ∘ v)) :
    LinearIndependent R v := by
  rw [LinearIndependent, Finsupp.linearCombination_linear_comp, LinearMap.coe_comp] at hfv
  exact hfv.of_comp

theorem LinearIndepOn.of_comp (f : M →ₗ[R] M') (hfv : LinearIndepOn R (f ∘ v) s) :
    LinearIndepOn R v s :=
  LinearIndependent.of_comp f hfv

/-- If `f` is a linear map injective on the span of the range of `v`, then the family `f ∘ v`
is linearly independent if and only if the family `v` is linearly independent.
See `LinearMap.linearIndependent_iff_of_disjoint` for the version with `Set.InjOn` replaced
by `Disjoint` when working over a ring. -/
protected theorem LinearMap.linearIndependent_iff_of_injOn (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (Set.range v))) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v := by
  simp_rw [LinearIndependent, Finsupp.linearCombination_linear_comp, coe_comp]
  rw [hf_inj.injective_iff]
  rw [← Finsupp.range_linearCombination, LinearMap.range_coe]

protected theorem LinearMap.linearIndepOn_iff_of_injOn (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (v '' s))) :
    LinearIndepOn R (f ∘ v) s ↔ LinearIndepOn R v s :=
  f.linearIndependent_iff_of_injOn (by rwa [← image_eq_range]) (v := fun i : s ↦ v i)

-- TODO : Rename this `LinearIndependent.of_subsingleton`.
@[nontriviality]
theorem linearIndependent_of_subsingleton [Subsingleton R] : LinearIndependent R v :=
  linearIndependent_iffₛ.2 fun _l _l' _hl => Subsingleton.elim _ _

@[nontriviality]
theorem LinearIndepOn.of_subsingleton [Subsingleton R] : LinearIndepOn R v s :=
  linearIndependent_of_subsingleton

theorem linearIndependent_equiv (e : ι ≃ ι') {f : ι' → M} :
    LinearIndependent R (f ∘ e) ↔ LinearIndependent R f :=
  ⟨fun h ↦ comp_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
    fun h ↦ h.comp _ e.injective⟩

theorem linearIndependent_equiv' (e : ι ≃ ι') {f : ι' → M} {g : ι → M} (h : f ∘ e = g) :
    LinearIndependent R g ↔ LinearIndependent R f :=
  h ▸ linearIndependent_equiv e

theorem linearIndepOn_equiv (e : ι ≃ ι') {f : ι' → M} {s : Set ι} :
    LinearIndepOn R (f ∘ e) s ↔ LinearIndepOn R f (e '' s) :=
  linearIndependent_equiv' (e.image s) <| by simp [funext_iff]

@[simp]
theorem linearIndepOn_univ : LinearIndepOn R v univ ↔ LinearIndependent R v :=
  linearIndependent_equiv' (Equiv.Set.univ ι) rfl

alias ⟨_, LinearIndependent.linearIndepOn⟩ := linearIndepOn_univ

theorem linearIndepOn_iff_image {ι} {s : Set ι} {f : ι → M} (hf : Set.InjOn f s) :
    LinearIndepOn R f s ↔ LinearIndepOn R id (f '' s) :=
  linearIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ hf) rfl

@[deprecated (since := "2025-02-14")] alias linearIndependent_image := linearIndepOn_iff_image

theorem linearIndepOn_range_iff {ι} {f : ι → ι'} (hf : Injective f) (g : ι' → M) :
    LinearIndepOn R g (range f) ↔ LinearIndependent R (g ∘ f) :=
  Iff.symm <| linearIndependent_equiv' (Equiv.ofInjective f hf) rfl

alias ⟨LinearIndependent.of_linearIndepOn_range, _⟩ := linearIndepOn_range_iff

theorem linearIndepOn_id_range_iff {ι} {f : ι → M} (hf : Injective f) :
    LinearIndepOn R id (range f) ↔ LinearIndependent R f :=
  linearIndepOn_range_iff hf id

alias ⟨LinearIndependent.of_linearIndepOn_id_range, _⟩ := linearIndepOn_id_range_iff

@[deprecated (since := "2025-02-15")] alias linearIndependent_subtype_range :=
    linearIndepOn_id_range_iff

@[deprecated (since := "2025-02-15")] alias LinearIndependent.of_subtype_range :=
    LinearIndependent.of_linearIndepOn_id_range

theorem LinearIndependent.linearIndepOn_id (i : LinearIndependent R v) :
    LinearIndepOn R id (range v) := by
  simpa using i.comp _ (rangeSplitting_injective v)

@[deprecated (since := "2025-02-15")] alias LinearIndependent.to_subtype_range :=
    LinearIndependent.linearIndepOn_id

@[deprecated (since := "2025-02-14")] alias
  LinearIndependent.coe_range := LinearIndependent.linearIndepOn_id

/-- A version of `LinearIndependent.linearIndepOn_id` with the set range equality as a hypothesis.
-/
theorem LinearIndependent.linearIndepOn_id' (hv : LinearIndependent R v) {t : Set M}
    (ht : Set.range v = t) : LinearIndepOn R id t :=
  ht ▸ hv.linearIndepOn_id

@[deprecated (since := "2025-02-16")] alias LinearIndependent.to_subtype_range' :=
    LinearIndependent.linearIndepOn_id'

section Indexed

theorem linearIndepOn_iffₛ : LinearIndepOn R v s ↔
      ∀ f ∈ Finsupp.supported R R s, ∀ g ∈ Finsupp.supported R R s,
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g → f = g := by
  simp only [LinearIndepOn, linearIndependent_iffₛ, Finsupp.mem_supported,
    Finsupp.linearCombination_apply, Set.subset_def, Finset.mem_coe]
  refine ⟨fun h l₁ h₁ l₂ h₂ eq ↦ (Finsupp.subtypeDomain_eq_iff h₁ h₂).1 <| h _ _ <|
    (Finsupp.sum_subtypeDomain_index h₁).trans eq ▸ (Finsupp.sum_subtypeDomain_index h₂).symm,
    fun h l₁ l₂ eq ↦ ?_⟩
  refine Finsupp.embDomain_injective (Embedding.subtype s) <| h _ ?_ _ ?_ ?_
  iterate 2 simpa using fun _ h _ ↦ h
  simp_rw [Finsupp.embDomain_eq_mapDomain]
  rwa [Finsupp.sum_mapDomain_index, Finsupp.sum_mapDomain_index] <;>
    intros <;> simp only [zero_smul, add_smul]

@[deprecated (since := "2025-02-15")] alias linearIndependent_comp_subtypeₛ := linearIndepOn_iffₛ

/-- An indexed set of vectors is linearly dependent iff there are two distinct
`Finsupp.LinearCombination`s of the vectors with the same value. -/
theorem linearDepOn_iff'ₛ : ¬LinearIndepOn R v s ↔
      ∃ f g : ι →₀ R, f ∈ Finsupp.supported R R s ∧ g ∈ Finsupp.supported R R s ∧
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g ∧ f ≠ g := by
  simp [linearIndepOn_iffₛ]

@[deprecated (since := "2025-02-15")] alias linearDependent_comp_subtype'ₛ := linearDepOn_iff'ₛ

/-- A version of `linearDepOn_iff'ₛ` with `Finsupp.linearCombination` unfolded. -/
theorem linearDepOn_iffₛ : ¬LinearIndepOn R v s ↔
      ∃ f g : ι →₀ R, f ∈ Finsupp.supported R R s ∧ g ∈ Finsupp.supported R R s ∧
        ∑ i ∈ f.support, f i • v i = ∑ i ∈ g.support, g i • v i ∧ f ≠ g :=
  linearDepOn_iff'ₛ

@[deprecated (since := "2025-02-15")] alias linearDependent_comp_subtypeₛ := linearDepOn_iffₛ

@[deprecated (since := "2025-02-15")] alias linearIndependent_subtypeₛ := linearIndepOn_iffₛ

theorem linearIndependent_restrict_iff :
    LinearIndependent R (s.restrict v) ↔ LinearIndepOn R v s := Iff.rfl

theorem LinearIndepOn.linearIndependent_restrict (hs : LinearIndepOn R v s) :
    LinearIndependent R (s.restrict v) :=
  hs

@[deprecated (since := "2025-02-15")] alias LinearIndependent.restrict_of_comp_subtype :=
    LinearIndepOn.linearIndependent_restrict

theorem linearIndepOn_iff_linearCombinationOnₛ :
    LinearIndepOn R v s ↔ Injective (Finsupp.linearCombinationOn ι M R v s) := by
  rw [← linearIndependent_restrict_iff]
  simp [LinearIndependent, Finsupp.linearCombination_restrict]

@[deprecated (since := "2025-02-15")] alias
  linearIndependent_iff_linearCombinationOnₛ := linearIndepOn_iff_linearCombinationOnₛ

end Indexed

section repr

/-- Canonical isomorphism between linear combinations and the span of linearly independent vectors.
-/
@[simps (rhsMd := default) symm_apply]
def LinearIndependent.linearCombinationEquiv (hv : LinearIndependent R v) :
    (ι →₀ R) ≃ₗ[R] span R (range v) := by
  refine LinearEquiv.ofBijective (LinearMap.codRestrict (span R (range v))
    (Finsupp.linearCombination R v) ?_) ⟨hv.codRestrict _, ?_⟩
  · simp_rw [← Finsupp.range_linearCombination]; exact fun c ↦ ⟨c, rfl⟩
  rw [← LinearMap.range_eq_top, LinearMap.range_eq_map, LinearMap.map_codRestrict,
    ← LinearMap.range_le_iff_comap, range_subtype, Submodule.map_top,
    Finsupp.range_linearCombination]

-- Porting note: The original theorem generated by `simps` was
--               different from the theorem on Lean 3, and not simp-normal form.
@[simp]
theorem LinearIndependent.linearCombinationEquiv_apply_coe (hv : LinearIndependent R v)
    (l : ι →₀ R) : hv.linearCombinationEquiv l = Finsupp.linearCombination R v l := rfl

/-- Linear combination representing a vector in the span of linearly independent vectors.

Given a family of linearly independent vectors, we can represent any vector in their span as
a linear combination of these vectors. These are provided by this linear map.
It is simply one direction of `LinearIndependent.linearCombinationEquiv`. -/
def LinearIndependent.repr (hv : LinearIndependent R v) : span R (range v) →ₗ[R] ι →₀ R :=
  hv.linearCombinationEquiv.symm

variable (hv : LinearIndependent R v) {i : ι}

@[simp]
theorem LinearIndependent.linearCombination_repr (x) :
    Finsupp.linearCombination R v (hv.repr x) = x :=
  Subtype.ext_iff.1 (LinearEquiv.apply_symm_apply hv.linearCombinationEquiv x)

theorem LinearIndependent.linearCombination_comp_repr :
    (Finsupp.linearCombination R v).comp hv.repr = Submodule.subtype _ :=
  LinearMap.ext <| hv.linearCombination_repr

theorem LinearIndependent.repr_ker : LinearMap.ker hv.repr = ⊥ := by
  rw [LinearIndependent.repr, LinearEquiv.ker]

theorem LinearIndependent.repr_range : LinearMap.range hv.repr = ⊤ := by
  rw [LinearIndependent.repr, LinearEquiv.range]

theorem LinearIndependent.repr_eq {l : ι →₀ R} {x : span R (range v)}
    (eq : Finsupp.linearCombination R v l = ↑x) : hv.repr x = l := by
  have :
    ↑((LinearIndependent.linearCombinationEquiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l) =
      Finsupp.linearCombination R v l :=
    rfl
  have : (LinearIndependent.linearCombinationEquiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l = x := by
    rw [eq] at this
    exact Subtype.ext_iff.2 this
  rw [← LinearEquiv.symm_apply_apply hv.linearCombinationEquiv l]
  rw [← this]
  rfl

theorem LinearIndependent.repr_eq_single (i) (x : span R (range v)) (hx : ↑x = v i) :
    hv.repr x = Finsupp.single i 1 := by
  apply hv.repr_eq
  simp [Finsupp.linearCombination_single, hx]

theorem LinearIndependent.span_repr_eq [Nontrivial R] (x) :
    Span.repr R (Set.range v) x =
      (hv.repr x).equivMapDomain (Equiv.ofInjective _ hv.injective) := by
  have p :
    (Span.repr R (Set.range v) x).equivMapDomain (Equiv.ofInjective _ hv.injective).symm =
      hv.repr x := by
    apply (LinearIndependent.linearCombinationEquiv hv).injective
    ext
    simp only [LinearIndependent.linearCombinationEquiv_apply_coe, Equiv.self_comp_ofInjective_symm,
      LinearIndependent.linearCombination_repr, Finsupp.linearCombination_equivMapDomain,
      Span.finsupp_linearCombination_repr]
  ext ⟨_, ⟨i, rfl⟩⟩
  simp [← p]

theorem LinearIndependent.eq_zero_of_smul_mem_span (hv : LinearIndependent R v) (i : ι) (a : R)
    (ha : a • v i ∈ span R (v '' (univ \ {i}))) : a = 0 := by
  rw [Finsupp.span_image_eq_map_linearCombination, mem_map] at ha
  rcases ha with ⟨l, hl, e⟩
  rw [linearIndependent_iffₛ.1 hv l (Finsupp.single i a) (by simp [e])] at hl
  by_contra hn
  exact (notMem_of_mem_diff (hl <| by simp [hn])) (mem_singleton _)

@[deprecated (since := "2025-05-13")]
alias LinearIndependent.not_smul_mem_span := LinearIndependent.eq_zero_of_smul_mem_span

nonrec lemma LinearIndepOn.eq_zero_of_smul_mem_span (hv : LinearIndepOn R v s) (hi : i ∈ s) (a : R)
    (ha : a • v i ∈ span R (v '' (s \ {i}))) : a = 0 :=
  hv.eq_zero_of_smul_mem_span ⟨i, hi⟩ _ <| by
    simpa [← comp_def, image_comp, image_diff Subtype.val_injective]

variable [Nontrivial R]

lemma LinearIndependent.notMem_span (hv : LinearIndependent R v) (i : ι) :
    v i ∉ span R (v '' {i}ᶜ) := fun hi ↦
  one_ne_zero <| hv.eq_zero_of_smul_mem_span i 1 <| by simpa [Set.compl_eq_univ_diff] using hi

@[deprecated (since := "2025-05-23")]
alias LinearIndependent.not_mem_span := LinearIndependent.notMem_span

lemma LinearIndepOn.notMem_span (hv : LinearIndepOn R v s) (hi : i ∈ s) :
    v i ∉ span R (v '' (s \ {i})) := fun hi' ↦
  one_ne_zero <| hv.eq_zero_of_smul_mem_span hi 1 <| by  simpa [Set.compl_eq_univ_diff] using hi'

@[deprecated (since := "2025-05-23")] alias LinearIndepOn.not_mem_span := LinearIndepOn.notMem_span

lemma LinearIndepOn.notMem_span_of_insert (hv : LinearIndepOn R v (insert i s)) (hi : i ∉ s) :
    v i ∉ span R (v '' s) := by simpa [hi] using hv.notMem_span <| mem_insert ..

@[deprecated (since := "2025-05-23")]
alias LinearIndepOn.not_mem_span_of_insert := LinearIndepOn.notMem_span_of_insert

end repr

section Maximal

universe v w

/--
A linearly independent family is maximal if there is no strictly larger linearly independent family.
-/
@[nolint unusedArguments]
def LinearIndependent.Maximal {ι : Type w} {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M]
    [Module R M] {v : ι → M} (_i : LinearIndependent R v) : Prop :=
  ∀ (s : Set M) (_i' : LinearIndependent R ((↑) : s → M)) (_h : range v ≤ s), range v = s

/-- An alternative characterization of a maximal linearly independent family,
quantifying over types (in the same universe as `M`) into which the indexing family injects.
-/
theorem LinearIndependent.maximal_iff {ι : Type w} {R : Type u} [Semiring R] [Nontrivial R]
    {M : Type v} [AddCommMonoid M] [Module R M] {v : ι → M} (i : LinearIndependent R v) :
    i.Maximal ↔
      ∀ (κ : Type v) (w : κ → M) (_i' : LinearIndependent R w) (j : ι → κ) (_h : w ∘ j = v),
        Surjective j := by
  constructor
  · rintro p κ w i' j rfl
    specialize p (range w) i'.linearIndepOn_id (range_comp_subset_range _ _)
    rw [range_comp, ← image_univ (f := w)] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p w i' h
    specialize
      p w ((↑) : w → M) i' (fun i => ⟨v i, range_subset_iff.mp h i⟩)
        (by
          ext
          simp)
    have q := congr_arg (fun s => ((↑) : w → M) '' s) p.range_eq
    dsimp at q
    rw [← image_univ, image_image] at q
    simpa using q

end Maximal

end Semiring

section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

theorem linearIndependent_iff_ker :
    LinearIndependent R v ↔ LinearMap.ker (Finsupp.linearCombination R v) = ⊥ :=
  LinearMap.ker_eq_bot.symm

theorem linearIndependent_iff :
    LinearIndependent R v ↔ ∀ l, Finsupp.linearCombination R v l = 0 → l = 0 := by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot']

/-- A version of `linearIndependent_iff` where the linear combination is a `Finset` sum. -/
theorem linearIndependent_iff' :
    LinearIndependent R v ↔
      ∀ s : Finset ι, ∀ g : ι → R, ∑ i ∈ s, g i • v i = 0 → ∀ i ∈ s, g i = 0 := by
  rw [linearIndependent_iff'ₛ]
  refine ⟨fun h s f ↦ ?_, fun h s f g ↦ ?_⟩
  · convert h s f 0; simp_rw [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  · rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    convert h s (f - g) using 3 <;> simp only [Pi.sub_apply, sub_smul, sub_eq_zero]

/-- A version of `linearIndependent_iff` where the linear combination is a `Finset` sum
of a function with support contained in the `Finset`. -/
theorem linearIndependent_iff'' :
    LinearIndependent R v ↔
      ∀ (s : Finset ι) (g : ι → R), (∀ i ∉ s, g i = 0) → ∑ i ∈ s, g i • v i = 0 → ∀ i, g i = 0 := by
  classical
  exact linearIndependent_iff'.trans
    ⟨fun H s g hg hv i => if his : i ∈ s then H s g hv i his else hg i his, fun H s g hg i hi => by
      convert
        H s (fun j => if j ∈ s then g j else 0) (fun j hj => if_neg hj)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, hg]) i
      exact (if_pos hi).symm⟩

theorem linearIndependent_add_smul_iff {c : ι → R} {i : ι} (h₀ : c i = 0) :
    LinearIndependent R (v + (c · • v i)) ↔ LinearIndependent R v := by
  simp [linearIndependent_iff_injective_finsuppLinearCombination,
    ← Finsupp.linearCombination_comp_addSingleEquiv i c h₀]

theorem not_linearIndependent_iff :
    ¬LinearIndependent R v ↔
      ∃ s : Finset ι, ∃ g : ι → R, ∑ i ∈ s, g i • v i = 0 ∧ ∃ i ∈ s, g i ≠ 0 := by
  rw [linearIndependent_iff']
  simp only [exists_prop, not_forall]

theorem Fintype.linearIndependent_iff [Fintype ι] :
    LinearIndependent R v ↔ ∀ g : ι → R, ∑ i, g i • v i = 0 → ∀ i, g i = 0 := by
  refine
    ⟨fun H g => by simpa using linearIndependent_iff'.1 H Finset.univ g, fun H =>
      linearIndependent_iff''.2 fun s g hg hs i => H _ ?_ _⟩
  rw [← hs]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [hg i hi, zero_smul]

theorem Fintype.not_linearIndependent_iff [Fintype ι] :
    ¬LinearIndependent R v ↔ ∃ g : ι → R, ∑ i, g i • v i = 0 ∧ ∃ i, g i ≠ 0 := by
  simpa using not_iff_not.2 Fintype.linearIndependent_iff

lemma linearIndepOn_finset_iff {s : Finset ι} :
    LinearIndepOn R v s ↔ ∀ f : ι → R, ∑ i ∈ s, f i • v i = 0 → ∀ i ∈ s, f i = 0 := by
  classical
  simp_rw [LinearIndepOn, Fintype.linearIndependent_iff]
  constructor
  · rintro hv f hf i hi
    rw [← s.sum_attach] at hf
    exact hv (f ∘ Subtype.val) hf ⟨i, hi⟩
  · rintro hv f hf₀ i
    simpa using hv (fun j ↦ if hj : j ∈ s then f ⟨j, hj⟩ else 0)
      (by simpa +contextual [← s.sum_attach]) i

lemma not_linearIndepOn_finset_iff {s : Finset ι} :
    ¬LinearIndepOn R v s ↔ ∃ f : ι → R, ∑ i ∈ s, f i • v i = 0 ∧ ∃ i ∈ s, f i ≠ 0 := by
  simpa using linearIndepOn_finset_iff.not

/-- If the kernel of a linear map is disjoint from the span of a family of vectors,
then the family is linearly independent iff it is linearly independent after composing with
the linear map. -/
protected theorem LinearMap.linearIndependent_iff_of_disjoint (f : M →ₗ[R] M')
    (hf_inj : Disjoint (span R (Set.range v)) (LinearMap.ker f)) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v :=
  f.linearIndependent_iff_of_injOn <| LinearMap.injOn_of_disjoint_ker le_rfl hf_inj

section LinearIndepOn

/-! The following give equivalent versions of `LinearIndepOn` and its negation. -/

theorem linearIndepOn_iff : LinearIndepOn R v s ↔
      ∀ l ∈ Finsupp.supported R R s, (Finsupp.linearCombination R v) l = 0 → l = 0 :=
  linearIndepOn_iffₛ.trans ⟨fun h l hl ↦ h l hl 0 (zero_mem _), fun h f hf g hg eq ↦
    sub_eq_zero.mp (h (f - g) (sub_mem hf hg) <| by rw [map_sub, eq, sub_self])⟩

@[deprecated (since := "2025-02-15")] alias linearIndependent_comp_subtype := linearIndepOn_iff

@[deprecated (since := "2025-02-15")] alias linearIndependent_subtype := linearIndepOn_iff

/-- An indexed set of vectors is linearly dependent iff there is a nontrivial
`Finsupp.linearCombination` of the vectors that is zero. -/
theorem linearDepOn_iff' : ¬LinearIndepOn R v s ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ Finsupp.linearCombination R v f = 0 ∧ f ≠ 0 := by
  simp [linearIndepOn_iff]

@[deprecated (since := "2025-02-15")] alias linearDependent_comp_subtype' := linearDepOn_iff'

/-- A version of `linearDepOn_iff'` with `Finsupp.linearCombination` unfolded. -/
theorem linearDepOn_iff : ¬LinearIndepOn R v s ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ ∑ i ∈ f.support, f i • v i = 0 ∧ f ≠ 0 :=
  linearDepOn_iff'

@[deprecated (since := "2025-02-15")] alias linearDependent_comp_subtype := linearDepOn_iff

theorem linearIndepOn_iff_disjoint : LinearIndepOn R v s ↔
      Disjoint (Finsupp.supported R R s) (LinearMap.ker <| Finsupp.linearCombination R v) := by
  rw [linearIndepOn_iff, LinearMap.disjoint_ker]

@[deprecated (since := "2025-02-15")] alias linearIndependent_comp_subtype_disjoint :=
    linearIndepOn_iff_disjoint

@[deprecated (since := "2025-02-15")] alias linearIndependent_subtype_disjoint :=
    linearIndepOn_iff_disjoint

theorem linearIndepOn_iff_linearCombinationOn :
    LinearIndepOn R v s ↔ (LinearMap.ker <| Finsupp.linearCombinationOn ι M R v s) = ⊥ :=
  linearIndepOn_iff_linearCombinationOnₛ.trans <|
    LinearMap.ker_eq_bot (M := Finsupp.supported R R s).symm

@[deprecated (since := "2025-02-15")] alias linearIndependent_iff_linearCombinationOn :=
  linearIndepOn_iff_linearCombinationOn

/-- A version of `linearIndepOn_iff` where the linear combination is a `Finset` sum. -/
lemma linearIndepOn_iff' : LinearIndepOn R v s ↔ ∀ (t : Finset ι) (g : ι → R), (t : Set ι) ⊆ s →
    ∑ i ∈ t, g i • v i = 0 → ∀ i ∈ t, g i = 0 := by
  classical
  rw [LinearIndepOn, linearIndependent_iff']
  refine ⟨fun h t g hts h0 i hit ↦ ?_, fun h t g h0 i hit ↦ ?_⟩
  · refine h (t.preimage _ Subtype.val_injective.injOn) (fun i ↦ g i) ?_ ⟨i, hts hit⟩ (by simpa)
    rwa [t.sum_preimage ((↑) : s → ι) Subtype.val_injective.injOn (fun i ↦ g i • v i)]
    simp only [Subtype.range_coe_subtype, setOf_mem_eq]
    exact fun x hxt hxs ↦ (hxs (hts hxt)) |>.elim
  replace h : ∀ i (hi : i ∈ s), ⟨i, hi⟩ ∈ t → ∀ (h : i ∈ s), g ⟨i, h⟩ = 0 := by
    simpa [h0] using h (t.image (↑)) (fun i ↦ if hi : i ∈ s then g ⟨i, hi⟩ else 0)
  apply h _ _ hit

/-- A version of `linearIndepOn_iff` where the linear combination is a `Finset` sum
of a function with support contained in the `Finset`. -/
lemma linearIndepOn_iff'' : LinearIndepOn R v s ↔ ∀ (t : Finset ι) (g : ι → R), (t : Set ι) ⊆ s →
    (∀ i ∉ t, g i = 0) → ∑ i ∈ t, g i • v i = 0 → ∀ i ∈ t, g i = 0 := by
  classical
  exact linearIndepOn_iff'.trans ⟨fun h t g hts htg h0 ↦ h _ _ hts h0, fun h t g hts h0 ↦
    by simpa +contextual [h0] using h t (fun i ↦ if i ∈ t then g i else 0) hts⟩

end LinearIndepOn

end Module

/-! ### Properties which require `Ring R` -/


section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

open LinearMap

theorem linearIndependent_iff_eq_zero_of_smul_mem_span :
    LinearIndependent R v ↔ ∀ (i : ι) (a : R), a • v i ∈ span R (v '' (univ \ {i})) → a = 0 :=
  ⟨fun hv ↦ hv.eq_zero_of_smul_mem_span, fun H =>
    linearIndependent_iff.2 fun l hl => by
      ext i; simp only [Finsupp.zero_apply]
      by_contra hn
      refine hn (H i _ ?_)
      refine (Finsupp.mem_span_image_iff_linearCombination R).2 ⟨Finsupp.single i (l i) - l, ?_, ?_⟩
      · rw [Finsupp.mem_supported']
        intro j hj
        have hij : j = i :=
          Classical.not_not.1 fun hij : j ≠ i =>
            hj ((mem_diff _).2 ⟨mem_univ _, fun h => hij (eq_of_mem_singleton h)⟩)
        simp [hij]
      · simp [hl]⟩

end Module

/-!
### Properties which require `DivisionRing K`

These can be considered generalizations of properties of linear independence in vector spaces.
-/


section Module

variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable {v : ι → V} {s t : Set ι} {x y : V}

open Submodule

theorem linearIndependent_iff_notMem_span :
    LinearIndependent K v ↔ ∀ i, v i ∉ span K (v '' (univ \ {i})) := by
  apply linearIndependent_iff_eq_zero_of_smul_mem_span.trans
  constructor
  · intro h i h_in_span
    apply one_ne_zero (h i 1 (by simp [h_in_span]))
  · intro h i a ha
    by_contra ha'
    exact False.elim (h _ ((smul_mem_iff _ ha').1 ha))

@[deprecated (since := "2025-05-23")]
alias linearIndependent_iff_not_mem_span := linearIndependent_iff_notMem_span

lemma linearIndepOn_iff_notMem_span :
    LinearIndepOn K v s ↔ ∀ i ∈ s, v i ∉ span K (v '' (s \ {i})) := by
  rw [LinearIndepOn, linearIndependent_iff_notMem_span, ← Function.comp_def]
  simp_rw [Set.image_comp]
  simp [Set.image_diff Subtype.val_injective]

@[deprecated (since := "2025-05-23")]
alias linearIndepOn_iff_not_mem_span := linearIndepOn_iff_notMem_span

end Module
