/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

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

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

assert_not_exists Cardinal

noncomputable section

open Function Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*}
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

theorem linearIndependent_iff_injective_linearCombination :
    LinearIndependent R v ↔ Injective (Finsupp.linearCombination R v) := Iff.rfl

alias ⟨LinearIndependent.injective_linearCombination, _⟩ :=
  linearIndependent_iff_injective_linearCombination

theorem Fintype.linearIndependent_iff_injective [Fintype ι] :
    LinearIndependent R v ↔ Injective (Fintype.linearCombination R ℕ v) := by
  simp [← Finsupp.linearCombination_eq_fintype_linearCombination, LinearIndependent]

theorem LinearIndependent.injective [Nontrivial R] (hv : LinearIndependent R v) : Injective v := by
  simpa [comp_def]
    using Injective.comp hv (Finsupp.single_left_injective one_ne_zero)

theorem LinearIndependent.ne_zero [Nontrivial R] (i : ι) (hv : LinearIndependent R v) :
    v i ≠ 0 := by
  intro h
  have := @hv (Finsupp.single i 1 : ι →₀ R) 0 (by simpa using h)
  simp at this

theorem linearIndependent_empty_type [IsEmpty ι] : LinearIndependent R v :=
  injective_of_subsingleton _

@[simp]
theorem linearIndependent_zero_iff [Nontrivial R] : LinearIndependent R (0 : ι → M) ↔ IsEmpty ι :=
  ⟨fun h ↦ not_nonempty_iff.1 fun ⟨i⟩ ↦ (h.ne_zero i rfl).elim,
    fun _ ↦ linearIndependent_empty_type⟩

variable (R M) in
theorem linearIndependent_empty : LinearIndependent R (fun x => x : (∅ : Set M) → M) :=
  linearIndependent_empty_type

variable (R v) in
@[simp]
theorem linearIndepOn_empty : LinearIndepOn R v ∅ :=
  linearIndependent_empty_type ..

theorem linearIndependent_set_subtype {s : Set ι} :
    LinearIndependent R (fun x : s ↦ v x) ↔ LinearIndepOn R v s := Iff.rfl

/-- A subfamily of a linearly independent family (i.e., a composition with an injective map) is a
linearly independent family. -/
theorem LinearIndependent.comp (h : LinearIndependent R v) (f : ι' → ι) (hf : Injective f) :
    LinearIndependent R (v ∘ f) := by
  simpa [comp_def] using Injective.comp h (Finsupp.mapDomain_injective hf)

@[deprecated (since := "2024-08-29")] alias linearIndependent_iff_injective_total :=
  linearIndependent_iff_injective_linearCombination

@[deprecated (since := "2024-08-29")] alias LinearIndependent.injective_total :=
  LinearIndependent.injective_linearCombination

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
            rintro i - hi <;> rw [Finsupp.not_mem_support_iff.mp hi, zero_smul]
        · contrapose! hni
          simp_rw [not_mem_union, Finsupp.not_mem_support_iff] at hni
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
  simp_rw [Fintype.linearIndependent_iff_injective,
    Injective, Fintype.linearCombination_apply, funext_iff]

/-- A family is linearly independent if and only if all of its finite subfamily is
linearly independent. -/
theorem linearIndependent_iff_finset_linearIndependent :
    LinearIndependent R v ↔ ∀ (s : Finset ι), LinearIndependent R (v ∘ (Subtype.val : s → ι)) :=
  ⟨fun H _ ↦ H.comp _ Subtype.val_injective, fun H ↦ linearIndependent_iff'ₛ.2 fun s f g eq i hi ↦
    Fintype.linearIndependent_iffₛ.1 (H s) (f ∘ Subtype.val) (g ∘ Subtype.val)
      (by simpa only [← s.sum_coe_sort] using eq) ⟨i, hi⟩⟩

theorem LinearIndependent.coe_range (i : LinearIndependent R v) :
    LinearIndependent R ((↑) : range v → M) := by simpa using i.comp _ (rangeSplitting_injective v)

/-- If the image of a family of vectors under a linear map is linearly independent, then so is
the original family. -/
theorem LinearIndependent.of_comp (f : M →ₗ[R] M') (hfv : LinearIndependent R (f ∘ v)) :
    LinearIndependent R v := by
  rw [LinearIndependent, Finsupp.linearCombination_linear_comp, LinearMap.coe_comp] at hfv
  exact hfv.of_comp

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

@[nontriviality]
theorem linearIndependent_of_subsingleton [Subsingleton R] : LinearIndependent R v :=
  linearIndependent_iffₛ.2 fun _l _l' _hl => Subsingleton.elim _ _

theorem linearIndependent_equiv (e : ι ≃ ι') {f : ι' → M} :
    LinearIndependent R (f ∘ e) ↔ LinearIndependent R f :=
  ⟨fun h ↦ comp_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
    fun h ↦ h.comp _ e.injective⟩

theorem linearIndependent_equiv' (e : ι ≃ ι') {f : ι' → M} {g : ι → M} (h : f ∘ e = g) :
    LinearIndependent R g ↔ LinearIndependent R f :=
  h ▸ linearIndependent_equiv e

@[simp]
theorem linearIndepOn_univ : LinearIndepOn R v univ ↔ LinearIndependent R v :=
  linearIndependent_equiv' (Equiv.Set.univ ι) rfl

section Subtype

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/

theorem linearIndependent_comp_subtypeₛ {s : Set ι} :
    LinearIndependent R (v ∘ (↑) : s → M) ↔
      ∀ f ∈ Finsupp.supported R R s, ∀ g ∈ Finsupp.supported R R s,
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g → f = g := by
  simp only [linearIndependent_iffₛ, (· ∘ ·), Finsupp.mem_supported,
    Finsupp.linearCombination_apply, Set.subset_def, Finset.mem_coe]
  refine ⟨fun h l₁ h₁ l₂ h₂ eq ↦ (Finsupp.subtypeDomain_eq_iff h₁ h₂).1 <| h _ _ <|
    (Finsupp.sum_subtypeDomain_index h₁).trans eq ▸ (Finsupp.sum_subtypeDomain_index h₂).symm,
    fun h l₁ l₂ eq ↦ ?_⟩
  refine Finsupp.embDomain_injective (Embedding.subtype s) <| h _ ?_ _ ?_ ?_
  iterate 2 simpa using fun _ h _ ↦ h
  simp_rw [Finsupp.embDomain_eq_mapDomain]
  rwa [Finsupp.sum_mapDomain_index, Finsupp.sum_mapDomain_index] <;>
    intros <;> simp only [zero_smul, add_smul]

theorem linearDependent_comp_subtype'ₛ {s : Set ι} :
    ¬LinearIndependent R (v ∘ (↑) : s → M) ↔
      ∃ f g : ι →₀ R, f ∈ Finsupp.supported R R s ∧ g ∈ Finsupp.supported R R s ∧
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g ∧ f ≠ g := by
  simp [linearIndependent_comp_subtypeₛ, and_left_comm]

/-- A version of `linearDependent_comp_subtype'ₛ` with `Finsupp.linearCombination` unfolded. -/
theorem linearDependent_comp_subtypeₛ {s : Set ι} :
    ¬LinearIndependent R (v ∘ (↑) : s → M) ↔
      ∃ f g : ι →₀ R, f ∈ Finsupp.supported R R s ∧ g ∈ Finsupp.supported R R s ∧
        ∑ i ∈ f.support, f i • v i = ∑ i ∈ g.support, g i • v i ∧ f ≠ g :=
  linearDependent_comp_subtype'ₛ

theorem linearIndependent_subtypeₛ {s : Set M} :
    LinearIndependent R (fun x ↦ x : s → M) ↔
      ∀ f ∈ Finsupp.supported R R s, ∀ g ∈ Finsupp.supported R R s,
        Finsupp.linearCombination R id f = Finsupp.linearCombination R id g → f = g :=
  linearIndependent_comp_subtypeₛ (v := id)

theorem linearIndependent_restrict_iff {s : Set ι} :
    LinearIndependent R (s.restrict v) ↔
      Injective (Finsupp.linearCombinationOn ι M R v s) := by
  simp [LinearIndependent, Finsupp.linearCombination_restrict]

theorem linearIndependent_iff_linearCombinationOnₛ {s : Set M} :
    LinearIndependent R (fun x ↦ x : s → M) ↔
      Injective (Finsupp.linearCombinationOn M M R id s) :=
  linearIndependent_restrict_iff (v := id)

end Subtype

section repr

/-- Canonical isomorphism between linear combinations and the span of linearly independent vectors.
-/
@[simps (config := { rhsMd := default }) symm_apply]
def LinearIndependent.linearCombinationEquiv (hv : LinearIndependent R v) :
    (ι →₀ R) ≃ₗ[R] span R (range v) := by
  refine LinearEquiv.ofBijective (LinearMap.codRestrict (span R (range v))
                                 (Finsupp.linearCombination R v) ?_) ⟨hv.codRestrict _, ?_⟩
  · simp_rw [← Finsupp.range_linearCombination]; exact fun c ↦ ⟨c, rfl⟩
  rw [← LinearMap.range_eq_top, LinearMap.range_eq_map, LinearMap.map_codRestrict,
    ← LinearMap.range_le_iff_comap, range_subtype, Submodule.map_top,
    Finsupp.range_linearCombination]

@[deprecated (since := "2024-08-29")] noncomputable alias LinearIndependent.totalEquiv :=
  LinearIndependent.linearCombinationEquiv

-- Porting note: The original theorem generated by `simps` was
--               different from the theorem on Lean 3, and not simp-normal form.
@[simp]
theorem LinearIndependent.linearCombinationEquiv_apply_coe (hv : LinearIndependent R v)
    (l : ι →₀ R) : hv.linearCombinationEquiv l = Finsupp.linearCombination R v l := rfl

@[deprecated (since := "2024-08-29")] alias LinearIndependent.totalEquiv_apply_coe :=
  LinearIndependent.linearCombinationEquiv_apply_coe
/-- Linear combination representing a vector in the span of linearly independent vectors.

Given a family of linearly independent vectors, we can represent any vector in their span as
a linear combination of these vectors. These are provided by this linear map.
It is simply one direction of `LinearIndependent.linearCombinationEquiv`. -/
def LinearIndependent.repr (hv : LinearIndependent R v) : span R (range v) →ₗ[R] ι →₀ R :=
  hv.linearCombinationEquiv.symm

variable (hv : LinearIndependent R v)

@[simp]
theorem LinearIndependent.linearCombination_repr (x) :
    Finsupp.linearCombination R v (hv.repr x) = x :=
  Subtype.ext_iff.1 (LinearEquiv.apply_symm_apply hv.linearCombinationEquiv x)

@[deprecated (since := "2024-08-29")] alias LinearIndependent.total_repr :=
  LinearIndependent.linearCombination_repr

theorem LinearIndependent.linearCombination_comp_repr :
    (Finsupp.linearCombination R v).comp hv.repr = Submodule.subtype _ :=
  LinearMap.ext <| hv.linearCombination_repr

@[deprecated (since := "2024-08-29")] alias LinearIndependent.total_comp_repr :=
  LinearIndependent.linearCombination_comp_repr

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

theorem LinearIndependent.not_smul_mem_span (hv : LinearIndependent R v) (i : ι) (a : R)
    (ha : a • v i ∈ span R (v '' (univ \ {i}))) : a = 0 := by
  rw [Finsupp.span_image_eq_map_linearCombination, mem_map] at ha
  rcases ha with ⟨l, hl, e⟩
  rw [linearIndependent_iffₛ.1 hv l (Finsupp.single i a) (by simp [e])] at hl
  by_contra hn
  exact (not_mem_of_mem_diff (hl <| by simp [hn])) (mem_singleton _)

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
    specialize p (range w) i'.coe_range (range_comp_subset_range _ _)
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

theorem linearIndependent_iff' :
    LinearIndependent R v ↔
      ∀ s : Finset ι, ∀ g : ι → R, ∑ i ∈ s, g i • v i = 0 → ∀ i ∈ s, g i = 0 := by
  rw [linearIndependent_iff'ₛ]
  refine ⟨fun h s f ↦ ?_, fun h s f g ↦ ?_⟩
  · convert h s f 0; simp_rw [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  · rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    convert h s (f - g) using 3 <;> simp only [Pi.sub_apply, sub_smul, sub_eq_zero]

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

section Subtype

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/

theorem linearIndependent_comp_subtype {s : Set ι} :
    LinearIndependent R (v ∘ (↑) : s → M) ↔
      ∀ l ∈ Finsupp.supported R R s, (Finsupp.linearCombination R v) l = 0 → l = 0 :=
  linearIndependent_comp_subtypeₛ.trans ⟨fun h l hl ↦ h l hl 0 (zero_mem _), fun h f hf g hg eq ↦
    sub_eq_zero.mp (h (f - g) (sub_mem hf hg) <| by rw [map_sub, eq, sub_self])⟩

theorem linearDependent_comp_subtype' {s : Set ι} :
    ¬LinearIndependent R (v ∘ (↑) : s → M) ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ Finsupp.linearCombination R v f = 0 ∧ f ≠ 0 := by
  simp [linearIndependent_comp_subtype, and_left_comm]

/-- A version of `linearDependent_comp_subtype'` with `Finsupp.linearCombination` unfolded. -/
theorem linearDependent_comp_subtype {s : Set ι} :
    ¬LinearIndependent R (v ∘ (↑) : s → M) ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ ∑ i ∈ f.support, f i • v i = 0 ∧ f ≠ 0 :=
  linearDependent_comp_subtype'

theorem linearIndependent_subtype {s : Set M} :
    LinearIndependent R (fun x => x : s → M) ↔
      ∀ l ∈ Finsupp.supported R R s, (Finsupp.linearCombination R id) l = 0 → l = 0 := by
  apply linearIndependent_comp_subtype (v := id)

theorem linearIndependent_comp_subtype_disjoint {s : Set ι} :
    LinearIndependent R (v ∘ (↑) : s → M) ↔
      Disjoint (Finsupp.supported R R s) (LinearMap.ker <| Finsupp.linearCombination R v) := by
  rw [linearIndependent_comp_subtype, LinearMap.disjoint_ker]

theorem linearIndependent_subtype_disjoint {s : Set M} :
    LinearIndependent R (fun x ↦ x : s → M) ↔
      Disjoint (Finsupp.supported R R s) (LinearMap.ker <| Finsupp.linearCombination R id) := by
  apply linearIndependent_comp_subtype_disjoint (v := id)

theorem linearIndependent_iff_linearCombinationOn {s : Set M} :
    LinearIndependent R (fun x ↦ x : s → M) ↔
    (LinearMap.ker <| Finsupp.linearCombinationOn M M R id s) = ⊥ :=
  linearIndependent_iff_linearCombinationOnₛ.trans <|
    LinearMap.ker_eq_bot (M := Finsupp.supported R R s).symm

@[deprecated (since := "2024-08-29")] alias linearIndependent_iff_totalOn :=
  linearIndependent_iff_linearCombinationOn

end Subtype

end Module

/-! ### Properties which require `Ring R` -/


section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

open LinearMap

theorem linearIndependent_iff_not_smul_mem_span :
    LinearIndependent R v ↔ ∀ (i : ι) (a : R), a • v i ∈ span R (v '' (univ \ {i})) → a = 0 :=
  ⟨fun hv ↦ hv.not_smul_mem_span, fun H =>
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
variable {v : ι → V} {s t : Set V} {x y : V}

open Submodule

theorem linearIndependent_iff_not_mem_span :
    LinearIndependent K v ↔ ∀ i, v i ∉ span K (v '' (univ \ {i})) := by
  apply linearIndependent_iff_not_smul_mem_span.trans
  constructor
  · intro h i h_in_span
    apply one_ne_zero (h i 1 (by simp [h_in_span]))
  · intro h i a ha
    by_contra ha'
    exact False.elim (h _ ((smul_mem_iff _ ha').1 ha))

end Module
