/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Linear independence

This file collects basic consequences of linear (in)dependence and includes specialized tests for
specific families of vectors.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `linearIndependent_empty_type`: a family indexed by an empty type is linearly independent;
* `linearIndependent_unique_iff`: if `ι` is a singleton, then `LinearIndependent K v` is
  equivalent to `v default ≠ 0`;
* `linearIndependent_sum`: type-specific test for linear independence of families of vector
  fields;
* `linearIndependent_singleton`: linear independence tests for set operations.

In many cases we additionally provide dot-style operations (e.g., `LinearIndependent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

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

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}
variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring


variable {v : ι → M}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (R) (v)

variable {R v}

/-- A set of linearly independent vectors in a module `M` over a semiring `K` is also linearly
independent over a subring `R` of `K`.

See also `LinearIndependent.restrict_scalars'` for a version with more convenient typeclass
assumptions.

TODO : `LinearIndepOn` version. -/
theorem LinearIndependent.restrict_scalars [Semiring K] [SMulWithZero R K] [Module K M]
    [IsScalarTower R K M] (hinj : Injective fun r : R ↦ r • (1 : K))
    (li : LinearIndependent K v) : LinearIndependent R v := by
  intro x y hxy
  let f := fun r : R => r • (1 : K)
  have := @li (x.mapRange f (by simp [f])) (y.mapRange f (by simp [f])) ?_
  · ext i
    exact hinj congr($this i)
  simpa [Finsupp.linearCombination, f, Finsupp.sum_mapRange_index]

variable (R) in
theorem LinearIndependent.restrict_scalars' [Semiring K] [SMulWithZero R K] [Module K M]
    [IsScalarTower R K M] [FaithfulSMul R K] [IsScalarTower R K K] {v : ι → M}
    (li : LinearIndependent K v) : LinearIndependent R v :=
  restrict_scalars ((faithfulSMul_iff_injective_smul_one R K).mp inferInstance) li

/-- If `v` is an injective family of vectors such that `f ∘ v` is linearly independent, then `v`
    spans a submodule disjoint from the kernel of `f`.
TODO : `LinearIndepOn` version. -/
theorem Submodule.range_ker_disjoint {f : M →ₗ[R] M'}
    (hv : LinearIndependent R (f ∘ v)) :
    Disjoint (span R (range v)) (LinearMap.ker f) := by
  rw [LinearIndependent, Finsupp.linearCombination_linear_comp] at hv
  rw [disjoint_iff_inf_le, ← Set.image_univ, Finsupp.span_image_eq_map_linearCombination,
    map_inf_eq_map_inf_comap, (LinearMap.ker_comp _ _).symm.trans
      (LinearMap.ker_eq_bot_of_injective hv), inf_bot_eq, map_bot]

/-- If `M / R` and `M' / R'` are modules, `i : R' → R` is a map, `j : M →+ M'` is a monoid map,
such that they are both injective, and compatible with the scalar
multiplications on `M` and `M'`, then `j` sends linearly independent families of vectors to
linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map_injOn`.
TODO : `LinearIndepOn` version. -/
theorem LinearIndependent.map_of_injective_injectiveₛ {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R' → R) (j : M →+ M') (hi : Injective i) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) : LinearIndependent R' (j ∘ v) := by
  rw [linearIndependent_iff'ₛ] at hv ⊢
  intro S r₁ r₂ H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
  exact hi <| hv _ _ _ (hj H) s hs

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map,
and `j : M →+ M'` is an injective monoid map, such that the scalar multiplications
on `M` and `M'` are compatible, then `j` sends linearly independent families
of vectors to linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map_injOn`.
TODO : `LinearIndepOn` version. -/
theorem LinearIndependent.map_of_surjective_injectiveₛ {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R → R') (j : M →+ M') (hi : Surjective i) (hj : Injective j)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) : LinearIndependent R' (j ∘ v) := by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine hv.map_of_injective_injectiveₛ i' j (fun _ _ h ↦ ?_) hj fun r m ↦ ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m, hi']

/-- If a linear map is injective on the span of a family of linearly independent vectors, then
the family stays linearly independent after composing with the linear map.
See `LinearIndependent.map` for the version with `Set.InjOn` replaced by `Disjoint`
when working over a ring. -/
theorem LinearIndependent.map_injOn (hv : LinearIndependent R v) (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (Set.range v))) : LinearIndependent R (f ∘ v) :=
  (f.linearIndependent_iff_of_injOn hf_inj).mpr hv

theorem LinearIndepOn.map_injOn (hv : LinearIndepOn R v s) (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (v '' s))) : LinearIndepOn R (f ∘ v) s :=
  (f.linearIndepOn_iff_of_injOn hf_inj).mpr hv

theorem LinearIndepOn.comp_of_image {s : Set ι'} {f : ι' → ι} (h : LinearIndepOn R v (f '' s))
    (hf : InjOn f s) : LinearIndepOn R (v ∘ f) s :=
  LinearIndependent.comp h _ (Equiv.Set.imageOfInjOn _ _ hf).injective

theorem LinearIndepOn.image_of_comp (f : ι → ι') (g : ι' → M) (hs : LinearIndepOn R (g ∘ f) s) :
    LinearIndepOn R g (f '' s) := by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (linearIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs

theorem LinearIndepOn.id_image (hs : LinearIndepOn R v s) : LinearIndepOn R id (v '' s) :=
  LinearIndepOn.image_of_comp v id hs

theorem LinearIndepOn_iff_linearIndepOn_image_injOn [Nontrivial R] :
    LinearIndepOn R v s ↔ LinearIndepOn R id (v '' s) ∧ InjOn v s :=
  ⟨fun h ↦ ⟨h.id_image, h.injOn⟩, fun h ↦ (linearIndepOn_iff_image h.2).2 h.1⟩

theorem linearIndepOn_congr {w : ι → M} (h : EqOn v w s) :
    LinearIndepOn R v s ↔ LinearIndepOn R w s := by
  rw [LinearIndepOn, LinearIndepOn]
  convert Iff.rfl using 2
  ext x
  exact h.symm x.2

theorem LinearIndepOn.congr {w : ι → M} (hli : LinearIndepOn R v s) (h : EqOn v w s) :
    LinearIndepOn R w s :=
  (linearIndepOn_congr h).1 hli

theorem LinearIndependent.group_smul {G : Type*} [hG : Group G] [MulAction G R]
    [SMul G M] [IsScalarTower G R M] [SMulCommClass G R M] {v : ι → M}
    (hv : LinearIndependent R v) (w : ι → G) : LinearIndependent R (w • v) := by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  refine (Group.isUnit (w i)).smul_left_cancel.mp ?_
  refine hv s (fun i ↦ w i • g₁ i) (fun i ↦ w i • g₂ i) (fun i hi ↦ ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_assoc, smul_comm] using hsum

@[simp]
theorem LinearIndependent.group_smul_iff {G : Type*} [hG : Group G] [MulAction G R]
    [MulAction G M] [IsScalarTower G R M] [SMulCommClass G R M] (v : ι → M) (w : ι → G) :
    LinearIndependent R (w • v) ↔ LinearIndependent R v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.group_smul w⟩
  convert h.group_smul (fun i ↦ (w i)⁻¹)
  simp [funext_iff]

-- This lemma cannot be proved with `LinearIndependent.group_smul` since the action of
-- `Rˣ` on `R` is not commutative.
theorem LinearIndependent.units_smul {v : ι → M} (hv : LinearIndependent R v) (w : ι → Rˣ) :
    LinearIndependent R (w • v) := by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  rw [← (w i).mul_left_inj]
  refine hv s (fun i ↦ g₁ i • w i) (fun i ↦ g₂ i • w i) (fun i hi ↦ ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_eq_mul, mul_smul, Pi.smul_apply'] using hsum

@[simp]
theorem LinearIndependent.units_smul_iff (v : ι → M) (w : ι → Rˣ) :
    LinearIndependent R (w • v) ↔ LinearIndependent R v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.units_smul w⟩
  convert h.units_smul (fun i ↦ (w i)⁻¹)
  simp [funext_iff]

theorem linearIndependent_span (hs : LinearIndependent R v) :
    LinearIndependent R (M := span R (range v))
      (fun i : ι ↦ ⟨v i, subset_span (mem_range_self i)⟩) :=
  LinearIndependent.of_comp (span R (range v)).subtype hs

/-- Every finite subset of a linearly independent set is linearly independent. -/
theorem linearIndependent_finset_map_embedding_subtype (s : Set M)
    (li : LinearIndependent R ((↑) : s → M)) (t : Finset s) :
    LinearIndependent R ((↑) : Finset.map (Embedding.subtype s) t → M) :=
  li.comp (fun _ ↦ ⟨_, by aesop⟩) <| by intro; simp

section Indexed

theorem linearIndepOn_of_finite (s : Set ι) (H : ∀ t ⊆ s, Set.Finite t → LinearIndepOn R v t) :
    LinearIndepOn R v s :=
  linearIndepOn_iffₛ.2 fun f hf g hg eq ↦
    linearIndepOn_iffₛ.1 (H _ (union_subset hf hg) <| (Finset.finite_toSet _).union <|
      Finset.finite_toSet _) f Set.subset_union_left g Set.subset_union_right eq

end Indexed

/-- Linear independent families are injective, even if you multiply either side. -/
theorem LinearIndependent.eq_of_smul_apply_eq_smul_apply {M : Type*} [AddCommMonoid M] [Module R M]
    {v : ι → M} (li : LinearIndependent R v) (c d : R) (i j : ι) (hc : c ≠ 0)
    (h : c • v i = d • v j) : i = j := by
  have h_single_eq : Finsupp.single i c = Finsupp.single j d :=
    li <| by simpa [Finsupp.linearCombination_apply] using h
  rcases (Finsupp.single_eq_single_iff ..).mp h_single_eq with (⟨H, _⟩ | ⟨hc, _⟩)
  · exact H
  · contradiction

section Subtype

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/

theorem LinearIndependent.disjoint_span_image (hv : LinearIndependent R v) {s t : Set ι}
    (hs : Disjoint s t) : Disjoint (Submodule.span R <| v '' s) (Submodule.span R <| v '' t) := by
  simp only [disjoint_def, Finsupp.mem_span_image_iff_linearCombination]
  rintro _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, H⟩
  rw [hv.finsuppLinearCombination_injective.eq_iff] at H; subst l₂
  have : l₁ = 0 := Submodule.disjoint_def.mp (Finsupp.disjoint_supported_supported hs) _ hl₁ hl₂
  simp [this]

theorem LinearIndependent.notMem_span_image [Nontrivial R] (hv : LinearIndependent R v) {s : Set ι}
    {x : ι} (h : x ∉ s) : v x ∉ Submodule.span R (v '' s) := by
  have h' : v x ∈ Submodule.span R (v '' {x}) := by
    rw [Set.image_singleton]
    exact mem_span_singleton_self (v x)
  intro w
  apply LinearIndependent.ne_zero x hv
  refine disjoint_def.1 (hv.disjoint_span_image ?_) (v x) h' w
  simpa using h

@[deprecated (since := "2025-05-23")]
alias LinearIndependent.not_mem_span_image := LinearIndependent.notMem_span_image

theorem LinearIndependent.linearCombination_ne_of_notMem_support [Nontrivial R]
    (hv : LinearIndependent R v) {x : ι} (f : ι →₀ R) (h : x ∉ f.support) :
    f.linearCombination R v ≠ v x := by
  replace h : x ∉ (f.support : Set ι) := h
  intro w
  have p : ∀ x ∈ Finsupp.supported R R f.support,
    Finsupp.linearCombination R v x ≠ f.linearCombination R v := by
    simpa [← w, Finsupp.span_image_eq_map_linearCombination] using hv.notMem_span_image h
  exact p f (f.mem_supported_support R) rfl

@[deprecated (since := "2025-05-23")]
alias LinearIndependent.linearCombination_ne_of_not_mem_support :=
  LinearIndependent.linearCombination_ne_of_notMem_support

end Subtype

section union

open LinearMap Finsupp

theorem LinearIndepOn.id_imageₛ {s : Set M} {f : M →ₗ[R] M'} (hs : LinearIndepOn R id s)
    (hf_inj : Set.InjOn f (span R s)) : LinearIndepOn R id (f '' s) :=
  id_image <| hs.map_injOn f (by simpa using hf_inj)

end union

theorem surjective_of_linearIndependent_of_span [Nontrivial R] (hv : LinearIndependent R v)
    (f : ι' ↪ ι) (hss : range v ⊆ span R (range (v ∘ f))) : Surjective f := by
  intro i
  let repr : (span R (range (v ∘ f)) : Type _) → ι' →₀ R := (hv.comp f f.injective).repr
  let l := (repr ⟨v i, hss (mem_range_self i)⟩).mapDomain f
  have h_total_l : Finsupp.linearCombination R v l = v i := by
    dsimp only [l]
    rw [Finsupp.linearCombination_mapDomain]
    rw [(hv.comp f f.injective).linearCombination_repr]
  have h_total_eq : Finsupp.linearCombination R v l = Finsupp.linearCombination R v
       (Finsupp.single i 1) := by
    rw [h_total_l, Finsupp.linearCombination_single, one_smul]
  have l_eq : l = _ := hv h_total_eq
  dsimp only [l] at l_eq
  rw [← Finsupp.embDomain_eq_mapDomain] at l_eq
  rcases Finsupp.single_of_embDomain_single (repr ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq with
    ⟨i', hi'⟩
  use i'
  exact hi'.2

theorem eq_of_linearIndepOn_id_of_span_subtype [Nontrivial R] {s t : Set M}
    (hs : LinearIndepOn R id s) (h : t ⊆ s) (hst : s ⊆ span R t) : s = t := by
  let f : t ↪ s :=
    ⟨fun x => ⟨x.1, h x.2⟩, fun a b hab => Subtype.coe_injective (Subtype.mk.inj hab)⟩
  have h_surj : Surjective f := by
    apply surjective_of_linearIndependent_of_span hs f _
    convert hst <;> simp [f, comp_def]
  change s = t
  apply Subset.antisymm _ h
  intro x hx
  rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩
  convert y.mem
  rw [← Subtype.mk.inj hy]

theorem le_of_span_le_span [Nontrivial R] {s t u : Set M} (hl : LinearIndepOn R id u)
    (hsu : s ⊆ u) (htu : t ⊆ u) (hst : span R s ≤ span R t) : s ⊆ t := by
  have :=
    eq_of_linearIndepOn_id_of_span_subtype (hl.mono (Set.union_subset hsu htu))
      Set.subset_union_right (Set.union_subset (Set.Subset.trans subset_span hst) subset_span)
  rw [← this]; apply Set.subset_union_left

theorem span_le_span_iff [Nontrivial R] {s t u : Set M} (hl : LinearIndependent R ((↑) : u → M))
    (hsu : s ⊆ u) (htu : t ⊆ u) : span R s ≤ span R t ↔ s ⊆ t :=
  ⟨le_of_span_le_span hl hsu htu, span_mono⟩

end Semiring

section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

open Finset in
/-- If `∑ i, f i • v i = ∑ i, g i • v i`, then for all `i`, `f i = g i`. -/
theorem LinearIndependent.eq_coords_of_eq [Fintype ι] {v : ι → M} (hv : LinearIndependent R v)
    {f : ι → R} {g : ι → R} (heq : ∑ i, f i • v i = ∑ i, g i • v i) (i : ι) : f i = g i := by
  rw [← sub_eq_zero, ← sum_sub_distrib] at heq
  simp_rw [← sub_smul] at heq
  exact sub_eq_zero.mp ((linearIndependent_iff'.mp hv) univ (fun i ↦ f i - g i) heq i (mem_univ i))

/-- If `v` is a linearly independent family of vectors and the kernel of a linear map `f` is
disjoint with the submodule spanned by the vectors of `v`, then `f ∘ v` is a linearly independent
family of vectors. See also `LinearIndependent.map'` for a special case assuming `ker f = ⊥`. -/
theorem LinearIndependent.map (hv : LinearIndependent R v) {f : M →ₗ[R] M'}
    (hf_inj : Disjoint (span R (range v)) (LinearMap.ker f)) : LinearIndependent R (f ∘ v) :=
  (f.linearIndependent_iff_of_disjoint hf_inj).mpr hv

/-- An injective linear map sends linearly independent families of vectors to linearly independent
families of vectors. See also `LinearIndependent.map` for a more general statement. -/
theorem LinearIndependent.map' (hv : LinearIndependent R v) (f : M →ₗ[R] M')
    (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ v) :=
  hv.map <| by simp_rw [hf_inj, disjoint_bot_right]

/-- If `M / R` and `M' / R'` are modules, `i : R' → R` is a map, `j : M →+ M'` is a monoid map,
such that they send non-zero elements to non-zero elements, and compatible with the scalar
multiplications on `M` and `M'`, then `j` sends linearly independent families of vectors to
linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map'`. -/
theorem LinearIndependent.map_of_injective_injective {R' M' : Type*}
    [Ring R'] [AddCommGroup M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R' → R) (j : M →+ M') (hi : ∀ r, i r = 0 → r = 0) (hj : ∀ m, j m = 0 → m = 0)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) : LinearIndependent R' (j ∘ v) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro S r' H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
  exact hi _ <| hv _ _ (hj _ H) s hs

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map which maps zero to zero,
`j : M →+ M'` is a monoid map which sends non-zero elements to non-zero elements, such that the
scalar multiplications on `M` and `M'` are compatible, then `j` sends linearly independent families
of vectors to linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map'`. -/
theorem LinearIndependent.map_of_surjective_injective {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R → R') (j : M →+ M') (hi : Surjective i) (hj : ∀ m, j m = 0 → m = 0)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) : LinearIndependent R' (j ∘ v) :=
  hv.map_of_surjective_injectiveₛ i _ hi ((injective_iff_map_eq_zero _).mpr hj) hc

/-- If `f` is an injective linear map, then the family `f ∘ v` is linearly independent
if and only if the family `v` is linearly independent. -/
protected theorem LinearMap.linearIndependent_iff (f : M →ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v :=
  f.linearIndependent_iff_of_disjoint <| by simp_rw [hf_inj, disjoint_bot_right]

/-- See `LinearIndependent.fin_cons` for a family of elements in a vector space. -/
theorem LinearIndependent.fin_cons' {m : ℕ} (x : M) (v : Fin m → M) (hli : LinearIndependent R v)
    (x_ortho : ∀ (c : R) (y : Submodule.span R (Set.range v)), c • x + y = (0 : M) → c = 0) :
    LinearIndependent R (Fin.cons x v : Fin m.succ → M) := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  rintro g total_eq j
  simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at total_eq
  have : g 0 = 0 := by
    refine x_ortho (g 0) ⟨∑ i : Fin m, g i.succ • v i, ?_⟩ total_eq
    exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [this, zero_smul, zero_add] at total_eq
  exact Fin.cases this (hli _ total_eq) j

end Module

/-! ### Properties which require `Ring R` -/


section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

theorem linearIndependent_sum {v : ι ⊕ ι' → M} :
    LinearIndependent R v ↔
      LinearIndependent R (v ∘ Sum.inl) ∧
        LinearIndependent R (v ∘ Sum.inr) ∧
          Disjoint (Submodule.span R (range (v ∘ Sum.inl)))
            (Submodule.span R (range (v ∘ Sum.inr))) := by
  classical
  rw [range_comp v, range_comp v]
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨h.comp _ Sum.inl_injective, h.comp _ Sum.inr_injective, ?_⟩
    exact h.disjoint_span_image <| isCompl_range_inl_range_inr.disjoint
  rintro ⟨hl, hr, hlr⟩
  rw [linearIndependent_iff'] at *
  intro s g hg i hi
  have :
    ((∑ i ∈ s.preimage Sum.inl Sum.inl_injective.injOn, (fun x => g x • v x) (Sum.inl i)) +
        ∑ i ∈ s.preimage Sum.inr Sum.inr_injective.injOn, (fun x => g x • v x) (Sum.inr i)) =
      0 := by
    -- Porting note: `g` must be specified.
    rw [Finset.sum_preimage' (g := fun x => g x • v x),
      Finset.sum_preimage' (g := fun x => g x • v x), ← Finset.sum_union, ← Finset.filter_or]
    · simpa only [← mem_union, range_inl_union_range_inr, mem_univ, Finset.filter_true]
    · exact Finset.disjoint_filter.2 fun x _ hx =>
        disjoint_left.1 isCompl_range_inl_range_inr.disjoint hx
  rw [← eq_neg_iff_add_eq_zero] at this
  rw [disjoint_def'] at hlr
  have A := by
    refine hlr _ (sum_mem fun i _ => ?_) _ (neg_mem <| sum_mem fun i _ => ?_) this
    · exact smul_mem _ _ (subset_span ⟨Sum.inl i, mem_range_self _, rfl⟩)
    · exact smul_mem _ _ (subset_span ⟨Sum.inr i, mem_range_self _, rfl⟩)
  rcases i with i | i
  · exact hl _ _ A i (Finset.mem_preimage.2 hi)
  · rw [this, neg_eq_zero] at A
    exact hr _ _ A i (Finset.mem_preimage.2 hi)

theorem LinearIndependent.sum_type {v' : ι' → M} (hv : LinearIndependent R v)
    (hv' : LinearIndependent R v')
    (h : Disjoint (Submodule.span R (range v)) (Submodule.span R (range v'))) :
    LinearIndependent R (Sum.elim v v') :=
  linearIndependent_sum.2 ⟨hv, hv', h⟩

theorem LinearIndepOn.union {t : Set ι} (hs : LinearIndepOn R v s) (ht : LinearIndepOn R v t)
    (hdj : Disjoint (span R (v '' s)) (span R (v '' t))) : LinearIndepOn R v (s ∪ t) := by
  nontriviality R
  classical
  have hli := LinearIndependent.sum_type hs ht (by rwa [← image_eq_range, ← image_eq_range])
  have hdj := (hdj.of_span₀ hs.zero_notMem_image).of_image
  rw [LinearIndepOn]
  convert (hli.comp _ (Equiv.Set.union hdj).injective) with ⟨x, hx | hx⟩
  · rw [comp_apply, Equiv.Set.union_apply_left _ hx, Sum.elim_inl]
  rw [comp_apply, Equiv.Set.union_apply_right _ hx, Sum.elim_inr]

theorem LinearIndepOn.id_union {s t : Set M} (hs : LinearIndepOn R id s) (ht : LinearIndepOn R id t)
    (hdj : Disjoint (span R s) (span R t)) : LinearIndepOn R id (s ∪ t) :=
  hs.union ht (by simpa)

theorem linearIndepOn_union_iff {t : Set ι} (hdj : Disjoint s t) :
    LinearIndepOn R v (s ∪ t) ↔
    LinearIndepOn R v s ∧ LinearIndepOn R v t ∧ Disjoint (span R (v '' s)) (span R (v '' t)) := by
  refine ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right, ?_⟩,
    fun h ↦ h.1.union h.2.1 h.2.2⟩
  convert h.disjoint_span_image (s := (↑) ⁻¹' s) (t := (↑) ⁻¹' t) (hdj.preimage _) <;>
  aesop

theorem linearIndepOn_id_union_iff {s t : Set M} (hdj : Disjoint s t) :
    LinearIndepOn R id (s ∪ t) ↔
    LinearIndepOn R id s ∧ LinearIndepOn R id t ∧ Disjoint (span R s) (span R t) := by
  rw [linearIndepOn_union_iff hdj, image_id, image_id]

open LinearMap

theorem LinearIndepOn.image {s : Set M} {f : M →ₗ[R] M'}
    (hs : LinearIndepOn R id s) (hf_inj : Disjoint (span R s) (LinearMap.ker f)) :
    LinearIndepOn R id (f '' s) :=
  hs.id_imageₛ <| LinearMap.injOn_of_disjoint_ker le_rfl hf_inj

-- See, for example, Keith Conrad's note [ConradLinearChar]
--  <https://kconrad.math.uconn.edu/blurbs/galoistheory/linearchar.pdf>
/-- Dedekind's linear independence of characters -/
@[stacks 0CKL]
theorem linearIndependent_monoidHom (G : Type*) [MulOneClass G] (L : Type*) [CommRing L]
    [NoZeroDivisors L] : LinearIndependent L (M := G → L) (fun f => f : (G →* L) → G → L) := by
  letI := Classical.decEq (G →* L)
  letI : MulAction L L := DistribMulAction.toMulAction
  -- We prove linear independence by showing that only the trivial linear combination vanishes.
  apply linearIndependent_iff'.2
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
  intro g hg
  -- Here
  -- * `a` is a new character we will insert into the `Finset` of characters `s`,
  -- * `ih` is the fact that only the trivial linear combination of characters in `s` is zero
  -- * `hg` is the fact that `g` are the coefficients of a linear combination summing to zero
  -- and it remains to prove that `g` vanishes on `insert a s`.
  -- We now make the key calculation:
  -- For any character `i` in the original `Finset`, we have `g i • i = g i • a` as functions
  -- on the monoid `G`.
  have h1 (i) (his : i ∈ s) : (g i • i : G → L) = g i • a := by
    ext x
    rw [← sub_eq_zero]
    apply ih (fun j => g j * j x - g j * a x) _ i his
    ext y
    -- After that, it's just a chase scene.
    calc
      (∑ i ∈ s, (g i * i x - g i * a x) • i : G → L) y =
          (∑ i ∈ s, g i * i x * i y) - ∑ i ∈ s, g i * a x * i y := by simp [sub_mul]
      _ = (∑ i ∈ insert a s, g i * i x * i y) -
            ∑ i ∈ insert a s, g i * a x * i y := by simp [Finset.sum_insert has]
      _ = (∑ i ∈ insert a s, g i * (i x * i y)) -
            ∑ i ∈ insert a s, a x * (g i * i y) := by
        congrm ∑ i ∈ insert a s, ?_ - ∑ i ∈ insert a s, ?_
        · rw [mul_assoc]
        · rw [mul_assoc, mul_left_comm]
      _ = (∑ i ∈ insert a s, g i • i : G → L) (x * y) -
            a x * (∑ i ∈ insert a s, (g i • (i : G → L))) y := by simp [Finset.mul_sum]
      _ = 0 := by rw [hg]; simp
  -- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`
  -- there is some element of the monoid on which it differs from `a`.
  have h2 (i) (his : i ∈ s) : ∃ y, i y ≠ a y := by
    by_contra! hia
    obtain rfl : i = a := MonoidHom.ext hia
    contradiction
  -- From these two facts we deduce that `g` actually vanishes on `s`,
  have h3 (i) (his : i ∈ s) : g i = 0 := by
    let ⟨y, hy⟩ := h2 i his
    have h : g i • i y = g i • a y := congr_fun (h1 i his) y
    rw [← sub_eq_zero, ← smul_sub, smul_eq_zero] at h
    exact h.resolve_right (sub_ne_zero_of_ne hy)
  -- And so, using the fact that the linear combination over `s` and over `insert a s` both
  -- vanish, we deduce that `g a = 0`.
  have h4 : g a = 0 :=
    calc
      g a = g a * 1 := (mul_one _).symm
      _ = (g a • a : G → L) 1 := by rw [← a.map_one]; rfl
      _ = (∑ i ∈ insert a s, g i • i : G → L) 1 := by
        rw [Finset.sum_insert has, Finset.sum_eq_zero, add_zero]
        simp +contextual [h3]
      _ = 0 := by rw [hg]; rfl
  -- Now we're done; the last two facts together imply that `g` vanishes on every element
  -- of `insert a s`.
  exact (Finset.forall_mem_insert ..).2 ⟨h4, h3⟩

end Module

section Nontrivial

variable [Ring R] [Nontrivial R] [AddCommGroup M]
variable [Module R M] [NoZeroSMulDivisors R M]
variable {s t : Set M}

theorem linearIndependent_unique_iff (v : ι → M) [Unique ι] :
    LinearIndependent R v ↔ v default ≠ 0 := by
  simp only [linearIndependent_iff, Finsupp.linearCombination_unique, smul_eq_zero]
  refine ⟨fun h hv => ?_, fun hv l hl => Finsupp.unique_ext <| hl.resolve_right hv⟩
  have := h (Finsupp.single default 1) (Or.inr hv)
  exact one_ne_zero (Finsupp.single_eq_zero.1 this)

alias ⟨_, linearIndependent_unique⟩ := linearIndependent_unique_iff

variable (R) in
@[simp]
theorem linearIndepOn_singleton_iff {i : ι} {v : ι → M} : LinearIndepOn R v {i} ↔ v i ≠ 0 :=
  ⟨fun h ↦ h.ne_zero rfl, fun h ↦ linearIndependent_unique _ h⟩

alias ⟨_, LinearIndepOn.singleton⟩ := linearIndepOn_singleton_iff

variable (R) in
theorem LinearIndepOn.id_singleton {x : M} (hx : x ≠ 0) : LinearIndepOn R id {x} :=
  linearIndependent_unique Subtype.val hx

@[simp]
theorem linearIndependent_subsingleton_index_iff [Subsingleton ι] (f : ι → M) :
    LinearIndependent R f ↔ ∀ i, f i ≠ 0 := by
  obtain (he | he) := isEmpty_or_nonempty ι
  · simp [linearIndependent_empty_type]
  obtain ⟨_⟩ := (unique_iff_subsingleton_and_nonempty (α := ι)).2 ⟨by assumption, he⟩
  rw [linearIndependent_unique_iff]
  exact ⟨fun h i ↦ by rwa [Unique.eq_default i], fun h ↦ h _⟩

end Nontrivial
