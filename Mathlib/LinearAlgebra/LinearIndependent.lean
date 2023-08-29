/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.Prod
import Mathlib.SetTheory.Cardinal.Basic

#align_import linear_algebra.linear_independent from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!

# Linear independence

This file defines linear independence in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define `LinearIndependent R v` as `ker (Finsupp.total ι M R v) = ⊥`. Here `Finsupp.total` is the
linear map sending a function `f : ι →₀ R` with finite support to the linear combination of vectors
from `v` with these coefficients. Then we prove that several other statements are equivalent to this
one, including injectivity of `Finsupp.total ι M R v` and some versions with explicitly written
linear combinations.

## Main definitions
All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `LinearIndependent R v` states that the elements of the family `v` are linearly independent.

* `LinearIndependent.repr hv x` returns the linear combination representing `x : span R (range v)`
on the linearly independent vectors `v`, given `hv : LinearIndependent R v`
(using classical choice). `LinearIndependent.repr hv` is provided as a linear map.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `Fintype.linearIndependent_iff`: if `ι` is a finite type, then any function `f : ι → R` has
  finite support, so we can reformulate the statement using `∑ i : ι, f i • v i` instead of a sum
  over an auxiliary `s : Finset ι`;
* `linearIndependent_empty_type`: a family indexed by an empty type is linearly independent;
* `linearIndependent_unique_iff`: if `ι` is a singleton, then `LinearIndependent K v` is
  equivalent to `v default ≠ 0`;
* `linearIndependent_option`, `linearIndependent_sum`, `linearIndependent_fin_cons`,
  `linearIndependent_fin_succ`: type-specific tests for linear independence of families of vector
  fields;
* `linearIndependent_insert`, `linearIndependent_union`, `linearIndependent_pair`,
  `linearIndependent_singleton`: linear independence tests for set operations.

In many cases we additionally provide dot-style operations (e.g., `LinearIndependent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

We also prove that, when working over a division ring,
any family of vectors includes a linear independent subfamily spanning the same subspace.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent.

If you want to use sets, use the family `(fun x ↦ x : s → M)` given a set `s : Set M`. The lemmas
`LinearIndependent.to_subtype_range` and `LinearIndependent.of_subtype_range` connect those two
worlds.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/


noncomputable section

open Function Set Submodule

open BigOperators Cardinal

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*}
variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

section Module

variable {v : ι → M}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']
variable [Module R M] [Module R M'] [Module R M'']
variable {a b : R} {x y : M}
variable (R) (v)

/-- `LinearIndependent R v` states the family of vectors `v` is linearly independent over `R`. -/
def LinearIndependent : Prop :=
  LinearMap.ker (Finsupp.total ι M R v) = ⊥
#align linear_independent LinearIndependent

variable {R} {v}

theorem linearIndependent_iff : LinearIndependent R v ↔ ∀ l, Finsupp.total ι M R v l = 0 → l = 0 :=
  by simp [LinearIndependent, LinearMap.ker_eq_bot']
     -- 🎉 no goals
#align linear_independent_iff linearIndependent_iff

theorem linearIndependent_iff' :
    LinearIndependent R v ↔
      ∀ s : Finset ι, ∀ g : ι → R, ∑ i in s, g i • v i = 0 → ∀ i ∈ s, g i = 0 :=
  linearIndependent_iff.trans
    ⟨fun hf s g hg i his =>
      have h :=
        hf (∑ i in s, Finsupp.single i (g i)) <| by
          simpa only [LinearMap.map_sum, Finsupp.total_single] using hg
          -- 🎉 no goals
      calc
        g i = (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single i (g i)) := by
          { rw [Finsupp.lapply_apply, Finsupp.single_eq_same] }
          -- 🎉 no goals
        _ = ∑ j in s, (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single j (g j)) :=
          Eq.symm <|
            Finset.sum_eq_single i
              (fun j _hjs hji => by rw [Finsupp.lapply_apply, Finsupp.single_eq_of_ne hji])
                                    -- 🎉 no goals
              fun hnis => hnis.elim his
        _ = (∑ j in s, Finsupp.single j (g j)) i :=
          (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R).map_sum.symm
        _ = 0 := FunLike.ext_iff.1 h i
        ,
      fun hf l hl =>
      Finsupp.ext fun i =>
        _root_.by_contradiction fun hni => hni <| hf _ _ hl _ <| Finsupp.mem_support_iff.2 hni⟩
#align linear_independent_iff' linearIndependent_iff'

theorem linearIndependent_iff'' :
    LinearIndependent R v ↔
      ∀ (s : Finset ι) (g : ι → R) (_hg : ∀ (i) (_ : i ∉ s), g i = 0),
        ∑ i in s, g i • v i = 0 → ∀ i, g i = 0 := by
  classical
  exact linearIndependent_iff'.trans
    ⟨fun H s g hg hv i => if his : i ∈ s then H s g hv i his else hg i his, fun H s g hg i hi => by
      convert
        H s (fun j => if j ∈ s then g j else 0) (fun j hj => if_neg hj)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, hg]) i
      exact (if_pos hi).symm⟩
#align linear_independent_iff'' linearIndependent_iff''

theorem not_linearIndependent_iff :
    ¬LinearIndependent R v ↔
      ∃ s : Finset ι, ∃ g : ι → R, ∑ i in s, g i • v i = 0 ∧ ∃ i ∈ s, g i ≠ 0 := by
  rw [linearIndependent_iff']
  -- ⊢ (¬∀ (s : Finset ι) (g : ι → R), ∑ i in s, g i • v i = 0 → ∀ (i : ι), i ∈ s → …
  simp only [exists_prop, not_forall]
  -- 🎉 no goals
#align not_linear_independent_iff not_linearIndependent_iff

theorem Fintype.linearIndependent_iff [Fintype ι] :
    LinearIndependent R v ↔ ∀ g : ι → R, ∑ i, g i • v i = 0 → ∀ i, g i = 0 := by
  refine'
    ⟨fun H g => by simpa using linearIndependent_iff'.1 H Finset.univ g, fun H =>
      linearIndependent_iff''.2 fun s g hg hs i => H _ _ _⟩
  rw [← hs]
  -- ⊢ ∑ i : ι, g i • v i = ∑ i in s, g i • v i
  refine' (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => _).symm
  -- ⊢ g i • v i = 0
  rw [hg i hi, zero_smul]
  -- 🎉 no goals
#align fintype.linear_independent_iff Fintype.linearIndependent_iff

/-- A finite family of vectors `v i` is linear independent iff the linear map that sends
`c : ι → R` to `∑ i, c i • v i` has the trivial kernel. -/
theorem Fintype.linearIndependent_iff' [Fintype ι] [DecidableEq ι] :
    LinearIndependent R v ↔
      LinearMap.ker (LinearMap.lsum R (fun _ ↦ R) ℕ fun i ↦ LinearMap.id.smulRight (v i)) = ⊥ :=
  by simp [Fintype.linearIndependent_iff, LinearMap.ker_eq_bot', funext_iff]
     -- 🎉 no goals
#align fintype.linear_independent_iff' Fintype.linearIndependent_iff'

theorem Fintype.not_linearIndependent_iff [Fintype ι] :
    ¬LinearIndependent R v ↔ ∃ g : ι → R, ∑ i, g i • v i = 0 ∧ ∃ i, g i ≠ 0 := by
  simpa using not_iff_not.2 Fintype.linearIndependent_iff
  -- 🎉 no goals
#align fintype.not_linear_independent_iff Fintype.not_linearIndependent_iff

theorem linearIndependent_empty_type [IsEmpty ι] : LinearIndependent R v :=
  linearIndependent_iff.mpr fun v _hv => Subsingleton.elim v 0
#align linear_independent_empty_type linearIndependent_empty_type

theorem LinearIndependent.ne_zero [Nontrivial R] (i : ι) (hv : LinearIndependent R v) : v i ≠ 0 :=
  fun h =>
  zero_ne_one' R <|
    Eq.symm
      (by
        suffices (Finsupp.single i 1 : ι →₀ R) i = 0 by simpa
        -- ⊢ ↑(Finsupp.single i 1) i = 0
        rw [linearIndependent_iff.1 hv (Finsupp.single i 1)]
        -- ⊢ ↑0 i = 0
        · simp
          -- 🎉 no goals
        · simp [h])
          -- 🎉 no goals
#align linear_independent.ne_zero LinearIndependent.ne_zero

lemma LinearIndependent.eq_zero_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t : R} (h' : s • x + t • y = 0) : s = 0 ∧ t = 0 := by
  have := linearIndependent_iff'.1 h Finset.univ ![s, t]
  -- ⊢ s = 0 ∧ t = 0
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, h',
    Finset.mem_univ, forall_true_left] at this
  exact ⟨this 0, this 1⟩
  -- 🎉 no goals

/-- A subfamily of a linearly independent family (i.e., a composition with an injective map) is a
linearly independent family. -/
theorem LinearIndependent.comp (h : LinearIndependent R v) (f : ι' → ι) (hf : Injective f) :
    LinearIndependent R (v ∘ f) := by
  rw [linearIndependent_iff, Finsupp.total_comp]
  -- ⊢ ∀ (l : ι' →₀ R), ↑(LinearMap.comp (Finsupp.total ι M R v) (Finsupp.lmapDomai …
  intro l hl
  -- ⊢ l = 0
  have h_map_domain : ∀ x, (Finsupp.mapDomain f l) (f x) = 0 := by
    rw [linearIndependent_iff.1 h (Finsupp.mapDomain f l) hl]; simp
  ext x
  -- ⊢ ↑l x = ↑0 x
  convert h_map_domain x
  -- ⊢ ↑l x = ↑(Finsupp.mapDomain f l) (f x)
  rw [Finsupp.mapDomain_apply hf]
  -- 🎉 no goals
#align linear_independent.comp LinearIndependent.comp

theorem LinearIndependent.coe_range (i : LinearIndependent R v) :
    LinearIndependent R ((↑) : range v → M) := by simpa using i.comp _ (rangeSplitting_injective v)
                                                  -- 🎉 no goals
#align linear_independent.coe_range LinearIndependent.coe_range

/-- If `v` is a linearly independent family of vectors and the kernel of a linear map `f` is
disjoint with the submodule spanned by the vectors of `v`, then `f ∘ v` is a linearly independent
family of vectors. See also `LinearIndependent.map'` for a special case assuming `ker f = ⊥`. -/
theorem LinearIndependent.map (hv : LinearIndependent R v) {f : M →ₗ[R] M'}
    (hf_inj : Disjoint (span R (range v)) (LinearMap.ker f)) : LinearIndependent R (f ∘ v) := by
  rw [disjoint_iff_inf_le, ← Set.image_univ, Finsupp.span_image_eq_map_total,
    map_inf_eq_map_inf_comap, map_le_iff_le_comap, comap_bot, Finsupp.supported_univ, top_inf_eq]
      at hf_inj
  unfold LinearIndependent at hv ⊢
  -- ⊢ LinearMap.ker (Finsupp.total ι M' R (↑f ∘ v)) = ⊥
  rw [hv, le_bot_iff] at hf_inj
  -- ⊢ LinearMap.ker (Finsupp.total ι M' R (↑f ∘ v)) = ⊥
  haveI : Inhabited M := ⟨0⟩
  -- ⊢ LinearMap.ker (Finsupp.total ι M' R (↑f ∘ v)) = ⊥
  rw [Finsupp.total_comp, @Finsupp.lmapDomain_total _ _ R _ _ _ _ _ _ _ _ _ _ f, LinearMap.ker_comp,
    hf_inj]
  exact fun _ => rfl
  -- 🎉 no goals
#align linear_independent.map LinearIndependent.map

/-- If `v` is an injective family of vectors such that `f ∘ v` is linearly independent, then `v`
    spans a submodule disjoint from the kernel of `f` -/
theorem Submodule.range_ker_disjoint {f : M →ₗ[R] M'}
    (hv : LinearIndependent R (f ∘ v)) :
    Disjoint (span R (range v)) (LinearMap.ker f) := by
  rw [LinearIndependent, Finsupp.total_comp, Finsupp.lmapDomain_total R _ f (fun _ ↦ rfl),
    LinearMap.ker_comp] at hv
  rw [disjoint_iff_inf_le, ← Set.image_univ, Finsupp.span_image_eq_map_total,
    map_inf_eq_map_inf_comap, hv, inf_bot_eq, map_bot]

/-- An injective linear map sends linearly independent families of vectors to linearly independent
families of vectors. See also `LinearIndependent.map` for a more general statement. -/
theorem LinearIndependent.map' (hv : LinearIndependent R v) (f : M →ₗ[R] M')
    (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ v) :=
  hv.map <| by simp [hf_inj]
               -- 🎉 no goals
#align linear_independent.map' LinearIndependent.map'

/-- If the image of a family of vectors under a linear map is linearly independent, then so is
the original family. -/
theorem LinearIndependent.of_comp (f : M →ₗ[R] M') (hfv : LinearIndependent R (f ∘ v)) :
    LinearIndependent R v :=
  linearIndependent_iff'.2 fun s g hg i his =>
    have : (∑ i : ι in s, g i • f (v i)) = 0 := by
      simp_rw [← f.map_smul, ← f.map_sum, hg, f.map_zero]
      -- 🎉 no goals
    linearIndependent_iff'.1 hfv s g this i his
#align linear_independent.of_comp LinearIndependent.of_comp

/-- If `f` is an injective linear map, then the family `f ∘ v` is linearly independent
if and only if the family `v` is linearly independent. -/
protected theorem LinearMap.linearIndependent_iff (f : M →ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v :=
  ⟨fun h => h.of_comp f, fun h => h.map <| by simp only [hf_inj, disjoint_bot_right]⟩
                                              -- 🎉 no goals
#align linear_map.linear_independent_iff LinearMap.linearIndependent_iff

@[nontriviality]
theorem linearIndependent_of_subsingleton [Subsingleton R] : LinearIndependent R v :=
  linearIndependent_iff.2 fun _l _hl => Subsingleton.elim _ _
#align linear_independent_of_subsingleton linearIndependent_of_subsingleton

theorem linearIndependent_equiv (e : ι ≃ ι') {f : ι' → M} :
    LinearIndependent R (f ∘ e) ↔ LinearIndependent R f :=
  ⟨fun h => Function.comp.right_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective, fun h =>
    h.comp _ e.injective⟩
#align linear_independent_equiv linearIndependent_equiv

theorem linearIndependent_equiv' (e : ι ≃ ι') {f : ι' → M} {g : ι → M} (h : f ∘ e = g) :
    LinearIndependent R g ↔ LinearIndependent R f :=
  h ▸ linearIndependent_equiv e
#align linear_independent_equiv' linearIndependent_equiv'

theorem linearIndependent_subtype_range {ι} {f : ι → M} (hf : Injective f) :
    LinearIndependent R ((↑) : range f → M) ↔ LinearIndependent R f :=
  Iff.symm <| linearIndependent_equiv' (Equiv.ofInjective f hf) rfl
#align linear_independent_subtype_range linearIndependent_subtype_range

alias ⟨LinearIndependent.of_subtype_range, _⟩ := linearIndependent_subtype_range
#align linear_independent.of_subtype_range LinearIndependent.of_subtype_range

theorem linearIndependent_image {ι} {s : Set ι} {f : ι → M} (hf : Set.InjOn f s) :
    (LinearIndependent R fun x : s => f x) ↔ LinearIndependent R fun x : f '' s => (x : M) :=
  linearIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ hf) rfl
#align linear_independent_image linearIndependent_image

theorem linearIndependent_span (hs : LinearIndependent R v) :
    @LinearIndependent ι R (span R (range v)) (fun i : ι => ⟨v i, subset_span (mem_range_self i)⟩) _
      _ _ :=
  LinearIndependent.of_comp (span R (range v)).subtype hs
#align linear_independent_span linearIndependent_span

/-- See `LinearIndependent.fin_cons` for a family of elements in a vector space. -/
theorem LinearIndependent.fin_cons' {m : ℕ} (x : M) (v : Fin m → M) (hli : LinearIndependent R v)
    (x_ortho : ∀ (c : R) (y : Submodule.span R (Set.range v)), c • x + y = (0 : M) → c = 0) :
    LinearIndependent R (Fin.cons x v : Fin m.succ → M) := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  -- ⊢ ∀ (g : Fin (m + 1) → R), ∑ i : Fin (m + 1), g i • Fin.cons x v i = 0 → ∀ (i  …
  rintro g total_eq j
  -- ⊢ g j = 0
  simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at total_eq
  -- ⊢ g j = 0
  have : g 0 = 0 := by
    refine' x_ortho (g 0) ⟨∑ i : Fin m, g i.succ • v i, _⟩ total_eq
    exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [this, zero_smul, zero_add] at total_eq
  -- ⊢ g j = 0
  exact Fin.cases this (hli _ total_eq) j
  -- 🎉 no goals
#align linear_independent.fin_cons' LinearIndependent.fin_cons'

/-- A set of linearly independent vectors in a module `M` over a semiring `K` is also linearly
independent over a subring `R` of `K`.
The implementation uses minimal assumptions about the relationship between `R`, `K` and `M`.
The version where `K` is an `R`-algebra is `LinearIndependent.restrict_scalars_algebras`.
 -/
theorem LinearIndependent.restrict_scalars [Semiring K] [SMulWithZero R K] [Module K M]
    [IsScalarTower R K M] (hinj : Function.Injective fun r : R => r • (1 : K))
    (li : LinearIndependent K v) : LinearIndependent R v := by
  refine' linearIndependent_iff'.mpr fun s g hg i hi => hinj _
  -- ⊢ (fun r => r • 1) (g i) = (fun r => r • 1) 0
  dsimp only; rw [zero_smul]
  -- ⊢ g i • 1 = 0 • 1
              -- ⊢ g i • 1 = 0
  refine' (linearIndependent_iff'.mp li : _) _ (g · • (1:K)) _ i hi
  -- ⊢ ∑ i in s, (fun x => g x • 1) i • v i = 0
  simp_rw [smul_assoc, one_smul]
  -- ⊢ ∑ x in s, g x • v x = 0
  exact hg
  -- 🎉 no goals
#align linear_independent.restrict_scalars LinearIndependent.restrict_scalars

/-- Every finite subset of a linearly independent set is linearly independent. -/
theorem linearIndependent_finset_map_embedding_subtype (s : Set M)
    (li : LinearIndependent R ((↑) : s → M)) (t : Finset s) :
    LinearIndependent R ((↑) : Finset.map (Embedding.subtype s) t → M) := by
  let f : t.map (Embedding.subtype s) → s := fun x =>
    ⟨x.1, by
      obtain ⟨x, h⟩ := x
      rw [Finset.mem_map] at h
      obtain ⟨a, _ha, rfl⟩ := h
      simp only [Subtype.coe_prop, Embedding.coe_subtype]⟩
  convert LinearIndependent.comp li f ?_
  -- ⊢ Injective f
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  -- ⊢ f { val := x, property := hx } = f { val := y, property := hy } → { val := x …
  rw [Finset.mem_map] at hx hy
  -- ⊢ f { val := x, property := hx✝ } = f { val := y, property := hy✝ } → { val := …
  obtain ⟨a, _ha, rfl⟩ := hx
  -- ⊢ f { val := ↑(Embedding.subtype s) a, property := hx } = f { val := y, proper …
  obtain ⟨b, _hb, rfl⟩ := hy
  -- ⊢ f { val := ↑(Embedding.subtype s) a, property := hx } = f { val := ↑(Embeddi …
  simp only [imp_self, Subtype.mk_eq_mk]
  -- 🎉 no goals
#align linear_independent_finset_map_embedding_subtype linearIndependent_finset_map_embedding_subtype

/-- If every finite set of linearly independent vectors has cardinality at most `n`,
then the same is true for arbitrary sets of linearly independent vectors.
-/
theorem linearIndependent_bounded_of_finset_linearIndependent_bounded {n : ℕ}
    (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    ∀ s : Set M, LinearIndependent R ((↑) : s → M) → #s ≤ n := by
  intro s li
  -- ⊢ #↑s ≤ ↑n
  apply Cardinal.card_le_of
  -- ⊢ ∀ (s_1 : Finset ↑s), Finset.card s_1 ≤ n
  intro t
  -- ⊢ Finset.card t ≤ n
  rw [← Finset.card_map (Embedding.subtype s)]
  -- ⊢ Finset.card (Finset.map (Embedding.subtype s) t) ≤ n
  apply H
  -- ⊢ LinearIndependent R fun i => ↑i
  apply linearIndependent_finset_map_embedding_subtype _ li
  -- 🎉 no goals
#align linear_independent_bounded_of_finset_linear_independent_bounded linearIndependent_bounded_of_finset_linearIndependent_bounded

section Subtype

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/


theorem linearIndependent_comp_subtype {s : Set ι} :
    LinearIndependent R (v ∘ (↑) : s → M) ↔
      ∀ l ∈ Finsupp.supported R R s, (Finsupp.total ι M R v) l = 0 → l = 0 := by
  simp only [linearIndependent_iff, (· ∘ ·), Finsupp.mem_supported, Finsupp.total_apply,
    Set.subset_def, Finset.mem_coe]
  constructor
  -- ⊢ (∀ (l : ↑s →₀ R), (Finsupp.sum l fun i a => a • v ↑i) = 0 → l = 0) → ∀ (l :  …
  · intro h l hl₁ hl₂
    -- ⊢ l = 0
    have := h (l.subtypeDomain s) ((Finsupp.sum_subtypeDomain_index hl₁).trans hl₂)
    -- ⊢ l = 0
    exact (Finsupp.subtypeDomain_eq_zero_iff hl₁).1 this
    -- 🎉 no goals
  · intro h l hl
    -- ⊢ l = 0
    refine' Finsupp.embDomain_eq_zero.1 (h (l.embDomain <| Function.Embedding.subtype s) _ _)
    -- ⊢ ∀ (x : ι), x ∈ (Finsupp.embDomain (Embedding.subtype s) l).support → x ∈ s
    · suffices ∀ i hi, ¬l ⟨i, hi⟩ = 0 → i ∈ s by simpa
      -- ⊢ ∀ (i : ι) (hi : i ∈ s), ¬↑l { val := i, property := hi } = 0 → i ∈ s
      intros
      -- ⊢ i✝ ∈ s
      assumption
      -- 🎉 no goals
    · rwa [Finsupp.embDomain_eq_mapDomain, Finsupp.sum_mapDomain_index]
      -- ⊢ ∀ (b : ι), 0 • v b = 0
      exacts [fun _ => zero_smul _ _, fun _ _ _ => add_smul _ _ _]
      -- 🎉 no goals
#align linear_independent_comp_subtype linearIndependent_comp_subtype

theorem linearDependent_comp_subtype' {s : Set ι} :
    ¬LinearIndependent R (v ∘ (↑) : s → M) ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ Finsupp.total ι M R v f = 0 ∧ f ≠ 0 :=
  by simp [linearIndependent_comp_subtype, and_left_comm]
     -- 🎉 no goals
#align linear_dependent_comp_subtype' linearDependent_comp_subtype'

/-- A version of `linearDependent_comp_subtype'` with `Finsupp.total` unfolded. -/
theorem linearDependent_comp_subtype {s : Set ι} :
    ¬LinearIndependent R (v ∘ (↑) : s → M) ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ ∑ i in f.support, f i • v i = 0 ∧ f ≠ 0 :=
  linearDependent_comp_subtype'
#align linear_dependent_comp_subtype linearDependent_comp_subtype

theorem linearIndependent_subtype {s : Set M} :
    LinearIndependent R (fun x => x : s → M) ↔
      ∀ l ∈ Finsupp.supported R R s, (Finsupp.total M M R id) l = 0 → l = 0 :=
  by apply @linearIndependent_comp_subtype _ _ _ id
     -- 🎉 no goals
#align linear_independent_subtype linearIndependent_subtype

theorem linearIndependent_comp_subtype_disjoint {s : Set ι} :
    LinearIndependent R (v ∘ (↑) : s → M) ↔
      Disjoint (Finsupp.supported R R s) (LinearMap.ker $ Finsupp.total ι M R v) :=
  by rw [linearIndependent_comp_subtype, LinearMap.disjoint_ker]
     -- 🎉 no goals
#align linear_independent_comp_subtype_disjoint linearIndependent_comp_subtype_disjoint

theorem linearIndependent_subtype_disjoint {s : Set M} :
    LinearIndependent R (fun x => x : s → M) ↔
      Disjoint (Finsupp.supported R R s) (LinearMap.ker $ Finsupp.total M M R id) :=
  by apply @linearIndependent_comp_subtype_disjoint _ _ _ id
     -- 🎉 no goals
#align linear_independent_subtype_disjoint linearIndependent_subtype_disjoint

theorem linearIndependent_iff_totalOn {s : Set M} :
    LinearIndependent R (fun x => x : s → M) ↔
    (LinearMap.ker $ Finsupp.totalOn M M R id s) = ⊥ := by
  rw [Finsupp.totalOn, LinearMap.ker, LinearMap.comap_codRestrict, Submodule.map_bot, comap_bot,
    LinearMap.ker_comp, linearIndependent_subtype_disjoint, disjoint_iff_inf_le, ←
    map_comap_subtype, map_le_iff_le_comap, comap_bot, ker_subtype, le_bot_iff]
#align linear_independent_iff_total_on linearIndependent_iff_totalOn

theorem LinearIndependent.restrict_of_comp_subtype {s : Set ι}
    (hs : LinearIndependent R (v ∘ (↑) : s → M)) : LinearIndependent R (s.restrict v) :=
  hs
#align linear_independent.restrict_of_comp_subtype LinearIndependent.restrict_of_comp_subtype

variable (R M)

theorem linearIndependent_empty : LinearIndependent R (fun x => x : (∅ : Set M) → M) := by
  simp [linearIndependent_subtype_disjoint]
  -- 🎉 no goals
#align linear_independent_empty linearIndependent_empty

variable {R M}

theorem LinearIndependent.mono {t s : Set M} (h : t ⊆ s) :
    LinearIndependent R (fun x => x : s → M) → LinearIndependent R (fun x => x : t → M) := by
  simp only [linearIndependent_subtype_disjoint]
  -- ⊢ Disjoint (Finsupp.supported R R s) (LinearMap.ker (Finsupp.total M M R id))  …
  exact Disjoint.mono_left (Finsupp.supported_mono h)
  -- 🎉 no goals
#align linear_independent.mono LinearIndependent.mono

theorem linearIndependent_of_finite (s : Set M)
    (H : ∀ (t) (_ : t ⊆ s), Set.Finite t → LinearIndependent R (fun x => x : t → M)) :
    LinearIndependent R (fun x => x : s → M) :=
  linearIndependent_subtype.2 fun l hl =>
    linearIndependent_subtype.1 (H _ hl (Finset.finite_toSet _)) l (Subset.refl _)
#align linear_independent_of_finite linearIndependent_of_finite

theorem linearIndependent_iUnion_of_directed {η : Type*} {s : η → Set M} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, LinearIndependent R (fun x => x : s i → M)) :
    LinearIndependent R (fun x => x : (⋃ i, s i) → M) := by
  by_cases hη : Nonempty η
  -- ⊢ LinearIndependent R fun x => ↑x
  · skip
    -- ⊢ LinearIndependent R fun x => ↑x
    refine' linearIndependent_of_finite (⋃ i, s i) fun t ht ft => _
    -- ⊢ LinearIndependent R fun x => ↑x
    rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
    -- ⊢ LinearIndependent R fun x => ↑x
    rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
    -- ⊢ LinearIndependent R fun x => ↑x
    exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
    -- 🎉 no goals
  · refine (linearIndependent_empty R M).mono (t := iUnion (s ·)) ?_
    -- ⊢ ⋃ (x : η), s x ⊆ ∅
    rintro _ ⟨_, ⟨i, _⟩, _⟩
    -- ⊢ a✝ ∈ ∅
    exact hη ⟨i⟩
    -- 🎉 no goals
#align linear_independent_Union_of_directed linearIndependent_iUnion_of_directed

theorem linearIndependent_sUnion_of_directed {s : Set (Set M)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, LinearIndependent R ((↑) : ((a : Set M) : Type _) → M)) :
    LinearIndependent R (fun x => x : ⋃₀ s → M) := by
  rw [sUnion_eq_iUnion];
  -- ⊢ LinearIndependent R fun x => ↑x
    exact linearIndependent_iUnion_of_directed hs.directed_val (by simpa using h)
    -- 🎉 no goals
#align linear_independent_sUnion_of_directed linearIndependent_sUnion_of_directed

theorem linearIndependent_biUnion_of_directed {η} {s : Set η} {t : η → Set M}
    (hs : DirectedOn (t ⁻¹'o (· ⊆ ·)) s) (h : ∀ a ∈ s, LinearIndependent R (fun x => x : t a → M)) :
    LinearIndependent R (fun x => x : (⋃ a ∈ s, t a) → M) := by
  rw [biUnion_eq_iUnion]
  -- ⊢ LinearIndependent R fun x => ↑x
  exact
    linearIndependent_iUnion_of_directed (directed_comp.2 <| hs.directed_val) (by simpa using h)
#align linear_independent_bUnion_of_directed linearIndependent_biUnion_of_directed

end Subtype

end Module

/-! ### Properties which require `Ring R` -/


section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
variable [Module R M] [Module R M'] [Module R M'']
variable {a b : R} {x y : M}

theorem linearIndependent_iff_injective_total :
    LinearIndependent R v ↔ Function.Injective (Finsupp.total ι M R v) :=
  linearIndependent_iff.trans
    (injective_iff_map_eq_zero (Finsupp.total ι M R v).toAddMonoidHom).symm
#align linear_independent_iff_injective_total linearIndependent_iff_injective_total

alias ⟨LinearIndependent.injective_total, _⟩ := linearIndependent_iff_injective_total
#align linear_independent.injective_total LinearIndependent.injective_total

theorem LinearIndependent.injective [Nontrivial R] (hv : LinearIndependent R v) : Injective v := by
  intro i j hij
  -- ⊢ i = j
  let l : ι →₀ R := Finsupp.single i (1 : R) - Finsupp.single j 1
  -- ⊢ i = j
  have h_total : Finsupp.total ι M R v l = 0 := by
    simp_rw [LinearMap.map_sub, Finsupp.total_apply]
    simp [hij]
  have h_single_eq : Finsupp.single i (1 : R) = Finsupp.single j 1 := by
    rw [linearIndependent_iff] at hv
    simp [eq_add_of_sub_eq' (hv l h_total)]
  simpa [Finsupp.single_eq_single_iff] using h_single_eq
  -- 🎉 no goals
#align linear_independent.injective LinearIndependent.injective

theorem LinearIndependent.to_subtype_range {ι} {f : ι → M} (hf : LinearIndependent R f) :
    LinearIndependent R ((↑) : range f → M) := by
  nontriviality R
  -- ⊢ LinearIndependent R Subtype.val
  exact (linearIndependent_subtype_range hf.injective).2 hf
  -- 🎉 no goals
#align linear_independent.to_subtype_range LinearIndependent.to_subtype_range

theorem LinearIndependent.to_subtype_range' {ι} {f : ι → M} (hf : LinearIndependent R f) {t}
    (ht : range f = t) : LinearIndependent R ((↑) : t → M) :=
  ht ▸ hf.to_subtype_range
#align linear_independent.to_subtype_range' LinearIndependent.to_subtype_range'

theorem LinearIndependent.image_of_comp {ι ι'} (s : Set ι) (f : ι → ι') (g : ι' → M)
    (hs : LinearIndependent R fun x : s => g (f x)) :
    LinearIndependent R fun x : f '' s => g x := by
  nontriviality R
  -- ⊢ LinearIndependent R fun x => g ↑x
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  -- ⊢ LinearIndependent R fun x => g ↑x
  exact (linearIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs
  -- 🎉 no goals
#align linear_independent.image_of_comp LinearIndependent.image_of_comp

theorem LinearIndependent.image {ι} {s : Set ι} {f : ι → M}
    (hs : LinearIndependent R fun x : s => f x) : LinearIndependent R fun x : f '' s => (x : M) :=
  by convert LinearIndependent.image_of_comp s f id hs
     -- 🎉 no goals
#align linear_independent.image LinearIndependent.image

theorem LinearIndependent.group_smul {G : Type*} [hG : Group G] [DistribMulAction G R]
    [DistribMulAction G M] [IsScalarTower G R M] [SMulCommClass G R M] {v : ι → M}
    (hv : LinearIndependent R v) (w : ι → G) : LinearIndependent R (w • v) := by
  rw [linearIndependent_iff''] at hv ⊢
  -- ⊢ ∀ (s : Finset ι) (g : ι → R), (∀ (i : ι), ¬i ∈ s → g i = 0) → ∑ i in s, g i  …
  intro s g hgs hsum i
  -- ⊢ g i = 0
  refine' (smul_eq_zero_iff_eq (w i)).1 _
  -- ⊢ w i • g i = 0
  refine' hv s (fun i => w i • g i) (fun i hi => _) _ i
  -- ⊢ (fun i => w i • g i) i = 0
  · dsimp only
    -- ⊢ w i • g i = 0
    exact (hgs i hi).symm ▸ smul_zero _
    -- 🎉 no goals
  · rw [← hsum, Finset.sum_congr rfl _]
    -- ⊢ ∀ (x : ι), x ∈ s → (fun i => w i • g i) x • v x = g x • (w • v) x
    intros
    -- ⊢ (fun i => w i • g i) x✝ • v x✝ = g x✝ • (w • v) x✝
    erw [Pi.smul_apply, smul_assoc, smul_comm]
    -- 🎉 no goals
#align linear_independent.group_smul LinearIndependent.group_smul

-- This lemma cannot be proved with `LinearIndependent.group_smul` since the action of
-- `Rˣ` on `R` is not commutative.
theorem LinearIndependent.units_smul {v : ι → M} (hv : LinearIndependent R v) (w : ι → Rˣ) :
    LinearIndependent R (w • v) := by
  rw [linearIndependent_iff''] at hv ⊢
  -- ⊢ ∀ (s : Finset ι) (g : ι → R), (∀ (i : ι), ¬i ∈ s → g i = 0) → ∑ i in s, g i  …
  intro s g hgs hsum i
  -- ⊢ g i = 0
  rw [← (w i).mul_left_eq_zero]
  -- ⊢ g i * ↑(w i) = 0
  refine' hv s (fun i => g i • (w i : R)) (fun i hi => _) _ i
  -- ⊢ (fun i => g i • ↑(w i)) i = 0
  · dsimp only
    -- ⊢ g i • ↑(w i) = 0
    exact (hgs i hi).symm ▸ zero_smul _ _
    -- 🎉 no goals
  · rw [← hsum, Finset.sum_congr rfl _]
    -- ⊢ ∀ (x : ι), x ∈ s → (fun i => g i • ↑(w i)) x • v x = g x • (w • v) x
    intros
    -- ⊢ (fun i => g i • ↑(w i)) x✝ • v x✝ = g x✝ • (w • v) x✝
    erw [Pi.smul_apply, smul_assoc]
    -- ⊢ g x✝ • ↑(w x✝) • v x✝ = g x✝ • w x✝ • v x✝
    rfl
    -- 🎉 no goals
#align linear_independent.units_smul LinearIndependent.units_smul

lemma LinearIndependent.eq_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t s' t' : R} (h' : s • x + t • y = s' • x + t' • y) : s = s' ∧ t = t' := by
  have : (s - s') • x + (t - t') • y = 0 := by
    rw [← sub_eq_zero_of_eq h', ← sub_eq_zero]
    simp only [sub_smul]
    abel
  simpa [sub_eq_zero] using h.eq_zero_of_pair this
  -- 🎉 no goals

section Maximal

universe v w

/--
A linearly independent family is maximal if there is no strictly larger linearly independent family.
-/
@[nolint unusedArguments]
def LinearIndependent.Maximal {ι : Type w} {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M]
    [Module R M] {v : ι → M} (_i : LinearIndependent R v) : Prop :=
  ∀ (s : Set M) (_i' : LinearIndependent R ((↑) : s → M)) (_h : range v ≤ s), range v = s
#align linear_independent.maximal LinearIndependent.Maximal

/-- An alternative characterization of a maximal linearly independent family,
quantifying over types (in the same universe as `M`) into which the indexing family injects.
-/
theorem LinearIndependent.maximal_iff {ι : Type w} {R : Type u} [Ring R] [Nontrivial R] {M : Type v}
    [AddCommGroup M] [Module R M] {v : ι → M} (i : LinearIndependent R v) :
    i.Maximal ↔
      ∀ (κ : Type v) (w : κ → M) (_i' : LinearIndependent R w) (j : ι → κ) (_h : w ∘ j = v),
        Surjective j := by
  constructor
  -- ⊢ Maximal i → ∀ (κ : Type v) (w : κ → M), LinearIndependent R w → ∀ (j : ι → κ …
  · rintro p κ w i' j rfl
    -- ⊢ Surjective j
    specialize p (range w) i'.coe_range (range_comp_subset_range _ _)
    -- ⊢ Surjective j
    rw [range_comp, ← @image_univ _ _ w] at p
    -- ⊢ Surjective j
    exact range_iff_surjective.mp (image_injective.mpr i'.injective p)
    -- 🎉 no goals
  · intro p w i' h
    -- ⊢ range v = w
    specialize
      p w ((↑) : w → M) i' (fun i => ⟨v i, range_subset_iff.mp h i⟩)
        (by
          ext
          simp)
    have q := congr_arg (fun s => ((↑) : w → M) '' s) p.range_eq
    -- ⊢ range v = w
    dsimp at q
    -- ⊢ range v = w
    rw [← image_univ, image_image] at q
    -- ⊢ range v = w
    simpa using q
    -- 🎉 no goals
#align linear_independent.maximal_iff LinearIndependent.maximal_iff

end Maximal

/-- Linear independent families are injective, even if you multiply either side. -/
theorem LinearIndependent.eq_of_smul_apply_eq_smul_apply {M : Type*} [AddCommGroup M] [Module R M]
    {v : ι → M} (li : LinearIndependent R v) (c d : R) (i j : ι) (hc : c ≠ 0)
    (h : c • v i = d • v j) : i = j := by
  let l : ι →₀ R := Finsupp.single i c - Finsupp.single j d
  -- ⊢ i = j
  have h_total : Finsupp.total ι M R v l = 0 := by
    simp_rw [LinearMap.map_sub, Finsupp.total_apply]
    simp [h]
  have h_single_eq : Finsupp.single i c = Finsupp.single j d := by
    rw [linearIndependent_iff] at li
    simp [eq_add_of_sub_eq' (li l h_total)]
  rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h_single_eq with (⟨H, _⟩ | ⟨hc, _⟩)
  -- ⊢ i = j
  · exact H
    -- 🎉 no goals
  · contradiction
    -- 🎉 no goals
#align linear_independent.eq_of_smul_apply_eq_smul_apply LinearIndependent.eq_of_smul_apply_eq_smul_apply

section Subtype

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/

theorem LinearIndependent.disjoint_span_image (hv : LinearIndependent R v) {s t : Set ι}
    (hs : Disjoint s t) : Disjoint (Submodule.span R <| v '' s) (Submodule.span R <| v '' t) := by
  simp only [disjoint_def, Finsupp.mem_span_image_iff_total]
  -- ⊢ ∀ (x : M), (∃ l, l ∈ Finsupp.supported R R s ∧ ↑(Finsupp.total ι M R v) l =  …
  rintro _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, H⟩
  -- ⊢ ↑(Finsupp.total ι M R v) l₁ = 0
  rw [hv.injective_total.eq_iff] at H; subst l₂
  -- ⊢ ↑(Finsupp.total ι M R v) l₁ = 0
                                       -- ⊢ ↑(Finsupp.total ι M R v) l₁ = 0
  have : l₁ = 0 := Submodule.disjoint_def.mp (Finsupp.disjoint_supported_supported hs) _ hl₁ hl₂
  -- ⊢ ↑(Finsupp.total ι M R v) l₁ = 0
  simp [this]
  -- 🎉 no goals
#align linear_independent.disjoint_span_image LinearIndependent.disjoint_span_image

theorem LinearIndependent.not_mem_span_image [Nontrivial R] (hv : LinearIndependent R v) {s : Set ι}
    {x : ι} (h : x ∉ s) : v x ∉ Submodule.span R (v '' s) := by
  have h' : v x ∈ Submodule.span R (v '' {x}) := by
    rw [Set.image_singleton]
    exact mem_span_singleton_self (v x)
  intro w
  -- ⊢ False
  apply LinearIndependent.ne_zero x hv
  -- ⊢ v x = 0
  refine' disjoint_def.1 (hv.disjoint_span_image _) (v x) h' w
  -- ⊢ Disjoint {x} s
  simpa using h
  -- 🎉 no goals
#align linear_independent.not_mem_span_image LinearIndependent.not_mem_span_image

theorem LinearIndependent.total_ne_of_not_mem_support [Nontrivial R] (hv : LinearIndependent R v)
    {x : ι} (f : ι →₀ R) (h : x ∉ f.support) : Finsupp.total ι M R v f ≠ v x := by
  replace h : x ∉ (f.support : Set ι) := h
  -- ⊢ ↑(Finsupp.total ι M R v) f ≠ v x
  have p := hv.not_mem_span_image h
  -- ⊢ ↑(Finsupp.total ι M R v) f ≠ v x
  intro w
  -- ⊢ False
  rw [← w] at p
  -- ⊢ False
  rw [Finsupp.span_image_eq_map_total] at p
  -- ⊢ False
  simp only [not_exists, not_and, mem_map] at p -- Porting note: `mem_map` isn't currently triggered
  -- ⊢ False
  exact p f (f.mem_supported_support R) rfl
  -- 🎉 no goals
#align linear_independent.total_ne_of_not_mem_support LinearIndependent.total_ne_of_not_mem_support

theorem linearIndependent_sum {v : Sum ι ι' → M} :
    LinearIndependent R v ↔
      LinearIndependent R (v ∘ Sum.inl) ∧
        LinearIndependent R (v ∘ Sum.inr) ∧
          Disjoint (Submodule.span R (range (v ∘ Sum.inl)))
            (Submodule.span R (range (v ∘ Sum.inr))) := by
  classical
  rw [range_comp v, range_comp v]
  refine' ⟨_, _⟩
  · intro h
    refine' ⟨h.comp _ Sum.inl_injective, h.comp _ Sum.inr_injective, _⟩
    refine' h.disjoint_span_image _
    -- Porting note: `isCompl_range_inl_range_inr.1` timeouts.
    exact IsCompl.disjoint isCompl_range_inl_range_inr
  rintro ⟨hl, hr, hlr⟩
  rw [linearIndependent_iff'] at *
  intro s g hg i hi
  have :
    ((∑ i in s.preimage Sum.inl (Sum.inl_injective.injOn _), (fun x => g x • v x) (Sum.inl i)) +
        ∑ i in s.preimage Sum.inr (Sum.inr_injective.injOn _), (fun x => g x • v x) (Sum.inr i)) =
      0 := by
    -- Porting note: `g` must be specified.
    rw [Finset.sum_preimage' (g := fun x => g x • v x),
      Finset.sum_preimage' (g := fun x => g x • v x), ← Finset.sum_union, ← Finset.filter_or]
    · simpa only [← mem_union, range_inl_union_range_inr, mem_univ, Finset.filter_True]
    · -- Porting note: Here was one `exact`, but timeouted.
      refine Finset.disjoint_filter.2 fun x _ hx =>
        disjoint_left.1 ?_ hx
      exact IsCompl.disjoint isCompl_range_inl_range_inr
  · rw [← eq_neg_iff_add_eq_zero] at this
    rw [disjoint_def'] at hlr
    have A := by
      refine hlr _ (sum_mem fun i _ => ?_) _ (neg_mem <| sum_mem fun i _ => ?_) this
      · exact smul_mem _ _ (subset_span ⟨Sum.inl i, mem_range_self _, rfl⟩)
      · exact smul_mem _ _ (subset_span ⟨Sum.inr i, mem_range_self _, rfl⟩)
    cases' i with i i
    · exact hl _ _ A i (Finset.mem_preimage.2 hi)
    · rw [this, neg_eq_zero] at A
      exact hr _ _ A i (Finset.mem_preimage.2 hi)
#align linear_independent_sum linearIndependent_sum

theorem LinearIndependent.sum_type {v' : ι' → M} (hv : LinearIndependent R v)
    (hv' : LinearIndependent R v')
    (h : Disjoint (Submodule.span R (range v)) (Submodule.span R (range v'))) :
    LinearIndependent R (Sum.elim v v') :=
  linearIndependent_sum.2 ⟨hv, hv', h⟩
#align linear_independent.sum_type LinearIndependent.sum_type

theorem LinearIndependent.union {s t : Set M} (hs : LinearIndependent R (fun x => x : s → M))
    (ht : LinearIndependent R (fun x => x : t → M)) (hst : Disjoint (span R s) (span R t)) :
    LinearIndependent R (fun x => x : ↥(s ∪ t) → M) :=
  (hs.sum_type ht <| by simpa).to_subtype_range' <| by simp
                        -- 🎉 no goals
                                                       -- 🎉 no goals
#align linear_independent.union LinearIndependent.union

theorem linearIndependent_iUnion_finite_subtype {ι : Type*} {f : ι → Set M}
    (hl : ∀ i, LinearIndependent R (fun x => x : f i → M))
    (hd : ∀ i, ∀ t : Set ι, t.Finite → i ∉ t → Disjoint (span R (f i)) (⨆ i ∈ t, span R (f i))) :
    LinearIndependent R (fun x => x : (⋃ i, f i) → M) := by
  classical
  rw [iUnion_eq_iUnion_finset f]
  apply linearIndependent_iUnion_of_directed
  · apply directed_of_sup
    exact fun t₁ t₂ ht => iUnion_mono fun i => iUnion_subset_iUnion_const fun h => ht h
  intro t
  induction' t using Finset.induction_on with i s his ih
  · refine' (linearIndependent_empty R M).mono _
    simp
  · rw [Finset.set_biUnion_insert]
    refine' (hl _).union ih _
    rw [span_iUnion₂]
    exact hd i s s.finite_toSet his
#align linear_independent_Union_finite_subtype linearIndependent_iUnion_finite_subtype

theorem linearIndependent_iUnion_finite {η : Type*} {ιs : η → Type*} {f : ∀ j : η, ιs j → M}
    (hindep : ∀ j, LinearIndependent R (f j))
    (hd : ∀ i, ∀ t : Set η,
      t.Finite → i ∉ t → Disjoint (span R (range (f i))) (⨆ i ∈ t, span R (range (f i)))) :
    LinearIndependent R fun ji : Σ j, ιs j => f ji.1 ji.2 := by
  nontriviality R
  -- ⊢ LinearIndependent R fun ji => f ji.fst ji.snd
  apply LinearIndependent.of_subtype_range
  -- ⊢ Injective fun ji => f ji.fst ji.snd
  · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
    -- ⊢ { fst := x₁, snd := x₂ } = { fst := y₁, snd := y₂ }
    by_cases h_cases : x₁ = y₁
    -- ⊢ { fst := x₁, snd := x₂ } = { fst := y₁, snd := y₂ }
    subst h_cases
    -- ⊢ { fst := x₁, snd := x₂ } = { fst := x₁, snd := y₂ }
    · apply Sigma.eq
      -- ⊢ Eq.recOn ?pos.h₁✝ { fst := x₁, snd := x₂ }.snd = { fst := x₁, snd := y₂ }.snd
      rw [LinearIndependent.injective (hindep _) hxy]
      -- ⊢ { fst := x₁, snd := x₂ }.fst = { fst := x₁, snd := y₂ }.fst
      rfl
      -- 🎉 no goals
    · have h0 : f x₁ x₂ = 0 := by
        apply
          disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁) fun h => h_cases (eq_of_mem_singleton h))
            (f x₁ x₂) (subset_span (mem_range_self _))
        rw [iSup_singleton]
        simp only at hxy
        rw [hxy]
        exact subset_span (mem_range_self y₂)
      exact False.elim ((hindep x₁).ne_zero _ h0)
      -- 🎉 no goals
  rw [range_sigma_eq_iUnion_range]
  -- ⊢ LinearIndependent R Subtype.val
  apply linearIndependent_iUnion_finite_subtype (fun j => (hindep j).to_subtype_range) hd
  -- 🎉 no goals
#align linear_independent_Union_finite linearIndependent_iUnion_finite

end Subtype

section repr

variable (hv : LinearIndependent R v)

/-- Canonical isomorphism between linear combinations and the span of linearly independent vectors.
-/
@[simps (config := { rhsMd := default }) symm_apply]
def LinearIndependent.totalEquiv (hv : LinearIndependent R v) :
    (ι →₀ R) ≃ₗ[R] span R (range v) := by
  apply LinearEquiv.ofBijective (LinearMap.codRestrict (span R (range v)) (Finsupp.total ι M R v) _)
  -- ⊢ Bijective ↑(LinearMap.codRestrict (span R (range v)) (Finsupp.total ι M R v) …
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_codRestrict]
    -- ⊢ LinearMap.ker (Finsupp.total ι M R v) = ⊥
    apply hv
    -- ⊢ ∀ (c : ι →₀ R), ↑(Finsupp.total ι M R v) c ∈ span R (range v)
    · intro l
      -- ⊢ ↑(Finsupp.total ι M R v) l ∈ span R (range v)
      rw [← Finsupp.range_total]
      -- ⊢ ↑(Finsupp.total ι M R v) l ∈ LinearMap.range (Finsupp.total ι M R v)
      rw [LinearMap.mem_range]
      -- ⊢ ∃ y, ↑(Finsupp.total ι M R v) y = ↑(Finsupp.total ι M R v) l
      apply mem_range_self l
      -- 🎉 no goals
  · rw [← LinearMap.range_eq_top, LinearMap.range_eq_map, LinearMap.map_codRestrict, ←
      LinearMap.range_le_iff_comap, range_subtype, Submodule.map_top]
    rw [Finsupp.range_total]
    -- 🎉 no goals
#align linear_independent.total_equiv LinearIndependent.totalEquiv
#align linear_independent.total_equiv_symm_apply LinearIndependent.totalEquiv_symm_apply

-- Porting note: The original theorem generated by `simps` was
--               different from the theorem on Lean 3, and not simp-normal form.
@[simp]
theorem LinearIndependent.totalEquiv_apply_coe (hv : LinearIndependent R v) (l : ι →₀ R) :
    hv.totalEquiv l = Finsupp.total ι M R v l := rfl
#align linear_independent.total_equiv_apply_coe LinearIndependent.totalEquiv_apply_coe

/-- Linear combination representing a vector in the span of linearly independent vectors.

Given a family of linearly independent vectors, we can represent any vector in their span as
a linear combination of these vectors. These are provided by this linear map.
It is simply one direction of `LinearIndependent.total_equiv`. -/
def LinearIndependent.repr (hv : LinearIndependent R v) : span R (range v) →ₗ[R] ι →₀ R :=
  hv.totalEquiv.symm
#align linear_independent.repr LinearIndependent.repr

@[simp]
theorem LinearIndependent.total_repr (x) : Finsupp.total ι M R v (hv.repr x) = x :=
  Subtype.ext_iff.1 (LinearEquiv.apply_symm_apply hv.totalEquiv x)
#align linear_independent.total_repr LinearIndependent.total_repr

theorem LinearIndependent.total_comp_repr :
    (Finsupp.total ι M R v).comp hv.repr = Submodule.subtype _ :=
  LinearMap.ext <| hv.total_repr
#align linear_independent.total_comp_repr LinearIndependent.total_comp_repr

theorem LinearIndependent.repr_ker : LinearMap.ker hv.repr = ⊥ := by
  rw [LinearIndependent.repr, LinearEquiv.ker]
  -- 🎉 no goals
#align linear_independent.repr_ker LinearIndependent.repr_ker

theorem LinearIndependent.repr_range : LinearMap.range hv.repr = ⊤ := by
  rw [LinearIndependent.repr, LinearEquiv.range]
  -- 🎉 no goals
#align linear_independent.repr_range LinearIndependent.repr_range

theorem LinearIndependent.repr_eq {l : ι →₀ R} {x : span R (range v)}
    (eq : Finsupp.total ι M R v l = ↑x) : hv.repr x = l := by
  have :
    ↑((LinearIndependent.totalEquiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l) =
      Finsupp.total ι M R v l :=
    rfl
  have : (LinearIndependent.totalEquiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l = x := by
    rw [eq] at this
    exact Subtype.ext_iff.2 this
  rw [← LinearEquiv.symm_apply_apply hv.totalEquiv l]
  -- ⊢ ↑(repr hv) x = ↑(LinearEquiv.symm (totalEquiv hv)) (↑(totalEquiv hv) l)
  rw [← this]
  -- ⊢ ↑(repr hv) (↑↑(totalEquiv hv) l) = ↑(LinearEquiv.symm (totalEquiv hv)) (↑(to …
  rfl
  -- 🎉 no goals
#align linear_independent.repr_eq LinearIndependent.repr_eq

theorem LinearIndependent.repr_eq_single (i) (x : span R (range v)) (hx : ↑x = v i) :
    hv.repr x = Finsupp.single i 1 := by
  apply hv.repr_eq
  -- ⊢ ↑(Finsupp.total ι M R v) (Finsupp.single i 1) = ↑x
  simp [Finsupp.total_single, hx]
  -- 🎉 no goals
#align linear_independent.repr_eq_single LinearIndependent.repr_eq_single

theorem LinearIndependent.span_repr_eq [Nontrivial R] (x) :
    Span.repr R (Set.range v) x =
      (hv.repr x).equivMapDomain (Equiv.ofInjective _ hv.injective) := by
  have p :
    (Span.repr R (Set.range v) x).equivMapDomain (Equiv.ofInjective _ hv.injective).symm =
      hv.repr x := by
    apply (LinearIndependent.totalEquiv hv).injective
    ext
    simp only [LinearIndependent.totalEquiv_apply_coe, Equiv.self_comp_ofInjective_symm,
      LinearIndependent.total_repr, Finsupp.total_equivMapDomain, Span.finsupp_total_repr]
  ext ⟨_, ⟨i, rfl⟩⟩
  -- ⊢ ↑(Span.repr R (range v) x) { val := v i, property := (_ : ∃ y, v y = v i) }  …
  simp [← p]
  -- 🎉 no goals
#align linear_independent.span_repr_eq LinearIndependent.span_repr_eq

theorem linearIndependent_iff_not_smul_mem_span :
    LinearIndependent R v ↔ ∀ (i : ι) (a : R), a • v i ∈ span R (v '' (univ \ {i})) → a = 0 :=
  ⟨fun hv i a ha => by
    rw [Finsupp.span_image_eq_map_total, mem_map] at ha
    -- ⊢ a = 0
    rcases ha with ⟨l, hl, e⟩
    -- ⊢ a = 0
    rw [sub_eq_zero.1 (linearIndependent_iff.1 hv (l - Finsupp.single i a) (by simp [e]))] at hl
    -- ⊢ a = 0
    by_contra hn
    -- ⊢ False
    exact (not_mem_of_mem_diff (hl <| by simp [hn])) (mem_singleton _), fun H =>
    -- 🎉 no goals
    linearIndependent_iff.2 fun l hl => by
      ext i; simp only [Finsupp.zero_apply]
      -- ⊢ ↑l i = ↑0 i
             -- ⊢ ↑l i = 0
      by_contra hn
      -- ⊢ False
      refine' hn (H i _ _)
      -- ⊢ ↑l i • v i ∈ span R (v '' (univ \ {i}))
      refine' (Finsupp.mem_span_image_iff_total R).2 ⟨Finsupp.single i (l i) - l, _, _⟩
      -- ⊢ Finsupp.single i (↑l i) - l ∈ Finsupp.supported R R (univ \ {i})
      · rw [Finsupp.mem_supported']
        -- ⊢ ∀ (x : ι), ¬x ∈ univ \ {i} → ↑(Finsupp.single i (↑l i) - l) x = 0
        intro j hj
        -- ⊢ ↑(Finsupp.single i (↑l i) - l) j = 0
        have hij : j = i :=
          Classical.not_not.1 fun hij : j ≠ i =>
            hj ((mem_diff _).2 ⟨mem_univ _, fun h => hij (eq_of_mem_singleton h)⟩)
        simp [hij]
        -- 🎉 no goals
      · simp [hl]⟩
        -- 🎉 no goals
#align linear_independent_iff_not_smul_mem_span linearIndependent_iff_not_smul_mem_span

/-- See also `CompleteLattice.independent_iff_linearIndependent_of_ne_zero`. -/
theorem LinearIndependent.independent_span_singleton (hv : LinearIndependent R v) :
    CompleteLattice.Independent fun i => R ∙ v i := by
  refine' CompleteLattice.independent_def.mp fun i => _
  -- ⊢ Disjoint ((fun i => span R {v i}) i) (⨆ (j : ι) (_ : j ≠ i), (fun i => span  …
  rw [disjoint_iff_inf_le]
  -- ⊢ (fun i => span R {v i}) i ⊓ ⨆ (j : ι) (_ : j ≠ i), (fun i => span R {v i}) j …
  intro m hm
  -- ⊢ m ∈ ⊥
  simp only [mem_inf, mem_span_singleton, iSup_subtype', ← span_range_eq_iSup] at hm
  -- ⊢ m ∈ ⊥
  obtain ⟨⟨r, rfl⟩, hm⟩ := hm
  -- ⊢ r • v i ∈ ⊥
  suffices r = 0 by simp [this]
  -- ⊢ r = 0
  apply linearIndependent_iff_not_smul_mem_span.mp hv i
  -- ⊢ r • v i ∈ span R (v '' (univ \ {i}))
  -- Porting note: The original proof was using `convert hm`.
  suffices v '' (univ \ {i}) = range fun j : { j // j ≠ i } => v j by rwa [this]
  -- ⊢ v '' (univ \ {i}) = range fun j => v ↑j
  ext
  -- ⊢ x✝ ∈ v '' (univ \ {i}) ↔ x✝ ∈ range fun j => v ↑j
  simp
  -- 🎉 no goals
#align linear_independent.independent_span_singleton LinearIndependent.independent_span_singleton

variable (R)

theorem exists_maximal_independent' (s : ι → M) :
    ∃ I : Set ι,
      (LinearIndependent R fun x : I => s x) ∧
        ∀ J : Set ι, I ⊆ J → (LinearIndependent R fun x : J => s x) → I = J := by
  let indep : Set ι → Prop := fun I => LinearIndependent R (s ∘ (↑) : I → M)
  -- ⊢ ∃ I, (LinearIndependent R fun x => s ↑x) ∧ ∀ (J : Set ι), I ⊆ J → (LinearInd …
  let X := { I : Set ι // indep I }
  -- ⊢ ∃ I, (LinearIndependent R fun x => s ↑x) ∧ ∀ (J : Set ι), I ⊆ J → (LinearInd …
  let r : X → X → Prop := fun I J => I.1 ⊆ J.1
  -- ⊢ ∃ I, (LinearIndependent R fun x => s ↑x) ∧ ∀ (J : Set ι), I ⊆ J → (LinearInd …
  have key : ∀ c : Set X, IsChain r c → indep (⋃ (I : X) (_ : I ∈ c), I) := by
    intro c hc
    dsimp
    rw [linearIndependent_comp_subtype]
    intro f hsupport hsum
    rcases eq_empty_or_nonempty c with (rfl | hn)
    · simpa using hsupport
    haveI : IsRefl X r := ⟨fun _ => Set.Subset.refl _⟩
    obtain ⟨I, _I_mem, hI⟩ : ∃ I ∈ c, (f.support : Set ι) ⊆ I :=
      hc.directedOn.exists_mem_subset_of_finset_subset_biUnion hn hsupport
    exact linearIndependent_comp_subtype.mp I.2 f hI hsum
  have trans : Transitive r := fun I J K => Set.Subset.trans
  -- ⊢ ∃ I, (LinearIndependent R fun x => s ↑x) ∧ ∀ (J : Set ι), I ⊆ J → (LinearInd …
  obtain ⟨⟨I, hli : indep I⟩, hmax : ∀ a, r ⟨I, hli⟩ a → r a ⟨I, hli⟩⟩ :=
    @exists_maximal_of_chains_bounded _ r
      (fun c hc => ⟨⟨⋃ I ∈ c, (I : Set ι), key c hc⟩, fun I => Set.subset_biUnion_of_mem⟩) @trans
  exact ⟨I, hli, fun J hsub hli => Set.Subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩
  -- 🎉 no goals
#align exists_maximal_independent' exists_maximal_independent'

theorem exists_maximal_independent (s : ι → M) :
    ∃ I : Set ι,
      (LinearIndependent R fun x : I => s x) ∧
        ∀ (i) (_ : i ∉ I), ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I) := by
  classical
    rcases exists_maximal_independent' R s with ⟨I, hIlinind, hImaximal⟩
    use I, hIlinind
    intro i hi
    specialize hImaximal (I ∪ {i}) (by simp)
    set J := I ∪ {i} with hJ
    have memJ : ∀ {x}, x ∈ J ↔ x = i ∨ x ∈ I := by simp [hJ]
    have hiJ : i ∈ J := by simp
    have h := by
      refine mt hImaximal ?_
      · intro h2
        rw [h2] at hi
        exact absurd hiJ hi
    obtain ⟨f, supp_f, sum_f, f_ne⟩ := linearDependent_comp_subtype.mp h
    have hfi : f i ≠ 0 := by
      contrapose hIlinind
      refine' linearDependent_comp_subtype.mpr ⟨f, _, sum_f, f_ne⟩
      simp only [Finsupp.mem_supported, hJ] at supp_f ⊢
      rintro x hx
      refine' (memJ.mp (supp_f hx)).resolve_left _
      rintro rfl
      exact hIlinind (Finsupp.mem_support_iff.mp hx)
    use f i, hfi
    have hfi' : i ∈ f.support := Finsupp.mem_support_iff.mpr hfi
    rw [← Finset.insert_erase hfi', Finset.sum_insert (Finset.not_mem_erase _ _),
      add_eq_zero_iff_eq_neg] at sum_f
    rw [sum_f]
    refine' neg_mem (sum_mem fun c hc => smul_mem _ _ (subset_span ⟨c, _, rfl⟩))
    exact (memJ.mp (supp_f (Finset.erase_subset _ _ hc))).resolve_left (Finset.ne_of_mem_erase hc)
#align exists_maximal_independent exists_maximal_independent

end repr

theorem surjective_of_linearIndependent_of_span [Nontrivial R] (hv : LinearIndependent R v)
    (f : ι' ↪ ι) (hss : range v ⊆ span R (range (v ∘ f))) : Surjective f := by
  intro i
  -- ⊢ ∃ a, ↑f a = i
  let repr : (span R (range (v ∘ f)) : Type _) → ι' →₀ R := (hv.comp f f.injective).repr
  -- ⊢ ∃ a, ↑f a = i
  let l := (repr ⟨v i, hss (mem_range_self i)⟩).mapDomain f
  -- ⊢ ∃ a, ↑f a = i
  have h_total_l : Finsupp.total ι M R v l = v i := by
    dsimp only []
    rw [Finsupp.total_mapDomain]
    rw [(hv.comp f f.injective).total_repr]
    -- Porting note: `rfl` isn't necessary.
  have h_total_eq : (Finsupp.total ι M R v) l = (Finsupp.total ι M R v) (Finsupp.single i 1) := by
    rw [h_total_l, Finsupp.total_single, one_smul]
  have l_eq : l = _ := LinearMap.ker_eq_bot.1 hv h_total_eq
  -- ⊢ ∃ a, ↑f a = i
  dsimp only [] at l_eq
  -- ⊢ ∃ a, ↑f a = i
  rw [← Finsupp.embDomain_eq_mapDomain] at l_eq
  -- ⊢ ∃ a, ↑f a = i
  rcases Finsupp.single_of_embDomain_single (repr ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq with
    ⟨i', hi'⟩
  use i'
  -- ⊢ ↑f i' = i
  exact hi'.2
  -- 🎉 no goals
#align surjective_of_linear_independent_of_span surjective_of_linearIndependent_of_span

theorem eq_of_linearIndependent_of_span_subtype [Nontrivial R] {s t : Set M}
    (hs : LinearIndependent R (fun x => x : s → M)) (h : t ⊆ s) (hst : s ⊆ span R t) : s = t := by
  let f : t ↪ s :=
    ⟨fun x => ⟨x.1, h x.2⟩, fun a b hab => Subtype.coe_injective (Subtype.mk.inj hab)⟩
  have h_surj : Surjective f := by
    apply surjective_of_linearIndependent_of_span hs f _
    convert hst <;> simp [comp]
  show s = t
  -- ⊢ s = t
  · apply Subset.antisymm _ h
    -- ⊢ s ⊆ t
    intro x hx
    -- ⊢ x ∈ t
    rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩
    -- ⊢ x ∈ t
    convert y.mem
    -- ⊢ x = ↑y
    rw [← Subtype.mk.inj hy]
    -- 🎉 no goals
#align eq_of_linear_independent_of_span_subtype eq_of_linearIndependent_of_span_subtype

open LinearMap

theorem LinearIndependent.image_subtype {s : Set M} {f : M →ₗ[R] M'}
    (hs : LinearIndependent R (fun x => x : s → M))
    (hf_inj : Disjoint (span R s) (LinearMap.ker f)) :
    LinearIndependent R (fun x => x : f '' s → M') := by
  rw [← @Subtype.range_coe _ s] at hf_inj
  -- ⊢ LinearIndependent R fun x => ↑x
  refine' (hs.map hf_inj).to_subtype_range' _
  -- ⊢ Set.range (↑f ∘ fun x => ↑x) = ↑f '' s
  simp [Set.range_comp f]
  -- 🎉 no goals
#align linear_independent.image_subtype LinearIndependent.image_subtype

theorem LinearIndependent.inl_union_inr {s : Set M} {t : Set M'}
    (hs : LinearIndependent R (fun x => x : s → M))
    (ht : LinearIndependent R (fun x => x : t → M')) :
    LinearIndependent R (fun x => x : ↥(inl R M M' '' s ∪ inr R M M' '' t) → M × M') := by
  refine' (hs.image_subtype _).union (ht.image_subtype _) _ <;> [simp; simp; skip]
  -- ⊢ Disjoint (span R (↑(inl R M M') '' s)) (span R (↑(inr R M M') '' t))
  simp only [span_image]
  -- ⊢ Disjoint (Submodule.map (inl R M M') (span R s)) (Submodule.map (inr R M M') …
  simp [disjoint_iff, prod_inf_prod]
  -- 🎉 no goals
#align linear_independent.inl_union_inr LinearIndependent.inl_union_inr

theorem linearIndependent_inl_union_inr' {v : ι → M} {v' : ι' → M'} (hv : LinearIndependent R v)
    (hv' : LinearIndependent R v') :
    LinearIndependent R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) :=
  (hv.map' (inl R M M') ker_inl).sum_type (hv'.map' (inr R M M') ker_inr) <| by
    refine' isCompl_range_inl_inr.disjoint.mono _ _ <;>
    -- ⊢ span R (Set.range (↑(inl R M M') ∘ v)) ≤ LinearMap.range (inl R M M')
      simp only [span_le, range_coe, range_comp_subset_range]
      -- 🎉 no goals
      -- 🎉 no goals
#align linear_independent_inl_union_inr' linearIndependent_inl_union_inr'

-- See, for example, Keith Conrad's note
--  <https://kconrad.math.uconn.edu/blurbs/galoistheory/linearchar.pdf>
/-- Dedekind's linear independence of characters -/
theorem linearIndependent_monoidHom (G : Type*) [Monoid G] (L : Type*) [CommRing L]
    [NoZeroDivisors L] : @LinearIndependent _ L (G → L) (fun f => f : (G →* L) → G → L) _ _ _ := by
  -- Porting note: Some casts are required.
  letI := Classical.decEq (G →* L);
  -- ⊢ LinearIndependent L fun f => ↑f
  letI : MulAction L L := DistribMulAction.toMulAction;
  -- ⊢ LinearIndependent L fun f => ↑f
  -- We prove linear independence by showing that only the trivial linear combination vanishes.
  exact linearIndependent_iff'.2
    -- To do this, we use `Finset` induction,
    -- Porting note: `False.elim` → `fun h => False.elim <| Finset.not_mem_empty _ h`
    fun s =>
      Finset.induction_on s
        (fun g _hg i h => False.elim <| Finset.not_mem_empty _ h) fun a s has ih g hg =>
        -- Here
        -- * `a` is a new character we will insert into the `Finset` of characters `s`,
        -- * `ih` is the fact that only the trivial linear combination of characters in `s` is zero
        -- * `hg` is the fact that `g` are the coefficients of a linear combination summing to zero
        -- and it remains to prove that `g` vanishes on `insert a s`.
        -- We now make the key calculation:
        -- For any character `i` in the original `Finset`, we have `g i • i = g i • a` as functions
        -- on the monoid `G`.
        have h1 : ∀ i ∈ s, (g i • (i : G → L)) = g i • (a : G → L) := fun i his =>
          funext fun x : G =>
            -- We prove these expressions are equal by showing
            -- the differences of their values on each monoid element `x` is zero
            eq_of_sub_eq_zero <|
            ih (fun j => g j * j x - g j * a x)
              (funext fun y : G => calc
                -- After that, it's just a chase scene.
                (∑ i in s, ((g i * i x - g i * a x) • (i : G → L))) y =
                    ∑ i in s, (g i * i x - g i * a x) * i y :=
                  Finset.sum_apply _ _ _
                _ = ∑ i in s, (g i * i x * i y - g i * a x * i y) :=
                  Finset.sum_congr rfl fun _ _ => sub_mul _ _ _
                _ = (∑ i in s, g i * i x * i y) - ∑ i in s, g i * a x * i y :=
                  Finset.sum_sub_distrib
                _ =
                    (g a * a x * a y + ∑ i in s, g i * i x * i y) -
                      (g a * a x * a y + ∑ i in s, g i * a x * i y) :=
                  by rw [add_sub_add_left_eq_sub]
                _ =
                    (∑ i in insert a s, g i * i x * i y) -
                      ∑ i in insert a s, g i * a x * i y :=
                  by rw [Finset.sum_insert has, Finset.sum_insert has]
                _ =
                    (∑ i in insert a s, g i * i (x * y)) -
                      ∑ i in insert a s, a x * (g i * i y) :=
                  congr
                    (congr_arg Sub.sub
                      (Finset.sum_congr rfl fun i _ => by rw [i.map_mul, mul_assoc]))
                    (Finset.sum_congr rfl fun _ _ => by rw [mul_assoc, mul_left_comm])
                _ =
                    (∑ i in insert a s, (g i • (i : G → L))) (x * y) -
                      a x * (∑ i in insert a s, (g i • (i : G → L))) y :=
                  by rw [Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]; rfl
                _ = 0 - a x * 0 := by rw [hg]; rfl
                _ = 0 := by rw [mul_zero, sub_zero]
                )
              i his
        -- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`
        -- there is some element of the monoid on which it differs from `a`.
        have h2 : ∀ i : G →* L, i ∈ s → ∃ y, i y ≠ a y := fun i his =>
          Classical.by_contradiction fun h =>
            have hia : i = a := MonoidHom.ext fun y =>
              Classical.by_contradiction fun hy => h ⟨y, hy⟩
            has <| hia ▸ his
        -- From these two facts we deduce that `g` actually vanishes on `s`,
        have h3 : ∀ i ∈ s, g i = 0 := fun i his =>
          let ⟨y, hy⟩ := h2 i his
          have h : g i • i y = g i • a y := congr_fun (h1 i his) y
          Or.resolve_right (mul_eq_zero.1 <| by rw [mul_sub, sub_eq_zero]; exact h)
            (sub_ne_zero_of_ne hy)
        -- And so, using the fact that the linear combination over `s` and over `insert a s` both
        -- vanish, we deduce that `g a = 0`.
        have h4 : g a = 0 :=
          calc
            g a = g a * 1 := (mul_one _).symm
            _ = (g a • (a : G → L)) 1 := by rw [← a.map_one]; rfl
            _ = (∑ i in insert a s, (g i • (i : G → L))) 1 := by
              rw [Finset.sum_eq_single a]
              · intro i his hia
                rw [Finset.mem_insert] at his
                rw [h3 i (his.resolve_left hia), zero_smul]
              · intro haas
                exfalso
                apply haas
                exact Finset.mem_insert_self a s
            _ = 0 := by rw [hg]; rfl
        -- Now we're done; the last two facts together imply that `g` vanishes on every element
        -- of `insert a s`.
        (Finset.forall_mem_insert _ _ _).2 ⟨h4, h3⟩
#align linear_independent_monoid_hom linearIndependent_monoidHom

theorem le_of_span_le_span [Nontrivial R] {s t u : Set M} (hl : LinearIndependent R ((↑) : u → M))
    (hsu : s ⊆ u) (htu : t ⊆ u) (hst : span R s ≤ span R t) : s ⊆ t := by
  have :=
    eq_of_linearIndependent_of_span_subtype (hl.mono (Set.union_subset hsu htu))
      (Set.subset_union_right _ _) (Set.union_subset (Set.Subset.trans subset_span hst) subset_span)
  rw [← this]; apply Set.subset_union_left
  -- ⊢ s ⊆ s ∪ t
               -- 🎉 no goals
#align le_of_span_le_span le_of_span_le_span

theorem span_le_span_iff [Nontrivial R] {s t u : Set M} (hl : LinearIndependent R ((↑) : u → M))
    (hsu : s ⊆ u) (htu : t ⊆ u) : span R s ≤ span R t ↔ s ⊆ t :=
  ⟨le_of_span_le_span hl hsu htu, span_mono⟩
#align span_le_span_iff span_le_span_iff

end Module

section Nontrivial

variable [Ring R] [Nontrivial R] [AddCommGroup M] [AddCommGroup M']

variable [Module R M] [NoZeroSMulDivisors R M] [Module R M']

variable {v : ι → M} {s t : Set M} {x y z : M}

theorem linearIndependent_unique_iff (v : ι → M) [Unique ι] :
    LinearIndependent R v ↔ v default ≠ 0 := by
  simp only [linearIndependent_iff, Finsupp.total_unique, smul_eq_zero]
  -- ⊢ (∀ (l : ι →₀ R), ↑l default = 0 ∨ v default = 0 → l = 0) ↔ v default ≠ 0
  refine' ⟨fun h hv => _, fun hv l hl => Finsupp.unique_ext <| hl.resolve_right hv⟩
  -- ⊢ False
  have := h (Finsupp.single default 1) (Or.inr hv)
  -- ⊢ False
  exact one_ne_zero (Finsupp.single_eq_zero.1 this)
  -- 🎉 no goals
#align linear_independent_unique_iff linearIndependent_unique_iff

alias ⟨_, linearIndependent_unique⟩ := linearIndependent_unique_iff
#align linear_independent_unique linearIndependent_unique

theorem linearIndependent_singleton {x : M} (hx : x ≠ 0) :
    LinearIndependent R (fun x => x : ({x} : Set M) → M) :=
  linearIndependent_unique ((↑) : ({x} : Set M) → M) hx
#align linear_independent_singleton linearIndependent_singleton

end Nontrivial

/-!
### Properties which require `DivisionRing K`

These can be considered generalizations of properties of linear independence in vector spaces.
-/


section Module

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V']

variable [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

open Submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type class) -/
theorem mem_span_insert_exchange :
    x ∈ span K (insert y s) → x ∉ span K s → y ∈ span K (insert x s) := by
  simp [mem_span_insert]
  -- ⊢ ∀ (x_1 : K) (x_2 : V), x_2 ∈ span K s → x = x_1 • y + x_2 → ¬x ∈ span K s →  …
  rintro a z hz rfl h
  -- ⊢ ∃ a_1 z_1, z_1 ∈ span K s ∧ y = a_1 • (a • y + z) + z_1
  refine' ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, _⟩
  -- ⊢ y = a⁻¹ • (a • y + z) + -a⁻¹ • z
  have a0 : a ≠ 0 := by
    rintro rfl
    simp_all
  simp [a0, smul_add, smul_smul]
  -- 🎉 no goals
#align mem_span_insert_exchange mem_span_insert_exchange

theorem linearIndependent_iff_not_mem_span :
    LinearIndependent K v ↔ ∀ i, v i ∉ span K (v '' (univ \ {i})) := by
  apply linearIndependent_iff_not_smul_mem_span.trans
  -- ⊢ (∀ (i : ι) (a : K), a • v i ∈ span K (v '' (univ \ {i})) → a = 0) ↔ ∀ (i : ι …
  constructor
  -- ⊢ (∀ (i : ι) (a : K), a • v i ∈ span K (v '' (univ \ {i})) → a = 0) → ∀ (i : ι …
  · intro h i h_in_span
    -- ⊢ False
    apply one_ne_zero (h i 1 (by simp [h_in_span]))
    -- 🎉 no goals
  · intro h i a ha
    -- ⊢ a = 0
    by_contra ha'
    -- ⊢ False
    exact False.elim (h _ ((smul_mem_iff _ ha').1 ha))
    -- 🎉 no goals
#align linear_independent_iff_not_mem_span linearIndependent_iff_not_mem_span

protected theorem LinearIndependent.insert (hs : LinearIndependent K (fun b => b : s → V))
    (hx : x ∉ span K s) : LinearIndependent K (fun b => b : ↥(insert x s) → V) := by
  rw [← union_singleton]
  -- ⊢ LinearIndependent K fun b => ↑b
  have x0 : x ≠ 0 := mt (by rintro rfl; apply zero_mem (span K s)) hx
  -- ⊢ LinearIndependent K fun b => ↑b
  apply hs.union (linearIndependent_singleton x0)
  -- ⊢ Disjoint (span K s) (span K {x})
  rwa [disjoint_span_singleton' x0]
  -- 🎉 no goals
#align linear_independent.insert LinearIndependent.insert

theorem linearIndependent_option' :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  -- Porting note: Explicit universe level is required in `Equiv.optionEquivSumPUnit`.
  rw [← linearIndependent_equiv (Equiv.optionEquivSumPUnit.{_, u'} ι).symm, linearIndependent_sum,
    @range_unique _ PUnit, @linearIndependent_unique_iff PUnit, disjoint_span_singleton]
  dsimp [(· ∘ ·)]
  -- ⊢ (LinearIndependent K fun x => v x) ∧ ¬x = 0 ∧ (x ∈ span K (range fun x => v  …
  refine' ⟨fun h => ⟨h.1, fun hx => h.2.1 <| h.2.2 hx⟩, fun h => ⟨h.1, _, fun hx => (h.2 hx).elim⟩⟩
  -- ⊢ ¬x = 0
  rintro rfl
  -- ⊢ False
  exact h.2 (zero_mem _)
  -- 🎉 no goals
#align linear_independent_option' linearIndependent_option'

theorem LinearIndependent.option (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) :=
  linearIndependent_option'.2 ⟨hv, hx⟩
#align linear_independent.option LinearIndependent.option

theorem linearIndependent_option {v : Option ι → V} :
    LinearIndependent K v ↔
      LinearIndependent K (v ∘ (↑) : ι → V) ∧ v none ∉ Submodule.span K (range (v ∘ (↑) : ι → V)) :=
  by simp only [← linearIndependent_option', Option.casesOn'_none_coe]
     -- 🎉 no goals
#align linear_independent_option linearIndependent_option

theorem linearIndependent_insert' {ι} {s : Set ι} {a : ι} {f : ι → V} (has : a ∉ s) :
    (LinearIndependent K fun x : ↥(insert a s) => f x) ↔
      (LinearIndependent K fun x : s => f x) ∧ f a ∉ Submodule.span K (f '' s) := by
  classical
  rw [← linearIndependent_equiv ((Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm),
    linearIndependent_option]
  -- Porting note: `simp [(· ∘ ·), range_comp f]` → `simp [(· ∘ ·)]; erw [range_comp f ..]; simp`
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  simp only [(· ∘ ·)]
  erw [range_comp f ((↑) : s → ι)]
  simp
#align linear_independent_insert' linearIndependent_insert'

theorem linearIndependent_insert (hxs : x ∉ s) :
    (LinearIndependent K fun b : ↥(insert x s) => (b : V)) ↔
      (LinearIndependent K fun b : s => (b : V)) ∧ x ∉ Submodule.span K s :=
  (@linearIndependent_insert' _ _ _ _ _ _ _ _ id hxs).trans <| by simp
                                                                  -- 🎉 no goals
#align linear_independent_insert linearIndependent_insert

theorem linearIndependent_pair {x y : V} (hx : x ≠ 0) (hy : ∀ a : K, a • x ≠ y) :
    LinearIndependent K ((↑) : ({x, y} : Set V) → V) :=
  pair_comm y x ▸ (linearIndependent_singleton hx).insert <|
    mt mem_span_singleton.1 (not_exists.2 hy)
#align linear_independent_pair linearIndependent_pair

theorem linearIndependent_fin_cons {n} {v : Fin n → V} :
    LinearIndependent K (Fin.cons x v : Fin (n + 1) → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  rw [← linearIndependent_equiv (finSuccEquiv n).symm, linearIndependent_option]
  -- ⊢ LinearIndependent K ((Fin.cons x v ∘ ↑(finSuccEquiv n).symm) ∘ some) ∧ ¬(Fin …
  -- Porting note: `convert Iff.rfl; ...` → `exact Iff.rfl`
  exact Iff.rfl
  -- 🎉 no goals
#align linear_independent_fin_cons linearIndependent_fin_cons

theorem linearIndependent_fin_snoc {n} {v : Fin n → V} :
    LinearIndependent K (Fin.snoc v x : Fin (n + 1) → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  -- Porting note: `rw` → `erw`
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  -- Here Lean can not see that `fun i ↦ Fin.cons x v (↑(finRotate (n + 1)) i)`
  -- matches with `?f ∘ ↑(finRotate (n + 1))`.
  erw [Fin.snoc_eq_cons_rotate, linearIndependent_equiv, linearIndependent_fin_cons]
  -- 🎉 no goals
#align linear_independent_fin_snoc linearIndependent_fin_snoc

/-- See `LinearIndependent.fin_cons'` for an uglier version that works if you
only have a module over a semiring. -/
theorem LinearIndependent.fin_cons {n} {v : Fin n → V} (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) : LinearIndependent K (Fin.cons x v : Fin (n + 1) → V) :=
  linearIndependent_fin_cons.2 ⟨hv, hx⟩
#align linear_independent.fin_cons LinearIndependent.fin_cons

theorem linearIndependent_fin_succ {n} {v : Fin (n + 1) → V} :
    LinearIndependent K v ↔
      LinearIndependent K (Fin.tail v) ∧ v 0 ∉ Submodule.span K (range <| Fin.tail v) :=
  by rw [← linearIndependent_fin_cons, Fin.cons_self_tail]
     -- 🎉 no goals
#align linear_independent_fin_succ linearIndependent_fin_succ

theorem linearIndependent_fin_succ' {n} {v : Fin (n + 1) → V} :
    LinearIndependent K v ↔
      LinearIndependent K (Fin.init v) ∧ v (Fin.last _) ∉ Submodule.span K (range <| Fin.init v) :=
  by rw [← linearIndependent_fin_snoc, Fin.snoc_init_self]
     -- 🎉 no goals
#align linear_independent_fin_succ' linearIndependent_fin_succ'

theorem linearIndependent_fin2 {f : Fin 2 → V} :
    LinearIndependent K f ↔ f 1 ≠ 0 ∧ ∀ a : K, a • f 1 ≠ f 0 := by
  rw [linearIndependent_fin_succ, linearIndependent_unique_iff, range_unique, mem_span_singleton,
    not_exists, show Fin.tail f default = f 1 by rw [← Fin.succ_zero_eq_one]; rfl]
#align linear_independent_fin2 linearIndependent_fin2

theorem exists_linearIndependent_extension (hs : LinearIndependent K ((↑) : s → V)) (hst : s ⊆ t) :
    ∃ (b : _) (_ : b ⊆ t), s ⊆ b ∧ t ⊆ span K b ∧ LinearIndependent K ((↑) : b → V) := by
  -- Porting note: The placeholder should be solved before `rcases`.
  have := by
    refine zorn_subset_nonempty { b | b ⊆ t ∧ LinearIndependent K ((↑) : b → V) } ?_ _ ⟨hst, hs⟩
    · refine' fun c hc cc _c0 => ⟨⋃₀ c, ⟨_, _⟩, fun x => _⟩
      · exact sUnion_subset fun x xc => (hc xc).1
      · exact linearIndependent_sUnion_of_directed cc.directedOn fun x xc => (hc xc).2
      · exact subset_sUnion_of_mem
  rcases this with
    ⟨b, ⟨bt, bi⟩, sb, h⟩
  · refine' ⟨b, bt, sb, fun x xt => _, bi⟩
    -- ⊢ x ∈ ↑(span K b)
    by_contra hn
    -- ⊢ False
    apply hn
    -- ⊢ x ∈ ↑(span K b)
    rw [← h _ ⟨insert_subset_iff.2 ⟨xt, bt⟩, bi.insert hn⟩ (subset_insert _ _)]
    -- ⊢ x ∈ ↑(span K (insert x b))
    exact subset_span (mem_insert _ _)
    -- 🎉 no goals
#align exists_linear_independent_extension exists_linearIndependent_extension

variable (K t)

theorem exists_linearIndependent :
    ∃ (b : _) (_ : b ⊆ t), span K b = span K t ∧ LinearIndependent K ((↑) : b → V) := by
  obtain ⟨b, hb₁, -, hb₂, hb₃⟩ :=
    exists_linearIndependent_extension (linearIndependent_empty K V) (Set.empty_subset t)
  exact ⟨b, hb₁, (span_eq_of_le _ hb₂ (Submodule.span_mono hb₁)).symm, hb₃⟩
  -- 🎉 no goals
#align exists_linear_independent exists_linearIndependent

variable {K t}

/-- `LinearIndependent.extend` adds vectors to a linear independent set `s ⊆ t` until it spans
all elements of `t`. -/
noncomputable def LinearIndependent.extend (hs : LinearIndependent K (fun x => x : s → V))
    (hst : s ⊆ t) : Set V :=
  Classical.choose (exists_linearIndependent_extension hs hst)
#align linear_independent.extend LinearIndependent.extend

theorem LinearIndependent.extend_subset (hs : LinearIndependent K (fun x => x : s → V))
    (hst : s ⊆ t) : hs.extend hst ⊆ t :=
  let ⟨hbt, _hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndependent_extension hs hst)
  hbt
#align linear_independent.extend_subset LinearIndependent.extend_subset

theorem LinearIndependent.subset_extend (hs : LinearIndependent K (fun x => x : s → V))
    (hst : s ⊆ t) : s ⊆ hs.extend hst :=
  let ⟨_hbt, hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndependent_extension hs hst)
  hsb
#align linear_independent.subset_extend LinearIndependent.subset_extend

theorem LinearIndependent.subset_span_extend (hs : LinearIndependent K (fun x => x : s → V))
    (hst : s ⊆ t) : t ⊆ span K (hs.extend hst) :=
  let ⟨_hbt, _hsb, htb, _hli⟩ := Classical.choose_spec (exists_linearIndependent_extension hs hst)
  htb
#align linear_independent.subset_span_extend LinearIndependent.subset_span_extend

theorem LinearIndependent.linearIndependent_extend (hs : LinearIndependent K (fun x => x : s → V))
    (hst : s ⊆ t) : LinearIndependent K ((↑) : hs.extend hst → V) :=
  let ⟨_hbt, _hsb, _htb, hli⟩ := Classical.choose_spec (exists_linearIndependent_extension hs hst)
  hli
#align linear_independent.linear_independent_extend LinearIndependent.linearIndependent_extend

-- variable {K V} -- Porting note: Redundant binder annotation update.

-- TODO(Mario): rewrite?
theorem exists_of_linearIndependent_of_finite_span {t : Finset V}
    (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ (span K ↑t : Submodule K V)) :
    ∃ t' : Finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card := by
  classical
  have :
    ∀ t : Finset V,
      ∀ s' : Finset V,
        ↑s' ⊆ s →
          s ∩ ↑t = ∅ →
            s ⊆ (span K ↑(s' ∪ t) : Submodule K V) →
              ∃ t' : Finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
    fun t =>
    Finset.induction_on t
      (fun s' hs' _ hss' =>
        have : s = ↑s' := eq_of_linearIndependent_of_span_subtype hs hs' <| by simpa using hss'
        ⟨s', by simp [this]⟩)
      fun b₁ t hb₁t ih s' hs' hst hss' =>
      have hb₁s : b₁ ∉ s := fun h => by
        have : b₁ ∈ s ∩ ↑(insert b₁ t) := ⟨h, Finset.mem_insert_self _ _⟩
        rwa [hst] at this
      have hb₁s' : b₁ ∉ s' := fun h => hb₁s <| hs' h
      have hst : s ∩ ↑t = ∅ :=
        eq_empty_of_subset_empty <|
          -- Porting note: `-inter_subset_left, -subset_inter_iff` required.
          Subset.trans
            (by simp [inter_subset_inter, Subset.refl, -inter_subset_left, -subset_inter_iff])
            (le_of_eq hst)
      Classical.by_cases (p := s ⊆ (span K ↑(s' ∪ t) : Submodule K V))
        (fun this =>
          let ⟨u, hust, hsu, Eq⟩ := ih _ hs' hst this
          have hb₁u : b₁ ∉ u := fun h => (hust h).elim hb₁s hb₁t
          ⟨insert b₁ u, by simp [insert_subset_insert hust], Subset.trans hsu (by simp), by
            simp [Eq, hb₁t, hb₁s', hb₁u]⟩)
        fun this =>
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this
        have hb₂t' : b₂ ∉ s' ∪ t := fun h => hb₂t <| subset_span h
        have : s ⊆ (span K ↑(insert b₂ s' ∪ t) : Submodule K V) := fun b₃ hb₃ => by
          have : ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : Set V) := by
            -- Porting note: Too many theorems to be excluded, so
            --               `simp only` is shorter.
            simp only [insert_eq, union_subset_union, Subset.refl,
              subset_union_right, Finset.union_insert, Finset.coe_insert]
          have hb₃ : b₃ ∈ span K (insert b₁ (insert b₂ ↑(s' ∪ t) : Set V)) :=
            span_mono this (hss' hb₃)
          have : s ⊆ (span K (insert b₁ ↑(s' ∪ t)) : Submodule K V) := by
            simpa [insert_eq, -singleton_union, -union_singleton] using hss'
          -- Porting note: `by exact` is required to prevent timeout.
          have hb₁ : b₁ ∈ span K (insert b₂ ↑(s' ∪ t)) := by
            exact mem_span_insert_exchange (this hb₂s) hb₂t
          rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset_iff, hb₂s, hs']) hst this
        -- Porting note: `hb₂t'` → `Finset.card_insert_of_not_mem hb₂t'`
        ⟨u, Subset.trans hust <| union_subset_union (Subset.refl _) (by simp [subset_insert]), hsu,
          by simp [eq, Finset.card_insert_of_not_mem hb₂t', hb₁t, hb₁s']⟩
  have eq : ((t.filter fun x => x ∈ s) ∪ t.filter fun x => x ∉ s) = t := by
    ext1 x
    by_cases x ∈ s <;> simp [*]
  apply
    Exists.elim
      (this (t.filter fun x => x ∉ s) (t.filter fun x => x ∈ s) (by simp [Set.subset_def])
        (by simp (config := { contextual := true }) [Set.ext_iff]) (by rwa [eq]))
  intro u h
  exact
    ⟨u, Subset.trans h.1 (by simp (config := { contextual := true }) [subset_def, and_imp, or_imp]),
      h.2.1, by simp only [h.2.2, eq]⟩
#align exists_of_linear_independent_of_finite_span exists_of_linearIndependent_of_finite_span

theorem exists_finite_card_le_of_finite_of_linearIndependent_of_span (ht : t.Finite)
    (hs : LinearIndependent K (fun x => x : s → V)) (hst : s ⊆ span K t) :
    ∃ h : s.Finite, h.toFinset.card ≤ ht.toFinset.card :=
  have : s ⊆ (span K ↑ht.toFinset : Submodule K V) := by simp; assumption
                                                         -- ⊢ s ⊆ ↑(span K t)
                                                               -- 🎉 no goals
  let ⟨u, _hust, hsu, Eq⟩ := exists_of_linearIndependent_of_finite_span hs this
  have : s.Finite := u.finite_toSet.subset hsu
  ⟨this, by rw [← Eq]; exact Finset.card_le_of_subset <| Finset.coe_subset.mp <| by simp [hsu]⟩
            -- ⊢ Finset.card (Finite.toFinset this) ≤ Finset.card u
                       -- 🎉 no goals
#align exists_finite_card_le_of_finite_of_linear_independent_of_span exists_finite_card_le_of_finite_of_linearIndependent_of_span

end Module
