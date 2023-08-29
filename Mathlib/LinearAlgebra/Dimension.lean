/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Scott Morrison
-/
import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.SetTheory.Cardinal.Cofinality

#align_import linear_algebra.dimension from "leanprover-community/mathlib"@"47a5f8186becdbc826190ced4312f8199f9db6a5"

/-!
# Dimension of modules and vector spaces

## Main definitions

* The rank of a module is defined as `Module.rank : Cardinal`.
  This is defined as the supremum of the cardinalities of linearly independent subsets.

* The rank of a linear map is defined as the rank of its range.

## Main statements

* `LinearMap.rank_le_of_injective`: the source of an injective linear map has dimension
  at most that of the target.
* `LinearMap.rank_le_of_surjective`: the target of a surjective linear map has dimension
  at most that of that source.
* `basis_finite_of_finite_spans`:
  the existence of a finite spanning set implies that any basis is finite.
* `infinite_basis_le_maximal_linearIndependent`:
  if `b` is an infinite basis for a module `M`,
  and `s` is a maximal linearly independent set,
  then the cardinality of `b` is bounded by the cardinality of `s`.

For modules over rings satisfying the rank condition

* `Basis.le_span`:
  the cardinality of a basis is bounded by the cardinality of any spanning set

For modules over rings satisfying the strong rank condition

* `linearIndependent_le_span`:
  For any linearly independent family `v : ι → M`
  and any finite spanning set `w : Set M`,
  the cardinality of `ι` is bounded by the cardinality of `w`.
* `linearIndependent_le_basis`:
  If `b` is a basis for a module `M`,
  and `s` is a linearly independent set,
  then the cardinality of `s` is bounded by the cardinality of `b`.

For modules over rings with invariant basis number
(including all commutative rings and all noetherian rings)

* `mk_eq_mk_of_basis`: the dimension theorem, any two bases of the same vector space have the same
  cardinality.

For vector spaces (i.e. modules over a field), we have

* `rank_quotient_add_rank`: if `V₁` is a submodule of `V`, then
  `Module.rank (V/V₁) + Module.rank V₁ = Module.rank V`.
* `rank_range_add_rank_ker`: the rank-nullity theorem.

## Implementation notes

Many theorems in this file are not universe-generic when they relate dimensions
in different universes. They should be as general as they can be without
inserting `lift`s. The types `V`, `V'`, ... all live in different universes,
and `V₁`, `V₂`, ... all live in the same universe.
-/


noncomputable section

universe u v v' v'' u₁' w w'

variable {K : Type u} {V V₁ V₂ V₃ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}

variable {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type*}

open BigOperators Cardinal Basis Submodule Function Set

section Module

section

variable [Semiring K] [AddCommMonoid V] [Module K V]

variable (K V)

/-- The rank of a module, defined as a term of type `Cardinal`.

We define this as the supremum of the cardinalities of linearly independent subsets.

For a free module over any ring satisfying the strong rank condition
(e.g. left-noetherian rings, commutative rings, and in particular division rings and fields),
this is the same as the dimension of the space (i.e. the cardinality of any basis).

In particular this agrees with the usual notion of the dimension of a vector space.

The definition is marked as protected to avoid conflicts with `_root_.rank`,
the rank of a linear map.
-/
protected irreducible_def Module.rank : Cardinal :=
  ⨆ ι : { s : Set V // LinearIndependent K ((↑) : s → V) }, (#ι.1)
#align module.rank Module.rank

end

section

variable {R : Type u} [Ring R]

variable {M : Type v} [AddCommGroup M] [Module R M]

variable {M' : Type v'} [AddCommGroup M'] [Module R M']

variable {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]

theorem LinearMap.lift_rank_le_of_injective (f : M →ₗ[R] M') (i : Injective f) :
    Cardinal.lift.{v'} (Module.rank R M) ≤ Cardinal.lift.{v} (Module.rank R M') := by
  simp only [Module.rank_def]
  -- ⊢ lift.{v', v} (⨆ (ι : { s // LinearIndependent R Subtype.val }), #↑↑ι) ≤ lift …
  rw [Cardinal.lift_iSup (Cardinal.bddAbove_range.{v', v'} _),
    Cardinal.lift_iSup (Cardinal.bddAbove_range.{v, v} _)]
  apply ciSup_mono' (Cardinal.bddAbove_range.{v', v} _)
  -- ⊢ ∀ (i : { s // LinearIndependent R Subtype.val }), ∃ i', lift.{v', v} #↑↑i ≤  …
  rintro ⟨s, li⟩
  -- ⊢ ∃ i', lift.{v', v} #↑↑{ val := s, property := li } ≤ lift.{v, v'} #↑↑i'
  refine' ⟨⟨f '' s, _⟩, Cardinal.lift_mk_le'.mpr ⟨(Equiv.Set.image f s i).toEmbedding⟩⟩
  -- ⊢ LinearIndependent R Subtype.val
  exact (li.map' _ <| LinearMap.ker_eq_bot.mpr i).image
  -- 🎉 no goals
#align linear_map.lift_rank_le_of_injective LinearMap.lift_rank_le_of_injective

theorem LinearMap.rank_le_of_injective (f : M →ₗ[R] M₁) (i : Injective f) :
    Module.rank R M ≤ Module.rank R M₁ :=
  Cardinal.lift_le.1 (f.lift_rank_le_of_injective i)
#align linear_map.rank_le_of_injective LinearMap.rank_le_of_injective

theorem rank_le {n : ℕ}
    (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    Module.rank R M ≤ n := by
  rw [Module.rank_def]
  -- ⊢ ⨆ (ι : { s // LinearIndependent R Subtype.val }), #↑↑ι ≤ ↑n
  apply ciSup_le'
  -- ⊢ ∀ (i : { s // LinearIndependent R Subtype.val }), #↑↑i ≤ ↑n
  rintro ⟨s, li⟩
  -- ⊢ #↑↑{ val := s, property := li } ≤ ↑n
  exact linearIndependent_bounded_of_finset_linearIndependent_bounded H _ li
  -- 🎉 no goals
#align rank_le rank_le


/-- The rank of the range of a linear map is at most the rank of the source. -/
-- The proof is: a free submodule of the range lifts to a free submodule of the
-- source, by arbitrarily lifting a basis.
theorem lift_rank_range_le (f : M →ₗ[R] M') : Cardinal.lift.{v}
    (Module.rank R (LinearMap.range f)) ≤ Cardinal.lift.{v'} (Module.rank R M) := by
  simp only [Module.rank_def]
  -- ⊢ lift.{v, v'} (⨆ (ι : { s // LinearIndependent R Subtype.val }), #↑↑ι) ≤ lift …
  rw [Cardinal.lift_iSup (Cardinal.bddAbove_range.{v', v'} _)]
  -- ⊢ ⨆ (i : { s // LinearIndependent R Subtype.val }), lift.{v, v'} #↑↑i ≤ lift.{ …
  apply ciSup_le'
  -- ⊢ ∀ (i : { s // LinearIndependent R Subtype.val }), lift.{v, v'} #↑↑i ≤ lift.{ …
  rintro ⟨s, li⟩
  -- ⊢ lift.{v, v'} #↑↑{ val := s, property := li } ≤ lift.{v', v} (⨆ (ι : { s // L …
  apply le_trans
  swap
  · apply Cardinal.lift_le.mpr
    -- ⊢ ?m.20621 ≤ ⨆ (ι : { s // LinearIndependent R Subtype.val }), #↑↑ι
    refine' le_ciSup (Cardinal.bddAbove_range.{v, v} _) ⟨rangeSplitting f '' s, _⟩
    -- ⊢ LinearIndependent R Subtype.val
    apply LinearIndependent.of_comp f.rangeRestrict
    -- ⊢ LinearIndependent R (↑(LinearMap.rangeRestrict f) ∘ Subtype.val)
    convert li.comp (Equiv.Set.rangeSplittingImageEquiv f s) (Equiv.injective _) using 1
    -- 🎉 no goals
  · exact (Cardinal.lift_mk_eq'.mpr ⟨Equiv.Set.rangeSplittingImageEquiv f s⟩).ge
    -- 🎉 no goals
#align lift_rank_range_le lift_rank_range_le

theorem rank_range_le (f : M →ₗ[R] M₁) : Module.rank R (LinearMap.range f) ≤ Module.rank R M := by
  simpa using lift_rank_range_le f
  -- 🎉 no goals
#align rank_range_le rank_range_le

theorem lift_rank_map_le (f : M →ₗ[R] M') (p : Submodule R M) :
    Cardinal.lift.{v} (Module.rank R (p.map f)) ≤ Cardinal.lift.{v'} (Module.rank R p) := by
  have h := lift_rank_range_le (f.comp (Submodule.subtype p))
  -- ⊢ lift.{v, v'} (Module.rank R { x // x ∈ Submodule.map f p }) ≤ lift.{v', v} ( …
  rwa [LinearMap.range_comp, range_subtype] at h
  -- 🎉 no goals
#align lift_rank_map_le lift_rank_map_le

theorem rank_map_le (f : M →ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map f) ≤ Module.rank R p := by simpa using lift_rank_map_le f p
                                                    -- 🎉 no goals
#align rank_map_le rank_map_le

theorem rank_le_of_submodule (s t : Submodule R M) (h : s ≤ t) :
    Module.rank R s ≤ Module.rank R t :=
  (ofLe h).rank_le_of_injective fun ⟨x, _⟩ ⟨y, _⟩ eq =>
    Subtype.eq <| show x = y from Subtype.ext_iff_val.1 eq
#align rank_le_of_submodule rank_le_of_submodule

/-- Two linearly equivalent vector spaces have the same dimension, a version with different
universes. -/
theorem LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') :
    Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') := by
  apply le_antisymm
  -- ⊢ lift.{v', v} (Module.rank R M) ≤ lift.{v, v'} (Module.rank R M')
  · exact f.toLinearMap.lift_rank_le_of_injective f.injective
    -- 🎉 no goals
  · exact f.symm.toLinearMap.lift_rank_le_of_injective f.symm.injective
    -- 🎉 no goals
#align linear_equiv.lift_rank_eq LinearEquiv.lift_rank_eq

/-- Two linearly equivalent vector spaces have the same dimension. -/
theorem LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank R M = Module.rank R M₁ :=
  Cardinal.lift_inj.1 f.lift_rank_eq
#align linear_equiv.rank_eq LinearEquiv.rank_eq

theorem rank_range_of_injective (f : M →ₗ[R] M₁) (h : Injective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M :=
  (LinearEquiv.ofInjective f h).rank_eq.symm
#align rank_eq_of_injective rank_range_of_injective

/-- Pushforwards of submodules along a `LinearEquiv` have the same dimension. -/
theorem LinearEquiv.rank_map_eq (f : M ≃ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map (f : M →ₗ[R] M₁)) = Module.rank R p :=
  (f.submoduleMap p).rank_eq.symm
#align linear_equiv.rank_map_eq LinearEquiv.rank_map_eq

variable (R M)

@[simp]
theorem rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M := by
  have : (⊤ : Submodule R M) ≃ₗ[R] M := LinearEquiv.ofTop ⊤ rfl
  -- ⊢ Module.rank R { x // x ∈ ⊤ } = Module.rank R M
  rw [this.rank_eq]
  -- 🎉 no goals
#align rank_top rank_top

variable {R M}

theorem rank_range_of_surjective (f : M →ₗ[R] M') (h : Surjective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M' :=
  by rw [LinearMap.range_eq_top.2 h, rank_top]
     -- 🎉 no goals
#align rank_range_of_surjective rank_range_of_surjective

theorem rank_submodule_le (s : Submodule R M) : Module.rank R s ≤ Module.rank R M := by
  rw [← rank_top R M]
  -- ⊢ Module.rank R { x // x ∈ s } ≤ Module.rank R { x // x ∈ ⊤ }
  exact rank_le_of_submodule _ _ le_top
  -- 🎉 no goals
#align rank_submodule_le rank_submodule_le

theorem LinearMap.rank_le_of_surjective (f : M →ₗ[R] M₁) (h : Surjective f) :
    Module.rank R M₁ ≤ Module.rank R M := by
  rw [← rank_range_of_surjective f h]
  -- ⊢ Module.rank R { x // x ∈ range f } ≤ Module.rank R M
  apply rank_range_le
  -- 🎉 no goals
#align linear_map.rank_le_of_surjective LinearMap.rank_le_of_surjective

theorem rank_quotient_le (p : Submodule R M) : Module.rank R (M ⧸ p) ≤ Module.rank R M :=
  (mkQ p).rank_le_of_surjective (surjective_quot_mk _)
#align rank_quotient_le rank_quotient_le

variable [Nontrivial R]

theorem cardinal_lift_le_rank_of_linearIndependent {ι : Type w} {v : ι → M}
    (hv : LinearIndependent R v) :
    Cardinal.lift.{v} #ι ≤ Cardinal.lift.{w} (Module.rank R M) := by
  apply le_trans
  · exact Cardinal.lift_mk_le'.mpr ⟨(Equiv.ofInjective _ hv.injective).toEmbedding⟩
    -- 🎉 no goals
  · simp only [Cardinal.lift_le, Module.rank_def]
    -- ⊢ #↑(range v) ≤ ⨆ (ι : { s // LinearIndependent R Subtype.val }), #↑↑ι
    apply le_trans
    swap
    · exact le_ciSup (Cardinal.bddAbove_range.{v, v} _) ⟨range v, hv.coe_range⟩
      -- 🎉 no goals
    · exact le_rfl
      -- 🎉 no goals
#align cardinal_lift_le_rank_of_linear_independent cardinal_lift_le_rank_of_linearIndependent

theorem cardinal_lift_le_rank_of_linearIndependent' {ι : Type w} {v : ι → M}
    (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι ≤ Cardinal.lift.{w} (Module.rank R M) :=
  cardinal_lift_le_rank_of_linearIndependent hv
#align cardinal_lift_le_rank_of_linear_independent' cardinal_lift_le_rank_of_linearIndependent'

theorem cardinal_le_rank_of_linearIndependent {ι : Type v} {v : ι → M}
    (hv : LinearIndependent R v) : #ι ≤ Module.rank R M := by
  simpa using cardinal_lift_le_rank_of_linearIndependent hv
  -- 🎉 no goals
#align cardinal_le_rank_of_linear_independent cardinal_le_rank_of_linearIndependent

theorem cardinal_le_rank_of_linearIndependent' {s : Set M}
    (hs : LinearIndependent R (fun x => x : s → M)) : #s ≤ Module.rank R M :=
  cardinal_le_rank_of_linearIndependent hs
#align cardinal_le_rank_of_linear_independent' cardinal_le_rank_of_linearIndependent'

variable (R M)

@[simp]
theorem rank_punit : Module.rank R PUnit = 0 := by
  rw [← bot_eq_zero, ← le_bot_iff, Module.rank_def]
  -- ⊢ ⨆ (ι : { s // LinearIndependent R Subtype.val }), #↑↑ι ≤ ⊥
  apply ciSup_le'
  -- ⊢ ∀ (i : { s // LinearIndependent R Subtype.val }), #↑↑i ≤ ⊥
  rintro ⟨s, li⟩
  -- ⊢ #↑↑{ val := s, property := li } ≤ ⊥
  rw [le_bot_iff, bot_eq_zero, Cardinal.mk_emptyCollection_iff, Subtype.coe_mk]
  -- ⊢ s = ∅
  by_contra h
  -- ⊢ False
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 h
  -- ⊢ False
  simpa using LinearIndependent.ne_zero (⟨a, ha⟩ : s) li
  -- 🎉 no goals
#align rank_punit rank_punit

@[simp]
theorem rank_bot : Module.rank R (⊥ : Submodule R M) = 0 := by
  have : (⊥ : Submodule R M) ≃ₗ[R] PUnit := botEquivPUnit
  -- ⊢ Module.rank R { x // x ∈ ⊥ } = 0
  rw [this.rank_eq, rank_punit]
  -- 🎉 no goals
#align rank_bot rank_bot

variable {R M}

theorem exists_mem_ne_zero_of_rank_pos {s : Submodule R M} (h : 0 < Module.rank R s) :
    ∃ b : M, b ∈ s ∧ b ≠ 0 :=
  exists_mem_ne_zero_of_ne_bot fun eq => by rw [eq, rank_bot] at h; exact lt_irrefl _ h
                                            -- ⊢ False
                                                                    -- 🎉 no goals
#align exists_mem_ne_zero_of_rank_pos exists_mem_ne_zero_of_rank_pos

/-- A linearly-independent family of vectors in a module over a non-trivial ring must be finite if
the module is Noetherian. -/
theorem LinearIndependent.finite_of_isNoetherian [IsNoetherian R M] {v : ι → M}
    (hv : LinearIndependent R v) : Finite ι := by
  have hwf := isNoetherian_iff_wellFounded.mp (by infer_instance : IsNoetherian R M)
  -- ⊢ Finite ι
  refine' CompleteLattice.WellFounded.finite_of_independent hwf hv.independent_span_singleton
    fun i contra => _
  apply hv.ne_zero i
  -- ⊢ v i = 0
  have : v i ∈ R ∙ v i := Submodule.mem_span_singleton_self (v i)
  -- ⊢ v i = 0
  rwa [contra, Submodule.mem_bot] at this
  -- 🎉 no goals
#align linear_independent.finite_of_is_noetherian LinearIndependent.finite_of_isNoetherian

theorem LinearIndependent.set_finite_of_isNoetherian [IsNoetherian R M] {s : Set M}
    (hi : LinearIndependent R ((↑) : s → M)) : s.Finite :=
  @Set.toFinite _ _ hi.finite_of_isNoetherian
#align linear_independent.set_finite_of_is_noetherian LinearIndependent.set_finite_of_isNoetherian

-- One might hope that a finite spanning set implies that any linearly independent set is finite.
-- While this is true over a division ring
-- (simply because any linearly independent set can be extended to a basis),
-- I'm not certain what more general statements are possible.
/--
Over any nontrivial ring, the existence of a finite spanning set implies that any basis is finite.
-/
lemma basis_finite_of_finite_spans (w : Set M) (hw : w.Finite) (s : span R w = ⊤) {ι : Type w}
    (b : Basis ι R M) : Finite ι := by
  classical
  haveI := hw.to_subtype
  cases nonempty_fintype w
  -- We'll work by contradiction, assuming `ι` is infinite.
  rw [← not_infinite_iff_finite]
  intro i
  -- Let `S` be the union of the supports of `x ∈ w` expressed as linear combinations of `b`.
  -- This is a finite set since `w` is finite.
  let S : Finset ι := Finset.univ.sup fun x : w => (b.repr x).support
  let bS : Set M := b '' S
  have h : ∀ x ∈ w, x ∈ span R bS := by
    intro x m
    rw [← b.total_repr x, Finsupp.span_image_eq_map_total, Submodule.mem_map]
    use b.repr x
    simp only [and_true_iff, eq_self_iff_true, Finsupp.mem_supported]
    change (b.repr x).support ≤ S
    convert Finset.le_sup (α := Finset ι) (by simp : (⟨x, m⟩ : w) ∈ Finset.univ)
    rfl
  -- Thus this finite subset of the basis elements spans the entire module.
  have k : span R bS = ⊤ := eq_top_iff.2 (le_trans s.ge (span_le.2 h))
  -- Now there is some `x : ι` not in `S`, since `ι` is infinite.
  obtain ⟨x, nm⟩ := Infinite.exists_not_mem_finset S
  -- However it must be in the span of the finite subset,
  have k' : b x ∈ span R bS := by
    rw [k]
    exact mem_top
  -- giving the desire contradiction.
  refine' b.linearIndependent.not_mem_span_image _ k'
  exact nm
#align basis_fintype_of_finite_spans basis_finite_of_finite_spansₓ

-- From [Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
/-- Over any ring `R`, if `b` is a basis for a module `M`,
and `s` is a maximal linearly independent set,
then the union of the supports of `x ∈ s` (when written out in the basis `b`) is all of `b`.
-/
theorem union_support_maximal_linearIndependent_eq_range_basis {ι : Type w} (b : Basis ι R M)
    {κ : Type w'} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) :
    ⋃ k, ((b.repr (v k)).support : Set ι) = Set.univ := by
  -- If that's not the case,
  by_contra h
  -- ⊢ False
  simp only [← Ne.def, ne_univ_iff_exists_not_mem, mem_iUnion, not_exists_not,
    Finsupp.mem_support_iff, Finset.mem_coe] at h
  -- We have some basis element `b b'` which is not in the support of any of the `v i`.
  obtain ⟨b', w⟩ := h
  -- ⊢ False
  -- Using this, we'll construct a linearly independent family strictly larger than `v`,
  -- by also using this `b b'`.
  let v' : Option κ → M := fun o => o.elim (b b') v
  -- ⊢ False
  have r : range v ⊆ range v' := by
    rintro - ⟨k, rfl⟩
    use some k
    rfl
  have r' : b b' ∉ range v := by
    rintro ⟨k, p⟩
    simpa [w] using congr_arg (fun m => (b.repr m) b') p
  have r'' : range v ≠ range v' := by
    intro e
    have p : b b' ∈ range v' := by
      use none
      rfl
    rw [← e] at p
    exact r' p
  have inj' : Injective v' := by
    rintro (_ | k) (_ | k) z
    · rfl
    · exfalso
      exact r' ⟨k, z.symm⟩
    · exfalso
      exact r' ⟨k, z⟩
    · congr
      exact i.injective z
  -- The key step in the proof is checking that this strictly larger family is linearly independent.
  have i' : LinearIndependent R ((↑) : range v' → M) := by
    rw [linearIndependent_subtype_range inj', linearIndependent_iff]
    intro l z
    rw [Finsupp.total_option] at z
    simp only [Option.elim'] at z
    change _ + Finsupp.total κ M R v l.some = 0 at z
    -- We have some linear combination of `b b'` and the `v i`, which we want to show is trivial.
    -- We'll first show the coefficient of `b b'` is zero,
    -- by expressing the `v i` in the basis `b`, and using that the `v i` have no `b b'` term.
    have l₀ : l none = 0 := by
      rw [← eq_neg_iff_add_eq_zero] at z
      replace z := neg_eq_iff_eq_neg.mpr z
      apply_fun fun x => b.repr x b' at z
      simp only [repr_self, LinearEquiv.map_smul, mul_one, Finsupp.single_eq_same, Pi.neg_apply,
        Finsupp.smul_single', LinearEquiv.map_neg, Finsupp.coe_neg] at z
      erw [FunLike.congr_fun (Finsupp.apply_total R (b.repr : M →ₗ[R] ι →₀ R) v l.some) b'] at z
      simpa [Finsupp.total_apply, w] using z
    -- Then all the other coefficients are zero, because `v` is linear independent.
    have l₁ : l.some = 0 := by
      rw [l₀, zero_smul, zero_add] at z
      exact linearIndependent_iff.mp i _ z
    -- Finally we put those facts together to show the linear combination is trivial.
    ext (_ | a)
    · simp only [l₀, Finsupp.coe_zero, Pi.zero_apply]
    · erw [FunLike.congr_fun l₁ a]
      simp only [Finsupp.coe_zero, Pi.zero_apply]
  dsimp [LinearIndependent.Maximal] at m
  -- ⊢ False
  specialize m (range v') i' r
  -- ⊢ False
  exact r'' m
  -- 🎉 no goals
#align union_support_maximal_linear_independent_eq_range_basis union_support_maximal_linearIndependent_eq_range_basis

/-- Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
theorem infinite_basis_le_maximal_linearIndependent' {ι : Type w} (b : Basis ι R M) [Infinite ι]
    {κ : Type w'} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) :
    Cardinal.lift.{w'} #ι ≤ Cardinal.lift.{w} #κ := by
  let Φ := fun k : κ => (b.repr (v k)).support
  -- ⊢ lift.{w', w} #ι ≤ lift.{w, w'} #κ
  have w₁ : #ι ≤ #(Set.range Φ) := by
    apply Cardinal.le_range_of_union_finset_eq_top
    exact union_support_maximal_linearIndependent_eq_range_basis b v i m
  have w₂ : Cardinal.lift.{w'} #(Set.range Φ) ≤ Cardinal.lift.{w} #κ := Cardinal.mk_range_le_lift
  -- ⊢ lift.{w', w} #ι ≤ lift.{w, w'} #κ
  exact (Cardinal.lift_le.mpr w₁).trans w₂
  -- 🎉 no goals
#align infinite_basis_le_maximal_linear_independent' infinite_basis_le_maximal_linearIndependent'

-- (See `infinite_basis_le_maximal_linearIndependent'` for the more general version
-- where the index types can live in different universes.)
/-- Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
theorem infinite_basis_le_maximal_linearIndependent {ι : Type w} (b : Basis ι R M) [Infinite ι]
    {κ : Type w} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) : #ι ≤ #κ :=
  Cardinal.lift_le.mp (infinite_basis_le_maximal_linearIndependent' b v i m)
#align infinite_basis_le_maximal_linear_independent infinite_basis_le_maximal_linearIndependent

theorem CompleteLattice.Independent.subtype_ne_bot_le_rank [NoZeroSMulDivisors R M]
    {V : ι → Submodule R M} (hV : CompleteLattice.Independent V) :
    Cardinal.lift.{v} #{ i : ι // V i ≠ ⊥ } ≤ Cardinal.lift.{w} (Module.rank R M) := by
  set I := { i : ι // V i ≠ ⊥ }
  -- ⊢ lift.{v, w} #I ≤ lift.{w, v} (Module.rank R M)
  have hI : ∀ i : I, ∃ v ∈ V i, v ≠ (0 : M) := by
    intro i
    rw [← Submodule.ne_bot_iff]
    exact i.prop
  choose v hvV hv using hI
  -- ⊢ lift.{v, w} #I ≤ lift.{w, v} (Module.rank R M)
  have : LinearIndependent R v := (hV.comp Subtype.coe_injective).linearIndependent _ hvV hv
  -- ⊢ lift.{v, w} #I ≤ lift.{w, v} (Module.rank R M)
  exact cardinal_lift_le_rank_of_linearIndependent' this
  -- 🎉 no goals
#align complete_lattice.independent.subtype_ne_bot_le_rank CompleteLattice.Independent.subtype_ne_bot_le_rank

end

section RankZero

variable {R : Type u} {M : Type v}

variable [Ring R] [AddCommGroup M] [Module R M]

@[simp]
theorem rank_subsingleton [Subsingleton R] : Module.rank R M = 1 := by
  haveI := Module.subsingleton R M
  -- ⊢ Module.rank R M = 1
  have : Nonempty { s : Set M // LinearIndependent R ((↑) : s → M) } :=
    ⟨⟨∅, linearIndependent_empty _ _⟩⟩
  rw [Module.rank_def, ciSup_eq_of_forall_le_of_forall_lt_exists_gt]
  -- ⊢ ∀ (i : { s // LinearIndependent R Subtype.val }), #↑↑i ≤ 1
  · rintro ⟨s, hs⟩
    -- ⊢ #↑↑{ val := s, property := hs } ≤ 1
    rw [Cardinal.mk_le_one_iff_set_subsingleton]
    -- ⊢ Set.Subsingleton ↑{ val := s, property := hs }
    apply subsingleton_of_subsingleton
    -- 🎉 no goals
  intro w hw
  -- ⊢ ∃ i, w < #↑↑i
  refine' ⟨⟨{0}, _⟩, _⟩
  -- ⊢ LinearIndependent R Subtype.val
  · rw [linearIndependent_iff']
    -- ⊢ ∀ (s : Finset { x // x ∈ {0} }) (g : { x // x ∈ {0} } → R), ∑ i in s, g i •  …
    intros
    -- ⊢ g✝ i✝ = 0
    exact Subsingleton.elim _ _
    -- 🎉 no goals
  · exact hw.trans_eq (Cardinal.mk_singleton _).symm
    -- 🎉 no goals
#align rank_subsingleton rank_subsingleton

variable [NoZeroSMulDivisors R M]

theorem rank_pos [Nontrivial M] : 0 < Module.rank R M := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  -- ⊢ 0 < Module.rank R M
  suffices 1 ≤ Module.rank R M by exact zero_lt_one.trans_le this
  -- ⊢ 1 ≤ Module.rank R M
  letI := Module.nontrivial R M
  -- ⊢ 1 ≤ Module.rank R M
  suffices LinearIndependent R fun y : ({x} : Set M) => (y : M) by
    simpa using cardinal_le_rank_of_linearIndependent this
  exact linearIndependent_singleton hx
  -- 🎉 no goals
#align rank_pos rank_pos

variable [Nontrivial R]

theorem rank_zero_iff_forall_zero : Module.rank R M = 0 ↔ ∀ x : M, x = 0 := by
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ ∀ (x : M), x = 0
  · contrapose! h
    -- ⊢ Module.rank R M ≠ 0
    obtain ⟨x, hx⟩ := h
    -- ⊢ Module.rank R M ≠ 0
    letI : Nontrivial M := nontrivial_of_ne _ _ hx
    -- ⊢ Module.rank R M ≠ 0
    exact rank_pos.ne'
    -- 🎉 no goals
  · have : (⊤ : Submodule R M) = ⊥ := by
      ext x
      simp [h x]
    rw [← rank_top, this, rank_bot]
    -- 🎉 no goals
#align rank_zero_iff_forall_zero rank_zero_iff_forall_zero

/-- See `rank_subsingleton` for the reason that `Nontrivial R` is needed. -/
theorem rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M :=
  rank_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm
#align rank_zero_iff rank_zero_iff

theorem rank_pos_iff_exists_ne_zero : 0 < Module.rank R M ↔ ∃ x : M, x ≠ 0 := by
  rw [← not_iff_not]
  -- ⊢ ¬0 < Module.rank R M ↔ ¬∃ x, x ≠ 0
  simpa using rank_zero_iff_forall_zero
  -- 🎉 no goals
#align rank_pos_iff_exists_ne_zero rank_pos_iff_exists_ne_zero

theorem rank_pos_iff_nontrivial : 0 < Module.rank R M ↔ Nontrivial M :=
  rank_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm
#align rank_pos_iff_nontrivial rank_pos_iff_nontrivial

end RankZero

section InvariantBasisNumber

variable {R : Type u} [Ring R] [InvariantBasisNumber R]

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The dimension theorem: if `v` and `v'` are two bases, their index types
have the same cardinalities. -/
theorem mk_eq_mk_of_basis (v : Basis ι R M) (v' : Basis ι' R M) :
    Cardinal.lift.{w'} #ι = Cardinal.lift.{w} #ι' := by
  classical
  haveI := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite ι
  · -- `v` is a finite basis, so by `basis_finite_of_finite_spans` so is `v'`.
    -- haveI : Finite (range v) := Set.finite_range v
    haveI := basis_finite_of_finite_spans _ (Set.finite_range v) v.span_eq v'
    cases nonempty_fintype ι'
    -- We clean up a little:
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype]
    simp only [Cardinal.lift_natCast, Cardinal.natCast_inj]
    -- Now we can use invariant basis number to show they have the same cardinality.
    apply card_eq_of_linearEquiv R
    exact
      (Finsupp.linearEquivFunOnFinite R R ι).symm.trans v.repr.symm ≪≫ₗ v'.repr ≪≫ₗ
        Finsupp.linearEquivFunOnFinite R R ι'
  · -- `v` is an infinite basis,
    -- so by `infinite_basis_le_maximal_linearIndependent`, `v'` is at least as big,
    -- and then applying `infinite_basis_le_maximal_linearIndependent` again
    -- we see they have the same cardinality.
    have w₁ := infinite_basis_le_maximal_linearIndependent' v _ v'.linearIndependent v'.maximal
    rcases Cardinal.lift_mk_le'.mp w₁ with ⟨f⟩
    haveI : Infinite ι' := Infinite.of_injective f f.2
    have w₂ := infinite_basis_le_maximal_linearIndependent' v' _ v.linearIndependent v.maximal
    exact le_antisymm w₁ w₂
#align mk_eq_mk_of_basis mk_eq_mk_of_basis

/-- Given two bases indexed by `ι` and `ι'` of an `R`-module, where `R` satisfies the invariant
basis number property, an equiv `ι ≃ ι' `. -/
def Basis.indexEquiv (v : Basis ι R M) (v' : Basis ι' R M) : ι ≃ ι' :=
  (Cardinal.lift_mk_eq'.1 <| mk_eq_mk_of_basis v v').some
#align basis.index_equiv Basis.indexEquiv

theorem mk_eq_mk_of_basis' {ι' : Type w} (v : Basis ι R M) (v' : Basis ι' R M) : #ι = #ι' :=
  Cardinal.lift_inj.1 <| mk_eq_mk_of_basis v v'
#align mk_eq_mk_of_basis' mk_eq_mk_of_basis'

end InvariantBasisNumber

section RankCondition

variable {R : Type u} [Ring R] [RankCondition R]

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An auxiliary lemma for `Basis.le_span`.

If `R` satisfies the rank condition,
then for any finite basis `b : Basis ι R M`,
and any finite spanning set `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem Basis.le_span'' {ι : Type*} [Fintype ι] (b : Basis ι R M) {w : Set M} [Fintype w]
    (s : span R w = ⊤) : Fintype.card ι ≤ Fintype.card w := by
  -- We construct a surjective linear map `(w → R) →ₗ[R] (ι → R)`,
  -- by expressing a linear combination in `w` as a linear combination in `ι`.
  fapply card_le_of_surjective' R
  -- ⊢ (↑w →₀ R) →ₗ[R] ι →₀ R
  · exact b.repr.toLinearMap.comp (Finsupp.total w M R (↑))
    -- 🎉 no goals
  · apply Surjective.comp (g := b.repr.toLinearMap)
    -- ⊢ Surjective ↑↑b.repr
    apply LinearEquiv.surjective
    -- ⊢ Surjective fun x => ↑(Finsupp.total (↑w) M R Subtype.val) x
    rw [← LinearMap.range_eq_top, Finsupp.range_total]
    -- ⊢ span R (range Subtype.val) = ⊤
    simpa using s
    -- 🎉 no goals
#align basis.le_span'' Basis.le_span''

/--
Another auxiliary lemma for `Basis.le_span`, which does not require assuming the basis is finite,
but still assumes we have a finite spanning set.
-/
theorem basis_le_span' {ι : Type*} (b : Basis ι R M) {w : Set M} [Fintype w] (s : span R w = ⊤) :
    #ι ≤ Fintype.card w := by
  haveI := nontrivial_of_invariantBasisNumber R
  -- ⊢ #ι ≤ ↑(Fintype.card ↑w)
  haveI := basis_finite_of_finite_spans w (toFinite _) s b
  -- ⊢ #ι ≤ ↑(Fintype.card ↑w)
  cases nonempty_fintype ι
  -- ⊢ #ι ≤ ↑(Fintype.card ↑w)
  rw [Cardinal.mk_fintype ι]
  -- ⊢ ↑(Fintype.card ι) ≤ ↑(Fintype.card ↑w)
  simp only [Cardinal.natCast_le]
  -- ⊢ Fintype.card ι ≤ Fintype.card ↑w
  exact Basis.le_span'' b s
  -- 🎉 no goals
#align basis_le_span' basis_le_span'

-- Note that if `R` satisfies the strong rank condition,
-- this also follows from `linearIndependent_le_span` below.
/-- If `R` satisfies the rank condition,
then the cardinality of any basis is bounded by the cardinality of any spanning set.
-/
theorem Basis.le_span {J : Set M} (v : Basis ι R M) (hJ : span R J = ⊤) : #(range v) ≤ #J := by
  haveI := nontrivial_of_invariantBasisNumber R
  -- ⊢ #↑(range ↑v) ≤ #↑J
  cases fintypeOrInfinite J
  -- ⊢ #↑(range ↑v) ≤ #↑J
  · rw [← Cardinal.lift_le, Cardinal.mk_range_eq_of_injective v.injective, Cardinal.mk_fintype J]
    -- ⊢ lift.{v, w} #ι ≤ lift.{w, v} ↑(Fintype.card ↑J)
    convert Cardinal.lift_le.{v}.2 (basis_le_span' v hJ)
    -- ⊢ lift.{w, v} ↑(Fintype.card ↑J) = lift.{v, w} ↑(Fintype.card ↑J)
    simp
    -- 🎉 no goals
  · let S : J → Set ι := fun j => ↑(v.repr j).support
    -- ⊢ #↑(range ↑v) ≤ #↑J
    let S' : J → Set M := fun j => v '' S j
    -- ⊢ #↑(range ↑v) ≤ #↑J
    have hs : range v ⊆ ⋃ j, S' j := by
      intro b hb
      rcases mem_range.1 hb with ⟨i, hi⟩
      have : span R J ≤ comap v.repr.toLinearMap (Finsupp.supported R R (⋃ j, S j)) :=
        span_le.2 fun j hj x hx => ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩
      rw [hJ] at this
      replace : v.repr (v i) ∈ Finsupp.supported R R (⋃ j, S j) := this trivial
      rw [v.repr_self, Finsupp.mem_supported, Finsupp.support_single_ne_zero _ one_ne_zero] at this
      · subst b
        rcases mem_iUnion.1 (this (Finset.mem_singleton_self _)) with ⟨j, hj⟩
        exact mem_iUnion.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩
    refine' le_of_not_lt fun IJ => _
    -- ⊢ False
    suffices #(⋃ j, S' j) < #(range v) by exact not_le_of_lt this ⟨Set.embeddingOfSubset _ _ hs⟩
    -- ⊢ #↑(⋃ (j : ↑J), S' j) < #↑(range ↑v)
    refine' lt_of_le_of_lt (le_trans Cardinal.mk_iUnion_le_sum_mk
      (Cardinal.sum_le_sum _ (fun _ => ℵ₀) _)) _
    · exact fun j => (Cardinal.lt_aleph0_of_finite _).le
      -- 🎉 no goals
    · simpa
      -- 🎉 no goals
#align basis.le_span Basis.le_span

end RankCondition

section StrongRankCondition

variable {R : Type u} [Ring R] [StrongRankCondition R]

variable {M : Type v} [AddCommGroup M] [Module R M]

open Submodule

-- An auxiliary lemma for `linearIndependent_le_span'`,
-- with the additional assumption that the linearly independent family is finite.
theorem linearIndependent_le_span_aux' {ι : Type*} [Fintype ι] (v : ι → M)
    (i : LinearIndependent R v) (w : Set M) [Fintype w] (s : range v ≤ span R w) :
    Fintype.card ι ≤ Fintype.card w := by
  -- We construct an injective linear map `(ι → R) →ₗ[R] (w → R)`,
  -- by thinking of `f : ι → R` as a linear combination of the finite family `v`,
  -- and expressing that (using the axiom of choice) as a linear combination over `w`.
  -- We can do this linearly by constructing the map on a basis.
  fapply card_le_of_injective' R
  -- ⊢ (ι →₀ R) →ₗ[R] ↑w →₀ R
  · apply Finsupp.total
    -- ⊢ ι → ↑w →₀ R
    exact fun i => Span.repr R w ⟨v i, s (mem_range_self i)⟩
    -- 🎉 no goals
  · intro f g h
    -- ⊢ f = g
    apply_fun Finsupp.total w M R (↑) at h
    -- ⊢ f = g
    simp only [Finsupp.total_total, Submodule.coe_mk, Span.finsupp_total_repr] at h
    -- ⊢ f = g
    rw [← sub_eq_zero, ← LinearMap.map_sub] at h
    -- ⊢ f = g
    exact sub_eq_zero.mp (linearIndependent_iff.mp i _ h)
    -- 🎉 no goals
#align linear_independent_le_span_aux' linearIndependent_le_span_aux'

/-- If `R` satisfies the strong rank condition,
then any linearly independent family `v : ι → M`
contained in the span of some finite `w : Set M`,
is itself finite.
-/
def linearIndependentFintypeOfLeSpanFintype {ι : Type*} (v : ι → M) (i : LinearIndependent R v)
    (w : Set M) [Fintype w] (s : range v ≤ span R w) : Fintype ι :=
  fintypeOfFinsetCardLe (Fintype.card w) fun t => by
    let v' := fun x : (t : Set ι) => v x
    -- ⊢ Finset.card t ≤ Fintype.card ↑w
    have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
    -- ⊢ Finset.card t ≤ Fintype.card ↑w
    have s' : range v' ≤ span R w := (range_comp_subset_range _ _).trans s
    -- ⊢ Finset.card t ≤ Fintype.card ↑w
    simpa using linearIndependent_le_span_aux' v' i' w s'
    -- 🎉 no goals
#align linear_independent_fintype_of_le_span_fintype linearIndependentFintypeOfLeSpanFintype

/-- If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
contained in the span of some finite `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem linearIndependent_le_span' {ι : Type*} (v : ι → M) (i : LinearIndependent R v) (w : Set M)
    [Fintype w] (s : range v ≤ span R w) : #ι ≤ Fintype.card w := by
  haveI : Fintype ι := linearIndependentFintypeOfLeSpanFintype v i w s
  -- ⊢ #ι ≤ ↑(Fintype.card ↑w)
  rw [Cardinal.mk_fintype]
  -- ⊢ ↑(Fintype.card ι) ≤ ↑(Fintype.card ↑w)
  simp only [Cardinal.natCast_le]
  -- ⊢ Fintype.card ι ≤ Fintype.card ↑w
  exact linearIndependent_le_span_aux' v i w s
  -- 🎉 no goals
#align linear_independent_le_span' linearIndependent_le_span'

/-- If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
and any finite spanning set `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem linearIndependent_le_span {ι : Type*} (v : ι → M) (i : LinearIndependent R v) (w : Set M)
    [Fintype w] (s : span R w = ⊤) : #ι ≤ Fintype.card w := by
  apply linearIndependent_le_span' v i w
  -- ⊢ range v ≤ ↑(span R w)
  rw [s]
  -- ⊢ range v ≤ ↑⊤
  exact le_top
  -- 🎉 no goals
#align linear_independent_le_span linearIndependent_le_span

/-- A version of `linearIndependent_le_span` for `Finset`. -/
theorem linearIndependent_le_span_finset {ι : Type*} (v : ι → M) (i : LinearIndependent R v)
    (w : Finset M) (s : span R (w : Set M) = ⊤) : #ι ≤ w.card := by
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using linearIndependent_le_span v i w s
  -- 🎉 no goals
#align linear_independent_le_span_finset linearIndependent_le_span_finset

/-- An auxiliary lemma for `linearIndependent_le_basis`:
we handle the case where the basis `b` is infinite.
-/
theorem linearIndependent_le_infinite_basis {ι : Type*} (b : Basis ι R M) [Infinite ι] {κ : Type _}
    (v : κ → M) (i : LinearIndependent R v) : #κ ≤ #ι := by
  classical
  by_contra h
  rw [not_le, ← Cardinal.mk_finset_of_infinite ι] at h
  let Φ := fun k : κ => (b.repr (v k)).support
  obtain ⟨s, w : Infinite ↑(Φ ⁻¹' {s})⟩ := Cardinal.exists_infinite_fiber Φ h (by infer_instance)
  let v' := fun k : Φ ⁻¹' {s} => v k
  have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
  have w' : Fintype (Φ ⁻¹' {s}) := by
    apply linearIndependentFintypeOfLeSpanFintype v' i' (s.image b)
    rintro m ⟨⟨p, ⟨rfl⟩⟩, rfl⟩
    simp only [SetLike.mem_coe, Subtype.coe_mk, Finset.coe_image]
    apply Basis.mem_span_repr_support
  exact w.false
#align linear_independent_le_infinite_basis linearIndependent_le_infinite_basis

/-- Over any ring `R` satisfying the strong rank condition,
if `b` is a basis for a module `M`,
and `s` is a linearly independent set,
then the cardinality of `s` is bounded by the cardinality of `b`.
-/
theorem linearIndependent_le_basis {ι : Type*} (b : Basis ι R M) {κ : Type _} (v : κ → M)
    (i : LinearIndependent R v) : #κ ≤ #ι := by
  classical
  -- We split into cases depending on whether `ι` is infinite.
  cases fintypeOrInfinite ι
  · rw [Cardinal.mk_fintype ι] -- When `ι` is finite, we have `linearIndependent_le_span`,
    haveI : Nontrivial R := nontrivial_of_invariantBasisNumber R
    rw [Fintype.card_congr (Equiv.ofInjective b b.injective)]
    exact linearIndependent_le_span v i (range b) b.span_eq
  · -- and otherwise we have `linearIndependent_le_infinite_basis`.
    exact linearIndependent_le_infinite_basis b v i
#align linear_independent_le_basis linearIndependent_le_basis

/-- Let `R` satisfy the strong rank condition. If `m` elements of a free rank `n` `R`-module are
linearly independent, then `m ≤ n`. -/
theorem Basis.card_le_card_of_linearIndependent_aux {R : Type*} [Ring R] [StrongRankCondition R]
    (n : ℕ) {m : ℕ} (v : Fin m → Fin n → R) : LinearIndependent R v → m ≤ n := fun h => by
  simpa using linearIndependent_le_basis (Pi.basisFun R (Fin n)) v h
  -- 🎉 no goals
#align basis.card_le_card_of_linear_independent_aux Basis.card_le_card_of_linearIndependent_aux

-- When the basis is not infinite this need not be true!
/-- Over any ring `R` satisfying the strong rank condition,
if `b` is an infinite basis for a module `M`,
then every maximal linearly independent set has the same cardinality as `b`.

This proof (along with some of the lemmas above) comes from
[Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
-/
theorem maximal_linearIndependent_eq_infinite_basis {ι : Type*} (b : Basis ι R M) [Infinite ι]
    {κ : Type _} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) : #κ = #ι := by
  apply le_antisymm
  -- ⊢ #κ ≤ #ι
  · exact linearIndependent_le_basis b v i
    -- 🎉 no goals
  · haveI : Nontrivial R := nontrivial_of_invariantBasisNumber R
    -- ⊢ #ι ≤ #κ
    exact infinite_basis_le_maximal_linearIndependent b v i m
    -- 🎉 no goals
#align maximal_linear_independent_eq_infinite_basis maximal_linearIndependent_eq_infinite_basis

theorem Basis.mk_eq_rank'' {ι : Type v} (v : Basis ι R M) : #ι = Module.rank R M := by
  haveI := nontrivial_of_invariantBasisNumber R
  -- ⊢ #ι = Module.rank R M
  rw [Module.rank_def]
  -- ⊢ #ι = ⨆ (ι : { s // LinearIndependent R Subtype.val }), #↑↑ι
  apply le_antisymm
  -- ⊢ #ι ≤ ⨆ (ι : { s // LinearIndependent R Subtype.val }), #↑↑ι
  · trans
    swap
    · apply le_ciSup (Cardinal.bddAbove_range.{v, v} _)
      -- ⊢ { s // LinearIndependent R Subtype.val }
      exact
        ⟨Set.range v, by
          convert v.reindexRange.linearIndependent
          ext
          simp⟩
    · exact (Cardinal.mk_range_eq v v.injective).ge
      -- 🎉 no goals
  · apply ciSup_le'
    -- ⊢ ∀ (i : { s // LinearIndependent R Subtype.val }), #↑↑i ≤ #ι
    rintro ⟨s, li⟩
    -- ⊢ #↑↑{ val := s, property := li } ≤ #ι
    apply linearIndependent_le_basis v _ li
    -- 🎉 no goals
#align basis.mk_eq_rank'' Basis.mk_eq_rank''

theorem Basis.mk_range_eq_rank (v : Basis ι R M) : #(range v) = Module.rank R M :=
  v.reindexRange.mk_eq_rank''
#align basis.mk_range_eq_rank Basis.mk_range_eq_rank

/-- If a vector space has a finite basis, then its dimension (seen as a cardinal) is equal to the
cardinality of the basis. -/
theorem rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) :
    Module.rank R M = Fintype.card ι := by
  classical
  haveI := nontrivial_of_invariantBasisNumber R
  rw [← h.mk_range_eq_rank, Cardinal.mk_fintype, Set.card_range_of_injective h.injective]
#align rank_eq_card_basis rank_eq_card_basis

theorem Basis.card_le_card_of_linearIndependent {ι : Type*} [Fintype ι] (b : Basis ι R M)
    {ι' : Type*} [Fintype ι'] {v : ι' → M} (hv : LinearIndependent R v) :
    Fintype.card ι' ≤ Fintype.card ι := by
  letI := nontrivial_of_invariantBasisNumber R
  -- ⊢ Fintype.card ι' ≤ Fintype.card ι
  simpa [rank_eq_card_basis b, Cardinal.mk_fintype] using
    cardinal_lift_le_rank_of_linearIndependent' hv
#align basis.card_le_card_of_linear_independent Basis.card_le_card_of_linearIndependent

theorem Basis.card_le_card_of_submodule (N : Submodule R M) [Fintype ι] (b : Basis ι R M)
    [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linearIndependent (b'.linearIndependent.map' N.subtype N.ker_subtype)
#align basis.card_le_card_of_submodule Basis.card_le_card_of_submodule

theorem Basis.card_le_card_of_le {N O : Submodule R M} (hNO : N ≤ O) [Fintype ι] (b : Basis ι R O)
    [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map' (Submodule.ofLe hNO) (N.ker_ofLe O _))
#align basis.card_le_card_of_le Basis.card_le_card_of_le

theorem Basis.mk_eq_rank (v : Basis ι R M) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{w} (Module.rank R M) := by
  haveI := nontrivial_of_invariantBasisNumber R
  -- ⊢ lift.{v, w} #ι = lift.{w, v} (Module.rank R M)
  rw [← v.mk_range_eq_rank, Cardinal.mk_range_eq_of_injective v.injective]
  -- 🎉 no goals
#align basis.mk_eq_rank Basis.mk_eq_rank

theorem Basis.mk_eq_rank'.{m} (v : Basis ι R M) :
    Cardinal.lift.{max v m} #ι = Cardinal.lift.{max w m} (Module.rank R M) :=
  Cardinal.lift_umax_eq.{w, v, m}.mpr v.mk_eq_rank
#align basis.mk_eq_rank' Basis.mk_eq_rank'

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
theorem Basis.nonempty_fintype_index_of_rank_lt_aleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Nonempty (Fintype ι) := by
  rwa [← Cardinal.lift_lt, ← b.mk_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0,
    Cardinal.lt_aleph0_iff_fintype] at h
#align basis.nonempty_fintype_index_of_rank_lt_aleph_0 Basis.nonempty_fintype_index_of_rank_lt_aleph0

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
noncomputable def Basis.fintypeIndexOfRankLtAleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Fintype ι :=
  Classical.choice (b.nonempty_fintype_index_of_rank_lt_aleph0 h)
#align basis.fintype_index_of_rank_lt_aleph_0 Basis.fintypeIndexOfRankLtAleph0

/-- If a module has a finite dimension, all bases are indexed by a finite set. -/
theorem Basis.finite_index_of_rank_lt_aleph0 {ι : Type*} {s : Set ι} (b : Basis s R M)
    (h : Module.rank R M < ℵ₀) : s.Finite :=
  finite_def.2 (b.nonempty_fintype_index_of_rank_lt_aleph0 h)
#align basis.finite_index_of_rank_lt_aleph_0 Basis.finite_index_of_rank_lt_aleph0

theorem rank_span {v : ι → M} (hv : LinearIndependent R v) :
    Module.rank R ↑(span R (range v)) = #(range v) := by
  haveI := nontrivial_of_invariantBasisNumber R
  -- ⊢ Module.rank R { x // x ∈ span R (range v) } = #↑(range v)
  rw [← Cardinal.lift_inj, ← (Basis.span hv).mk_eq_rank,
    Cardinal.mk_range_eq_of_injective (@LinearIndependent.injective ι R M v _ _ _ _ hv)]
#align rank_span rank_span

theorem rank_span_set {s : Set M} (hs : LinearIndependent R (fun x => x : s → M)) :
    Module.rank R ↑(span R s) = #s := by
  rw [← @setOf_mem_eq _ s, ← Subtype.range_coe_subtype]
  -- ⊢ Module.rank R { x // x ∈ span R (range Subtype.val) } = #↑(range Subtype.val)
  exact rank_span hs
  -- 🎉 no goals
#align rank_span_set rank_span_set

/-- An induction (and recursion) principle for proving results about all submodules of a fixed
finite free module `M`. A property is true for all submodules of `M` if it satisfies the following
"inductive step": the property is true for a submodule `N` if it's true for all submodules `N'`
of `N` with the property that there exists `0 ≠ x ∈ N` such that the sum `N' + Rx` is direct. -/
def Submodule.inductionOnRank [IsDomain R] [Fintype ι] (b : Basis ι R M)
    (P : Submodule R M → Sort*) (ih : ∀ N : Submodule R M,
    (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (N : Submodule R M) : P N :=
  Submodule.inductionOnRankAux b P ih (Fintype.card ι) N fun hs hli => by
    simpa using b.card_le_card_of_linearIndependent hli
    -- 🎉 no goals
#align submodule.induction_on_rank Submodule.inductionOnRank

/-- If `S` a module-finite free `R`-algebra, then the `R`-rank of a nonzero `R`-free
ideal `I` of `S` is the same as the rank of `S`. -/
theorem Ideal.rank_eq {R S : Type*} [CommRing R] [StrongRankCondition R] [Ring S] [IsDomain S]
    [Algebra R S] {n m : Type*} [Fintype n] [Fintype m] (b : Basis n R S) {I : Ideal S}
    (hI : I ≠ ⊥) (c : Basis m R I) : Fintype.card m = Fintype.card n := by
  obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
  -- ⊢ Fintype.card m = Fintype.card n
  have : LinearIndependent R fun i => b i • a := by
    have hb := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    simp only [← smul_assoc, ← Finset.sum_smul, smul_eq_zero] at hg
    exact hg.resolve_right ha
  exact le_antisymm
    (b.card_le_card_of_linearIndependent (c.linearIndependent.map' (Submodule.subtype I)
      ((LinearMap.ker_eq_bot (f := (Submodule.subtype I : I →ₗ[R] S))).mpr Subtype.coe_injective)))
    (c.card_le_card_of_linearIndependent this)
#align ideal.rank_eq Ideal.rank_eq

variable (R)

@[simp]
theorem rank_self : Module.rank R R = 1 := by
  rw [← Cardinal.lift_inj, ← (Basis.singleton PUnit R).mk_eq_rank, Cardinal.mk_punit]
  -- 🎉 no goals
#align rank_self rank_self

end StrongRankCondition

section Free

variable [Ring K] [StrongRankCondition K]

variable [AddCommGroup V] [Module K V] [Module.Free K V]

variable [AddCommGroup V'] [Module K V'] [Module.Free K V']

variable [AddCommGroup V₁] [Module K V₁] [Module.Free K V₁]

namespace Module.Free

variable (K V)

/-- The rank of a free module `M` over `R` is the cardinality of `ChooseBasisIndex R M`. -/
theorem rank_eq_card_chooseBasisIndex : Module.rank K V = #(ChooseBasisIndex K V) :=
  (chooseBasis K V).mk_eq_rank''.symm
#align module.free.rank_eq_card_choose_basis_index Module.Free.rank_eq_card_chooseBasisIndex

/-- The rank of a free module `V` over an infinite scalar ring `K` is the cardinality of `V`
whenever `#R < #V`. -/
lemma rank_eq_mk_of_infinite_lt [Infinite K] (h_lt : lift.{v} #K < lift.{u} #V) :
    Module.rank K V = #V := by
  have : Infinite V := infinite_iff.mpr <| lift_le.mp <| le_trans (by simp) h_lt.le
  -- ⊢ Module.rank K V = #V
  have h : lift #V = lift #(ChooseBasisIndex K V →₀ K) := lift_mk_eq'.mpr ⟨(chooseBasis K V).repr⟩
  -- ⊢ Module.rank K V = #V
  simp only [mk_finsupp_lift_of_infinite', lift_id', ← rank_eq_card_chooseBasisIndex, lift_max,
    lift_lift] at h
  refine lift_inj.mp ((max_eq_iff.mp h.symm).resolve_right <| not_and_of_not_left _ ?_).left
  -- ⊢ ¬lift.{v, u} #K = lift.{max u v, v} #V
  exact (lift_umax.{v, u}.symm ▸ h_lt).ne
  -- 🎉 no goals

end Module.Free

open Module.Free

open Cardinal

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linearEquiv_of_lift_rank_eq
    (cnd : Cardinal.lift.{v'} (Module.rank K V) = Cardinal.lift.{v} (Module.rank K V')) :
    Nonempty (V ≃ₗ[K] V') := by
  obtain ⟨⟨_, B⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  -- ⊢ Nonempty (V ≃ₗ[K] V')
  obtain ⟨⟨_, B'⟩⟩ := Module.Free.exists_basis (R := K) (M := V')
  -- ⊢ Nonempty (V ≃ₗ[K] V')
  have : Cardinal.lift.{v', v} #_ = Cardinal.lift.{v, v'} #_ := by
    rw [B.mk_eq_rank'', cnd, B'.mk_eq_rank'']
  exact (Cardinal.lift_mk_eq.{v, v', 0}.1 this).map (B.equiv B')
  -- 🎉 no goals
#align nonempty_linear_equiv_of_lift_rank_eq nonempty_linearEquiv_of_lift_rank_eq

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linearEquiv_of_rank_eq (cond : Module.rank K V = Module.rank K V₁) :
    Nonempty (V ≃ₗ[K] V₁) :=
  nonempty_linearEquiv_of_lift_rank_eq <| congr_arg _ cond
#align nonempty_linear_equiv_of_rank_eq nonempty_linearEquiv_of_rank_eq

section

variable (V V' V₁)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def LinearEquiv.ofLiftRankEq
    (cond : Cardinal.lift.{v'} (Module.rank K V) = Cardinal.lift.{v} (Module.rank K V')) :
    V ≃ₗ[K] V' :=
  Classical.choice (nonempty_linearEquiv_of_lift_rank_eq cond)
#align linear_equiv.of_lift_rank_eq LinearEquiv.ofLiftRankEq

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def LinearEquiv.ofRankEq (cond : Module.rank K V = Module.rank K V₁) : V ≃ₗ[K] V₁ :=
  Classical.choice (nonempty_linearEquiv_of_rank_eq cond)
#align linear_equiv.of_rank_eq LinearEquiv.ofRankEq

end

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem LinearEquiv.nonempty_equiv_iff_lift_rank_eq : Nonempty (V ≃ₗ[K] V') ↔
    Cardinal.lift.{v'} (Module.rank K V) = Cardinal.lift.{v} (Module.rank K V') :=
  ⟨fun ⟨h⟩ => LinearEquiv.lift_rank_eq h, fun h => nonempty_linearEquiv_of_lift_rank_eq h⟩
#align linear_equiv.nonempty_equiv_iff_lift_rank_eq LinearEquiv.nonempty_equiv_iff_lift_rank_eq

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem LinearEquiv.nonempty_equiv_iff_rank_eq :
    Nonempty (V ≃ₗ[K] V₁) ↔ Module.rank K V = Module.rank K V₁ :=
  ⟨fun ⟨h⟩ => LinearEquiv.rank_eq h, fun h => nonempty_linearEquiv_of_rank_eq h⟩
#align linear_equiv.nonempty_equiv_iff_rank_eq LinearEquiv.nonempty_equiv_iff_rank_eq

/-- If `M` and `N` are free, then the rank of `M × N` is
`(Module.rank R M).lift + (Module.rank R N).lift`. -/
@[simp]
theorem rank_prod : Module.rank K (V × V') =
    Cardinal.lift.{v'} (Module.rank K V) + Cardinal.lift.{v, v'} (Module.rank K V') := by
  simpa [rank_eq_card_chooseBasisIndex K V, rank_eq_card_chooseBasisIndex K V', lift_umax,
    lift_umax'] using ((chooseBasis K V).prod (chooseBasis K V')).mk_eq_rank.symm
#align rank_prod rank_prod

/-- If `M` and `N` are free (and lie in the same universe), the rank of `M × N` is
  `(Module.rank R M) + (Module.rank R N)`. -/
theorem rank_prod' : Module.rank K (V × V₁) = Module.rank K V + Module.rank K V₁ := by simp
                                                                                       -- 🎉 no goals
#align rank_prod' rank_prod'

section Fintype

variable [∀ i, AddCommGroup (φ i)] [∀ i, Module K (φ i)] [∀ i, Module.Free K (φ i)]

open LinearMap

/-- The rank of a finite product of free modules is the sum of the ranks. -/
-- this result is not true without the freeness assumption
@[simp]
theorem rank_pi [Finite η] : Module.rank K (∀ i, φ i) =
    Cardinal.sum fun i => Module.rank K (φ i) := by
  cases nonempty_fintype η
  -- ⊢ Module.rank K ((i : η) → φ i) = sum fun i => Module.rank K (φ i)
  let B i := chooseBasis K (φ i)
  -- ⊢ Module.rank K ((i : η) → φ i) = sum fun i => Module.rank K (φ i)
  let b : Basis _ K (∀ i, φ i) := Pi.basis fun i => B i
  -- ⊢ Module.rank K ((i : η) → φ i) = sum fun i => Module.rank K (φ i)
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']
  -- 🎉 no goals
#align rank_pi rank_pi

variable [Fintype η]

theorem rank_fun {V η : Type u} [Fintype η] [AddCommGroup V] [Module K V] [Module.Free K V] :
    Module.rank K (η → V) = Fintype.card η * Module.rank K V := by
  rw [rank_pi, Cardinal.sum_const', Cardinal.mk_fintype]
  -- 🎉 no goals
#align rank_fun rank_fun

theorem rank_fun_eq_lift_mul : Module.rank K (η → V) =
    (Fintype.card η : Cardinal.{max u₁' v}) * Cardinal.lift.{u₁'} (Module.rank K V) :=
  by rw [rank_pi, Cardinal.sum_const, Cardinal.mk_fintype, Cardinal.lift_natCast]
     -- 🎉 no goals
#align rank_fun_eq_lift_mul rank_fun_eq_lift_mul

theorem rank_fun' : Module.rank K (η → K) = Fintype.card η := by
  rw [rank_fun_eq_lift_mul, rank_self, Cardinal.lift_one, mul_one, Cardinal.natCast_inj]
  -- 🎉 no goals
#align rank_fun' rank_fun'

theorem rank_fin_fun (n : ℕ) : Module.rank K (Fin n → K) = n := by simp [rank_fun']
                                                                   -- 🎉 no goals
#align rank_fin_fun rank_fin_fun

end Fintype

-- TODO: merge with the `Finrank` content
/-- An `n`-dimensional `K`-vector space is equivalent to `Fin n → K`. -/
def finDimVectorspaceEquiv (n : ℕ) (hn : Module.rank K V = n) : V ≃ₗ[K] Fin n → K := by
  haveI := nontrivial_of_invariantBasisNumber K
  -- ⊢ V ≃ₗ[K] Fin n → K
  have : Cardinal.lift.{u} (n : Cardinal.{v}) = Cardinal.lift.{v} (n : Cardinal.{u}) := by simp
  -- ⊢ V ≃ₗ[K] Fin n → K
  have hn := Cardinal.lift_inj.{v, u}.2 hn
  -- ⊢ V ≃ₗ[K] Fin n → K
  rw [this] at hn
  -- ⊢ V ≃ₗ[K] Fin n → K
  rw [← @rank_fin_fun K _ _ n] at hn
  -- ⊢ V ≃ₗ[K] Fin n → K
  haveI : Module.Free K (Fin n → K) := Module.Free.pi _ _
  -- ⊢ V ≃ₗ[K] Fin n → K
  exact Classical.choice (nonempty_linearEquiv_of_lift_rank_eq hn)
  -- 🎉 no goals
#align fin_dim_vectorspace_equiv finDimVectorspaceEquiv

end Free

section DivisionRing

variable [DivisionRing K]

variable [AddCommGroup V] [Module K V]

variable [AddCommGroup V'] [Module K V']

variable [AddCommGroup V₁] [Module K V₁]

/-- If a vector space has a finite dimension, the index set of `Basis.ofVectorSpace` is finite. -/
theorem Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0 (h : Module.rank K V < ℵ₀) :
    (Basis.ofVectorSpaceIndex K V).Finite :=
  finite_def.2 <| (Basis.ofVectorSpace K V).nonempty_fintype_index_of_rank_lt_aleph0 h
#align basis.finite_of_vector_space_index_of_rank_lt_aleph_0 Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0

-- TODO how far can we generalise this?
-- When `s` is finite, we could prove this for any ring satisfying the strong rank condition
-- using `linearIndependent_le_span'`
theorem rank_span_le (s : Set V) : Module.rank K (span K s) ≤ #s := by
  obtain ⟨b, hb, hsab, hlib⟩ := exists_linearIndependent K s
  -- ⊢ Module.rank K { x // x ∈ span K s } ≤ #↑s
  convert Cardinal.mk_le_mk_of_subset hb
  -- ⊢ Module.rank K { x // x ∈ span K s } = #↑b
  rw [← hsab, rank_span_set hlib]
  -- 🎉 no goals
#align rank_span_le rank_span_le

theorem rank_span_of_finset (s : Finset V) : Module.rank K (span K (↑s : Set V)) < ℵ₀ :=
  calc
    Module.rank K (span K (↑s : Set V)) ≤ #(↑s : Set V) := rank_span_le (s : Set V)
    _ = s.card := by rw [Finset.coe_sort_coe, Cardinal.mk_coe_finset]
                     -- 🎉 no goals
    _ < ℵ₀ := Cardinal.nat_lt_aleph0 _
#align rank_span_of_finset rank_span_of_finset

theorem rank_quotient_add_rank (p : Submodule K V) :
    Module.rank K (V ⧸ p) + Module.rank K p = Module.rank K V := by
  classical
    let ⟨f⟩ := quotient_prod_linearEquiv p
    exact rank_prod'.symm.trans f.rank_eq
#align rank_quotient_add_rank rank_quotient_add_rank

/-- rank-nullity theorem -/
theorem rank_range_add_rank_ker (f : V →ₗ[K] V₁) :
    Module.rank K (LinearMap.range f) + Module.rank K (LinearMap.ker f) = Module.rank K V := by
  haveI := fun p : Submodule K V => Classical.decEq (V ⧸ p)
  -- ⊢ Module.rank K { x // x ∈ LinearMap.range f } + Module.rank K { x // x ∈ Line …
  rw [← f.quotKerEquivRange.rank_eq, rank_quotient_add_rank]
  -- 🎉 no goals
#align rank_range_add_rank_ker rank_range_add_rank_ker

theorem rank_eq_of_surjective (f : V →ₗ[K] V₁) (h : Surjective f) :
    Module.rank K V = Module.rank K V₁ + Module.rank K (LinearMap.ker f) := by
  rw [← rank_range_add_rank_ker f, ← rank_range_of_surjective f h]
  -- 🎉 no goals
#align rank_eq_of_surjective rank_eq_of_surjective

/-- Given a family of `n` linearly independent vectors in a space of dimension `> n`, one may extend
the family by another vector while retaining linear independence. -/
theorem exists_linear_independent_cons_of_lt_rank {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (h : n < Module.rank K V) :
    ∃ (x : V), LinearIndependent K (Fin.cons x v) := by
  have A : Submodule.span K (range v) ≠ ⊤ := by
    intro H
    rw [← rank_top, ← H] at h
    have : Module.rank K (Submodule.span K (range v)) ≤ n := by
      have := Cardinal.mk_range_le_lift (f := v)
      simp only [Cardinal.lift_id'] at this
      exact (rank_span_le _).trans (this.trans (by simp))
    exact lt_irrefl _ (h.trans_le this)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ Submodule.span K (range v) := by
    contrapose! A
    exact Iff.mpr Submodule.eq_top_iff' A
  exact ⟨x, linearIndependent_fin_cons.2 ⟨hv, hx⟩⟩
  -- 🎉 no goals

/-- Given a family of `n` linearly independent vectors in a space of dimension `> n`, one may extend
the family by another vector while retaining linear independence. -/
theorem exists_linear_independent_snoc_of_lt_rank {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (h : n < Module.rank K V) :
    ∃ (x : V), LinearIndependent K (Fin.snoc v x) := by
  simpa [linearIndependent_fin_cons, ← linearIndependent_fin_snoc]
    using exists_linear_independent_cons_of_lt_rank hv h

/-- Given a nonzero vector in a space of dimension `> 1`, one may find another vector linearly
independent of the first one. -/
theorem exists_linear_independent_pair_of_one_lt_rank
    (h : 1 < Module.rank K V) {x : V} (hx : x ≠ 0) :
    ∃ y, LinearIndependent K ![x, y] := by
  obtain ⟨y, hy⟩ := exists_linear_independent_snoc_of_lt_rank (linearIndependent_unique ![x] hx) h
  -- ⊢ ∃ y, LinearIndependent K ![x, y]
  have : Fin.snoc ![x] y = ![x, y] := Iff.mp List.ofFn_inj rfl
  -- ⊢ ∃ y, LinearIndependent K ![x, y]
  rw [this] at hy
  -- ⊢ ∃ y, LinearIndependent K ![x, y]
  exact ⟨y, hy⟩
  -- 🎉 no goals

section

variable [AddCommGroup V₂] [Module K V₂]

variable [AddCommGroup V₃] [Module K V₃]

open LinearMap

/-- This is mostly an auxiliary lemma for `Submodule.rank_sup_add_rank_inf_eq`. -/
theorem rank_add_rank_split (db : V₂ →ₗ[K] V) (eb : V₃ →ₗ[K] V) (cd : V₁ →ₗ[K] V₂)
    (ce : V₁ →ₗ[K] V₃) (hde : ⊤ ≤ LinearMap.range db ⊔ LinearMap.range eb) (hgd : ker cd = ⊥)
    (eq : db.comp cd = eb.comp ce) (eq₂ : ∀ d e, db d = eb e → ∃ c, cd c = d ∧ ce c = e) :
    Module.rank K V + Module.rank K V₁ = Module.rank K V₂ + Module.rank K V₃ := by
  have hf : Surjective (coprod db eb) := by rwa [← range_eq_top, range_coprod, eq_top_iff]
  -- ⊢ Module.rank K V + Module.rank K V₁ = Module.rank K V₂ + Module.rank K V₃
  conv =>
    rhs
    rw [← rank_prod', rank_eq_of_surjective _ hf]
  congr 1
  -- ⊢ Module.rank K V₁ = Module.rank K { x // x ∈ ker (coprod db eb) }
  apply LinearEquiv.rank_eq
  -- ⊢ V₁ ≃ₗ[K] { x // x ∈ ker (coprod db eb) }
  let L : V₁ →ₗ[K] ker (coprod db eb) := by -- Porting note: this is needed to avoid a timeout
    refine' LinearMap.codRestrict _ (prod cd (-ce)) _
    · intro c
      simp only [add_eq_zero_iff_eq_neg, LinearMap.prod_apply, mem_ker, Pi.prod, coprod_apply,
        neg_neg, map_neg, neg_apply]
      exact LinearMap.ext_iff.1 eq c
  refine' LinearEquiv.ofBijective L ⟨_, _⟩
  -- ⊢ Injective ↑L
  · rw [← ker_eq_bot, ker_codRestrict, ker_prod, hgd, bot_inf_eq]
    -- 🎉 no goals
  · rw [← range_eq_top, eq_top_iff, range_codRestrict, ← map_le_iff_le_comap, Submodule.map_top,
      range_subtype]
    rintro ⟨d, e⟩
    -- ⊢ (d, e) ∈ ker (coprod db eb) → (d, e) ∈ LinearMap.range (LinearMap.prod cd (- …
    have h := eq₂ d (-e)
    -- ⊢ (d, e) ∈ ker (coprod db eb) → (d, e) ∈ LinearMap.range (LinearMap.prod cd (- …
    simp only [add_eq_zero_iff_eq_neg, LinearMap.prod_apply, mem_ker, SetLike.mem_coe,
      Prod.mk.inj_iff, coprod_apply, map_neg, neg_apply, LinearMap.mem_range, Pi.prod] at h ⊢
    intro hde
    -- ⊢ ∃ y, ↑cd y = d ∧ -↑ce y = e
    rcases h hde with ⟨c, h₁, h₂⟩
    -- ⊢ ∃ y, ↑cd y = d ∧ -↑ce y = e
    refine' ⟨c, h₁, _⟩
    -- ⊢ -↑ce c = e
    rw [h₂, _root_.neg_neg]
    -- 🎉 no goals
#align rank_add_rank_split rank_add_rank_split

theorem Submodule.rank_sup_add_rank_inf_eq (s t : Submodule K V) :
    Module.rank K (s ⊔ t : Submodule K V) + Module.rank K (s ⊓ t : Submodule K V) =
    Module.rank K s + Module.rank K t :=
  rank_add_rank_split (ofLe le_sup_left) (ofLe le_sup_right) (ofLe inf_le_left) (ofLe inf_le_right)
    (by
      rw [← map_le_map_iff' (ker_subtype <| s ⊔ t), Submodule.map_sup, Submodule.map_top, ←
        LinearMap.range_comp, ← LinearMap.range_comp, subtype_comp_ofLe, subtype_comp_ofLe,
        range_subtype, range_subtype, range_subtype])
    (ker_ofLe _ _ _) (by ext ⟨x, hx⟩; rfl)
                         -- ⊢ ↑(↑(LinearMap.comp (ofLe (_ : s ≤ s ⊔ t)) (ofLe (_ : s ⊓ t ≤ s))) { val := x …
                                      -- 🎉 no goals
    (by
      rintro ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ eq
      -- ⊢ ∃ c, ↑(ofLe (_ : s ⊓ t ≤ s)) c = { val := b₁, property := hb₁ } ∧ ↑(ofLe (_  …
      obtain rfl : b₁ = b₂ := congr_arg Subtype.val eq
      -- ⊢ ∃ c, ↑(ofLe (_ : s ⊓ t ≤ s)) c = { val := b₁, property := hb₁ } ∧ ↑(ofLe (_  …
      exact ⟨⟨b₁, hb₁, hb₂⟩, rfl, rfl⟩)
      -- 🎉 no goals
#align submodule.rank_sup_add_rank_inf_eq Submodule.rank_sup_add_rank_inf_eq

theorem Submodule.rank_add_le_rank_add_rank (s t : Submodule K V) :
    Module.rank K (s ⊔ t : Submodule K V) ≤ Module.rank K s + Module.rank K t := by
  rw [← Submodule.rank_sup_add_rank_inf_eq]
  -- ⊢ Module.rank K { x // x ∈ s ⊔ t } ≤ Module.rank K { x // x ∈ s ⊔ t } + Module …
  exact self_le_add_right _ _
  -- 🎉 no goals
#align submodule.rank_add_le_rank_add_rank Submodule.rank_add_le_rank_add_rank

end

end DivisionRing

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]

variable [AddCommGroup V'] [Module K V']

/-- The `ι` indexed basis on `V`, where `ι` is an empty type and `V` is zero-dimensional.

See also `FiniteDimensional.finBasis`.
-/
def Basis.ofRankEqZero {ι : Type*} [IsEmpty ι] (hV : Module.rank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := rank_zero_iff.1 hV
  Basis.empty _
#align basis.of_rank_eq_zero Basis.ofRankEqZero

@[simp]
theorem Basis.ofRankEqZero_apply {ι : Type*} [IsEmpty ι] (hV : Module.rank K V = 0) (i : ι) :
    Basis.ofRankEqZero hV i = 0 :=
  rfl
#align basis.of_rank_eq_zero_apply Basis.ofRankEqZero_apply

theorem le_rank_iff_exists_linearIndependent {c : Cardinal} :
    c ≤ Module.rank K V ↔ ∃ s : Set V, #s = c ∧ LinearIndependent K ((↑) : s → V) := by
  constructor
  -- ⊢ c ≤ Module.rank K V → ∃ s, #↑s = c ∧ LinearIndependent K Subtype.val
  · intro h
    -- ⊢ ∃ s, #↑s = c ∧ LinearIndependent K Subtype.val
    let t := Basis.ofVectorSpace K V
    -- ⊢ ∃ s, #↑s = c ∧ LinearIndependent K Subtype.val
    rw [← t.mk_eq_rank'', Cardinal.le_mk_iff_exists_subset] at h
    -- ⊢ ∃ s, #↑s = c ∧ LinearIndependent K Subtype.val
    rcases h with ⟨s, hst, hsc⟩
    -- ⊢ ∃ s, #↑s = c ∧ LinearIndependent K Subtype.val
    exact ⟨s, hsc, (ofVectorSpaceIndex.linearIndependent K V).mono hst⟩
    -- 🎉 no goals
  · rintro ⟨s, rfl, si⟩
    -- ⊢ #↑s ≤ Module.rank K V
    exact cardinal_le_rank_of_linearIndependent si
    -- 🎉 no goals
#align le_rank_iff_exists_linear_independent le_rank_iff_exists_linearIndependent

theorem le_rank_iff_exists_linearIndependent_finset {n : ℕ} : ↑n ≤ Module.rank K V ↔
    ∃ s : Finset V, s.card = n ∧ LinearIndependent K ((↑) : ↥(s : Set V) → V) := by
  simp only [le_rank_iff_exists_linearIndependent, Cardinal.mk_set_eq_nat_iff_finset]
  -- ⊢ (∃ s, (∃ t, ↑t = s ∧ Finset.card t = n) ∧ LinearIndependent K Subtype.val) ↔ …
  constructor
  -- ⊢ (∃ s, (∃ t, ↑t = s ∧ Finset.card t = n) ∧ LinearIndependent K Subtype.val) → …
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    -- ⊢ ∃ s, Finset.card s = Finset.card t ∧ LinearIndependent K Subtype.val
    exact ⟨t, rfl, si⟩
    -- 🎉 no goals
  · rintro ⟨s, rfl, si⟩
    -- ⊢ ∃ s_1, (∃ t, ↑t = s_1 ∧ Finset.card t = Finset.card s) ∧ LinearIndependent K …
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩
    -- 🎉 no goals
#align le_rank_iff_exists_linear_independent_finset le_rank_iff_exists_linearIndependent_finset

/-- A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
theorem rank_le_one_iff : Module.rank K V ≤ 1 ↔ ∃ v₀ : V, ∀ v, ∃ r : K, r • v₀ = v := by
  let b := Basis.ofVectorSpace K V
  -- ⊢ Module.rank K V ≤ 1 ↔ ∃ v₀, ∀ (v : V), ∃ r, r • v₀ = v
  constructor
  -- ⊢ Module.rank K V ≤ 1 → ∃ v₀, ∀ (v : V), ∃ r, r • v₀ = v
  · intro hd
    -- ⊢ ∃ v₀, ∀ (v : V), ∃ r, r • v₀ = v
    rw [← b.mk_eq_rank'', Cardinal.le_one_iff_subsingleton, subsingleton_coe] at hd
    -- ⊢ ∃ v₀, ∀ (v : V), ∃ r, r • v₀ = v
    rcases eq_empty_or_nonempty (ofVectorSpaceIndex K V) with (hb | ⟨⟨v₀, hv₀⟩⟩)
    -- ⊢ ∃ v₀, ∀ (v : V), ∃ r, r • v₀ = v
    · use 0
      -- ⊢ ∀ (v : V), ∃ r, r • 0 = v
      have h' : ∀ v : V, v = 0 := by simpa [hb, Submodule.eq_bot_iff] using b.span_eq.symm
      -- ⊢ ∀ (v : V), ∃ r, r • 0 = v
      intro v
      -- ⊢ ∃ r, r • 0 = v
      simp [h' v]
      -- 🎉 no goals
    · use v₀
      -- ⊢ ∀ (v : V), ∃ r, r • v₀ = v
      have h' : (K ∙ v₀) = ⊤ := by simpa [hd.eq_singleton_of_mem hv₀] using b.span_eq
      -- ⊢ ∀ (v : V), ∃ r, r • v₀ = v
      intro v
      -- ⊢ ∃ r, r • v₀ = v
      have hv : v ∈ (⊤ : Submodule K V) := mem_top
      -- ⊢ ∃ r, r • v₀ = v
      rwa [← h', mem_span_singleton] at hv
      -- 🎉 no goals
  · rintro ⟨v₀, hv₀⟩
    -- ⊢ Module.rank K V ≤ 1
    have h : (K ∙ v₀) = ⊤ := by
      ext
      simp [mem_span_singleton, hv₀]
    rw [← rank_top, ← h]
    -- ⊢ Module.rank K { x // x ∈ span K {v₀} } ≤ 1
    refine' (rank_span_le _).trans_eq _
    -- ⊢ #↑{v₀} = 1
    simp
    -- 🎉 no goals
#align rank_le_one_iff rank_le_one_iff

/-- A submodule has dimension at most `1` if and only if there is a
single vector in the submodule such that the submodule is contained in
its span. -/
theorem rank_submodule_le_one_iff (s : Submodule K V) :
    Module.rank K s ≤ 1 ↔ ∃ v₀ ∈ s, s ≤ K ∙ v₀ := by
  simp_rw [rank_le_one_iff, le_span_singleton_iff]
  -- ⊢ (∃ v₀, ∀ (v : { x // x ∈ s }), ∃ r, r • v₀ = v) ↔ ∃ v₀, v₀ ∈ s ∧ ∀ (v : V),  …
  constructor
  -- ⊢ (∃ v₀, ∀ (v : { x // x ∈ s }), ∃ r, r • v₀ = v) → ∃ v₀, v₀ ∈ s ∧ ∀ (v : V),  …
  · rintro ⟨⟨v₀, hv₀⟩, h⟩
    -- ⊢ ∃ v₀, v₀ ∈ s ∧ ∀ (v : V), v ∈ s → ∃ r, r • v₀ = v
    use v₀, hv₀
    -- ⊢ ∀ (v : V), v ∈ s → ∃ r, r • v₀ = v
    intro v hv
    -- ⊢ ∃ r, r • v₀ = v
    obtain ⟨r, hr⟩ := h ⟨v, hv⟩
    -- ⊢ ∃ r, r • v₀ = v
    use r
    -- ⊢ r • v₀ = v
    simp_rw [Subtype.ext_iff, coe_smul] at hr
    -- ⊢ r • v₀ = v
    exact hr
    -- 🎉 no goals
  · rintro ⟨v₀, hv₀, h⟩
    -- ⊢ ∃ v₀, ∀ (v : { x // x ∈ s }), ∃ r, r • v₀ = v
    use ⟨v₀, hv₀⟩
    -- ⊢ ∀ (v : { x // x ∈ s }), ∃ r, r • { val := v₀, property := hv₀ } = v
    rintro ⟨v, hv⟩
    -- ⊢ ∃ r, r • { val := v₀, property := hv₀ } = { val := v, property := hv }
    obtain ⟨r, hr⟩ := h v hv
    -- ⊢ ∃ r, r • { val := v₀, property := hv₀ } = { val := v, property := hv }
    use r
    -- ⊢ r • { val := v₀, property := hv₀ } = { val := v, property := hv }
    simp_rw [Subtype.ext_iff, coe_smul]
    -- ⊢ r • v₀ = v
    exact hr
    -- 🎉 no goals
#align rank_submodule_le_one_iff rank_submodule_le_one_iff

/-- A submodule has dimension at most `1` if and only if there is a
single vector, not necessarily in the submodule, such that the
submodule is contained in its span. -/
theorem rank_submodule_le_one_iff' (s : Submodule K V) :
    Module.rank K s ≤ 1 ↔ ∃ v₀, s ≤ K ∙ v₀ := by
  rw [rank_submodule_le_one_iff]
  -- ⊢ (∃ v₀, v₀ ∈ s ∧ s ≤ span K {v₀}) ↔ ∃ v₀, s ≤ span K {v₀}
  constructor
  -- ⊢ (∃ v₀, v₀ ∈ s ∧ s ≤ span K {v₀}) → ∃ v₀, s ≤ span K {v₀}
  · rintro ⟨v₀, _, h⟩
    -- ⊢ ∃ v₀, s ≤ span K {v₀}
    exact ⟨v₀, h⟩
    -- 🎉 no goals
  · rintro ⟨v₀, h⟩
    -- ⊢ ∃ v₀, v₀ ∈ s ∧ s ≤ span K {v₀}
    by_cases hw : ∃ w : V, w ∈ s ∧ w ≠ 0
    -- ⊢ ∃ v₀, v₀ ∈ s ∧ s ≤ span K {v₀}
    · rcases hw with ⟨w, hw, hw0⟩
      -- ⊢ ∃ v₀, v₀ ∈ s ∧ s ≤ span K {v₀}
      use w, hw
      -- ⊢ s ≤ span K {w}
      rcases mem_span_singleton.1 (h hw) with ⟨r', rfl⟩
      -- ⊢ s ≤ span K {r' • v₀}
      have h0 : r' ≠ 0 := by
        rintro rfl
        simp at hw0
      rwa [span_singleton_smul_eq (IsUnit.mk0 _ h0) _]
      -- 🎉 no goals
    · push_neg at hw
      -- ⊢ ∃ v₀, v₀ ∈ s ∧ s ≤ span K {v₀}
      rw [← Submodule.eq_bot_iff] at hw
      -- ⊢ ∃ v₀, v₀ ∈ s ∧ s ≤ span K {v₀}
      simp [hw]
      -- 🎉 no goals
#align rank_submodule_le_one_iff' rank_submodule_le_one_iff'

theorem Submodule.rank_le_one_iff_isPrincipal (W : Submodule K V) :
    Module.rank K W ≤ 1 ↔ W.IsPrincipal := by
  simp only [rank_le_one_iff, Submodule.IsPrincipal_iff, le_antisymm_iff, le_span_singleton_iff,
    span_singleton_le_iff_mem]
  constructor
  -- ⊢ (∃ v₀, ∀ (v : { x // x ∈ W }), ∃ r, r • v₀ = v) → ∃ a, (∀ (v : V), v ∈ W → ∃ …
  · rintro ⟨⟨m, hm⟩, hm'⟩
    -- ⊢ ∃ a, (∀ (v : V), v ∈ W → ∃ r, r • a = v) ∧ a ∈ W
    choose f hf using hm'
    -- ⊢ ∃ a, (∀ (v : V), v ∈ W → ∃ r, r • a = v) ∧ a ∈ W
    exact ⟨m, ⟨fun v hv => ⟨f ⟨v, hv⟩, congr_arg ((↑) : W → V) (hf ⟨v, hv⟩)⟩, hm⟩⟩
    -- 🎉 no goals
  · rintro ⟨a, ⟨h, ha⟩⟩
    -- ⊢ ∃ v₀, ∀ (v : { x // x ∈ W }), ∃ r, r • v₀ = v
    choose f hf using h
    -- ⊢ ∃ v₀, ∀ (v : { x // x ∈ W }), ∃ r, r • v₀ = v
    exact ⟨⟨a, ha⟩, fun v => ⟨f v.1 v.2, Subtype.ext (hf v.1 v.2)⟩⟩
    -- 🎉 no goals
#align submodule.rank_le_one_iff_is_principal Submodule.rank_le_one_iff_isPrincipal

theorem Module.rank_le_one_iff_top_isPrincipal :
    Module.rank K V ≤ 1 ↔ (⊤ : Submodule K V).IsPrincipal := by
  rw [← Submodule.rank_le_one_iff_isPrincipal, rank_top]
  -- 🎉 no goals
#align module.rank_le_one_iff_top_is_principal Module.rank_le_one_iff_top_isPrincipal

end DivisionRing

end Module

/-! ### The rank of a linear map -/


namespace LinearMap

section Ring

variable [Ring K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]

variable [AddCommGroup V'] [Module K V']

/-- `rank f` is the rank of a `LinearMap` `f`, defined as the dimension of `f.range`. -/
abbrev rank (f : V →ₗ[K] V') : Cardinal :=
  Module.rank K (LinearMap.range f)
#align linear_map.rank LinearMap.rank

theorem rank_le_range (f : V →ₗ[K] V') : rank f ≤ Module.rank K V' :=
  rank_submodule_le _
#align linear_map.rank_le_range LinearMap.rank_le_range

theorem rank_le_domain (f : V →ₗ[K] V₁) : rank f ≤ Module.rank K V :=
  rank_range_le _
#align linear_map.rank_le_domain LinearMap.rank_le_domain

@[simp]
theorem rank_zero [Nontrivial K] : rank (0 : V →ₗ[K] V') = 0 := by
  rw [rank, LinearMap.range_zero, rank_bot]
  -- 🎉 no goals
#align linear_map.rank_zero LinearMap.rank_zero

variable [AddCommGroup V''] [Module K V'']

theorem rank_comp_le_left (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') : rank (f.comp g) ≤ rank f := by
  refine' rank_le_of_submodule _ _ _
  -- ⊢ range (comp f g) ≤ range f
  rw [LinearMap.range_comp]
  -- ⊢ Submodule.map f (range g) ≤ range f
  exact LinearMap.map_le_range
  -- 🎉 no goals
#align linear_map.rank_comp_le_left LinearMap.rank_comp_le_left

theorem lift_rank_comp_le_right (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') :
    Cardinal.lift.{v'} (rank (f.comp g)) ≤ Cardinal.lift.{v''} (rank g) := by
  rw [rank, rank, LinearMap.range_comp]; exact lift_rank_map_le _ _
  -- ⊢ lift.{v', v''} (Module.rank K { x // x ∈ Submodule.map f (range g) }) ≤ lift …
                                         -- 🎉 no goals
#align linear_map.lift_rank_comp_le_right LinearMap.lift_rank_comp_le_right

/-- The rank of the composition of two maps is less than the minimum of their ranks. -/
theorem lift_rank_comp_le (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') :
    Cardinal.lift.{v'} (rank (f.comp g)) ≤
      min (Cardinal.lift.{v'} (rank f)) (Cardinal.lift.{v''} (rank g)) :=
  le_min (Cardinal.lift_le.mpr <| rank_comp_le_left _ _) (lift_rank_comp_le_right _ _)
#align linear_map.lift_rank_comp_le LinearMap.lift_rank_comp_le

variable [AddCommGroup V'₁] [Module K V'₁]

theorem rank_comp_le_right (g : V →ₗ[K] V') (f : V' →ₗ[K] V'₁) : rank (f.comp g) ≤ rank g := by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le_right g f
  -- 🎉 no goals
#align linear_map.rank_comp_le_right LinearMap.rank_comp_le_right

/-- The rank of the composition of two maps is less than the minimum of their ranks.

See `lift_rank_comp_le` for the universe-polymorphic version. -/
theorem rank_comp_le (g : V →ₗ[K] V') (f : V' →ₗ[K] V'₁) :
    rank (f.comp g) ≤ min (rank f) (rank g) := by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le g f
  -- 🎉 no goals
#align linear_map.rank_comp_le LinearMap.rank_comp_le

end Ring

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]

variable [AddCommGroup V'] [Module K V']

theorem rank_add_le (f g : V →ₗ[K] V') : rank (f + g) ≤ rank f + rank g :=
  calc
    rank (f + g) ≤ Module.rank K (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') := by
      refine' rank_le_of_submodule _ _ _
      -- ⊢ range (f + g) ≤ range f ⊔ range g
      exact LinearMap.range_le_iff_comap.2 <| eq_top_iff'.2 fun x =>
        show f x + g x ∈ (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') from
        mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
    _ ≤ rank f + rank g := Submodule.rank_add_le_rank_add_rank _ _
#align linear_map.rank_add_le LinearMap.rank_add_le

theorem rank_finset_sum_le {η} (s : Finset η) (f : η → V →ₗ[K] V') :
    rank (∑ d in s, f d) ≤ ∑ d in s, rank (f d) :=
  @Finset.sum_hom_rel _ _ _ _ _ (fun a b => rank a ≤ b) f (fun d => rank (f d)) s
    (le_of_eq rank_zero) fun _ _ _ h => le_trans (rank_add_le _ _) (add_le_add_left h _)
#align linear_map.rank_finset_sum_le LinearMap.rank_finset_sum_le

theorem le_rank_iff_exists_linearIndependent {c : Cardinal} {f : V →ₗ[K] V'} :
    c ≤ rank f ↔ ∃ s : Set V, Cardinal.lift.{v'} #s =
    Cardinal.lift.{v} c ∧ LinearIndependent K fun x : s => f x := by
  rcases f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict with ⟨g, hg⟩
  -- ⊢ c ≤ rank f ↔ ∃ s, lift.{v', v} #↑s = lift.{v, v'} c ∧ LinearIndependent K fu …
  have fg : LeftInverse f.rangeRestrict g := LinearMap.congr_fun hg
  -- ⊢ c ≤ rank f ↔ ∃ s, lift.{v', v} #↑s = lift.{v, v'} c ∧ LinearIndependent K fu …
  refine' ⟨fun h => _, _⟩
  -- ⊢ ∃ s, lift.{v', v} #↑s = lift.{v, v'} c ∧ LinearIndependent K fun x => ↑f ↑x
  · rcases _root_.le_rank_iff_exists_linearIndependent.1 h with ⟨s, rfl, si⟩
    -- ⊢ ∃ s_1, lift.{v', v} #↑s_1 = lift.{v, v'} #↑s ∧ LinearIndependent K fun x =>  …
    refine' ⟨g '' s, Cardinal.mk_image_eq_lift _ _ fg.injective, _⟩
    -- ⊢ LinearIndependent K fun x => ↑f ↑x
    replace fg : ∀ x, f (g x) = x
    -- ⊢ ∀ (x : { x // x ∈ range f }), ↑f (↑g x) = ↑x
    · intro x
      -- ⊢ ↑f (↑g x) = ↑x
      convert congr_arg Subtype.val (fg x)
      -- 🎉 no goals
    replace si : LinearIndependent K fun x : s => f (g x)
    -- ⊢ LinearIndependent K fun x => ↑f (↑g ↑x)
    · simpa only [fg] using si.map' _ (ker_subtype _)
      -- 🎉 no goals
    exact si.image_of_comp s g f
    -- 🎉 no goals
  · rintro ⟨s, hsc, si⟩
    -- ⊢ c ≤ rank f
    have : LinearIndependent K fun x : s => f.rangeRestrict x :=
      LinearIndependent.of_comp f.range.subtype (by convert si)
    convert cardinal_le_rank_of_linearIndependent this.image
    -- ⊢ c = #↑(↑(rangeRestrict f) '' s)
    rw [← Cardinal.lift_inj, ← hsc, Cardinal.mk_image_eq_of_injOn_lift]
    -- ⊢ InjOn (↑(rangeRestrict f)) s
    exact injOn_iff_injective.2 this.injective
    -- 🎉 no goals
#align linear_map.le_rank_iff_exists_linear_independent LinearMap.le_rank_iff_exists_linearIndependent

theorem le_rank_iff_exists_linearIndependent_finset {n : ℕ} {f : V →ₗ[K] V'} :
    ↑n ≤ rank f ↔ ∃ s : Finset V, s.card = n ∧ LinearIndependent K fun x : (s : Set V) => f x := by
  simp only [le_rank_iff_exists_linearIndependent, Cardinal.lift_natCast, Cardinal.lift_eq_nat_iff,
    Cardinal.mk_set_eq_nat_iff_finset]
  constructor
  -- ⊢ (∃ s, (∃ t, ↑t = s ∧ Finset.card t = n) ∧ LinearIndependent K fun x => ↑f ↑x …
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    -- ⊢ ∃ s, Finset.card s = Finset.card t ∧ LinearIndependent K fun x => ↑f ↑x
    exact ⟨t, rfl, si⟩
    -- 🎉 no goals
  · rintro ⟨s, rfl, si⟩
    -- ⊢ ∃ s_1, (∃ t, ↑t = s_1 ∧ Finset.card t = Finset.card s) ∧ LinearIndependent K …
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩
    -- 🎉 no goals
#align linear_map.le_rank_iff_exists_linear_independent_finset LinearMap.le_rank_iff_exists_linearIndependent_finset

end DivisionRing

end LinearMap
