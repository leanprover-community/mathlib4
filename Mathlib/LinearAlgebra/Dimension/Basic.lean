/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Scott Morrison
-/
import Mathlib.LinearAlgebra.LinearIndependent

#align_import linear_algebra.dimension from "leanprover-community/mathlib"@"47a5f8186becdbc826190ced4312f8199f9db6a5"

/-!
# Dimension of modules and vector spaces

## Main definitions

* The rank of a module is defined as `Module.rank : Cardinal`.
  This is defined as the supremum of the cardinalities of linearly independent subsets.

## Main statements

* `LinearMap.rank_le_of_injective`: the source of an injective linear map has dimension
  at most that of the target.
* `LinearMap.rank_le_of_surjective`: the target of a surjective linear map has dimension
  at most that of that source.

## Implementation notes

Many theorems in this file are not universe-generic when they relate dimensions
in different universes. They should be as general as they can be without
inserting `lift`s. The types `M`, `M'`, ... all live in different universes,
and `M₁`, `M₂`, ... all live in the same universe.
-/


noncomputable section

universe w w' u u' v v'

variable {R : Type u} {R' : Type u'} {M M₁ : Type v} {M' : Type v'}

open Cardinal Submodule Function Set

section Module

section

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable (R M)

/-- The rank of a module, defined as a term of type `Cardinal`.

We define this as the supremum of the cardinalities of linearly independent subsets.

For a free module over any ring satisfying the strong rank condition
(e.g. left-noetherian rings, commutative rings, and in particular division rings and fields),
this is the same as the dimension of the space (i.e. the cardinality of any basis).

In particular this agrees with the usual notion of the dimension of a vector space.

-/
protected irreducible_def Module.rank : Cardinal :=
  ⨆ ι : { s : Set M // LinearIndependent R ((↑) : s → M) }, (#ι.1)
#align module.rank Module.rank

theorem rank_le_card : Module.rank R M ≤ #M :=
  (Module.rank_def _ _).trans_le (ciSup_le' fun _ ↦ mk_set_le _)

lemma nonempty_linearIndependent_set : Nonempty {s : Set M // LinearIndependent R ((↑) : s → M)} :=
  ⟨⟨∅, linearIndependent_empty _ _⟩⟩

end

variable [Ring R] [Ring R'] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M₁]
variable [Module R M] [Module R M'] [Module R M₁] [Module R' M'] [Module R' M₁]

namespace LinearIndependent

variable [Nontrivial R]

theorem cardinal_lift_le_rank {ι : Type w} {v : ι → M}
    (hv : LinearIndependent R v) :
    Cardinal.lift.{v} #ι ≤ Cardinal.lift.{w} (Module.rank R M) := by
  rw [Module.rank]
  refine le_trans ?_ (lift_le.mpr <| le_ciSup (bddAbove_range.{v, v} _) ⟨_, hv.coe_range⟩)
  exact lift_mk_le'.mpr ⟨(Equiv.ofInjective _ hv.injective).toEmbedding⟩
#align cardinal_lift_le_rank_of_linear_independent LinearIndependent.cardinal_lift_le_rank
#align cardinal_lift_le_rank_of_linear_independent' LinearIndependent.cardinal_lift_le_rank

lemma aleph0_le_rank {ι : Type w} [Infinite ι] {v : ι → M}
    (hv : LinearIndependent R v) : ℵ₀ ≤ Module.rank R M :=
  aleph0_le_lift.mp <| (aleph0_le_lift.mpr <| aleph0_le_mk ι).trans hv.cardinal_lift_le_rank

theorem cardinal_le_rank {ι : Type v} {v : ι → M}
    (hv : LinearIndependent R v) : #ι ≤ Module.rank R M := by
  simpa using hv.cardinal_lift_le_rank
#align cardinal_le_rank_of_linear_independent LinearIndependent.cardinal_le_rank

theorem cardinal_le_rank' {s : Set M}
    (hs : LinearIndependent R (fun x => x : s → M)) : #s ≤ Module.rank R M :=
  hs.cardinal_le_rank
#align cardinal_le_rank_of_linear_independent' LinearIndependent.cardinal_le_rank'

end LinearIndependent

@[deprecated (since := "2023-12-27")]
alias cardinal_lift_le_rank_of_linearIndependent := LinearIndependent.cardinal_lift_le_rank
@[deprecated (since := "2023-12-27")]
alias cardinal_lift_le_rank_of_linearIndependent' := LinearIndependent.cardinal_lift_le_rank
@[deprecated (since := "2023-12-27")]
alias cardinal_le_rank_of_linearIndependent := LinearIndependent.cardinal_le_rank
@[deprecated (since := "2023-12-27")]
alias cardinal_le_rank_of_linearIndependent' := LinearIndependent.cardinal_le_rank'

section SurjectiveInjective

section Module

/-- If `M / R` and `M' / R'` are modules, `i : R' → R` is a map which sends non-zero elements to
non-zero elements, `j : M →+ M'` is an injective group homomorphism, such that the scalar
multiplications on `M` and `M'` are compatible, then the rank of `M / R` is smaller than or equal to
the rank of `M' / R'`. As a special case, taking `R = R'` it is
`LinearMap.lift_rank_le_of_injective`. -/
theorem lift_rank_le_of_injective_injective (i : R' → R) (j : M →+ M')
    (hi : ∀ r, i r = 0 → r = 0) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    lift.{v'} (Module.rank R M) ≤ lift.{v} (Module.rank R' M') := by
  simp_rw [Module.rank, lift_iSup (bddAbove_range.{v', v'} _), lift_iSup (bddAbove_range.{v, v} _)]
  exact ciSup_mono' (bddAbove_range.{v', v} _) fun ⟨s, h⟩ ↦ ⟨⟨j '' s,
    (h.map_of_injective_injective i j hi (fun _ _ ↦ hj <| by rwa [j.map_zero]) hc).image⟩,
      lift_mk_le'.mpr ⟨(Equiv.Set.image j s hj).toEmbedding⟩⟩

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map which maps zero to zero,
`j : M →+ M'` is an injective group homomorphism, such that the scalar multiplications on `M` and
`M'` are compatible, then the rank of `M / R` is smaller than or equal to the rank of `M' / R'`.
As a special case, taking `R = R'` it is `LinearMap.lift_rank_le_of_injective`. -/
theorem lift_rank_le_of_surjective_injective (i : ZeroHom R R') (j : M →+ M')
    (hi : Surjective i) (hj : Injective j) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    lift.{v'} (Module.rank R M) ≤ lift.{v} (Module.rank R' M') := by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine lift_rank_le_of_injective_injective i' j (fun _ h ↦ ?_) hj fun r m ↦ ?_
  · apply_fun i at h
    rwa [hi', i.map_zero] at h
  rw [hc (i' r) m, hi']

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a bijective map which maps zero to zero,
`j : M ≃+ M'` is a group isomorphism, such that the scalar multiplications on `M` and `M'` are
compatible, then the rank of `M / R` is equal to the rank of `M' / R'`.
As a special case, taking `R = R'` it is `LinearEquiv.lift_rank_eq`. -/
theorem lift_rank_eq_of_equiv_equiv (i : ZeroHom R R') (j : M ≃+ M')
    (hi : Bijective i) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    lift.{v'} (Module.rank R M) = lift.{v} (Module.rank R' M') :=
  (lift_rank_le_of_surjective_injective i j hi.2 j.injective hc).antisymm <|
    lift_rank_le_of_injective_injective i j.symm (fun _ _ ↦ hi.1 <| by rwa [i.map_zero])
      j.symm.injective fun _ _ ↦ j.symm_apply_eq.2 <| by erw [hc, j.apply_symm_apply]

/-- The same-universe version of `lift_rank_le_of_injective_injective`. -/
theorem rank_le_of_injective_injective (i : R' → R) (j : M →+ M₁)
    (hi : ∀ r, i r = 0 → r = 0) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    Module.rank R M ≤ Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc

/-- The same-universe version of `lift_rank_le_of_surjective_injective`. -/
theorem rank_le_of_surjective_injective (i : ZeroHom R R') (j : M →+ M₁)
    (hi : Surjective i) (hj : Injective j)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.rank R M ≤ Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc

/-- The same-universe version of `lift_rank_eq_of_equiv_equiv`. -/
theorem rank_eq_of_equiv_equiv (i : ZeroHom R R') (j : M ≃+ M₁)
    (hi : Bijective i) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.rank R M = Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hi hc

end Module

namespace Algebra

variable {R : Type w} {S : Type v} [CommRing R] [Ring S] [Algebra R S]
  {R' : Type w'} {S' : Type v'} [CommRing R'] [Ring S'] [Algebra R' S']

/-- If `S / R` and `S' / R'` are algebras, `i : R' →+* R` and `j : S →+* S'` are injective ring
homomorphisms, such that `R' → R → S → S'` and `R' → S'` commute, then the rank of `S / R` is
smaller than or equal to the rank of `S' / R'`. -/
theorem lift_rank_le_of_injective_injective
    (i : R' →+* R) (j : S →+* S') (hi : Injective i) (hj : Injective j)
    (hc : (j.comp (algebraMap R S)).comp i = algebraMap R' S') :
    lift.{v'} (Module.rank R S) ≤ lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_le_of_injective_injective i j
    (fun _ _ ↦ hi <| by rwa [i.map_zero]) hj fun r _ ↦ ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp_rw [smul_def, AddMonoidHom.coe_coe, map_mul, this]

/-- If `S / R` and `S' / R'` are algebras, `i : R →+* R'` is a surjective ring homomorphism,
`j : S →+* S'` is an injective ring homomorphism, such that `R → R' → S'` and `R → S → S'` commute,
then the rank of `S / R` is smaller than or equal to the rank of `S' / R'`. -/
theorem lift_rank_le_of_surjective_injective
    (i : R →+* R') (j : S →+* S') (hi : Surjective i) (hj : Injective j)
    (hc : (algebraMap R' S').comp i = j.comp (algebraMap R S)) :
    lift.{v'} (Module.rank R S) ≤ lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_le_of_surjective_injective i j hi hj fun r _ ↦ ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp only [smul_def, AddMonoidHom.coe_coe, map_mul, ZeroHom.coe_coe, this]

/-- If `S / R` and `S' / R'` are algebras, `i : R ≃+* R'` and `j : S ≃+* S'` are
ring isomorphisms, such that `R → R' → S'` and `R → S → S'` commute,
then the rank of `S / R` is equal to the rank of `S' / R'`. -/
theorem lift_rank_eq_of_equiv_equiv (i : R ≃+* R') (j : S ≃+* S')
    (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) :
    lift.{v'} (Module.rank R S) = lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_eq_of_equiv_equiv i j i.bijective fun r _ ↦ ?_
  have := congr($hc r)
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, comp_apply] at this
  simp only [smul_def, RingEquiv.coe_toAddEquiv, map_mul, ZeroHom.coe_coe, this]

variable {S' : Type v} [CommRing R'] [Ring S'] [Algebra R' S']

/-- The same-universe version of `Algebra.lift_rank_le_of_injective_injective`. -/
theorem rank_le_of_injective_injective
    (i : R' →+* R) (j : S →+* S') (hi : Injective i) (hj : Injective j)
    (hc : (j.comp (algebraMap R S)).comp i = algebraMap R' S') :
    Module.rank R S ≤ Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc

/-- The same-universe version of `Algebra.lift_rank_le_of_surjective_injective`. -/
theorem rank_le_of_surjective_injective
    (i : R →+* R') (j : S →+* S') (hi : Surjective i) (hj : Injective j)
    (hc : (algebraMap R' S').comp i = j.comp (algebraMap R S)) :
    Module.rank R S ≤ Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc

/-- The same-universe version of `Algebra.lift_rank_eq_of_equiv_equiv`. -/
theorem rank_eq_of_equiv_equiv (i : R ≃+* R') (j : S ≃+* S')
    (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) :
    Module.rank R S = Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hc

end Algebra

end SurjectiveInjective

section

theorem LinearMap.lift_rank_le_of_injective (f : M →ₗ[R] M') (i : Injective f) :
    Cardinal.lift.{v'} (Module.rank R M) ≤ Cardinal.lift.{v} (Module.rank R M') :=
  lift_rank_le_of_injective_injective (RingHom.id R) f (fun _ h ↦ h) i f.map_smul
#align linear_map.lift_rank_le_of_injective LinearMap.lift_rank_le_of_injective

theorem LinearMap.rank_le_of_injective (f : M →ₗ[R] M₁) (i : Injective f) :
    Module.rank R M ≤ Module.rank R M₁ :=
  Cardinal.lift_le.1 (f.lift_rank_le_of_injective i)
#align linear_map.rank_le_of_injective LinearMap.rank_le_of_injective

/-- The rank of the range of a linear map is at most the rank of the source. -/
-- The proof is: a free submodule of the range lifts to a free submodule of the
-- source, by arbitrarily lifting a basis.
theorem lift_rank_range_le (f : M →ₗ[R] M') : Cardinal.lift.{v}
    (Module.rank R (LinearMap.range f)) ≤ Cardinal.lift.{v'} (Module.rank R M) := by
  simp only [Module.rank_def]
  rw [Cardinal.lift_iSup (Cardinal.bddAbove_range.{v', v'} _)]
  apply ciSup_le'
  rintro ⟨s, li⟩
  apply le_trans
  swap
  · apply Cardinal.lift_le.mpr
    refine le_ciSup (Cardinal.bddAbove_range.{v, v} _) ⟨rangeSplitting f '' s, ?_⟩
    apply LinearIndependent.of_comp f.rangeRestrict
    convert li.comp (Equiv.Set.rangeSplittingImageEquiv f s) (Equiv.injective _) using 1
  · exact (Cardinal.lift_mk_eq'.mpr ⟨Equiv.Set.rangeSplittingImageEquiv f s⟩).ge
#align lift_rank_range_le lift_rank_range_le

theorem rank_range_le (f : M →ₗ[R] M₁) : Module.rank R (LinearMap.range f) ≤ Module.rank R M := by
  simpa using lift_rank_range_le f
#align rank_range_le rank_range_le

theorem lift_rank_map_le (f : M →ₗ[R] M') (p : Submodule R M) :
    Cardinal.lift.{v} (Module.rank R (p.map f)) ≤ Cardinal.lift.{v'} (Module.rank R p) := by
  have h := lift_rank_range_le (f.comp (Submodule.subtype p))
  rwa [LinearMap.range_comp, range_subtype] at h
#align lift_rank_map_le lift_rank_map_le

theorem rank_map_le (f : M →ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map f) ≤ Module.rank R p := by simpa using lift_rank_map_le f p
#align rank_map_le rank_map_le

theorem rank_le_of_submodule (s t : Submodule R M) (h : s ≤ t) :
    Module.rank R s ≤ Module.rank R t :=
  (Submodule.inclusion h).rank_le_of_injective fun ⟨x, _⟩ ⟨y, _⟩ eq =>
    Subtype.eq <| show x = y from Subtype.ext_iff_val.1 eq
#align rank_le_of_submodule rank_le_of_submodule

/-- Two linearly equivalent vector spaces have the same dimension, a version with different
universes. -/
theorem LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') :
    Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') := by
  apply le_antisymm
  · exact f.toLinearMap.lift_rank_le_of_injective f.injective
  · exact f.symm.toLinearMap.lift_rank_le_of_injective f.symm.injective
#align linear_equiv.lift_rank_eq LinearEquiv.lift_rank_eq

/-- Two linearly equivalent vector spaces have the same dimension. -/
theorem LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank R M = Module.rank R M₁ :=
  Cardinal.lift_inj.1 f.lift_rank_eq
#align linear_equiv.rank_eq LinearEquiv.rank_eq

theorem lift_rank_range_of_injective (f : M →ₗ[R] M') (h : Injective f) :
    lift.{v} (Module.rank R (LinearMap.range f)) = lift.{v'} (Module.rank R M) :=
  (LinearEquiv.ofInjective f h).lift_rank_eq.symm

theorem rank_range_of_injective (f : M →ₗ[R] M₁) (h : Injective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M :=
  (LinearEquiv.ofInjective f h).rank_eq.symm
#align rank_eq_of_injective rank_range_of_injective

theorem LinearEquiv.lift_rank_map_eq (f : M ≃ₗ[R] M') (p : Submodule R M) :
    lift.{v} (Module.rank R (p.map (f : M →ₗ[R] M'))) = lift.{v'} (Module.rank R p) :=
  (f.submoduleMap p).lift_rank_eq.symm

/-- Pushforwards of submodules along a `LinearEquiv` have the same dimension. -/
theorem LinearEquiv.rank_map_eq (f : M ≃ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map (f : M →ₗ[R] M₁)) = Module.rank R p :=
  (f.submoduleMap p).rank_eq.symm
#align linear_equiv.rank_map_eq LinearEquiv.rank_map_eq

variable (R M)

@[simp]
theorem rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M :=
  (LinearEquiv.ofTop ⊤ rfl).rank_eq
#align rank_top rank_top

variable {R M}

theorem rank_range_of_surjective (f : M →ₗ[R] M') (h : Surjective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M' := by
  rw [LinearMap.range_eq_top.2 h, rank_top]
#align rank_range_of_surjective rank_range_of_surjective

theorem rank_submodule_le (s : Submodule R M) : Module.rank R s ≤ Module.rank R M := by
  rw [← rank_top R M]
  exact rank_le_of_submodule _ _ le_top
#align rank_submodule_le rank_submodule_le

theorem LinearMap.lift_rank_le_of_surjective (f : M →ₗ[R] M') (h : Surjective f) :
    lift.{v} (Module.rank R M') ≤ lift.{v'} (Module.rank R M) := by
  rw [← rank_range_of_surjective f h]
  apply lift_rank_range_le

theorem LinearMap.rank_le_of_surjective (f : M →ₗ[R] M₁) (h : Surjective f) :
    Module.rank R M₁ ≤ Module.rank R M := by
  rw [← rank_range_of_surjective f h]
  apply rank_range_le
#align linear_map.rank_le_of_surjective LinearMap.rank_le_of_surjective

@[nontriviality, simp]
theorem rank_subsingleton [Subsingleton R] : Module.rank R M = 1 := by
  haveI := Module.subsingleton R M
  have : Nonempty { s : Set M // LinearIndependent R ((↑) : s → M) } :=
    ⟨⟨∅, linearIndependent_empty _ _⟩⟩
  rw [Module.rank_def, ciSup_eq_of_forall_le_of_forall_lt_exists_gt]
  · rintro ⟨s, hs⟩
    rw [Cardinal.mk_le_one_iff_set_subsingleton]
    apply subsingleton_of_subsingleton
  intro w hw
  refine ⟨⟨{0}, ?_⟩, ?_⟩
  · rw [linearIndependent_iff']
    intros
    exact Subsingleton.elim _ _
  · exact hw.trans_eq (Cardinal.mk_singleton _).symm
#align rank_subsingleton rank_subsingleton

end
