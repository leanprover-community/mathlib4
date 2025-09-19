/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Set.Card

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
The supremum may not be attained, see https://mathoverflow.net/a/263053.

For a free module over any ring satisfying the strong rank condition
(e.g. left-Noetherian rings, commutative rings, and in particular division rings and fields),
this is the same as the dimension of the space (i.e. the cardinality of any basis).

In particular this agrees with the usual notion of the dimension of a vector space.

See also `Module.finrank` for a `ℕ`-valued function which returns the correct value
for a finite-dimensional vector space (but 0 for an infinite-dimensional vector space).
-/
@[stacks 09G3 "first part"]
protected irreducible_def Module.rank : Cardinal :=
  ⨆ ι : { s : Set M // LinearIndepOn R id s }, (#ι.1)

theorem rank_le_card : Module.rank R M ≤ #M :=
  (Module.rank_def _ _).trans_le (ciSup_le' fun _ ↦ mk_set_le _)

instance nonempty_linearIndependent_set : Nonempty {s : Set M // LinearIndepOn R id s} :=
  ⟨⟨∅, linearIndepOn_empty _ _⟩⟩

end

namespace LinearIndependent
variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Nontrivial R]

theorem cardinal_lift_le_rank {ι : Type w} {v : ι → M}
    (hv : LinearIndependent R v) :
    Cardinal.lift.{v} #ι ≤ Cardinal.lift.{w} (Module.rank R M) := by
  rw [Module.rank]
  refine le_trans ?_ (lift_le.mpr <| le_ciSup (bddAbove_range _) ⟨_, hv.linearIndepOn_id⟩)
  exact lift_mk_le'.mpr ⟨(Equiv.ofInjective _ hv.injective).toEmbedding⟩

lemma aleph0_le_rank {ι : Type w} [Infinite ι] {v : ι → M}
    (hv : LinearIndependent R v) : ℵ₀ ≤ Module.rank R M :=
  aleph0_le_lift.mp <| (aleph0_le_lift.mpr <| aleph0_le_mk ι).trans hv.cardinal_lift_le_rank

theorem cardinal_le_rank {ι : Type v} {v : ι → M}
    (hv : LinearIndependent R v) : #ι ≤ Module.rank R M := by
  simpa using hv.cardinal_lift_le_rank

theorem cardinal_le_rank' {s : Set M}
    (hs : LinearIndependent R (fun x => x : s → M)) : #s ≤ Module.rank R M :=
  hs.cardinal_le_rank

theorem _root_.LinearIndepOn.encard_le_toENat_rank {ι : Type*} {v : ι → M} {s : Set ι}
    (hs : LinearIndepOn R v s) : s.encard ≤ (Module.rank R M).toENat := by
  simpa using OrderHom.mono (β := ℕ∞) Cardinal.toENat hs.linearIndependent.cardinal_lift_le_rank

end LinearIndependent

section SurjectiveInjective

section Semiring
variable [Semiring R] [AddCommMonoid M] [Module R M] [Semiring R']

section
variable [AddCommMonoid M'] [Module R' M']

/-- If `M / R` and `M' / R'` are modules, `i : R' → R` is an injective map
non-zero elements, `j : M →+ M'` is an injective monoid homomorphism, such that the scalar
multiplications on `M` and `M'` are compatible, then the rank of `M / R` is smaller than or equal to
the rank of `M' / R'`. As a special case, taking `R = R'` it is
`LinearMap.lift_rank_le_of_injective`. -/
theorem lift_rank_le_of_injective_injectiveₛ (i : R' → R) (j : M →+ M')
    (hi : Injective i) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    lift.{v'} (Module.rank R M) ≤ lift.{v} (Module.rank R' M') := by
  simp_rw [Module.rank, lift_iSup (bddAbove_range _)]
  exact ciSup_mono' (bddAbove_range _) fun ⟨s, h⟩ ↦ ⟨⟨j '' s,
    LinearIndepOn.id_image (h.linearIndependent.map_of_injective_injectiveₛ i j hi hj hc)⟩,
    lift_mk_le'.mpr ⟨(Equiv.Set.image j s hj).toEmbedding⟩⟩

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map, and
`j : M →+ M'` is an injective monoid homomorphism, such that the scalar multiplications on `M` and
`M'` are compatible, then the rank of `M / R` is smaller than or equal to the rank of `M' / R'`.
As a special case, taking `R = R'` it is `LinearMap.lift_rank_le_of_injective`. -/
theorem lift_rank_le_of_surjective_injective (i : R → R') (j : M →+ M')
    (hi : Surjective i) (hj : Injective j) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    lift.{v'} (Module.rank R M) ≤ lift.{v} (Module.rank R' M') := by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine lift_rank_le_of_injective_injectiveₛ i' j (fun _ _ h ↦ ?_) hj fun r m ↦ ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m, hi']

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a bijective map which maps zero to zero,
`j : M ≃+ M'` is a group isomorphism, such that the scalar multiplications on `M` and `M'` are
compatible, then the rank of `M / R` is equal to the rank of `M' / R'`.
As a special case, taking `R = R'` it is `LinearEquiv.lift_rank_eq`. -/
theorem lift_rank_eq_of_equiv_equiv (i : R → R') (j : M ≃+ M')
    (hi : Bijective i) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    lift.{v'} (Module.rank R M) = lift.{v} (Module.rank R' M') :=
  (lift_rank_le_of_surjective_injective i j hi.2 j.injective hc).antisymm <|
    lift_rank_le_of_injective_injectiveₛ i j.symm hi.1
      j.symm.injective fun _ _ ↦ j.symm_apply_eq.2 <| by simp_all
end

section
variable [AddCommMonoid M₁] [Module R' M₁]

/-- The same-universe version of `lift_rank_le_of_injective_injective`. -/
theorem rank_le_of_injective_injectiveₛ (i : R' → R) (j : M →+ M₁)
    (hi : Injective i) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    Module.rank R M ≤ Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_injective_injectiveₛ i j hi hj hc

/-- The same-universe version of `lift_rank_le_of_surjective_injective`. -/
theorem rank_le_of_surjective_injective (i : R → R') (j : M →+ M₁)
    (hi : Surjective i) (hj : Injective j)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.rank R M ≤ Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc

/-- The same-universe version of `lift_rank_eq_of_equiv_equiv`. -/
theorem rank_eq_of_equiv_equiv (i : R → R') (j : M ≃+ M₁)
    (hi : Bijective i) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.rank R M = Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hi hc

end
end Semiring

section Ring
variable [Ring R] [AddCommGroup M] [Module R M] [Ring R']

/-- If `M / R` and `M' / R'` are modules, `i : R' → R` is a map which sends non-zero elements to
non-zero elements, `j : M →+ M'` is an injective group homomorphism, such that the scalar
multiplications on `M` and `M'` are compatible, then the rank of `M / R` is smaller than or equal to
the rank of `M' / R'`. As a special case, taking `R = R'` it is
`LinearMap.lift_rank_le_of_injective`. -/
theorem lift_rank_le_of_injective_injective [AddCommGroup M'] [Module R' M']
    (i : R' → R) (j : M →+ M') (hi : ∀ r, i r = 0 → r = 0) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    lift.{v'} (Module.rank R M) ≤ lift.{v} (Module.rank R' M') := by
  simp_rw [Module.rank, lift_iSup (bddAbove_range _)]
  exact ciSup_mono' (bddAbove_range _) fun ⟨s, h⟩ ↦
    ⟨⟨j '' s, LinearIndepOn.id_image <| h.linearIndependent.map_of_injective_injective i j hi
      (fun _ _ ↦ hj <| by rwa [j.map_zero]) hc⟩,
    lift_mk_le'.mpr ⟨(Equiv.Set.image j s hj).toEmbedding⟩⟩

/-- The same-universe version of `lift_rank_le_of_injective_injective`. -/
theorem rank_le_of_injective_injective [AddCommGroup M₁] [Module R' M₁]
    (i : R' → R) (j : M →+ M₁) (hi : ∀ r, i r = 0 → r = 0) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    Module.rank R M ≤ Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc

end Ring

namespace Algebra

variable {R : Type w} {S : Type v} [CommSemiring R] [Semiring S] [Algebra R S]
  {R' : Type w'} {S' : Type v'} [CommSemiring R'] [Semiring S'] [Algebra R' S']

/-- If `S / R` and `S' / R'` are algebras, `i : R' →+* R` and `j : S →+* S'` are injective ring
homomorphisms, such that `R' → R → S → S'` and `R' → S'` commute, then the rank of `S / R` is
smaller than or equal to the rank of `S' / R'`. -/
theorem lift_rank_le_of_injective_injective
    (i : R' →+* R) (j : S →+* S') (hi : Injective i) (hj : Injective j)
    (hc : (j.comp (algebraMap R S)).comp i = algebraMap R' S') :
    lift.{v'} (Module.rank R S) ≤ lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_le_of_injective_injectiveₛ i j hi hj fun r _ ↦ ?_
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
  simp only [smul_def, AddMonoidHom.coe_coe, map_mul, this]

/-- If `S / R` and `S' / R'` are algebras, `i : R ≃+* R'` and `j : S ≃+* S'` are
ring isomorphisms, such that `R → R' → S'` and `R → S → S'` commute,
then the rank of `S / R` is equal to the rank of `S' / R'`. -/
theorem lift_rank_eq_of_equiv_equiv (i : R ≃+* R') (j : S ≃+* S')
    (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) :
    lift.{v'} (Module.rank R S) = lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_eq_of_equiv_equiv i j i.bijective fun r _ ↦ ?_
  have := congr($hc r)
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, comp_apply] at this
  simp only [smul_def, RingEquiv.coe_toAddEquiv, map_mul, this]

variable {S' : Type v} [Semiring S'] [Algebra R' S']

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

variable [Semiring R] [AddCommMonoid M] [Module R M]
  [Semiring R'] [AddCommMonoid M'] [AddCommMonoid M₁]
  [Module R M'] [Module R M₁] [Module R' M'] [Module R' M₁]

section

theorem LinearMap.lift_rank_le_of_injective (f : M →ₗ[R] M') (i : Injective f) :
    Cardinal.lift.{v'} (Module.rank R M) ≤ Cardinal.lift.{v} (Module.rank R M') :=
  lift_rank_le_of_injective_injectiveₛ (RingHom.id R) f (fun _ _ h ↦ h) i f.map_smul

theorem LinearMap.rank_le_of_injective (f : M →ₗ[R] M₁) (i : Injective f) :
    Module.rank R M ≤ Module.rank R M₁ :=
  Cardinal.lift_le.1 (f.lift_rank_le_of_injective i)

/-- The rank of the range of a linear map is at most the rank of the source. -/
-- The proof is: a free submodule of the range lifts to a free submodule of the
-- source, by arbitrarily lifting a basis.
theorem lift_rank_range_le (f : M →ₗ[R] M') : Cardinal.lift.{v}
    (Module.rank R (LinearMap.range f)) ≤ Cardinal.lift.{v'} (Module.rank R M) := by
  simp only [Module.rank_def]
  rw [Cardinal.lift_iSup (Cardinal.bddAbove_range _)]
  apply ciSup_le'
  rintro ⟨s, li⟩
  apply le_trans
  swap
  · apply Cardinal.lift_le.mpr
    refine le_ciSup (Cardinal.bddAbove_range _) ⟨rangeSplitting f '' s, ?_⟩
    apply LinearIndependent.of_comp f.rangeRestrict
    convert li.comp (Equiv.Set.rangeSplittingImageEquiv f s) (Equiv.injective _) using 1
  · exact (Cardinal.lift_mk_eq'.mpr ⟨Equiv.Set.rangeSplittingImageEquiv f s⟩).ge

theorem rank_range_le (f : M →ₗ[R] M₁) : Module.rank R (LinearMap.range f) ≤ Module.rank R M := by
  simpa using lift_rank_range_le f

theorem lift_rank_map_le (f : M →ₗ[R] M') (p : Submodule R M) :
    Cardinal.lift.{v} (Module.rank R (p.map f)) ≤ Cardinal.lift.{v'} (Module.rank R p) := by
  have h := lift_rank_range_le (f.comp (Submodule.subtype p))
  rwa [LinearMap.range_comp, range_subtype] at h

theorem rank_map_le (f : M →ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map f) ≤ Module.rank R p := by simpa using lift_rank_map_le f p

lemma Submodule.rank_mono {s t : Submodule R M} (h : s ≤ t) : Module.rank R s ≤ Module.rank R t :=
  (Submodule.inclusion h).rank_le_of_injective fun ⟨x, _⟩ ⟨y, _⟩ eq =>
    Subtype.eq <| show x = y from Subtype.ext_iff.1 eq

/-- Two linearly equivalent vector spaces have the same dimension, a version with different
universes. -/
theorem LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') :
    Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') := by
  apply le_antisymm
  · exact f.toLinearMap.lift_rank_le_of_injective f.injective
  · exact f.symm.toLinearMap.lift_rank_le_of_injective f.symm.injective

/-- Two linearly equivalent vector spaces have the same dimension. -/
theorem LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank R M = Module.rank R M₁ :=
  Cardinal.lift_inj.1 f.lift_rank_eq

theorem lift_rank_range_of_injective (f : M →ₗ[R] M') (h : Injective f) :
    lift.{v} (Module.rank R (LinearMap.range f)) = lift.{v'} (Module.rank R M) :=
  (LinearEquiv.ofInjective f h).lift_rank_eq.symm

theorem rank_range_of_injective (f : M →ₗ[R] M₁) (h : Injective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M :=
  (LinearEquiv.ofInjective f h).rank_eq.symm

theorem LinearEquiv.lift_rank_map_eq (f : M ≃ₗ[R] M') (p : Submodule R M) :
    lift.{v} (Module.rank R (p.map (f : M →ₗ[R] M'))) = lift.{v'} (Module.rank R p) :=
  (f.submoduleMap p).lift_rank_eq.symm

/-- Pushforwards of submodules along a `LinearEquiv` have the same dimension. -/
theorem LinearEquiv.rank_map_eq (f : M ≃ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map (f : M →ₗ[R] M₁)) = Module.rank R p :=
  (f.submoduleMap p).rank_eq.symm

variable (R M)

@[simp]
theorem rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M :=
  (LinearEquiv.ofTop ⊤ rfl).rank_eq

variable {R M}

theorem rank_range_of_surjective (f : M →ₗ[R] M') (h : Surjective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M' := by
  rw [LinearMap.range_eq_top.2 h, rank_top]

theorem Submodule.rank_le (s : Submodule R M) : Module.rank R s ≤ Module.rank R M := by
  rw [← rank_top R M]
  exact rank_mono le_top

theorem LinearMap.lift_rank_le_of_surjective (f : M →ₗ[R] M') (h : Surjective f) :
    lift.{v} (Module.rank R M') ≤ lift.{v'} (Module.rank R M) := by
  rw [← rank_range_of_surjective f h]
  apply lift_rank_range_le

theorem LinearMap.rank_le_of_surjective (f : M →ₗ[R] M₁) (h : Surjective f) :
    Module.rank R M₁ ≤ Module.rank R M := by
  rw [← rank_range_of_surjective f h]
  apply rank_range_le

lemma rank_le_of_isSMulRegular {S : Type*} [CommSemiring S] [Algebra S R] [Module S M]
    [IsScalarTower S R M] (L L' : Submodule R M) {s : S} (hr : IsSMulRegular M s)
    (h : ∀ x ∈ L, s • x ∈ L') :
    Module.rank R L ≤ Module.rank R L' :=
  ((Algebra.lsmul S R M s).restrict h).rank_le_of_injective <|
    fun _ _ h ↦ by simpa using hr (Subtype.ext_iff.mp h)

variable (R R' M) in
lemma Module.rank_top_le_rank_of_isScalarTower [Module R' M]
    [SMulWithZero R R'] [IsScalarTower R R' M] [FaithfulSMul R R'] [IsScalarTower R R' R'] :
    Module.rank R' M ≤ Module.rank R M := by
  rw [Module.rank, Module.rank]
  exact ciSup_le' fun ⟨s, hs⟩ ↦ le_ciSup_of_le (Cardinal.bddAbove_range _)
    ⟨s, hs.restrict_scalars (by simpa [← faithfulSMul_iff_injective_smul_one])⟩ le_rfl

variable (R R') in
lemma Module.lift_rank_bot_le_lift_rank_of_isScalarTower (T : Type w) [Module R R']
    [NonAssocSemiring T] [Module R T] [Module R' T] [IsScalarTower R' T T] [FaithfulSMul R' T]
    [IsScalarTower R R' T] :
    Cardinal.lift.{w} (Module.rank R R') ≤ Cardinal.lift (Module.rank R T) :=
  LinearMap.lift_rank_le_of_injective ((LinearMap.toSpanSingleton R' T 1).restrictScalars R) <|
    (faithfulSMul_iff_injective_smul_one R' T).mp ‹_›

variable (R R') in
lemma Module.rank_bot_le_rank_of_isScalarTower (T : Type u') [Module R R'] [NonAssocSemiring T]
    [Module R T] [Module R' T] [IsScalarTower R' T T] [FaithfulSMul R' T] [IsScalarTower R R' T] :
    Module.rank R R' ≤ Module.rank R T := by
  simpa using Module.lift_rank_bot_le_lift_rank_of_isScalarTower R R' T

end

end Module
