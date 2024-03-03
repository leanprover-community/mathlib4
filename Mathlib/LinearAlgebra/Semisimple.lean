/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.AnnihilatingPolynomial
import Mathlib.Order.CompleteSublattice
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.QuotientNilpotent
import Mathlib.RingTheory.SimpleModule

/-!
# Semisimple linear endomorphisms

Given an `R`-module `M` together with an `R`-linear endomorphism `f : M → M`, the following two
conditions are equivalent:
 1. Every `f`-invariant submodule of `M` has an `f`-invariant complement.
 2. `M` is a semisimple `R[X]`-module, where the action of the polynomial ring is induced by `f`.

A linear endomorphism `f` satisfying these equivalent conditions is known as a *semisimple*
endomorphism. We provide basic definitions and results about such endomorphisms in this file.

## Main definitions / results:
 * `Module.End.IsSemisimple`: the definition that a linear endomorphism is semisimple
 * `Module.End.isSemisimple_iff`: the characterisation of semisimplicity in terms of invariant
   submodules.
 * `Module.End.eq_zero_of_isNilpotent_isSemisimple`: the zero endomorphism is the only endomorphism
   that is both nilpotent and semisimple.
 * `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`: an endomorphism that is a root of a
   square-free polynomial is semisimple (in finite dimensions over a field).

## TODO

In finite dimensions over a field:
 * Sum / difference / product of commuting semisimple endomorphisms is semisimple
 * If semisimple then generalized eigenspace is eigenspace
 * Converse of `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`
 * Restriction of semisimple endomorphism is semisimple
 * Triangularizable iff diagonalisable for semisimple endomorphisms

-/

open Set Function Polynomial

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module.End

section CommRing

variable (f g : End R M)

/-- A linear endomorphism of an `R`-module `M` is called *semisimple* if the induced `R[X]`-module
structure on `M` is semisimple. This is equivalent to saying that every `f`-invariant `R`-submodule
of `M` has an `f`-invariant complement: see `Module.End.isSemisimple_iff`. -/
abbrev IsSemisimple := IsSemisimpleModule R[X] (AEval' f)

variable {f g}

lemma isSemisimple_iff :
    f.IsSemisimple ↔ ∀ p : Submodule R M, p ≤ p.comap f → ∃ q, q ≤ q.comap f ∧ IsCompl p q := by
  set s := (AEval.comapSubmodule R M f).range
  have h : s = {p : Submodule R M | p ≤ p.comap f} := AEval.range_comapSubmodule R M f
  let e := CompleteLatticeHom.toOrderIsoRangeOfInjective _ (AEval.injective_comapSubmodule R M f)
  simp_rw [Module.End.IsSemisimple, IsSemisimpleModule, e.complementedLattice_iff,
    s.isComplemented_iff, ← SetLike.mem_coe, h, mem_setOf_eq]

@[simp]
lemma isSemisimple_zero [IsSemisimpleModule R M] : IsSemisimple (0 : Module.End R M) := by
  simpa [isSemisimple_iff] using exists_isCompl

@[simp]
lemma isSemisimple_id [IsSemisimpleModule R M] : IsSemisimple (LinearMap.id : Module.End R M) := by
  simpa [isSemisimple_iff] using exists_isCompl

@[simp] lemma isSemisimple_neg : (-f).IsSemisimple ↔ f.IsSemisimple := by simp [isSemisimple_iff]

lemma eq_zero_of_isNilpotent_isSemisimple (hn : IsNilpotent f) (hs : f.IsSemisimple) : f = 0 := by
  have ⟨n, h0⟩ := hn
  rw [← aeval_X (R := R) f]; rw [← aeval_X_pow (R := R) f] at h0
  rw [← RingHom.mem_ker, ← AEval.annihilator_eq_ker_aeval (M := M)] at h0 ⊢
  exact hs.annihilator_isRadical ⟨n, h0⟩

end CommRing

section field

variable {K : Type*} [Field K] [Module K M] {f g : End K M}

lemma IsSemisimple_smul_iff {t : K} (ht : t ≠ 0) :
    (t • f).IsSemisimple ↔ f.IsSemisimple := by
  simp [isSemisimple_iff, Submodule.comap_smul f (h := ht)]

lemma IsSemisimple_smul (t : K) (h : f.IsSemisimple) :
    (t • f).IsSemisimple := by
  wlog ht : t ≠ 0; · simp [not_not.mp ht]
  rwa [IsSemisimple_smul_iff ht]

theorem isSemisimple_of_squarefree_aeval_eq_zero [FiniteDimensional K M]
    {p : K[X]} (hp : Squarefree p) (hpf : aeval f p = 0) : f.IsSemisimple := by
  rw [← RingHom.mem_ker, ← AEval.annihilator_eq_ker_aeval (M := M), mem_annihilator,
      ← IsTorsionBy, ← isTorsionBySet_singleton_iff, isTorsionBySet_iff_is_torsion_by_span] at hpf
  let R := K[X] ⧸ Ideal.span {p}
  have : IsReduced R :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_iff_span_singleton.mp hp.isRadical)
  have : FiniteDimensional K R := (AdjoinRoot.powerBasis hp.ne_zero).finite
  haveI : IsArtinianRing R := .of_finite K R
  letI : Module R (AEval' f) := Module.IsTorsionBySet.module hpf
  let e : AEval' f →ₛₗ[Ideal.Quotient.mk (Ideal.span {p})] AEval' f :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ ↦ rfl }
  exact (e.isSemisimpleModule_iff_of_bijective bijective_id).mpr inferInstance

variable [FiniteDimensional K M]

/-- The minimal polynomial of a semisimple endomorphism is square free -/
theorem IsSemisimple.minpoly_squarefree (hf : f.IsSemisimple) : Squarefree (minpoly K f) :=
  IsRadical.squarefree (minpoly.ne_zero <| isIntegral _) <| by
    rw [isRadical_iff_span_singleton, span_minpoly_eq_annihilator]; exact hf.annihilator_isRadical

section PerfectField

variable [PerfectField K] (comm : Commute f g) (hf : f.IsSemisimple) (hg : g.IsSemisimple)

theorem isSemisimple_of_mem_adjoin {a : End K M} (ha : a ∈ Algebra.adjoin K {f, g}) :
    a.IsSemisimple := by
  let R := K[X] ⧸ Ideal.span {minpoly K f}
  let S := AdjoinRoot ((minpoly K g).map <| algebraMap K R)
  have : Finite K R := (AdjoinRoot.powerBasis' <| minpoly.monic <| isIntegral f).finite
  have : Finite R S := (AdjoinRoot.powerBasis' <| (minpoly.monic <| isIntegral g).map _).finite
  have : IsScalarTower K R S := .of_algebraMap_eq fun _ ↦ rfl
  have : Finite K S := .trans R S
  have : IsArtinianRing R := .of_finite K R
  have : IsArtinianRing S := .of_finite R S
  have : IsReduced R := (Ideal.isRadical_iff_quotient_reduced _).mp <|
    span_minpoly_eq_annihilator K f ▸ hf.annihilator_isRadical
  have : IsReduced S := by
    simp_rw [AdjoinRoot, ← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
    exact (PerfectField.separable_iff_squarefree.mpr hg.minpoly_squarefree).map.squarefree.isRadical
  let φ : S →ₐ[K] End K M := Ideal.Quotient.liftₐ _ (eval₂AlgHom' (Ideal.Quotient.liftₐ _ (aeval f)
    fun a ↦ ?_) g ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_ : _ ≤ RingHom.ker _)
  rotate_left 1
  · rw [Ideal.span, ← minpoly.ker_aeval_eq_span_minpoly]; exact id
  · rintro ⟨p⟩; exact p.induction_on (fun k ↦ by simp [Algebra.commute_algebraMap_left])
      (fun p q hp hq ↦ by simpa using hp.add_left hq)
      fun n k ↦ by simpa [pow_succ', ← mul_assoc _ _ X] using (·.mul_left comm)
  · simpa only [RingHom.mem_ker, eval₂AlgHom'_apply, eval₂_map, AlgHom.comp_algebraMap_of_tower]
      using minpoly.aeval K g
  have : Algebra.adjoin K {f, g} ≤ φ.range := Algebra.adjoin_le fun x ↦ by
    rintro (hx | hx) <;> rw [hx]
    · exact ⟨AdjoinRoot.of _ (AdjoinRoot.root _), (eval₂_C _ _).trans (aeval_X f)⟩
    · exact ⟨AdjoinRoot.root _, eval₂_X _ _⟩
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp (this ha)
  refine isSemisimple_of_squarefree_aeval_eq_zero
    ((minpoly.isRadical K p).squarefree <| minpoly.ne_zero <| .of_finite K p) ?_
  rw [aeval_algHom, φ.comp_apply, minpoly.aeval, φ.map_zero]

theorem isSemisimple_add_of_commute : (f + g).IsSemisimple := isSemisimple_of_mem_adjoin comm
  hf hg <| add_mem (Algebra.subset_adjoin <| .inl rfl) (Algebra.subset_adjoin <| .inr rfl)

theorem isSemisimple_mul_of_commute : (f * g).IsSemisimple := isSemisimple_of_mem_adjoin comm
  hf hg <| mul_mem (Algebra.subset_adjoin <| .inl rfl) (Algebra.subset_adjoin <| .inr rfl)

end PerfectField

end field

end Module.End
