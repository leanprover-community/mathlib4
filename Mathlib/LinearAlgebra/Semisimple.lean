/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
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
 * `Module.End.IsSemisimple.minpoly_squarefree`: the minimal polynomial of a semisimple
   endomorphism is squarefree.
 * `IsSemisimple.of_mem_adjoin_pair`: every endomorphism in the subalgebra generated by two
   commuting semisimple endomorphisms is semisimple, if the base field is perfect.
## TODO

In finite dimensions over a field:
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

@[simp]
lemma isSemisimple_sub_algebraMap_iff {μ : R} :
    (f - algebraMap R (End R M) μ).IsSemisimple ↔ f.IsSemisimple := by
  suffices ∀ p : Submodule R M, p ≤ p.comap (f - algebraMap R (Module.End R M) μ) ↔ p ≤ p.comap f by
    simp [isSemisimple_iff, this]
  refine fun p ↦ ⟨fun h x hx ↦ ?_, fun h x hx ↦ p.sub_mem (h hx) (p.smul_mem μ hx)⟩
  simpa using p.add_mem (h hx) (p.smul_mem μ hx)

lemma IsSemisimple.restrict {p : Submodule R M} {hp : MapsTo f p p} (hf : f.IsSemisimple) :
    IsSemisimple (f.restrict hp) := by
  simp only [isSemisimple_iff] at hf ⊢
  intro q hq
  replace hq : MapsTo f (q.map p.subtype) (q.map p.subtype) := by
    rintro - ⟨⟨x, hx⟩, hx', rfl⟩; exact ⟨⟨f x, hp hx⟩, by simpa using hq hx', rfl⟩
  obtain ⟨r, hr₁, hr₂⟩ := hf _ hq
  refine ⟨r.comap p.subtype, fun x hx ↦ hr₁ hx, ?_⟩
  rw [← q.comap_map_eq_of_injective p.injective_subtype]
  exact p.isCompl_comap_subtype_of_isCompl_of_le hr₂ <| p.map_subtype_le q

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

theorem isSemisimple_of_squarefree_aeval_eq_zero {p : K[X]}
    (hp : Squarefree p) (hpf : aeval f p = 0) : f.IsSemisimple := by
  rw [← RingHom.mem_ker, ← AEval.annihilator_eq_ker_aeval (M := M), mem_annihilator,
      ← IsTorsionBy, ← isTorsionBySet_singleton_iff, isTorsionBySet_iff_is_torsion_by_span] at hpf
  let R := K[X] ⧸ Ideal.span {p}
  have : IsReduced R :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_iff_span_singleton.mp hp.isRadical)
  have : FiniteDimensional K R := (AdjoinRoot.powerBasis hp.ne_zero).finite
  have : IsArtinianRing R := .of_finite K R
  have : IsSemisimpleRing R := IsArtinianRing.isSemisimpleRing_of_isReduced R
  letI : Module R (AEval' f) := Module.IsTorsionBySet.module hpf
  let e : AEval' f →ₛₗ[Ideal.Quotient.mk (Ideal.span {p})] AEval' f :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ ↦ rfl }
  exact (e.isSemisimpleModule_iff_of_bijective bijective_id).mpr inferInstance

variable [FiniteDimensional K M]

section

variable (hf : f.IsSemisimple)
include hf

/-- The minimal polynomial of a semisimple endomorphism is square free -/
theorem IsSemisimple.minpoly_squarefree : Squarefree (minpoly K f) :=
  IsRadical.squarefree (minpoly.ne_zero <| Algebra.IsIntegral.isIntegral _) <| by
    rw [isRadical_iff_span_singleton, span_minpoly_eq_annihilator]; exact hf.annihilator_isRadical

protected theorem IsSemisimple.aeval (p : K[X]) : (aeval f p).IsSemisimple :=
  let R := K[X] ⧸ Ideal.span {minpoly K f}
  have : Finite K R :=
    (AdjoinRoot.powerBasis' <| minpoly.monic <| Algebra.IsIntegral.isIntegral f).finite
  have : IsReduced R := (Ideal.isRadical_iff_quotient_reduced _).mp <|
    span_minpoly_eq_annihilator K f ▸ hf.annihilator_isRadical
  isSemisimple_of_squarefree_aeval_eq_zero ((minpoly.isRadical K _).squarefree <|
    minpoly.ne_zero <| .of_finite K <| Ideal.Quotient.mkₐ K (.span {minpoly K f}) p) <| by
      rw [← Ideal.Quotient.liftₐ_comp (.span {minpoly K f}) (aeval f)
        fun a h ↦ by rwa [Ideal.span, ← minpoly.ker_aeval_eq_span_minpoly] at h, aeval_algHom,
        AlgHom.comp_apply, AlgHom.comp_apply, ← aeval_algHom_apply, minpoly.aeval, map_zero]

theorem IsSemisimple.of_mem_adjoin_singleton {a : End K M}
    (ha : a ∈ Algebra.adjoin K {f}) : a.IsSemisimple := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha; obtain ⟨p, rfl⟩ := ha; exact .aeval hf _

protected theorem IsSemisimple.pow (n : ℕ) : (f ^ n).IsSemisimple :=
  .of_mem_adjoin_singleton hf (pow_mem (Algebra.self_mem_adjoin_singleton _ _) _)

end

section PerfectField

variable [PerfectField K] (comm : Commute f g) (hf : f.IsSemisimple) (hg : g.IsSemisimple)
include comm hf hg

attribute [local simp] Submodule.Quotient.quot_mk_eq_mk in
theorem IsSemisimple.of_mem_adjoin_pair {a : End K M} (ha : a ∈ Algebra.adjoin K {f, g}) :
    a.IsSemisimple := by
  let R := K[X] ⧸ Ideal.span {minpoly K f}
  let S := AdjoinRoot ((minpoly K g).map <| algebraMap K R)
  have : Finite K R :=
    (AdjoinRoot.powerBasis' <| minpoly.monic <| Algebra.IsIntegral.isIntegral f).finite
  have : Finite R S :=
    (AdjoinRoot.powerBasis' <| (minpoly.monic <| Algebra.IsIntegral.isIntegral g).map _).finite
  #adaptation_note
  /--
  After https://github.com/leanprover/lean4/pull/4119 we either need
  to specify the `(S := R)` argument, or use `set_option maxSynthPendingDepth 2 in`.

  In either case this step is too slow!
  -/
  set_option maxSynthPendingDepth 2 in
  have : IsScalarTower K R S := .of_algebraMap_eq fun _ ↦ rfl
  have : Finite K S := .trans R S
  have : IsArtinianRing R := .of_finite K R
  have : IsReduced R := (Ideal.isRadical_iff_quotient_reduced _).mp <|
    span_minpoly_eq_annihilator K f ▸ hf.annihilator_isRadical
  have : IsReduced S := by
    simp_rw [S, AdjoinRoot, ← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
    exact (PerfectField.separable_iff_squarefree.mpr hg.minpoly_squarefree).map.squarefree.isRadical
  let φ : S →ₐ[K] End K M := Ideal.Quotient.liftₐ _ (eval₂AlgHom' (Ideal.Quotient.liftₐ _ (aeval f)
    fun a ↦ ?_) g ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_ : _ ≤ RingHom.ker _)
  rotate_left 1
  · rw [Ideal.span, ← minpoly.ker_aeval_eq_span_minpoly]; exact id
  · rintro ⟨p⟩; exact p.induction_on (fun k ↦ by simp [R, Algebra.commute_algebraMap_left])
      (fun p q hp hq ↦ by simpa using hp.add_left hq)
      fun n k ↦ by simpa [R, pow_succ, ← mul_assoc _ _ X] using (·.mul_left comm)
  · simpa only [RingHom.mem_ker, eval₂AlgHom'_apply, eval₂_map, AlgHom.comp_algebraMap_of_tower]
      using minpoly.aeval K g
  have : Algebra.adjoin K {f, g} ≤ φ.range := Algebra.adjoin_le fun x ↦ by
    rintro (hx | hx) <;> rw [hx]
    · exact ⟨AdjoinRoot.of _ (AdjoinRoot.root _), (eval₂_C _ _).trans (aeval_X f)⟩
    · exact ⟨AdjoinRoot.root _, eval₂_X _ _⟩
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp (this ha)
  refine isSemisimple_of_squarefree_aeval_eq_zero
    ((minpoly.isRadical K p).squarefree <| minpoly.ne_zero <| .of_finite K p) ?_
  rw [aeval_algHom, φ.comp_apply, minpoly.aeval, map_zero]

theorem IsSemisimple.add_of_commute : (f + g).IsSemisimple := .of_mem_adjoin_pair
  comm hf hg <| add_mem (Algebra.subset_adjoin <| .inl rfl) (Algebra.subset_adjoin <| .inr rfl)

theorem IsSemisimple.sub_of_commute : (f - g).IsSemisimple := .of_mem_adjoin_pair
  comm hf hg <| sub_mem (Algebra.subset_adjoin <| .inl rfl) (Algebra.subset_adjoin <| .inr rfl)

theorem IsSemisimple.mul_of_commute : (f * g).IsSemisimple := .of_mem_adjoin_pair
  comm hf hg <| mul_mem (Algebra.subset_adjoin <| .inl rfl) (Algebra.subset_adjoin <| .inr rfl)

end PerfectField

end field

end Module.End
