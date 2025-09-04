/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!

# The meta properties of finitely-presented ring homomorphisms.

The main result is `RingHom.finitePresentation_isLocal`.

-/

open scoped Pointwise TensorProduct

namespace RingHom

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Being finitely-presented is preserved by localizations. -/
theorem finitePresentation_localizationPreserves : LocalizationPreserves @FinitePresentation := by
  introv R hf
  letI := f.toAlgebra
  letI := ((algebraMap S S').comp f).toAlgebra
  let f' : R' →+* S' := IsLocalization.map S' f M.le_comap_map
  letI := f'.toAlgebra
  haveI : IsScalarTower R R' S' :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp M.le_comap_map).symm
  obtain ⟨n, g, hgsurj, hgker⟩ := hf
  let MX : Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) M
  haveI : IsLocalization MX (MvPolynomial (Fin n) R') :=
    inferInstanceAs <| IsLocalization (M.map MvPolynomial.C) (MvPolynomial (Fin n) R')
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S M) S' :=
    inferInstanceAs <| IsLocalization (M.map f) S'
  let g' : MvPolynomial (Fin n) R' →ₐ[R'] S' := IsLocalization.mapₐ M R' _ S' g
  let k : RingHom.ker g →ₗ[MvPolynomial (Fin n) R] RingHom.ker g' :=
    AlgHom.toKerIsLocalization M R' _ S' g
  have : IsLocalizedModule MX k := AlgHom.toKerIsLocalization_isLocalizedModule M _ _ _ g
  have : Module.Finite (MvPolynomial (Fin n) R) (ker g) := Module.Finite.iff_fg.mpr hgker
  exact ⟨n, g', IsLocalization.mapₐ_surjective_of_surjective M R' _ S' g hgsurj,
    Module.Finite.iff_fg.mp (Module.Finite.of_isLocalizedModule MX k)⟩

/-- Being finitely-presented is stable under composition. -/
theorem finitePresentation_stableUnderComposition : StableUnderComposition @FinitePresentation := by
  introv R hf hg
  exact hg.comp hf

/-- If `R` is a ring, then `Rᵣ` is `R`-finitely-presented for any `r : R`. -/
theorem finitePresentation_holdsForLocalizationAway :
    HoldsForLocalizationAway @FinitePresentation := by
  introv R _
  suffices Algebra.FinitePresentation R S by
    rw [RingHom.FinitePresentation]
    convert this; ext
    rw [Algebra.smul_def]; rfl
  exact IsLocalization.Away.finitePresentation r

/--
If `S` is an `R`-algebra with a surjection from a finitely-presented `R`-algebra `A`, such that
localized at a spanning set `{ r }` of elements of `A`, `Sᵣ` is finitely-presented, then
`S` is finitely presented.
This is almost `finitePresentation_ofLocalizationSpanTarget`. The difference is,
that here the set `t` generates the unit ideal of `A`, while in the general version,
it only generates a quotient of `A`.
-/
lemma finitePresentation_ofLocalizationSpanTarget_aux
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    [Algebra.FinitePresentation R A] (f : A →ₐ[R] S) (hf : Function.Surjective f)
    (t : Finset A) (ht : Ideal.span (t : Set A) = ⊤)
    (H : ∀ g : t, Algebra.FinitePresentation R (Localization.Away (f g))) :
    Algebra.FinitePresentation R S := by
  apply Algebra.FinitePresentation.of_surjective hf
  apply ker_fg_of_localizationSpan t ht
  intro g
  let f' : Localization.Away g.val →ₐ[R] Localization.Away (f g) :=
    Localization.awayMapₐ f g.val
  have (g : t) : Algebra.FinitePresentation R (Localization.Away g.val) :=
    haveI : Algebra.FinitePresentation A (Localization.Away g.val) :=
      IsLocalization.Away.finitePresentation g.val
    Algebra.FinitePresentation.trans R A (Localization.Away g.val)
  apply Algebra.FinitePresentation.ker_fG_of_surjective f'
  exact IsLocalization.Away.mapₐ_surjective_of_surjective _ hf

/-- Finite-presentation can be checked on a standard covering of the target. -/
theorem finitePresentation_ofLocalizationSpanTarget :
    OfLocalizationSpanTarget @FinitePresentation := by
  rw [ofLocalizationSpanTarget_iff_finite]
  introv R hs H
  classical
  letI := f.toAlgebra
  replace H : ∀ r : s, Algebra.FinitePresentation R (Localization.Away (r : S)) := by
    intro r; simp_rw [RingHom.FinitePresentation] at H
    convert H r; ext; simp_rw [Algebra.smul_def]; rfl
  /-
  We already know that `S` is of finite type over `R`, so we have a surjection
  `MvPolynomial (Fin n) R →ₐ[R] S`. To reason about the kernel, we want to check it on the stalks
  of preimages of `s`. But the preimages do not necessarily span `MvPolynomial (Fin n) R`, so
  we quotient out by an ideal and apply `finitePresentation_ofLocalizationSpanTarget_aux`.
  -/
  have hfintype : Algebra.FiniteType R S := by
    apply finiteType_ofLocalizationSpanTarget f s hs
    intro r
    convert_to Algebra.FiniteType R (Localization.Away r.val)
    · rw [RingHom.FiniteType]
      constructor <;> intro h <;> convert h <;> ext <;> simp_rw [Algebra.smul_def] <;> rfl
    · infer_instance
  rw [RingHom.FinitePresentation]
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hfintype
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_iff_linearCombination S (s : Set S) 1).mp
      (show (1 : S) ∈ Ideal.span (s : Set S) by rw [hs]; trivial)
  choose g' hg' using (fun g : s ↦ hf g)
  choose h' hh' using (fun g : s ↦ hf (l g))
  let I : Ideal (MvPolynomial (Fin n) R) := Ideal.span { ∑ g : s, g' g * h' g - 1 }
  let A := MvPolynomial (Fin n) R ⧸ I
  have hfI : ∀ a ∈ I, f a = 0 := by
    intro p hp
    simp only [Finset.univ_eq_attach, I, Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp only [map_mul, map_sub, map_sum, map_one, hg', hh']
    rw [Finsupp.linearCombination_apply_of_mem_supported (α := (s : Set S)) S (s := s.attach)] at hl
    · rw [← hl]
      simp only [Finset.coe_sort_coe, smul_eq_mul, mul_comm, sub_self, zero_mul]
    · rintro a -
      simp
  let f' : A →ₐ[R] S := Ideal.Quotient.liftₐ I f hfI
  have hf' : Function.Surjective f' :=
    Ideal.Quotient.lift_surjective_of_surjective I hfI hf
  let t : Finset A := Finset.image (fun g ↦ g' g) Finset.univ
  have ht : Ideal.span (t : Set A) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : ∑ g : { x // x ∈ s }, g' g * h' g = (1 : A) := by
      apply eq_of_sub_eq_zero
      rw [← map_one (Ideal.Quotient.mk I), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.subset_span
      simp
    simp_rw [← this, Finset.univ_eq_attach, map_sum, map_mul]
    refine Ideal.sum_mem _ (fun g _ ↦ Ideal.mul_mem_right _ _ <| Ideal.subset_span ?_)
    simp [t]
  have : Algebra.FinitePresentation R A := by
    apply Algebra.FinitePresentation.quotient
    simp only [Finset.univ_eq_attach, I]
    exact ⟨{∑ g ∈ s.attach, g' g * h' g - 1}, by simp⟩
  have Ht (g : t) : Algebra.FinitePresentation R (Localization.Away (f' g)) := by
    have : ∃ (a : S) (hb : a ∈ s), (Ideal.Quotient.mk I) (g' ⟨a, hb⟩) = g.val := by
      obtain ⟨g, hg⟩ := g
      convert hg
      simp [A, t]
    obtain ⟨r, hr, hrr⟩ := this
    simp only [f']
    rw [← hrr, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    simp_rw [coe_coe]
    rw [hg']
    apply H
  exact finitePresentation_ofLocalizationSpanTarget_aux f' hf' t ht Ht

/-- Being finitely-presented is a local property of rings. -/
theorem finitePresentation_isLocal : PropertyIsLocal @FinitePresentation :=
  ⟨finitePresentation_localizationPreserves.away,
    finitePresentation_ofLocalizationSpanTarget,
    finitePresentation_ofLocalizationSpanTarget.ofLocalizationSpan
      (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finitePresentation_holdsForLocalizationAway).left,
    (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      finitePresentation_holdsForLocalizationAway).right⟩

/-- Being finitely-presented respects isomorphisms. -/
theorem finitePresentation_respectsIso : RingHom.RespectsIso @RingHom.FinitePresentation :=
  RingHom.finitePresentation_isLocal.respectsIso

/-- Being finitely-presented is stable under base change. -/
theorem finitePresentation_isStableUnderBaseChange :
    IsStableUnderBaseChange @FinitePresentation := by
  apply IsStableUnderBaseChange.mk
  · exact finitePresentation_respectsIso
  · introv h
    replace h : Algebra.FinitePresentation R T := by
      rw [RingHom.FinitePresentation] at h; convert h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.FinitePresentation S (S ⊗[R] T) by
      rw [RingHom.FinitePresentation]; convert this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

end RingHom
