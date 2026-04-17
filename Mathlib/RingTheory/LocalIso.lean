/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.OpenImmersion
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Local isomorphisms

A ring homomorphism is a local isomorphism if source locally (in the geometric sense)
it is a standard open immersion.
-/

universe w v u

public section

open TensorProduct

instance isScalarTower_localizationAlgebra {R : Type*} [CommSemiring R] (M : Submonoid R)
    (S : Type*)
    [CommSemiring S] [Algebra R S] {Rₘ : Type*} {Sₘ : Type*} [CommSemiring Rₘ] [CommSemiring Sₘ]
    [Algebra R Rₘ] [IsLocalization M Rₘ] [Algebra S Sₘ]
    [i : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] :
    letI : Algebra Rₘ Sₘ := localizationAlgebra M S
    IsScalarTower R Rₘ Sₘ :=
  letI : Algebra Rₘ Sₘ := localizationAlgebra M S
  .of_algebraMap_eq' <| by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq R S Sₘ]

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
noncomputable
def IsLocalization.tensorProductEquivOfMapIncludeRight
    {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {T : Type*} [CommSemiring T] [Algebra R T] (M : Submonoid S)
    (Sₘ : Type*) [CommSemiring Sₘ] [Algebra R Sₘ] [Algebra S Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization M Sₘ]
    (A : Type*) [CommSemiring A] [Algebra T A]
    [Algebra (T ⊗[R] S) A] [IsScalarTower T (T ⊗[R] S) A]
    [IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := T))) A] :
    T ⊗[R] Sₘ ≃ₐ[T] A :=
  letI M' : Submonoid (T ⊗[R] S) := Algebra.algebraMapSubmonoid (T ⊗[R] S) M
  letI : Algebra (T ⊗[R] S) (T ⊗[R] Sₘ) :=
    (Algebra.TensorProduct.map (AlgHom.id R T) (IsScalarTower.toAlgHom R _ _)).toAlgebra
  haveI : IsScalarTower T (T ⊗[R] S) (T ⊗[R] Sₘ) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI : IsLocalization M' (T ⊗[R] Sₘ) := by
    let : Algebra S (T ⊗[R] Sₘ) := .compHom _ (algebraMap S Sₘ)
    have : IsScalarTower S (T ⊗[R] S) (T ⊗[R] Sₘ) := .of_algebraMap_eq' rfl
    have : IsScalarTower S Sₘ (T ⊗[R] Sₘ) := .of_algebraMap_eq' rfl
    rw [Algebra.isLocalization_iff_isPushout _ Sₘ, Algebra.IsPushout.comm,
      ← Algebra.IsPushout.comp_iff R _ T]
    infer_instance
  haveI : IsLocalization M' A :=
    inferInstanceAs <|
      IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := T))) _
  (IsLocalization.algEquiv M' _ _).restrictScalars T

noncomputable
def IsLocalization.Away.tensorProductEquiv
    {T R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T]
    (g : S) (Sₘ : Type*) [CommSemiring Sₘ] [Algebra R Sₘ] [Algebra S Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization.Away g Sₘ] :
    T ⊗[R] Sₘ ≃ₐ[T] Localization.Away ((1 : T) ⊗ₜ[R] g) :=
  haveI : IsLocalization
      ((Submonoid.powers g).map (Algebra.TensorProduct.includeRight (R := R) (A := T)))
      (Localization.Away ((1 : T) ⊗ₜ[R] g)) := by
    simp only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply]
    infer_instance
  IsLocalization.tensorProductEquivOfMapIncludeRight (.powers g) _ _

/-- An `R`-algebra `S` is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
class Algebra.IsLocalIso (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] : Prop where
  exists_notMem_isStandardOpenImmersion (q : Ideal S) [q.IsPrime] :
    ∃ g ∉ q, IsStandardOpenImmersion R (Localization.Away g)

namespace Algebra.IsLocalIso

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

lemma span_isStandardOpenImmersion_eq_top [Algebra.IsLocalIso R S] :
    Ideal.span {g : S | Algebra.IsStandardOpenImmersion R (Localization.Away g)} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hms⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨g, hgm, hstd⟩ :=
    Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := R) m
  exact hgm (hms (Ideal.subset_span hstd))

lemma iff_span_isStandardOpenImmersion_eq_top :
    IsLocalIso R S ↔
      Ideal.span {g : S | IsStandardOpenImmersion R (Localization.Away g)} = ⊤ := by
  refine ⟨fun _ ↦ span_isStandardOpenImmersion_eq_top R S, fun h ↦ ⟨fun q hq ↦ ?_⟩⟩
  by_contra!
  apply hq.ne_top
  rw [_root_.eq_top_iff, ← h, Ideal.span_le]
  grind [SetLike.mem_coe]

end Algebra.IsLocalIso

/-- A ring homomorphism is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
@[stacks 096E "(1)", algebraize]
def RingHom.IsLocalIso {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IsLocalIso R S

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Algebra.IsLocalIso

instance (priority := 100) [IsStandardOpenImmersion R S] : IsLocalIso R S where
  exists_notMem_isStandardOpenImmersion q hq := by
    use 1, hq.one_notMem
    exact IsStandardOpenImmersion.trans _ S _

lemma of_span_range_eq_top {ι : Type*} (f : ι → S) (h : Ideal.span (Set.range f) = ⊤)
    (T : ι → Type*) [∀ i, CommSemiring (T i)] [∀ i, Algebra R (T i)] [∀ i, Algebra S (T i)]
    [∀ i, IsScalarTower R S (T i)] [∀ i, IsLocalization.Away (f i) (T i)]
    [∀ i, IsLocalIso R (T i)] : IsLocalIso R S := by
  refine ⟨fun q hq ↦ ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, f i ∉ q := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff] at h
    have : ⟨q, hq⟩ ∈ ⨆ i, PrimeSpectrum.basicOpen (f i) := by simp [h]
    simpa using this
  have : ⟨q, hq⟩ ∈ PrimeSpectrum.basicOpen (f i) := hi
  rw [← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range (T i)] at this
  obtain ⟨q', hq'⟩ := this
  obtain ⟨g', hg', h⟩ := exists_notMem_isStandardOpenImmersion (R := R) q'.1
  obtain ⟨n, g, hg⟩ := IsLocalization.Away.surj (f i) g'
  refine ⟨g * (f i), ?_, ?_⟩
  · refine Ideal.IsPrime.mul_notMem hq ?_ hi
    simp only [PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal] at hq'
    rwa [← hq', Ideal.mem_comap, ← hg, Ideal.mul_unit_mem_iff_mem]
    exact (IsLocalization.Away.algebraMap_isUnit (f i)).pow n
  · have : IsLocalization.Away g' (Localization.Away (algebraMap S (T i) g)) := by
      rw [← hg]
      exact .of_associated
        (associated_mul_unit_right _ _ ((IsLocalization.Away.algebraMap_isUnit (f i)).pow n)).symm
    let e₁ : Localization.Away (algebraMap S (T i) g) ≃ₐ[S] Localization.Away (g * f i) :=
      IsLocalization.algEquiv (.powers (g * f i)) _ _
    let e₂ : Localization.Away g' ≃ₐ[R] Localization.Away (g * f i) :=
      ((IsLocalization.algEquiv (.powers g') _ _).restrictScalars R).trans (e₁.restrictScalars R)
    exact .of_algEquiv e₂

lemma of_span_eq_top {s : Set S} (h : Ideal.span s = ⊤)
    (h : ∀ x ∈ s, IsLocalIso R (Localization.Away x)) : IsLocalIso R S := by
  have heq : Ideal.span (Set.range fun i : s ↦ i.1) = ⊤ := by simpa
  have (i : s) : IsLocalIso R (Localization.Away i.1) := h _ i.property
  exact .of_span_range_eq_top _ heq fun i ↦ Localization.Away i.1

lemma pi_of_finite {ι : Type*} (R : Type*) (S : ι → Type*) [CommSemiring R]
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] [Finite ι] [∀ i, IsLocalIso R (S i)] :
    IsLocalIso R (∀ i, S i)  := by
  classical
  let (i : ι) : Algebra (∀ i, S i) (S i) := (Pi.evalAlgHom R S i).toAlgebra
  have (i : ι) : IsLocalization.Away ((fun i ↦ Pi.single i (1 : S i)) i) ((fun i ↦ S i) i) := by
    apply IsLocalization.away_of_isIdempotentElem
    · simp [IsIdempotentElem, ← Pi.single_mul_left]
    · apply RingHom.ker_evalRingHom
    · apply (Pi.evalRingHom S i).surjective
  apply of_span_range_eq_top (fun i ↦ Pi.single i (1 : S i)) _ fun i ↦ S i
  exact Ideal.span_single_eq_top _

instance refl : IsLocalIso R R := inferInstance

variable (R S) in
/-- Local isomorphisms are stable under composition. -/
lemma trans (T : Type*) [CommSemiring T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalIso R S] [IsLocalIso S T] : IsLocalIso R T := by
  -- The proof is purely formal given that open immersions are stable under composition.
  let s : Set S := {g : S | IsStandardOpenImmersion R (Localization.Away g)}
  let T' (g : S) := Localization.Away (algebraMap S T g)
  let (g : S) : Algebra (Localization.Away g) (T' g) := localizationAlgebra (.powers g) T
  let T'' (g : S) (x : T) := Localization.Away (algebraMap _ (T' g) x)
  let t (g : S) : Set T := {x : T | IsStandardOpenImmersion (Localization.Away g) (T'' g x)}
  let ι : Type _ := Σ i : s, t i.1
  have (i : ι) : IsStandardOpenImmersion (Localization.Away i.1.1) (T'' i.1 i.2) := i.2.2
  suffices h : Ideal.span (Set.range fun i : ι ↦ algebraMap S T i.1 * i.2) = ⊤ by
    have (i : ι) : IsStandardOpenImmersion R (T'' i.1 i.2) :=
      have : IsScalarTower R (Localization.Away i.1.1) (T' i.1.1) :=
        IsScalarTower.to₁₃₄ _ S _ _
      have : IsStandardOpenImmersion (Localization.Away i.1.1) (T'' i.1.1 i.2.1) := i.2.2
      have : IsStandardOpenImmersion R (Localization.Away i.1.1) := i.1.2
      .trans _ (Localization.Away i.1.1) _
    exact .of_span_range_eq_top _ h fun i : ι ↦ T'' i.1 i.2
  have h1 := congr(Ideal.map (algebraMap S T) $(span_isStandardOpenImmersion_eq_top R S))
  rw [Ideal.map_top, Ideal.map_span] at h1
  nth_rw 1 [_root_.eq_top_iff, ← Ideal.top_mul ⊤, ← h1, ← span_isStandardOpenImmersion_eq_top S T,
    Ideal.span_mul_span, Ideal.span_le, Set.mul_subset_iff]
  simp only [Set.mem_image, Set.mem_setOf_eq, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro g hg x hx
  refine Ideal.subset_span ⟨⟨⟨g, hg⟩, ⟨x, ?_⟩⟩, rfl⟩
  simp only [Set.mem_setOf_eq, t]
  let : Algebra (Localization.Away x) (T'' g x) :=
    localizationAlgebra (.powers x) (T' g)
  have : IsScalarTower S (Localization.Away x) (T'' g x) :=
    IsScalarTower.to₁₃₄ _ T _ _
  have : IsLocalization (algebraMapSubmonoid (Localization.Away x) (.powers g)) (T'' g x) := by
    have : algebraMapSubmonoid (Localization.Away x) (.powers g) =
      algebraMapSubmonoid (Localization.Away x) (.powers (algebraMap S T g)) := by
        simp [IsScalarTower.algebraMap_apply S T (Localization.Away x)]
    rw [this]
    exact .commutes _ (T' g) _ (.powers x) (.powers (algebraMap S T g))
  have : IsPushout S (Localization.Away x) (Localization.Away g) (T'' g x) :=
    Algebra.isPushout_of_isLocalization (.powers g) _ _ _
  exact .of_isPushout S (Localization.Away x) _ _

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
set_option backward.isDefEq.respectTransparency false in
instance (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalIso R S] :
    IsLocalIso T (T ⊗[R] S) := by
  rw [iff_span_isStandardOpenImmersion_eq_top, _root_.eq_top_iff,
    ← Ideal.map_top TensorProduct.includeRight, ← span_isStandardOpenImmersion_eq_top R S,
    Ideal.map_le_iff_le_comap, Ideal.span_le]
  intro g hg
  apply Ideal.subset_span
  simp only [Set.mem_setOf_eq] at hg ⊢
  exact .of_algEquiv (IsLocalization.Away.tensorProductEquiv _ (Localization.Away g))

end Algebra.IsLocalIso

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}

lemma RingHom.isLocalIso_algebraMap [Algebra R S] :
    (algebraMap R S).IsLocalIso ↔ Algebra.IsLocalIso R S := by
  rw [RingHom.IsLocalIso, toAlgebra_algebraMap]

set_option backward.isDefEq.respectTransparency false in
lemma RingHom.isLocalIso_iff_locally_isStandardOpenImmersion {R S : Type u} [CommRing R]
    [CommRing S] (f : R →+* S) :
    f.IsLocalIso ↔ f.Locally RingHom.IsStandardOpenImmersion := by
  algebraize [f]
  rw [RingHom.IsLocalIso, Algebra.IsLocalIso.iff_span_isStandardOpenImmersion_eq_top,
    RingHom.locally_iff_span_eq_top, ← RingHom.algebraMap_toAlgebra f]
  simp_rw [← IsScalarTower.algebraMap_eq R S, RingHom.isStandardOpenImmersion_algebraMap]

namespace RingHom.IsLocalIso

/-- A bijective ring homomorphism is a local isomorphism. -/
lemma of_bijective (hf : Function.Bijective f) : f.IsLocalIso := by
  algebraize [f]
  haveI := Algebra.IsStandardOpenImmersion.of_bijective hf
  change Algebra.IsLocalIso R S
  infer_instance

/-- The composition of local isomorphisms is a local isomorphism. -/
lemma comp {T : Type*} [CommSemiring T] {g : S →+* T} (hg : g.IsLocalIso) (hf : f.IsLocalIso) :
    (g.comp f).IsLocalIso := by
  algebraize [f, g, g.comp f]
  exact Algebra.IsLocalIso.trans R S T

lemma stableUnderComposition : StableUnderComposition IsLocalIso :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma respectsIso : RespectsIso IsLocalIso :=
  stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

end RingHom.IsLocalIso
