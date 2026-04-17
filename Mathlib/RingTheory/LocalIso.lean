/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.OpenImmersion
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Local isomorphisms

A ring homomorphism is a local isomorphism if source locally (in the geometric sense)
it is a standard open immersion.

## Main declarations

- `Algebra.IsLocalIso`: The class of algebras that are locally standard open immersions.

We show that local isomorphisms are local, stable under composition and base change.

## Implementation note

Most results in this file follow purely formally from the corresponding property of
standard open immersion. We could use the `RingHom.Locally` API to obtain them, but
it would yield results with less universe generality and we would have to replace
`CommSemiring` by `CommRing`. In the future, we may consider refactoring the API
for `RingHom` properties to allow for also treating properties of `CommSemiring`s
and then simplify the proofs in this file.
-/

universe w v u

public section

open TensorProduct

/-- An `R`-algebra `S` is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
@[stacks 096E "(1) in the algebra formulation"]
class Algebra.IsLocalIso (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] : Prop where
  exists_notMem_isStandardOpenImmersion (q : Ideal S) [q.IsPrime] :
    ∃ g ∉ q, IsStandardOpenImmersion R (Localization.Away g)

namespace Algebra.IsLocalIso

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (R S) in
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

variable (T : Type*) [CommSemiring T]

variable (R S) in
/-- Local isomorphisms are stable under composition. -/
lemma trans [Algebra S T] [Algebra R T] [IsScalarTower R S T]
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

variable {T} in
lemma of_algEquiv [Algebra R T] (e : S ≃ₐ[R] T) [IsLocalIso R S] : IsLocalIso R T := by
  algebraize [e.toAlgHom.toRingHom]
  have : IsStandardOpenImmersion S T := .of_bijective e.bijective
  exact .trans _ S _

variable {T} in
lemma iff_of_algEquiv [Algebra R T] (e : S ≃ₐ[R] T) : IsLocalIso R S ↔ IsLocalIso R T :=
  ⟨fun _ ↦ .of_algEquiv e, fun _ ↦ .of_algEquiv e.symm⟩

instance [Algebra R T] [IsLocalIso R S] : IsLocalIso T (T ⊗[R] S) := by
  rw [iff_span_isStandardOpenImmersion_eq_top, _root_.eq_top_iff,
    ← Ideal.map_top Algebra.TensorProduct.includeRight, ← span_isStandardOpenImmersion_eq_top R S,
    Ideal.map_le_iff_le_comap, Ideal.span_le]
  intro g hg
  apply Ideal.subset_span
  simp only [Set.mem_setOf_eq] at hg ⊢
  exact .of_algEquiv <| IsLocalization.Away.tensorProductEquivTMulRight R T g (Localization.Away g)

end Algebra.IsLocalIso
