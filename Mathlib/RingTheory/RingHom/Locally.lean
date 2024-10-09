/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.Away.Lemmas

/-!
# Target local closure of ring homomorphism properties

If `P` is a property of ring homomorphisms, we call `Locally P` the closure of `P` with
respect to standard open coverings on the (algebraic) target (i.e. geometric source). Hence
for `f : R →+* S`, the property `Locally P` holds if it holds locally on `S`, i.e. if there exists
a subset `{ t }` of `S` generating the unit ideal, such that `P` holds for all compositions
`R →+* Sₜ`.

Assuming without further mention that `P` is stable under composition with isomorphisms,
`Locally P` is local on the target by construction, i.e. it satisfies
`OfLocalizationSpanTarget`. If `P` itself is local on the target, `Locally P` coincides with `P`.

The `Locally` construction preserves various properties of `P`, e.g. if `P` is stable under
composition, base change, etc., so is `Locally P`.

## Main results

- `RingHom.locally_ofLocalizationSpanTarget`: `Locally P` is local on the target.

-/

universe u v

open TensorProduct

namespace RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop)

/--
For a property of ring homomorphisms `P`, `Locally P` holds for `f : R →+* S` if
it holds locally on `S`, i.e. if there exists a subset `{ t }` of `S` generating
the unit ideal, such that `P` holds for all compositions `R →+* Sₜ`.

We may require `s` to be finite here, for the equivalence, see `locally_iff_finite`.
-/
def Locally {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∃ (s : Set S) (_ : Ideal.span s = ⊤),
    ∀ t ∈ s, P ((algebraMap S (Localization.Away t)).comp f)

variable {R S : Type u} [CommRing R] [CommRing S]

lemma locally_iff_finite (f : R →+* S) :
    Locally P f ↔ ∃ (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤),
      ∀ t ∈ s, P ((algebraMap S (Localization.Away t)).comp f) := by
  constructor
  · intro ⟨s, hsone, hs⟩
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hsone
    exact ⟨s', h₂, fun t ht ↦ hs t (h₁ ht)⟩
  · intro ⟨s, hsone, hs⟩
    use s, hsone, hs

variable {P}

/-- If `P` respects isomorphisms, to check `P` holds locally for `f : R →+* S`, it suffices
to check `P` holds on a standard open cover. -/
lemma locally_of_exists (hP : RespectsIso P) (f : R →+* S) {ι : Type*} (s : ι → S)
    (hsone : Ideal.span (Set.range s) = ⊤)
    (Sₜ : ι → Type u) [∀ i, CommRing (Sₜ i)] [∀ i, Algebra S (Sₜ i)]
    [∀ i, IsLocalization.Away (s i) (Sₜ i)] (hf : ∀ i, P ((algebraMap S (Sₜ i)).comp f)) :
    Locally P f := by
  use Set.range s, hsone
  rintro - ⟨i, rfl⟩
  let e : Localization.Away (s i) ≃+* Sₜ i :=
    (IsLocalization.algEquiv (Submonoid.powers (s i)) _ _).toRingEquiv
  have : algebraMap S (Localization.Away (s i)) = e.symm.toRingHom.comp (algebraMap S (Sₜ i)) :=
    RingHom.ext (fun x ↦ (AlgEquiv.commutes (IsLocalization.algEquiv _ _ _).symm _).symm)
  rw [this, RingHom.comp_assoc]
  exact hP.left _ _ (hf i)

/-- Equivalence variant of `locally_of_exists`. This is sometimes easier to use, if the
`IsLocalization.Away` instance can't be automatically inferred. -/
lemma locally_iff_exists (hP : RespectsIso P) (f : R →+* S) :
    Locally P f ↔ ∃ (ι : Type u) (s : ι → S) (_ : Ideal.span (Set.range s) = ⊤) (Sₜ : ι → Type u)
      (_ : (i : ι) → CommRing (Sₜ i)) (_ : (i : ι) → Algebra S (Sₜ i))
      (_ : (i : ι) → IsLocalization.Away (s i : S) (Sₜ i)),
      ∀ i, P ((algebraMap S (Sₜ i)).comp f) :=
  ⟨fun ⟨s, hsone, hs⟩ ↦ ⟨s, fun t : s ↦ (t : S), by simpa, fun t ↦ Localization.Away (t : S),
      inferInstance, inferInstance, inferInstance, fun t ↦ hs t.val t.property⟩,
    fun ⟨ι, s, hsone, Sₜ, _, _, hislocal, hs⟩ ↦ locally_of_exists hP f s hsone Sₜ hs⟩

/-- In the definition of `Locally` we may replace `Localization.Away` with an arbitrary
algebra satisfying `IsLocalization.Away`. -/
lemma locally_iff_isLocalization (hP : RespectsIso P) (f : R →+* S) :
    Locally P f ↔ ∃ (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤),
      ∀ t ∈ s, ∀ (Sₜ : Type u) [CommRing Sₜ] [Algebra S Sₜ] [IsLocalization.Away t Sₜ],
      P ((algebraMap S Sₜ).comp f) := by
  rw [locally_iff_finite P f]
  refine ⟨fun ⟨s, hsone, hs⟩ ↦ ⟨s, hsone, fun t ht Sₜ _ _ _ ↦ ?_⟩, fun ⟨s, hsone, hs⟩ ↦ ?_⟩
  · let e : Localization.Away t ≃+* Sₜ :=
      (IsLocalization.algEquiv (Submonoid.powers t) _ _).toRingEquiv
    have : algebraMap S Sₜ = e.toRingHom.comp (algebraMap S (Localization.Away t)) :=
      RingHom.ext (fun x ↦ (AlgEquiv.commutes (IsLocalization.algEquiv _ _ _) _).symm)
    rw [this, RingHom.comp_assoc]
    exact hP.left _ _ (hs t ht)
  · exact ⟨s, hsone, fun t ht ↦ hs t ht _⟩

/-- If `f` satisfies `P`, then in particular it satisfies `Locally P`. -/
lemma locally_of (hP : RespectsIso P) (f : R →+* S) (hf : P f) : Locally P f := by
  use {1}
  let e : S ≃+* Localization.Away (1 : S) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).toRingEquiv
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  exact hP.left f e hf

/-- If `P` is local on the target, then `Locally P` coincides with `P`. -/
lemma locally_iff_of_localizationSpanTarget (hPi : RespectsIso P)
    (hPs : OfLocalizationSpanTarget P) {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Locally P f ↔ P f :=
  ⟨fun ⟨s, hsone, hs⟩ ↦ hPs f s hsone (fun a ↦ hs a.val a.property), locally_of hPi f⟩

section OfLocalizationSpanTarget

/-- `Locally P` is local on the target. -/
lemma locally_ofLocalizationSpanTarget (hP : RespectsIso P) :
    OfLocalizationSpanTarget (Locally P) := by
  intro R S _ _ f s hsone hs
  choose t htone ht using hs
  rw [locally_iff_exists hP]
  refine ⟨(a : s) × t a, IsLocalization.Away.mulNumerator s t,
      IsLocalization.Away.span_range_mulNumerator_eq_top hsone htone,
      fun ⟨a, b⟩ ↦ Localization.Away b.val, inferInstance, inferInstance, fun ⟨a, b⟩ ↦ ?_, ?_⟩
  · haveI : IsLocalization.Away ((algebraMap S (Localization.Away a.val))
        (IsLocalization.Away.sec a.val b.val).1) (Localization.Away b.val) := by
      apply IsLocalization.Away.of_associated (r := b.val)
      rw [← IsLocalization.Away.sec_spec]
      apply associated_mul_unit_right
      rw [map_pow _ _]
      exact IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit _)
    apply IsLocalization.Away.mul' (Localization.Away a.val) (Localization.Away b.val)
  · intro ⟨a, b⟩
    rw [IsScalarTower.algebraMap_eq S (Localization.Away a.val) (Localization.Away b.val)]
    apply ht _ _ b.property

end OfLocalizationSpanTarget

end RingHom
