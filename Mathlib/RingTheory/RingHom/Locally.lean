/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.BaseChange
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
- `RingHom.locally_holdsForLocalizationAway`: `Locally P` holds for localization away maps
  if `P` does.
- `RingHom.locally_isStableUnderBaseChange`: `Locally P` is stable under base change if `P` is.
- `RingHom.locally_stableUnderComposition`: `Locally P` is stable under composition
  if `P` is and `P` is preserved under localizations.
- `RingHom.locally_stableUnderCompositionWithLocalizationAway`: `Locally P` is stable under
  composition with localization away maps if `P` is.
- `RingHom.locally_localizationPreserves`: If `P` is preserved by localizations, then so is
  `Locally P`.

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

lemma locally_of_locally {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hPQ : ∀ {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}, P f → Q f)
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S} (hf : Locally P f) : Locally Q f := by
  obtain ⟨s, hsone, hs⟩ := hf
  exact ⟨s, hsone, fun t ht ↦ hPQ (hs t ht)⟩

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

section Stability

/-- If `P` respects isomorphism, so does `Locally P`. -/
lemma locally_respectsIso (hPi : RespectsIso P) : RespectsIso (Locally P) where
  left {R S T} _ _ _ f e := fun ⟨s, hsone, hs⟩ ↦ by
    refine ⟨e '' s, ?_, ?_⟩
    · rw [← Ideal.map_span, hsone, Ideal.map_top]
    · rintro - ⟨a, ha, rfl⟩
      let e' : Localization.Away a ≃+* Localization.Away (e a) :=
        IsLocalization.ringEquivOfRingEquiv _ _ e (Submonoid.map_powers e a)
      have : (algebraMap T (Localization.Away (e a))).comp e.toRingHom =
          e'.toRingHom.comp (algebraMap S (Localization.Away a)) := by
        ext x
        simp [e']
      rw [← RingHom.comp_assoc, this, RingHom.comp_assoc]
      apply hPi.left
      exact hs a ha
  right {R S T} _ _ _ f e := fun ⟨s, hsone, hs⟩ ↦
    ⟨s, hsone, fun a ha ↦ (RingHom.comp_assoc _ _ _).symm ▸ hPi.right _ _ (hs a ha)⟩

/-- If `P` holds for localization away maps, then so does `Locally P`. -/
lemma locally_holdsForLocalizationAway (hPa : HoldsForLocalizationAway P) :
    HoldsForLocalizationAway (Locally P) := by
  introv R _
  use {1}
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  let e : S ≃ₐ[R] (Localization.Away (1 : S)) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).restrictScalars R
  haveI : IsLocalization.Away r (Localization.Away (1 : S)) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) e
  rw [← IsScalarTower.algebraMap_eq]
  apply hPa _ r

/-- If `P` preserves localizations, then `Locally P` is stable under composition if `P` is. -/
lemma locally_stableUnderComposition (hPi : RespectsIso P) (hPl : LocalizationPreserves P)
    (hPc : StableUnderComposition P) :
    StableUnderComposition (Locally P) := by
  classical
  intro R S T _ _ _ f g hf hg
  rw [locally_iff_finite] at hf hg
  obtain ⟨sf, hsfone, hsf⟩ := hf
  obtain ⟨sg, hsgone, hsg⟩ := hg
  rw [locally_iff_exists hPi]
  refine ⟨sf × sg, fun (a, b) ↦ g a * b, ?_,
      fun (a, b) ↦ Localization.Away ((algebraMap T (Localization.Away b.val)) (g a.val)),
      inferInstance, inferInstance, inferInstance, ?_⟩
  · rw [eq_top_iff, ← hsgone, Ideal.span_le]
    intro t ht
    have : 1 ∈ Ideal.span (Set.range <| fun a : sf ↦ a.val) := by simp [hsfone]
    simp only [Ideal.mem_span_range_iff_exists_fun, SetLike.mem_coe] at this ⊢
    obtain ⟨cf, hcf⟩ := this
    let cg : sg → T := Pi.single ⟨t, ht⟩ 1
    use fun (a, b) ↦ g (cf a) * cg b
    simp [cg, Pi.single_apply, Fintype.sum_prod_type, ← mul_assoc, ← Finset.sum_mul, ← map_mul,
      ← map_sum, hcf] at hcf ⊢
  · intro ⟨a, b⟩
    let g' := (algebraMap T (Localization.Away b.val)).comp g
    let a' := (algebraMap T (Localization.Away b.val)) (g a.val)
    have : (algebraMap T <| Localization.Away a').comp (g.comp f) =
        (Localization.awayMap g' a.val).comp ((algebraMap S (Localization.Away a.val)).comp f) := by
      ext x
      simp only [coe_comp, Function.comp_apply, a']
      change _ = Localization.awayMap g' a.val (algebraMap S _ (f x))
      simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
    simp only [this, a']
    apply hPc _ _ (hsf a.val a.property)
    apply @hPl _ _ _ _ g' _ _ _ _ _ _ _ _ ?_ (hsg b.val b.property)
    exact IsLocalization.Away.instMapRingHomPowersOfCoe (Localization.Away (g' a.val)) a.val

/-- If `P` is stable under composition with localization away maps on the right,
then so is `Locally P`. -/
lemma locally_StableUnderCompositionWithLocalizationAwayTarget
    (hP0 : RespectsIso P)
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) :
    StableUnderCompositionWithLocalizationAwayTarget (Locally P) := by
  intro R S T _ _ _ _ t _ f hf
  simp only [locally_iff_isLocalization hP0 f] at hf
  obtain ⟨s, hsone, hs⟩ := hf
  refine ⟨algebraMap S T '' s, ?_, ?_⟩
  · rw [← Ideal.map_span, hsone, Ideal.map_top]
  · rintro - ⟨a, ha, rfl⟩
    letI : Algebra (Localization.Away a) (Localization.Away (algebraMap S T a)) :=
      (IsLocalization.Away.map _ _ (algebraMap S T) a).toAlgebra
    have : (algebraMap (Localization.Away a) (Localization.Away (algebraMap S T a))).comp
        (algebraMap S (Localization.Away a)) =
        (algebraMap T (Localization.Away (algebraMap S T a))).comp (algebraMap S T) := by
      simp [algebraMap_toAlgebra, IsLocalization.Away.map]
    rw [← comp_assoc, ← this, comp_assoc]
    haveI : IsScalarTower S (Localization.Away a) (Localization.Away ((algebraMap S T) a)) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      simp [algebraMap_toAlgebra, IsLocalization.Away.map, ← IsScalarTower.algebraMap_apply]
    haveI : IsLocalization.Away (algebraMap S (Localization.Away a) t)
        (Localization.Away (algebraMap S T a)) :=
      IsLocalization.Away.commutes _ T ((Localization.Away (algebraMap S T a))) a t
    apply hPa _ (algebraMap S (Localization.Away a) t)
    apply hs a ha

/-- If `P` is stable under composition with localization away maps on the left,
then so is `Locally P`. -/
lemma locally_StableUnderCompositionWithLocalizationAwaySource
    (hPa : StableUnderCompositionWithLocalizationAwaySource P) :
    StableUnderCompositionWithLocalizationAwaySource (Locally P) := by
  intro R S T _ _ _ _ r _ f ⟨s, hsone, hs⟩
  refine ⟨s, hsone, fun t ht ↦ ?_⟩
  rw [← comp_assoc]
  exact hPa _ r _ (hs t ht)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- If `P` is stable under base change, then so is `Locally P`. -/
lemma locally_isStableUnderBaseChange (hPi : RespectsIso P) (hPb : IsStableUnderBaseChange P) :
    IsStableUnderBaseChange (Locally P) := by
  apply IsStableUnderBaseChange.mk (locally_respectsIso hPi)
  introv hf
  obtain ⟨s, hsone, hs⟩ := hf
  rw [locally_iff_exists hPi]
  letI (a : s) : Algebra (S ⊗[R] T) (S ⊗[R] Localization.Away a.val) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R _ _)).toRingHom.toAlgebra
  letI (a : s) : Algebra T (S ⊗[R] Localization.Away a.val) :=
    ((algebraMap _ (S ⊗[R] Localization.Away a.val)).comp (algebraMap T (S ⊗[R] T))).toAlgebra
  haveI (a : s) : IsScalarTower T (S ⊗[R] T) (S ⊗[R] Localization.Away a.val) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI (a : s) : IsScalarTower T (Localization.Away a.val) (S ⊗[R] Localization.Away a.val) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI (a : s) : IsScalarTower S (S ⊗[R] T) (S ⊗[R] Localization.Away a.val) :=
      IsScalarTower.of_algebraMap_eq <| by
    intro x
    simp [RingHom.algebraMap_toAlgebra]
  haveI (a : s) : Algebra.IsPushout T (Localization.Away a.val) (S ⊗[R] T)
      (S ⊗[R] Localization.Away a.val) := by
    rw [← Algebra.IsPushout.comp_iff R _ S]
    infer_instance
  refine ⟨s, fun a ↦ Algebra.TensorProduct.includeRight a.val, ?_,
      fun a ↦ (S ⊗[R] Localization.Away a.val), inferInstance, inferInstance, ?_, ?_⟩
  · rw [← Set.image_eq_range, ← Ideal.map_span, hsone, Ideal.map_top]
  · intro a
    convert_to IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[R] T) (Submonoid.powers a.val))
        (S ⊗[R] Localization.Away a.val)
    · simp only [Algebra.TensorProduct.includeRight_apply, Algebra.algebraMapSubmonoid,
        Submonoid.map_powers]
      rfl
    · rw [← isLocalizedModule_iff_isLocalization, isLocalizedModule_iff_isBaseChange
        (S := Submonoid.powers a.val) (A := Localization.Away a.val)]
      exact Algebra.IsPushout.out
  · intro a
    have : (algebraMap (S ⊗[R] T) (S ⊗[R] Localization.Away a.val)).comp
        Algebra.TensorProduct.includeLeftRingHom =
        Algebra.TensorProduct.includeLeftRingHom := by
      ext x
      simp [RingHom.algebraMap_toAlgebra]
    rw [this]
    apply hPb R (Localization.Away a.val)
    rw [IsScalarTower.algebraMap_eq R T (Localization.Away a.val)]
    apply hs a a.property

/-- If `P` is preserved by localization away, then so is `Locally P`. -/
lemma locally_localizationAwayPreserves (hPl : LocalizationAwayPreserves P) :
    LocalizationAwayPreserves (Locally P) := by
  introv R hf
  obtain ⟨s, hsone, hs⟩ := hf
  rw [locally_iff_exists hPl.respectsIso]
  let rₐ (a : s) : Localization.Away a.val := algebraMap _ _ (f r)
  let Sₐ (a : s) := Localization.Away (rₐ a)
  haveI (a : s) :
      IsLocalization.Away (((algebraMap S (Localization.Away a.val)).comp f) r) (Sₐ a) :=
    inferInstanceAs (IsLocalization.Away (rₐ a) (Sₐ a))
  haveI (a : s) : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away a.val)
    (Submonoid.map f (Submonoid.powers r))) (Sₐ a) := by
    convert inferInstanceAs (IsLocalization.Away (rₐ a) (Sₐ a))
    simp [rₐ, Sₐ, Algebra.algebraMapSubmonoid]
  have H (a : s) : Submonoid.powers (f r) ≤
      (Submonoid.powers (rₐ a)).comap (algebraMap S (Localization.Away a.val)) := by
    simp [rₐ, Sₐ, Submonoid.powers_le]
  letI (a : s) : Algebra S' (Sₐ a) :=
    (IsLocalization.map (Sₐ a) (algebraMap S (Localization.Away a.val)) (H a)).toAlgebra
  haveI (a : s) : IsScalarTower S S' (Sₐ a) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp (H a)).symm
  refine ⟨s, fun a ↦ algebraMap S S' a.val, ?_, Sₐ,
      inferInstance, inferInstance, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [← Set.image_eq_range, ← Ideal.map_span, hsone, Ideal.map_top]
  · convert IsLocalization.commutes (T := Sₐ a) (M₁ := (Submonoid.powers r).map f) (S₁ := S')
      (S₂ := Localization.Away a.val) (M₂ := Submonoid.powers a.val)
    simp [Algebra.algebraMapSubmonoid]
  · rw [algebraMap_toAlgebra, IsLocalization.Away.map, IsLocalization.map_comp_map]
    exact hPl ((algebraMap _ (Localization.Away a.val)).comp f) r R' (Sₐ a) (hs _ a.2)

/-- If `P` is preserved by localizations, then so is `Locally P`. -/
lemma locally_localizationPreserves (hPl : LocalizationPreserves P) :
    LocalizationPreserves (Locally P) := by
  introv R hf
  obtain ⟨s, hsone, hs⟩ := hf
  rw [locally_iff_exists hPl.away.respectsIso]
  let Mₐ (a : s) : Submonoid (Localization.Away a.val) :=
    (M.map f).map (algebraMap S (Localization.Away a.val))
  let Sₐ (a : s) := Localization (Mₐ a)
  have hM (a : s) : M.map ((algebraMap S (Localization.Away a.val)).comp f) = Mₐ a :=
    (M.map_map _ _).symm
  haveI (a : s) :
      IsLocalization (M.map ((algebraMap S (Localization.Away a.val)).comp f)) (Sₐ a) := by
    rw [hM]
    infer_instance
  haveI (a : s) :
      IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away a.val) (M.map f)) (Sₐ a) :=
    inferInstanceAs <| IsLocalization (Mₐ a) (Sₐ a)
  letI (a : s) : Algebra S' (Sₐ a) :=
    (IsLocalization.map (Sₐ a) (algebraMap S (Localization.Away a.val))
      (M.map f).le_comap_map).toAlgebra
  haveI (a : s) : IsScalarTower S S' (Sₐ a) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp (M.map f).le_comap_map).symm
  refine ⟨s, fun a ↦ algebraMap S S' a.val, ?_, Sₐ,
      inferInstance, inferInstance, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [← Set.image_eq_range, ← Ideal.map_span, hsone, Ideal.map_top]
  · convert IsLocalization.commutes (T := Sₐ a) (M₁ := M.map f) (S₁ := S')
      (S₂ := Localization.Away a.val) (M₂ := Submonoid.powers a.val)
    simp [Algebra.algebraMapSubmonoid]
  · rw [algebraMap_toAlgebra, IsLocalization.map_comp_map]
    apply hPl
    exact hs a.val a.property

/-- If `P` is preserved by localizations and stable under composition with localization
away maps, then `Locally P` is a local property of ring homomorphisms. -/
lemma locally_propertyIsLocal (hPl : LocalizationAwayPreserves P)
    (hPa : StableUnderCompositionWithLocalizationAway P) : PropertyIsLocal (Locally P) where
  localizationAwayPreserves := locally_localizationAwayPreserves hPl
  StableUnderCompositionWithLocalizationAwayTarget :=
    locally_StableUnderCompositionWithLocalizationAwayTarget hPl.respectsIso hPa.right
  ofLocalizationSpan := (locally_ofLocalizationSpanTarget hPl.respectsIso).ofLocalizationSpan
    (locally_StableUnderCompositionWithLocalizationAwaySource hPa.left)
  ofLocalizationSpanTarget := locally_ofLocalizationSpanTarget hPl.respectsIso

end Stability

end RingHom
