/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Order.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Grothendieck abelian categories have enough injectives

TODO

-/

universe w v u

lemma Cardinal.zero_lt_ord_iff (κ : Cardinal.{w}) : 0 < κ.ord ↔ κ ≠ 0 := by
  constructor
  · intro h h'
    simp only [h', ord_zero, lt_self_iff_false] at h
  · intro h
    by_contra!
    exact h (ord_eq_zero.1 (le_antisymm this (Ordinal.zero_le _)))

namespace CategoryTheory

open Category Opposite Limits

noncomputable instance (o : Ordinal.{w}) : SuccOrder o.toType :=
  SuccOrder.ofLinearWellFoundedLT o.toType

variable {C : Type u} [Category.{v} C]

namespace Subobject

lemma mk_lt_mk_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
    (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) (hf : ¬ IsIso f) :
    Subobject.mk i₁ < Subobject.mk i₂ := by
  obtain _ | h := (mk_le_mk_of_comm _ fac).lt_or_eq
  · assumption
  · exfalso
    refine hf ⟨ofMkLEMk i₂ i₁ (by rw [h]), ?_, ?_⟩
    · simp only [← cancel_mono i₁, assoc, ofMkLEMk_comp, fac, id_comp]
    · simp only [← cancel_mono i₂, assoc, ofMkLEMk_comp, fac, id_comp]

lemma mk_lt_mk_iff_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
    (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) :
    Subobject.mk i₁ < Subobject.mk i₂ ↔ ¬ IsIso f :=
  ⟨fun h hf ↦ by simp only [mk_eq_mk_of_comm i₁ i₂ (asIso f) fac, lt_self_iff_false] at h,
    mk_lt_mk_of_comm f fac⟩

end Subobject

section Preadditive

variable [Preadditive C]

variable {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {j : X ⟶ Y} {g : B ⟶ Y}
  [HasBinaryBiproduct B X]

namespace CommSq

variable (h : CommSq f i j g)

@[simps]
noncomputable def shortComplex : ShortComplex C where
  f := biprod.lift i (-f)
  g := biprod.desc g j
  zero := by simp [h.w]

end CommSq

namespace IsPushout

variable (h : IsPushout f i j g)

noncomputable def isColimitCokernelCoforkShortComplex :
    IsColimit (CokernelCofork.ofπ _ h.shortComplex.zero) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun b hb ↦ h.desc (biprod.inr ≫ b) (biprod.inl ≫ b) (by
      dsimp at hb
      simp only [biprod.lift_eq, Preadditive.neg_comp,
        Preadditive.sub_comp, assoc, ← sub_eq_add_neg, sub_eq_zero] at hb
      exact hb.symm)) (by aesop_cat) (fun _ _ _ hm ↦ by
        refine h.hom_ext (by simpa using biprod.inr ≫= hm)
          (by simpa using biprod.inl ≫= hm))

lemma epi_shortComplex_g : Epi h.shortComplex.g := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro _ b hb
  exact Cofork.IsColimit.hom_ext h.isColimitCokernelCoforkShortComplex
    (by simpa using hb)

end IsPushout

end Preadditive

section Abelian

namespace IsPushout

variable [Abelian C] {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {j : X ⟶ Y} {g : B ⟶ Y}

lemma shortComplex_exact (h : IsPushout f i j g) : h.shortComplex.Exact :=
  h.shortComplex.exact_of_g_is_cokernel
    h.isColimitCokernelCoforkShortComplex

lemma hom_eq_add_up_to_refinements (h : IsPushout f i j g) {T : C} (y : T ⟶ Y) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (b : T' ⟶ B) (x : T' ⟶ X),
      π ≫ y = b ≫ g + x ≫ j := by
  have := h.epi_shortComplex_g
  obtain ⟨T', π, _, z, hz⟩ := surjective_up_to_refinements_of_epi h.shortComplex.g y
  refine ⟨T', π, inferInstance, z ≫ biprod.fst, z ≫ biprod.snd, ?_⟩
  simp only [hz, assoc, ← Preadditive.comp_add]
  congr
  aesop_cat

lemma mono_of_isPushout_of_isPullback_of_mono {A B X Y : C}
    {f : A ⟶ X} {i : A ⟶ B} {j : X ⟶ Y} {g : B ⟶ Y}
    (h₁ : IsPushout f i j g) {Z : C} {j' : X ⟶ Z} {g' : B ⟶ Z}
    (h₂ : IsPullback f i j' g') (k : Y ⟶ Z)
    (fac₁ : j ≫ k = j') (fac₂ : g ≫ k = g') [Mono i] [Mono j'] : Mono k :=
  Preadditive.mono_of_cancel_zero _ (fun {T₀} y hy ↦ by
    obtain ⟨T₁, π, _, b, x, eq⟩ := hom_eq_add_up_to_refinements h₁ y
    have fac₃ : x ≫ j' = (-b) ≫ g' := by
      rw [Preadditive.neg_comp, ← add_eq_zero_iff_eq_neg, ← fac₂, ← fac₁,
        ← assoc, ← assoc, ← Preadditive.add_comp,
        add_comm, ← eq, assoc, hy, comp_zero]
    have fac₃ : (-x) ≫ j' = b ≫ g' := by
      rw [Preadditive.neg_comp, neg_eq_iff_add_eq_zero, add_comm, ← fac₂, ← fac₁,
        ← assoc, ← assoc, ← Preadditive.add_comp, ← eq, assoc, hy, comp_zero]
    obtain ⟨x', hx'⟩ : ∃ x', π ≫ y = x' ≫ j := by
      refine ⟨x + h₂.lift (-x) b fac₃ ≫ f, ?_⟩
      rw [eq, Preadditive.add_comp, assoc, h₁.w, IsPullback.lift_snd_assoc, add_comm]
    rw [← cancel_epi π, comp_zero, reassoc_of% hx', fac₁] at hy
    obtain rfl := zero_of_comp_mono _ hy
    rw [zero_comp] at hx'
    rw [← cancel_epi π, hx', comp_zero])

end IsPushout

end Abelian

namespace Abelian

variable [Abelian C]


end Abelian

namespace IsDetecting

lemma isIso_iff_of_mono {S : Set C} (hS : IsDetecting S)
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    IsIso f ↔ ∀ (s : S), Function.Surjective ((coyoneda.obj (op s.1)).map f) := by
  constructor
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    rintro ⟨A, _⟩
    exact (h A).2
  · intro hf
    apply hS
    rintro A hA g
    apply existsUnique_of_exists_of_unique
    · exact hf ⟨A, hA⟩ g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_mono f, h₁, h₂]

end IsDetecting

namespace Abelian

namespace IsGrothendieckAbelian

variable [Abelian C]

inductive generatingMonomorphisms (G : C) : MorphismProperty C
  | mono (X : Subobject G) : generatingMonomorphisms G X.arrow

variable (G : C)

abbrev generatingMonomorphismsPushouts := (generatingMonomorphisms G).pushouts

lemma isomorphisms_le_generatingMonomorphismsPushouts :
    MorphismProperty.isomorphisms C ≤ generatingMonomorphismsPushouts G :=
  MorphismProperty.isomorphisms_le_pushouts _ (fun _ ↦ ⟨_, _, _, ⟨⊤⟩, 0, inferInstance⟩)

variable {G} (hG : IsSeparator G)

namespace TransfiniteCompositionMonoPushouts

include hG

lemma exists_generatingMonomorphismsPushouts {X Y : C} (p : X ⟶ Y) [Mono p]
    (hp : ¬ IsIso p) :
    ∃ (X' : C) (i : X ⟶ X') (p' : X' ⟶ Y) (_ : generatingMonomorphismsPushouts G i)
      (_ : ¬ IsIso i) (_ : Mono p'), i ≫ p' = p := by
  rw [hG.isDetector.isIso_iff_of_mono] at hp
  simp only [coyoneda_obj_obj, Subtype.forall, Set.mem_singleton_iff, forall_eq,
    Function.Surjective, not_forall, not_exists] at hp
  obtain ⟨f, hf⟩ := hp
  let φ : pushout (pullback.fst p f) (pullback.snd p f) ⟶ Y :=
    pushout.desc p f pullback.condition
  refine ⟨pushout (pullback.fst p f) (pullback.snd p f), pushout.inl _ _, φ,
    ⟨_, _, _, (Subobject.underlyingIso _).hom ≫ pullback.fst _ _,
    pushout.inr _ _, ⟨Subobject.mk (pullback.snd p f)⟩,
    (IsPushout.of_hasPushout (pullback.fst p f) (pullback.snd p f)).of_iso
      ((Subobject.underlyingIso _).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩, ?_, ?_, by simp [φ]⟩
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    obtain ⟨a, ha⟩ := (h G).2 (pushout.inr _ _)
    exact hf a (by simpa [φ] using ha =≫ φ)
  · exact (IsPushout.of_hasPushout _ _).mono_of_isPushout_of_isPullback_of_mono
      (IsPullback.of_hasPullback p f) φ (by simp [φ]) (by simp [φ])

variable {X : C}

lemma exists_larger_subobject {X : C} (A : Subobject X) (hA : A ≠ ⊤) :
    ∃ (A' : Subobject X) (h : A < A'),
      generatingMonomorphismsPushouts G (Subobject.ofLE _ _ h.le) := by
  induction' A using Subobject.ind with Y f _
  obtain ⟨X', i, p', hi, hi', hp', fac⟩ := exists_generatingMonomorphismsPushouts hG f
    (by simpa only [Subobject.isIso_iff_mk_eq_top] using hA)
  refine ⟨Subobject.mk p', Subobject.mk_lt_mk_of_comm i fac hi',
    (MorphismProperty.arrow_mk_iso_iff _ ?_).2 hi⟩
  refine Arrow.isoMk (Subobject.underlyingIso f) (Subobject.underlyingIso p') ?_
  dsimp
  simp only [← cancel_mono p', assoc, fac,
    Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]

open Classical in
noncomputable def largerSubobject (A : Subobject X) : Subobject X :=
  if hA : A = ⊤ then ⊤ else (exists_larger_subobject hG A hA).choose

variable (X) in
@[simp]
lemma largerSubobject_top : largerSubobject hG (⊤ : Subobject X) = ⊤ := dif_pos rfl

lemma lt_largerSubobject (A : Subobject X) (hA : A ≠ ⊤) :
    A < largerSubobject hG A := by
  dsimp only [largerSubobject]
  rw [dif_neg hA]
  exact (exists_larger_subobject hG A hA).choose_spec.choose

lemma le_largerSubobject (A : Subobject X) :
    A ≤ largerSubobject hG A := by
  by_cases hA : A = ⊤
  · subst hA
    simp only [largerSubobject_top, le_refl]
  · exact (lt_largerSubobject hG A hA).le

lemma generatingMonomorphismsPushouts_ofLE_le_largerSubobject (A : Subobject X) :
      generatingMonomorphismsPushouts G (Subobject.ofLE _ _ (le_largerSubobject hG A)) := by
  by_cases hA : A = ⊤
  · subst hA
    have := (Subobject.isIso_arrow_iff_eq_top (largerSubobject hG (⊤ : Subobject X))).2 (by simp)
    exact (MorphismProperty.arrow_mk_iso_iff _
      (Arrow.isoMk (asIso (Subobject.arrow _)) (asIso (Subobject.arrow _)) (by simp))).2
        (isomorphisms_le_generatingMonomorphismsPushouts G (𝟙 X)
          (MorphismProperty.isomorphisms.infer_property _))
  · refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1
      (exists_larger_subobject hG A hA).choose_spec.choose_spec
    exact Arrow.isoMk (Iso.refl _)
      (Subobject.isoOfEq _ _ ((by simp [largerSubobject, dif_neg hA])))

variable [IsGrothendieckAbelian.{w} C]

lemma top_mem_range (A₀ : Subobject X) {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J] (hJ : Cardinal.mk (Shrink (Subobject X)) < Cardinal.mk J) :
    ∃ (j : J), transfiniteIterate (largerSubobject hG) j A₀ = ⊤ :=
  top_mem_range_transfiniteIterate (largerSubobject hG) A₀ (lt_largerSubobject hG) (by simp)
    (fun h ↦ (lt_self_iff_false _).1 (lt_of_le_of_lt
      (Cardinal.mk_le_of_injective ((equivShrink.{w} (Subobject X)).injective.comp h)) hJ))

lemma exists_ordinal (A₀ : Subobject X) :
    ∃ (o : Ordinal.{w}) (j : o.toType), transfiniteIterate (largerSubobject hG) j A₀ = ⊤ := by
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject X)))
  have : OrderBot κ.ord.toType := Ordinal.toTypeOrderBotOfPos (by
    rw [Cardinal.zero_lt_ord_iff]
    exact Cardinal.succ_ne_zero _)
  exact ⟨κ.ord, top_mem_range hG A₀ (lt_of_lt_of_le (Order.lt_succ _) (by simp))⟩

section

variable (A₀ : Subobject X) (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

@[simps]
noncomputable def functorToMonoOver : J ⥤ MonoOver X where
  obj j := MonoOver.mk' (transfiniteIterate (largerSubobject hG) j A₀).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE _ _
      (monotone_transfiniteIterate _ _ (le_largerSubobject hG) (leOfHom f)))

noncomputable abbrev functor : J ⥤ C :=
  functorToMonoOver hG A₀ J ⋙ MonoOver.forget _ ⋙ Over.forget _

/-instance : (functor hG A₀ J).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    -- use variant of `subobject_mk_of_isColimit_eq_iSup` from
    -- `CategoryTheory.Presentable.GrothendieckAbelian` in #20014
    sorry

--example (j : J) : ((functor hG A₀ J).restrictionLE j).IsWellOrderContinuous := inferInstance -/

lemma mono_functor_map_le_succ (j : J) (hj : ¬IsMax j) :
    generatingMonomorphismsPushouts G ((functor hG A₀ J).map (homOfLE (Order.le_succ j))) := by
  refine (MorphismProperty.arrow_mk_iso_iff _ ?_).2
    (generatingMonomorphismsPushouts_ofLE_le_largerSubobject hG
      (transfiniteIterate (largerSubobject hG) j A₀))
  exact Arrow.isoMk (Iso.refl _) (Subobject.isoOfEq _ _ (transfiniteIterate_succ _ _ _ hj))
    (by simp [MonoOver.forget])

end

section

variable {A : C} {f : A ⟶ X} [Mono f] (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]
variable {j : J} (hj : transfiniteIterate (largerSubobject hG) j (Subobject.mk f) = ⊤)

noncomputable def arrowIso :
    Arrow.mk f ≅ Arrow.mk (((functor hG (Subobject.mk f) J).coconeLE j).ι.app ⊥) := by
  let t := transfiniteIterate (largerSubobject hG) j (Subobject.mk f)
  have := (Subobject.isIso_arrow_iff_eq_top t).mpr hj
  refine (Arrow.isoMk (Subobject.isoOfEq _ _ (transfiniteIterate_bot _ _) ≪≫
    Subobject.underlyingIso f) (asIso t.arrow) ?_).symm
  simp [MonoOver.forget]
  rfl

end

end TransfiniteCompositionMonoPushouts

end IsGrothendieckAbelian

end Abelian

end CategoryTheory
