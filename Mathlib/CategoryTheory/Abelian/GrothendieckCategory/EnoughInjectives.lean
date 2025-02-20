/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.Monomorphisms
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Monomorphisms
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.Order.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Grothendieck abelian categories have enough injectives

TODO

-/

universe w v u

lemma Set.Iic.succ_eq {α : Type u} [PartialOrder α] [SuccOrder α] {j : α}
    (k : Set.Iic j) (hk : ¬ IsMax k) :
    Order.succ k = Order.succ k.1 :=
  coe_succ_of_mem (by
    obtain ⟨k, hk'⟩ := k
    simp only [mem_Iic] at hk' ⊢
    rw [Order.succ_le_iff_of_not_isMax
      (fun hk' ↦ hk (fun ⟨a, ha⟩ hka ↦ by exact hk' hka))]
    obtain _ | rfl := hk'.lt_or_eq
    · assumption
    · exfalso
      exact hk (fun x _ ↦ x.2))

lemma _root_.Set.Iio.nonempty {J : Type w} [LinearOrder J] [OrderBot J]
    (j : J) (hj : Order.IsSuccLimit j) : Nonempty (Set.Iio j) :=
  ⟨⟨⊥, Ne.bot_lt (by simpa using hj.not_isMin)⟩⟩

namespace CategoryTheory

open Category Opposite Limits ZeroObject

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

lemma map_mk {A X Y : C} (i : A ⟶ X) [Mono i] (f : X ⟶ Y) [Mono f] :
    (map f).obj (mk i) = mk (i ≫ f) :=
  rfl

lemma map_obj_injective {X Y : C} (f : X ⟶ Y) [Mono f] :
    Function.Injective (Subobject.map f).obj := by
  intro X₁ X₂ h
  induction' X₁ using Subobject.ind with X₁ i₁ _
  induction' X₂ using Subobject.ind with X₂ i₂ _
  simp only [map_mk] at h
  exact mk_eq_mk_of_comm _ _ (isoOfMkEqMk _ _ h) (by simp [← cancel_mono f])

lemma hasCardinalLT_of_mono {Y : C} {κ : Cardinal.{w}}
    (h : HasCardinalLT (Subobject Y) κ) {X : C} (f : X ⟶ Y) [Mono f] :
    HasCardinalLT (Subobject X) κ :=
  h.of_injective _ (map_obj_injective f)

end Subobject

section Abelian

namespace IsPushout

variable [Abelian C] {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {j : X ⟶ Y} {g : B ⟶ Y}

lemma mono_of_isPullback_of_mono {A B X Y : C}
    {f : A ⟶ X} {i : A ⟶ B} {j : X ⟶ Y} {g : B ⟶ Y}
    (h₁ : IsPushout f i j g) {Z : C} {j' : X ⟶ Z} {g' : B ⟶ Z}
    (h₂ : IsPullback f i j' g') (k : Y ⟶ Z)
    (fac₁ : j ≫ k = j') (fac₂ : g ≫ k = g') [Mono j'] : Mono k :=
  Preadditive.mono_of_cancel_zero _ (fun {T₀} y hy ↦ by
    obtain ⟨T₁, π, _, x, b, eq⟩ := hom_eq_add_up_to_refinements h₁ y
    have fac₃ : (-x) ≫ j' = b ≫ g' := by
      rw [Preadditive.neg_comp, neg_eq_iff_add_eq_zero, ← fac₂, ← fac₁,
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

namespace IsGrothendieckAbelian

section

variable {J : Type w} [SmallCategory J] {X : C} (F : J ⥤ MonoOver X) [Abelian C]
  [IsGrothendieckAbelian.{w} C]
  [IsFiltered J] (c : Cocone (F ⋙ MonoOver.forget _)) [Mono c.pt.hom]
  (h : Subobject.mk c.pt.hom = ⨆ j, Subobject.mk (F.obj j).obj.hom)

noncomputable def isColimitMapCoconeOfSubobjectMkEqISup :
    IsColimit ((Over.forget _).mapCocone c) := by
  let f : colimit (F ⋙ MonoOver.forget X ⋙ Over.forget X) ⟶ X :=
    colimit.desc _ (Cocone.mk X
      { app j := (F.obj j).obj.hom
        naturality {j j'} g := by simp [MonoOver.forget] })
  have := mono_of_isColimit_monoOver F (colimit.isColimit _) f (by simp [f])
  have := subobject_mk_of_isColimit_eq_iSup F (colimit.isColimit _) f (by simp [f])
  rw [← h] at this
  refine IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocones.ext (Subobject.isoOfMkEqMk _ _ this) (fun j ↦ ?_))
  rw [← cancel_mono (c.pt.hom)]
  dsimp
  rw [Category.assoc, Subobject.ofMkLEMk_comp, Over.w]
  apply colimit.ι_desc

end

def generatingMonomorphisms (G : C) : MorphismProperty C :=
  MorphismProperty.ofHoms (fun (X : Subobject G) ↦ X.arrow)

instance (G : C) [Small.{w} (Subobject G)] :
    MorphismProperty.IsSmall.{w} (generatingMonomorphisms G) := by
  dsimp [generatingMonomorphisms]
  infer_instance

lemma generatingMonomorphisms_le_monomorphisms (G : C) :
    generatingMonomorphisms G ≤ MorphismProperty.monomorphisms C := by
  rintro _ _ _ ⟨X⟩
  exact inferInstanceAs (Mono _)

variable (G : C)

abbrev generatingMonomorphismsPushouts := (generatingMonomorphisms G).pushouts

variable [Abelian C]

lemma isomorphisms_le_generatingMonomorphismsPushouts :
    MorphismProperty.isomorphisms C ≤ generatingMonomorphismsPushouts G :=
  MorphismProperty.isomorphisms_le_pushouts _ (fun _ ↦ ⟨_, _, _, ⟨⊤⟩, 0, inferInstance⟩)

variable {G}

namespace TransfiniteCompositionMonoPushouts

variable (hG : IsSeparator G)
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
  · exact (IsPushout.of_hasPushout _ _).mono_of_isPullback_of_mono
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
  have : OrderBot κ.ord.toType := Ordinal.toTypeOrderBot (by
    simp only [ne_eq, Cardinal.ord_eq_zero]
    apply Cardinal.succ_ne_zero)
  exact ⟨κ.ord, top_mem_range hG A₀ (lt_of_lt_of_le (Order.lt_succ _) (by simp [κ]))⟩

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

instance : (functor hG A₀ J).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    have := Set.Iio.nonempty _ hm
    let c := (Set.principalSegIio m).cocone (functorToMonoOver hG A₀ J ⋙ MonoOver.forget _)
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio m).monotone.functor ⋙ functorToMonoOver hG A₀ J) c
    dsimp [c]
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit (largerSubobject hG) A₀ m hm⟩

lemma mono_functor_map_le_succ (j : J) (hj : ¬IsMax j) :
    generatingMonomorphismsPushouts G ((functor hG A₀ J).map (homOfLE (Order.le_succ j))) := by
  refine (MorphismProperty.arrow_mk_iso_iff _ ?_).2
    (generatingMonomorphismsPushouts_ofLE_le_largerSubobject hG
      (transfiniteIterate (largerSubobject hG) j A₀))
  exact Arrow.isoMk (Iso.refl _) (Subobject.isoOfEq _ _ (transfiniteIterate_succ _ _ _ hj))
    (by simp [MonoOver.forget])

variable {J} in
noncomputable def transfiniteCompositionOfShape'' (j : J) :
  (generatingMonomorphismsPushouts G).TransfiniteCompositionOfShape (Set.Iic j)
    ((functor hG A₀ J).map (homOfLE bot_le : ⊥ ⟶ j)) where
  F := (Set.initialSegIic j).monotone.functor ⋙ functor hG A₀ J
  isoBot := Iso.refl _
  incl :=
    { app k := (functor hG A₀ J).map (homOfLE k.2)
      naturality k k' h := by simp [MonoOver.forget] }
  isColimit := colimitOfDiagramTerminal isTerminalTop _
  map_mem k hk := by
    dsimp [MonoOver.forget]
    convert generatingMonomorphismsPushouts_ofLE_le_largerSubobject hG
      (transfiniteIterate (largerSubobject hG) k.1 A₀) using 2
    all_goals
      rw [Set.Iic.succ_eq _ hk, transfiniteIterate_succ _ _ _ (Set.not_isMax_coe _ hk)]

end

variable {A : C} {f : A ⟶ X} [Mono f] {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J] {j : J}

noncomputable def transfiniteCompositionOfShape
    (hj : transfiniteIterate (largerSubobject hG) j (Subobject.mk f) = ⊤) :
    (generatingMonomorphismsPushouts G).TransfiniteCompositionOfShape (Set.Iic j) f := by
  let t := transfiniteIterate (largerSubobject hG) j (Subobject.mk f)
  have := (Subobject.isIso_arrow_iff_eq_top t).mpr hj
  apply (transfiniteCompositionOfShape'' hG (Subobject.mk f) j).ofArrowIso
  refine Arrow.isoMk ((Subobject.isoOfEq _ _ (transfiniteIterate_bot _ _) ≪≫
    Subobject.underlyingIso f)) (asIso t.arrow) ?_
  dsimp [MonoOver.forget]
  rw [assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow,
    Subobject.ofLE_arrow]

lemma transfiniteCompositionsOfShape
    (hj : transfiniteIterate (largerSubobject hG) j (Subobject.mk f) = ⊤) :
    (generatingMonomorphismsPushouts G).transfiniteCompositionsOfShape (Set.Iic j) f :=
  (transfiniteCompositionOfShape hG hj).mem

end TransfiniteCompositionMonoPushouts

open TransfiniteCompositionMonoPushouts in
lemma generatingMonomorphisms_rlp [IsGrothendieckAbelian.{w} C] (hG : IsSeparator G) :
    (generatingMonomorphisms G).rlp = (MorphismProperty.monomorphisms C).rlp := by
  apply le_antisymm
  · intro X Y p hp A B i (_ : Mono i)
    obtain ⟨o, j, hj⟩ := exists_ordinal hG (Subobject.mk i)
    have ho : Nonempty o.toType := ⟨j⟩
    rw [o.toType_nonempty_iff_ne_zero] at ho
    let _ : OrderBot o.toType := by
      apply Ordinal.toTypeOrderBot
      by_contra!
      exact ho (by simpa using this)
    refine MorphismProperty.transfiniteCompositionsOfShape_le_llp_rlp _ _ _
      (transfiniteCompositionsOfShape hG hj) _
      (by simpa)
  · exact MorphismProperty.antitone_rlp (generatingMonomorphisms_le_monomorphisms _)

open MorphismProperty

instance (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] :
    IsCardinalFiltered κ.ord.toType κ :=
  isCardinalFiltered_preorder _ _ (fun ι f hs ↦ by
    have h : Function.Surjective (fun i ↦ (⟨f i, i, rfl⟩ : Set.range f)) := fun _ ↦ by aesop
    have pif := Cardinal.mk_le_of_surjective h
    obtain ⟨j, hj⟩ := Ordinal.lt_cof_type (α := κ.ord.toType) (r := (· < ·))
      (S := Set.range f) (lt_of_le_of_lt (Cardinal.mk_le_of_surjective h) (lt_of_lt_of_le hs
          (by simp [hκ.out.cof_eq])))
    exact ⟨j, fun i ↦ (hj (f i) (by simp)).le⟩)

variable (G) in
lemma hasSmallObjectArgument_generatingMonomorphisms
    [IsGrothendieckAbelian.{w} C] :
    HasSmallObjectArgument.{w} (generatingMonomorphisms G) := by
  obtain ⟨κ, hκ', hκ⟩ := HasCardinalLT.exists_regular_cardinal.{w} (Subobject G)
  have : Fact κ.IsRegular := ⟨hκ'⟩
  letI := Cardinal.toTypeOrderBot hκ'.ne_zero
  exact ⟨κ, inferInstance, inferInstance,
    { preservesColimit {A B X Y} i hi f hf := by
        let hf' : (monomorphisms C).TransfiniteCompositionOfShape κ.ord.toType f :=
          { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
            map_mem j hj := by
              have := (hf.attachCells j hj).pushouts_coproducts
              simp only [ofHoms_homFamily] at this
              refine (?_ : _ ≤ monomorphisms C) _ this
              simp only [pushouts_le_iff, coproducts_le_iff]
              exact generatingMonomorphisms_le_monomorphisms G }
        have := hf'.mono_map
        apply preservesColimit_coyoneda_obj_of_mono (Y := hf.F) (κ := κ)
        obtain ⟨S⟩ := hi
        exact Subobject.hasCardinalLT_of_mono hκ S.arrow }⟩


lemma llp_rlp_monomorphisms [IsGrothendieckAbelian.{w} C] (hG : IsSeparator G) :
    (monomorphisms C).rlp.llp = monomorphisms C := by
  have := hasSmallObjectArgument_generatingMonomorphisms.{w} G
  refine le_antisymm ?_ (le_llp_rlp _)
  rw [← generatingMonomorphisms_rlp hG, llp_rlp_of_hasSmallObjectArgument]
  trans (transfiniteCompositions.{w} (coproducts.{w} (monomorphisms C)).pushouts).retracts
  · apply retracts_monotone
    apply transfiniteCompositions_monotone
    apply pushouts_monotone
    apply coproducts_monotone
    apply generatingMonomorphisms_le_monomorphisms
  · simp

lemma hasFunctorialFactorization_monomorphisms_rlp_monomorphisms
    [IsGrothendieckAbelian.{w} C] (hG : IsSeparator G) :
    HasFunctorialFactorization (monomorphisms C) (monomorphisms C).rlp := by
  have := hasSmallObjectArgument_generatingMonomorphisms.{w} G
  rw [← generatingMonomorphisms_rlp hG, ← llp_rlp_monomorphisms hG,
    ← generatingMonomorphisms_rlp hG]
  infer_instance

instance enoughInjectives [IsGrothendieckAbelian.{w} C] :
    EnoughInjectives C where
  presentation X := by
    have := hasFunctorialFactorization_monomorphisms_rlp_monomorphisms.{w}
      (isSeparator_separator C)
    have fac := factorizationData (monomorphisms C) (monomorphisms C).rlp (0 : X ⟶ 0)
    exact ⟨{
        f := fac.i
        injective := by
          rw [injective_iff_rlp_monomorphisms_zero]
          convert fac.hp
          apply (isZero_zero C).eq_of_tgt
        mono := fac.hi
    }⟩

end IsGrothendieckAbelian

end CategoryTheory
