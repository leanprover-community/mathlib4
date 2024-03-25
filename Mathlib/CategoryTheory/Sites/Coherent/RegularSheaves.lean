/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Limits.Final
/-!

# Sheaves for the regular topology

This file characterises sheaves for the regular topology.

## Main results

* `isSheaf_iff_equalizerCondition`: In a preregular category with pullbacks, the sheaves for the
  regular topology are precisely the presheaves satisfying an equaliser condition with respect to
  effective epimorphisms.

* `isSheaf_of_projective`: In a preregular category in which every object is projective, every
  presheaf is a sheaf for the regular topology.
-/

namespace CategoryTheory

open Limits

variable {C D E : Type*} [Category C] [Category D] [Category E]

open Opposite Presieve Functor

/-- A presieve is *regular* if it consists of a single effective epimorphism. -/
class Presieve.regular {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a single epimorphism. -/
  single_epi : ∃ (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : Unit) ↦ Y)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f

namespace regularTopology

lemma equalizerCondition_w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) :
    P.map π.op ≫ P.map c.fst.op = P.map π.op ≫ P.map c.snd.op := by
  simp only [← Functor.map_comp, ← op_comp, c.condition]

def SingleEqualizerCondition (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B) : Prop :=
  ∀ (c : PullbackCone π π) (_ : IsLimit c),
    Nonempty (IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)))

/--
A contravariant functor on `C` satisfies `EqualizerCondition` if it takes kernel pairs of effective
epimorphisms to equalizer diagrams.
-/
def EqualizerCondition (P : Cᵒᵖ ⥤ D) : Prop :=
  ∀ ⦃X B : C⦄ (π : X ⟶ B) [EffectiveEpi π], SingleEqualizerCondition P π

/-- The equalizer condition is preserved by natural isomorphism. -/
theorem equalizerCondition_of_natIso {P P' : Cᵒᵖ ⥤ D} (i : P ≅ P')
    (hP : EqualizerCondition P) : EqualizerCondition P' := fun X B π _ c hc ↦
  ⟨Fork.isLimitOfIsos _ (hP π c hc).some _ (i.app _) (i.app _) (i.app _)⟩

/-- Precomposing with a pullback-preserving functor preserves the equalizer condition. -/
theorem equalizerCondition_precomp_of_preservesPullback (P : Cᵒᵖ ⥤ D) (F : E ⥤ C)
    [∀ {X B} (π : X ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) F]
    [F.PreservesEffectiveEpis] (hP : EqualizerCondition P) : EqualizerCondition (F.op ⋙ P) := by
  intro X B π _ c hc
  have h : P.map (F.map π).op = (F.op ⋙ P).map π.op := by simp
  refine ⟨(IsLimit.equivIsoLimit (ForkOfι.ext ?_ _ h)) ?_⟩
  · simp only [Functor.comp_map, op_map, Quiver.Hom.unop_op, ← map_comp, ← op_comp, c.condition]
  · refine (hP (F.map π) (PullbackCone.mk (F.map c.fst) (F.map c.snd) ?_) ?_).some
    · simp only [← map_comp, c.condition]
    · exact (isLimitMapConePullbackConeEquiv F c.condition)
        (isLimitOfPreserves F (hc.ofIsoLimit (PullbackCone.ext (Iso.refl _) (by simp) (by simp))))

/-- The canonical map to the explicit equalizer. -/
def MapToEqualizer (P : Cᵒᵖ ⥤ Type*) {W X B : C} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } := fun t ↦
  ⟨P.map f.op t, by simp only [Set.mem_setOf_eq, ← FunctorToTypes.map_comp_apply, ← op_comp, w]⟩

theorem EqualizerCondition.bijective_mapToEqualizer_pullback (P : Cᵒᵖ ⥤ Type*)
    (hP : EqualizerCondition P) : ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π],
    Function.Bijective
      (MapToEqualizer P π (pullback.fst (f := π) (g := π)) (pullback.snd (f := π) (g := π))
        pullback.condition) := by
  intro X B π _ _
  specialize hP π _ (pullbackIsPullback π π)
  rw [Types.type_equalizer_iff_unique] at hP
  rw [Function.bijective_iff_existsUnique]
  intro ⟨b, hb⟩
  obtain ⟨a, ha₁, ha₂⟩ := hP b hb
  refine ⟨a, ?_, ?_⟩
  · simpa [MapToEqualizer] using ha₁
  · simpa [MapToEqualizer] using ha₂

theorem EqualizerCondition.mk (P : Cᵒᵖ ⥤ Type*)
    (hP : ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], Function.Bijective
    (MapToEqualizer P π (pullback.fst (f := π) (g := π)) (pullback.snd (f := π) (g := π))
    pullback.condition)) : EqualizerCondition P := by
  intro X B π _ c hc
  have : HasPullback π π := ⟨c, hc⟩
  specialize hP X B π
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  have h₁ : ((pullbackIsPullback π π).conePointUniqueUpToIso hc).hom ≫ c.fst =
    pullback.fst (f := π) (g := π) := by simp
  have hb' : P.map (pullback.fst (f := π) (g := π)).op b = P.map pullback.snd.op b := by
    rw [← h₁, op_comp, FunctorToTypes.map_comp_apply, hb]
    simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb'⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [MapToEqualizer] using ha₁
  · simpa [MapToEqualizer] using ha₂

lemma equalizerCondition_iff_isIso_lift_w (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B)
    [HasPullback π π] : P.map π.op ≫ P.map (pullback.fst (f := π) (g := π)).op =
    P.map π.op ≫ P.map (pullback.snd).op := by
  simp only [← Functor.map_comp, ← op_comp, pullback.condition]

lemma mapToEqualizer_eq_comp (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B)
    [HasPullback π π] : MapToEqualizer P π pullback.fst pullback.snd pullback.condition =
    equalizer.lift (P.map π.op) (equalizerCondition_iff_isIso_lift_w P π) ≫
    (Types.equalizerIso _ _).hom := by
  rw [← Iso.comp_inv_eq (α := Types.equalizerIso _ _)]
  apply equalizer.hom_ext
  aesop

/-- An alternative phrasing of the explicit equalizer condition, using more categorical language. -/
theorem equalizerCondition_iff_isIso_lift (P : Cᵒᵖ ⥤ Type*) : EqualizerCondition P ↔
    ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], IsIso
    (equalizer.lift (P.map π.op) (equalizerCondition_iff_isIso_lift_w P π)) := by
  constructor
  · intro hP X B π _ _
    have h := hP.bijective_mapToEqualizer_pullback _ X B π
    rw [← isIso_iff_bijective, mapToEqualizer_eq_comp] at h
    exact IsIso.of_isIso_comp_right (equalizer.lift (P.map π.op)
      (equalizerCondition_iff_isIso_lift_w P π))
      (Types.equalizerIso _ _).hom
  · intro hP
    apply EqualizerCondition.mk
    intro X B π _ _
    rw [mapToEqualizer_eq_comp, ← isIso_iff_bijective]
    infer_instance

/-- `P` satisfies the equalizer condition iff its precomposition by an equivalence does. -/
theorem equalizerCondition_iff_of_equivalence (P : Cᵒᵖ ⥤ D)
    (e : C ≌ E) : EqualizerCondition P ↔ EqualizerCondition (e.op.inverse ⋙ P) :=
  ⟨fun h ↦ equalizerCondition_precomp_of_preservesPullback P e.inverse h, fun h ↦
    equalizerCondition_of_natIso (e.op.funInvIdAssoc P)
      (equalizerCondition_precomp_of_preservesPullback (e.op.inverse ⋙ P) e.functor h)⟩

namespace SingleEqualizerConditionIffNonemptyIsLimit

variable {P : Cᵒᵖ ⥤ D} ⦃X B : C⦄ {π : X ⟶ B}

noncomputable def isLimitMapCone (hP : SingleEqualizerCondition P π) (c : PullbackCone π π) (hc : IsLimit c) :
    IsLimit (P.mapCone (Sieve.ofArrows
      (fun (_ : Unit) => X) (fun _ => π)).arrows.cocone.op) where
  lift s := Fork.IsLimit.lift (hP c hc).some
    (s.π.app (Opposite.op ⟨Over.mk π, Sieve.ofArrows_mk _ _ Unit.unit⟩))
      ((s.w ((by exact Over.homMk c.fst rfl) : ⟨Over.mk (c.fst ≫ π),
          (Sieve.mem_ofArrows_iff _ _ _).2 ⟨Unit.unit, _, rfl⟩⟩ ⟶ ⟨Over.mk π, _⟩).op).trans
        (s.w ((by exact Over.homMk c.snd c.condition.symm) : ⟨Over.mk (c.fst ≫ π), _⟩ ⟶ ⟨Over.mk π, _⟩).op).symm)
  fac s j := by
    obtain ⟨_, a, _, ⟨⟨⟩⟩, fac⟩ := j.unop.2
    let φ : j.unop ⟶ ⟨Over.mk π, Sieve.ofArrows_mk _ _ Unit.unit⟩ := Over.homMk a fac
    have h := (P.mapCone (Cocone.op
      (cocone (Sieve.ofArrows (fun (_ : Unit) ↦ X) fun _ ↦ π).arrows))).w φ.op
    dsimp at h ⊢
    rw [← h]
    erw [Fork.IsLimit.lift_ι'_assoc (hP c hc).some]
    exact s.w φ.op
  uniq s m hm := by
    apply Fork.IsLimit.hom_ext (hP c hc).some
    erw [Fork.IsLimit.lift_ι' (hP c hc).some]
    exact hm (Opposite.op ⟨Over.mk π, _⟩)

section

variable (hP : IsLimit (P.mapCone (Cocone.op
  (cocone (Sieve.ofArrows (fun (_ : Unit) ↦ X) fun _ ↦ π).arrows))))
  {c : PullbackCone π π} (hc : IsLimit c)

section

variable (s : Fork (P.map c.fst.op) (P.map c.snd.op))
  (Y : (FullSubcategory fun (f : Over B) ↦
      (Sieve.ofArrows (fun (_ : Unit) ↦ X) fun _ ↦ π).arrows f.hom)ᵒᵖ )

-- a name should be given to this `FullSubcategory`, `Sieve.category` ?
-- also an abbreviation `(Pre)sieve.ofArrow`
noncomputable def coneOfConeπApp : s.pt ⟶ P.obj (op Y.unop.obj.left) :=
  s.ι ≫ P.map ((Sieve.mem_ofArrows_iff _ _ _).1 Y.unop.2).choose_spec.choose.op

lemma coneOfConeπApp_eq (f : Y.unop.obj.left ⟶ X)
    (fac : f ≫ π = Y.unop.obj.hom) :
    coneOfConeπApp s Y = s.ι ≫ P.map f.op := by
  have := hc
  suffices ∀ (f' : Y.unop.obj.left ⟶ X) (_ : f' ≫ π = Y.unop.obj.hom),
      s.ι ≫ P.map f'.op = s.ι ≫ P.map f.op from
    this _ ((Sieve.mem_ofArrows_iff _ _ _).1 Y.unop.2).choose_spec.choose_spec.symm
  intro f' fac'
  obtain ⟨g, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hc f f' (fac.trans fac'.symm)
  dsimp
  simp only [Functor.map_comp, s.condition_assoc]

@[simps]
noncomputable def coneOfCone :
    Cone ((diagram (Sieve.ofArrows (fun (_ : Unit) ↦ X) fun _ ↦ π).arrows).op ⋙ P) where
  pt := s.pt
  π :=
    { app := coneOfConeπApp s
      naturality := fun Y Y' φ => by
        have := hc
        obtain ⟨⟨⟩, f, hf⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 Y.unop.2
        dsimp
        rw [Category.id_comp, coneOfConeπApp_eq hc s Y f hf.symm,
          coneOfConeπApp_eq hc s Y' (φ.unop.left ≫ f)
            (by rw [Category.assoc, ← hf, Over.w φ.unop]), op_comp, Functor.map_comp,
          Category.assoc] }

end

noncomputable def isLimitFork : IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)) :=
  Fork.IsLimit.mk _ (fun s => hP.lift (coneOfCone hc s)) (fun s => by
    have h := hP.fac (coneOfCone hc s) (Opposite.op (⟨Over.mk π, Sieve.ofArrows_mk _ _ Unit.unit⟩))
    dsimp at h ⊢
    rw [h, coneOfConeπApp_eq hc s _ (by exact 𝟙 X) (by simp)]
    simp) (fun s m hm => hP.hom_ext (fun j => by
      rw [hP.fac (coneOfCone hc s) j]
      obtain ⟨_, a, _, ⟨⟨⟩⟩, fac⟩ := j.unop.2
      dsimp at hm a ⊢
      rw [← fac, op_comp, Functor.map_comp, reassoc_of% hm, coneOfConeπApp_eq hc s j _ fac]))

end

end SingleEqualizerConditionIffNonemptyIsLimit


section

open WalkingParallelPair WalkingParallelPairHom
lemma _root_.CategoryTheory.Limits.parallelPair_initial_mk' {X Y : C} (f g : X ⟶ Y)
    (h₁ : ∀ Z, Nonempty (X ⟶ Z))
    (h₂ : ∀ ⦃Z : C⦄ (i j : X ⟶ Z),
      Zigzag (J := CostructuredArrow (parallelPair f g) Z)
        (CostructuredArrow.mk (Y := zero) i)
        (CostructuredArrow.mk (Y := zero) j)) : (parallelPair f g).Initial where
  out Z := by
    have : Nonempty (CostructuredArrow (parallelPair f g) Z) :=
      ⟨CostructuredArrow.mk (Y := zero) (h₁ Z).some⟩
    have : ∀ (x : CostructuredArrow (parallelPair f g) Z), Zigzag x
      (CostructuredArrow.mk (Y := zero) (h₁ Z).some) := by
        rintro ⟨(_|_), ⟨⟩, φ⟩
        · apply h₂
        · refine Relation.ReflTransGen.trans ?_ (h₂ (f ≫ φ) _)
          exact Relation.ReflTransGen.single (Or.inr ⟨CostructuredArrow.homMk left⟩)
    exact zigzag_isConnected (fun x y => (this x).trans (zigzag_symmetric (this y)))

lemma _root_.CategoryTheory.Limits.parallelPair_initial_mk {X Y : C} (f g : X ⟶ Y)
    (h₁ : ∀ Z, Nonempty (X ⟶ Z))
    (h₂ : ∀ ⦃Z : C⦄ (i j : X ⟶ Z), ∃ (a : Y ⟶ Z), i = f ≫ a ∧ j = g ≫ a) :
    (parallelPair f g).Initial :=
  parallelPair_initial_mk' f g h₁ (fun Z i j => by
    obtain ⟨a, rfl, rfl⟩ := h₂ i j
    have z₁ : Zigzag (J := CostructuredArrow (parallelPair f g) Z)
      (CostructuredArrow.mk (Y := zero) (f ≫ a))
      (CostructuredArrow.mk (Y := one) a) := Relation.ReflTransGen.single
        (Or.inl ⟨CostructuredArrow.homMk left⟩)
    have z₃ : Zigzag (J := CostructuredArrow (parallelPair f g) Z)
      (CostructuredArrow.mk (Y := one) a)
      (CostructuredArrow.mk (Y := zero) (g ≫ a)) := Relation.ReflTransGen.single
        (Or.inr ⟨CostructuredArrow.homMk right⟩)
    exact z₁.trans z₃)

-- change the definition of `Presieve.diagram` to make this the source category
abbrev _root_.CategoryTheory.Presieve.category {X : C} (P : Presieve X) :=
  FullSubcategory fun f : Over X => P f.hom

abbrev _root_.CategoryTheory.Presieve.categoryMk {X : C} (P : Presieve X)
  {Y : C} (f : Y ⟶ X) (hf : P f) : P.category := ⟨Over.mk f, hf⟩

theorem parallelPair_pullback_initial {X B : C} (π : X ⟶ B)
    (c : PullbackCone π π) (hc : IsLimit c) :
    (parallelPair (C := (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows.categoryᵒᵖ)
    (Y := op ((Presieve.categoryMk _ (c.fst ≫ π) ⟨_, c.fst, π, ofArrows.mk (), rfl⟩)))
    (X := op ((Presieve.categoryMk _ π (Sieve.ofArrows_mk _ _ Unit.unit))))
    (Quiver.Hom.op (Over.homMk c.fst)) (Quiver.Hom.op (Over.homMk c.snd c.condition.symm))).Initial :=
  CategoryTheory.Limits.parallelPair_initial_mk _ _ (by
    rintro ⟨Z, T, φ, _, ⟨_⟩, fac⟩
    exact ⟨Quiver.Hom.op (Over.homMk _ fac)⟩) (by
    rintro ⟨⟨Z, ⟨⟩, α⟩, T, φ, _, ⟨_⟩, fac⟩ ⟨i, ⟨⟩, hi⟩ ⟨j, ⟨⟩, hj⟩
    dsimp at α φ fac i hi j hj
    refine' ⟨Quiver.Hom.op (Over.homMk (PullbackCone.IsLimit.lift hc i j (by rw [hi, hj]))),
      _, _⟩
    · apply Quiver.Hom.unop_inj
      apply (fullSubcategoryInclusion _).map_injective
      ext
      symm
      apply PullbackCone.IsLimit.lift_fst
    · apply Quiver.Hom.unop_inj
      apply (fullSubcategoryInclusion _).map_injective
      ext
      symm
      apply PullbackCone.IsLimit.lift_snd)


end


open SingleEqualizerConditionIffNonemptyIsLimit in
lemma singleEqualizerCondition_iff_nonempty_isLimit (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B)
    [HasPullback π π] :
    SingleEqualizerCondition P π ↔
      Nonempty (IsLimit (P.mapCone
        (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows.cocone.op)) := by
  constructor
  · intro hP
    exact ⟨isLimitMapCone hP _ (pullbackIsPullback _ _)⟩
  · rintro ⟨hP⟩ c hc
    exact ⟨isLimitFork hP hc⟩

lemma equalizerCondition_iff_isSheaf (F : Cᵒᵖ ⥤ D) [Preregular C]
    [∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] :
    EqualizerCondition F ↔ Presheaf.IsSheaf (regularTopology C) F := by
  dsimp [regularTopology]
  rw [Presheaf.isSheaf_iff_isLimit_coverage]
  constructor
  · rintro hF X _ ⟨Y, f, rfl, _⟩
    exact (singleEqualizerCondition_iff_nonempty_isLimit F f).1 (hF f)
  · intro hF Y X f _
    exact (singleEqualizerCondition_iff_nonempty_isLimit F f).2 (hF _ ⟨_, f, rfl, inferInstance⟩)

/-lemma EqualizerCondition.isSheafFor {B : C} {S : Presieve B} [S.regular] [S.hasPullbacks]
    {F : Cᵒᵖ ⥤ Type*} (hF : EqualizerCondition F) : S.IsSheafFor F := by
  obtain ⟨X, π, hS, πsurj⟩ := Presieve.regular.single_epi (R := S)
  subst hS
  rw [isSheafFor_arrows_iff_pullbacks]
  intro y h
  have : (Presieve.singleton π).hasPullbacks := by rw [← ofArrows_pUnit]; infer_instance
  have : HasPullback π π := hasPullbacks.has_pullbacks Presieve.singleton.mk Presieve.singleton.mk
  let c : PullbackCone π π := (IsPullback.of_hasPullback π π).cone
  have hc : IsLimit c := IsPullback.isLimit _
  specialize hF π c hc
  rw [Types.type_equalizer_iff_unique] at hF
  obtain ⟨t, ht⟩ := hF (y ()) (h () ())
  exact ⟨t, fun _ ↦ ht.1, fun _ h ↦ ht.2 _ (h _)⟩

lemma equalizerCondition_of_regular {F : Cᵒᵖ ⥤ Type*}
    (hSF : ∀ {B : C} (S : Presieve B) [S.regular] [S.hasPullbacks], S.IsSheafFor F) :
    EqualizerCondition F := by
  apply EqualizerCondition.mk
  intro X B π _ _
  have : (ofArrows (fun _ ↦ X) (fun _ ↦ π)).regular := ⟨X, π, rfl, inferInstance⟩
  have : (ofArrows (fun () ↦ X) (fun _ ↦ π)).hasPullbacks := ⟨
      fun hf _ hg ↦ (by cases hf; cases hg; infer_instance)⟩
  specialize hSF (ofArrows (fun () ↦ X) (fun _ ↦ π))
  rw [isSheafFor_arrows_iff_pullbacks] at hSF
  rw [Function.bijective_iff_existsUnique]
  intro ⟨x, hx⟩
  obtain ⟨t, ht, ht'⟩ := hSF (fun _ ↦ x) (fun _ _ ↦ hx)
  refine ⟨t, ?_, fun y h ↦ ht' y ?_⟩
  · simpa [MapToEqualizer] using ht ()
  · simpa [MapToEqualizer] using h-/

lemma isSheafFor_regular_of_projective {X : C} (S : Presieve X) [S.regular] [Projective X]
    (F : Cᵒᵖ ⥤ Type*) : S.IsSheafFor F := by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  rw [isSheafFor_arrows_iff]
  refine fun x hx ↦ ⟨F.map (Projective.factorThru (𝟙 _) f).op <| x (), fun _ ↦ ?_, fun y h ↦ ?_⟩
  · simpa using (hx () () Y (𝟙 Y) (f ≫ (Projective.factorThru (𝟙 _) f)) (by simp)).symm
  · simp only [← h (), ← FunctorToTypes.map_comp_apply, ← op_comp, Projective.factorThru_comp,
      op_id, FunctorToTypes.map_id_apply]
/-
/-- A presheaf is a sheaf for the regular topology iff it satisfies `EqualizerCondition` -/
theorem EqualizerCondition.isSheaf_iff (F : Cᵒᵖ ⥤ Type*)
    [∀ ⦃X Y : C⦄ (π : X ⟶ Y) [EffectiveEpi π], HasPullback π π] [Preregular C] :
    Presieve.IsSheaf (regularTopology C) F ↔ EqualizerCondition F := by
  rw [regularTopology, Presieve.isSheaf_coverage]
  refine ⟨fun h ↦ equalizerCondition_of_regular fun S ⟨Y, f, hh⟩ _ ↦ h S ⟨Y, f, hh⟩, ?_⟩
  rintro h X S ⟨Y, f, rfl, hf⟩
  exact @isSheafFor _ _ _ _ ⟨Y, f, rfl, hf⟩ ⟨fun g _ h ↦ by cases g; cases h; infer_instance⟩ _ h
  -/

/-- Every presheaf is a sheaf for the regular topology if every object of `C` is projective. -/
theorem isSheaf_of_projective' (F : Cᵒᵖ ⥤ Type*) [Preregular C] [∀ (X : C), Projective X] :
    IsSheaf (regularTopology C) F :=
  (isSheaf_coverage _ _).mpr fun S ⟨_, h⟩ ↦ have : S.regular := ⟨_, h⟩
    isSheafFor_regular_of_projective _ _

theorem isSheaf_of_projective (F : Cᵒᵖ ⥤ D) [Preregular C] [∀ (X : C), Projective X] :
    Presheaf.IsSheaf (regularTopology C) F :=
  fun _ => by apply isSheaf_of_projective'

/-- Every Yoneda-presheaf is a sheaf for the regular topology. -/
lemma isSheaf_yoneda_obj [Preregular C] (W : C)  :
    Presieve.IsSheaf (regularTopology C) (yoneda.obj W) := by
  rw [regularTopology, isSheaf_coverage]
  intro X S ⟨_, hS⟩
  have : S.regular := ⟨_, hS⟩
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  have h_colim := isColimitOfEffectiveEpiStruct f hf.effectiveEpi.some
  rw [← Sieve.generateSingleton_eq, ← Presieve.ofArrows_pUnit] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (Presieve.ofArrows (fun () ↦ Y) (fun () ↦ f))
  obtain ⟨t, t_amalg, t_uniq⟩ :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  · convert Presieve.isAmalgamation_restrict (Sieve.le_generate
      (Presieve.ofArrows (fun () ↦ Y) (fun () ↦ f))) _ _ t_amalg
    exact (Presieve.restrict_extend hx).symm
  · exact fun y hy ↦ t_uniq y <| Presieve.isAmalgamation_sieveExtend x y hy

/-- The regular topology on any preregular category is subcanonical. -/
theorem subcanonical [Preregular C] : Sheaf.Subcanonical (regularTopology C) :=
  Sheaf.Subcanonical.of_yoneda_isSheaf _ isSheaf_yoneda_obj

end regularTopology

end CategoryTheory
