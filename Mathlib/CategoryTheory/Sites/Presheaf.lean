/-
Copyright (c) 2027 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!

-/

@[expose] public section

universe w v v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {A : Type*} [Category.{v} A] {B : Type*} [Category.{v} B]

variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)

variable {P : ObjectProperty C}

def ObjectProperty.isHomInjective (P : ObjectProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ Z, P Z → Function.Injective fun (g : _ ⟶ Z) ↦ f ≫ g

def Presieve.leftComp {X : C} (R : Presieve X) (Y : C) :
    (X ⟶ Y) → ∀ (T : C) (u : T ⟶ X) (_ : R u), T ⟶ Y :=
  fun g _ u _ ↦ u ≫ g

def ObjectProperty.IsJointlyHomInjective (P : ObjectProperty C) {X : C} (R : Presieve X) : Prop :=
  ∀ Z, P Z → Function.Injective fun (g : X ⟶ Z) (T : C) (u : T ⟶ X) (_ : R u) ↦ u ≫ g

def ObjectProperty.IsJointlyHomSurjective (P : ObjectProperty C) {X : C} (R : Presieve X) : Prop :=
  ∀ Z, P Z → Function.Surjective fun (g : X ⟶ Z) (T : C) (u : T ⟶ X) (_ : R u) ↦ u ≫ g

def ObjectProperty.IsJointlyLocal (P : ObjectProperty C) {X : C} (R : Presieve X) : Prop :=
  ∀ Z, P Z → Function.Bijective fun (g : X ⟶ Z) (T : C) (u : T ⟶ X) (_ : R u) ↦ u ≫ g

lemma ObjectProperty.IsJointlyLocal.isJointlyHomInjective {X : C} {R : Presieve X}
    (h : P.IsJointlyLocal R) :
    P.IsJointlyHomInjective R :=
  fun Z hZ ↦ (h Z hZ).injective

lemma ObjectProperty.IsJointlyLocal.isJointlyHomSurjective {X : C} {R : Presieve X}
    (h : P.IsJointlyLocal R) :
    P.IsJointlyHomSurjective R :=
  fun Z hZ ↦ (h Z hZ).surjective

lemma ObjectProperty.isJointlyHomInjective_ofArrows_iff {X : C} {ι : Type*}
    {Y : ι → C} {f : ∀ i, Y i ⟶ X} :
    P.IsJointlyHomInjective (.ofArrows _ f) ↔
      ∀ Z, P Z → Function.Injective (fun (g : X ⟶ Z) (i : ι) ↦ f i ≫ g) := by
  refine ⟨fun h Z hZ a b hab ↦ h Z hZ ?_, fun h Z hZ a b hab ↦ h Z hZ ?_⟩
  · ext _ _ ⟨i⟩
    exact congr($(hab) i)
  · ext i
    exact congr($(hab) _ _ ⟨i⟩)

lemma ObjectProperty.isJointlyLocal_singleton (P : ObjectProperty C) {X Y : C} (f : X ⟶ Y) :
    P.IsJointlyLocal (.singleton f) ↔ P.isLocal f := by
  refine ⟨fun h Z hZ ↦ ⟨?_, ?_⟩, fun h Z hZ ↦ ⟨?_, ?_⟩⟩
  · intro a b hab
    apply (h Z hZ).injective
    ext _ _ ⟨⟩
    simpa
  · intro a
    obtain ⟨u, hu⟩ := (h Z hZ).surjective fun T v hv ↦ eqToHom (by cases hv; rfl) ≫ a
    exact ⟨u, by simp [dsimp% congr($(hu) _ _ ⟨⟩)]⟩
  · intro a b hab
    exact (h Z hZ).injective congr($(hab) _ _ ⟨⟩)
  · intro a
    obtain ⟨u, hu⟩ := (h Z hZ).surjective (a _ _ ⟨⟩)
    exact ⟨u, by ext _ _ ⟨⟩; simpa⟩

set_option backward.isDefEq.respectTransparency false in
lemma Adjunction.bijective_map_comp_iff {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y)
    (Z : D) :
    Function.Bijective (fun (g : F.obj Y ⟶ Z) ↦ F.map f ≫ g) ↔
      Function.Bijective (fun (g : Y ⟶ G.obj Z) ↦ f ≫ g) := by
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective,
    ← Function.Bijective.of_comp_iff _ (adj.homEquiv _ _).symm.bijective]
  congr!
  ext g
  simp [Adjunction.homEquiv_apply, Adjunction.homEquiv_symm_apply, ]

open Limits

def Sieve.equivSubfunctorYoneda (X : C) : Sieve X ≃ Subfunctor (yoneda.obj X) where
  toFun S := ⟨fun Y ↦ { f | S f }, fun {Y Z} g f hf ↦ S.downward_closed hf _⟩
  invFun F := ⟨fun Y f ↦ f ∈ F.obj (.op Y), fun {Y Z} f hf g ↦ F.map g.op hf⟩

@[simps]
def Sieve.shrinkFunctor [LocallySmall.{w} C] {X : C} (S : Sieve X) :
    Subfunctor (shrinkYoneda.{w}.obj X) where
  obj Y := { f | S (shrinkYonedaObjObjEquiv f) }
  map {Y Z} g f hf := by
    simpa [shrinkYonedaObjObjEquiv_map] using S.downward_closed hf _

set_option backward.isDefEq.respectTransparency false in
@[simps]
noncomputable
def Sieve.shrinkFunctorHomEquiv [LocallySmall.{w} C] {F : Cᵒᵖ ⥤ Type w} {X : C} {S : Sieve X} :
    (S.shrinkFunctor.toFunctor ⟶ F) ≃ { x : S.arrows.FamilyOfElements F // x.Compatible } where
  toFun t := ⟨fun Y f hf ↦ t.app _ ⟨shrinkYonedaObjObjEquiv.symm f, by simpa⟩, by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z f g hf
    simp only [shrinkFunctor_obj, ← FunctorToTypes.naturality]
    rw! [shrinkYonedaObjObjEquiv_symm_comp]
    rfl⟩
  invFun t :=
    { app X f := t.1 _ f.mem
      naturality Y Z g := by
        ext ⟨f, hf⟩
        dsimp
        convert t.2.to_sieveCompatible _ _ _
        simp only [Opposite.op_unop, shrinkYonedaObjObjEquiv_map]
        rfl }
  left_inv t := by cat_disch
  right_inv x := by
    ext
    dsimp
    rw! [Equiv.apply_symm_apply]
    simp

set_option backward.isDefEq.respectTransparency false in
lemma Sieve.shrinkFunctor_ι_comp_eq_iff_isAmalgamation [LocallySmall.{w} C] (F : Cᵒᵖ ⥤ Type w)
    {X : C} {S : Sieve X} (f : S.shrinkFunctor.toFunctor ⟶ F) (g : shrinkYoneda.{w}.obj X ⟶ F) :
    S.shrinkFunctor.ι ≫ g = f ↔
      (Sieve.shrinkFunctorHomEquiv f).1.IsAmalgamation (shrinkYonedaEquiv g) := by
  simp only [Presieve.FamilyOfElements.IsAmalgamation]
  dsimp
  refine ⟨?_, ?_⟩
  · rintro rfl Y f hf
    simp [shrinkYonedaEquiv_naturality, shrinkYonedaEquiv_comp, shrinkYonedaEquiv_shrinkYoneda_map]
  · intro h
    ext Y ⟨u, hu⟩
    convert h (shrinkYonedaObjObjEquiv u) hu
    · rw [shrinkYonedaEquiv_naturality, shrinkYonedaEquiv_comp, shrinkYonedaEquiv_shrinkYoneda_map]
      simp
    · rw! [Equiv.symm_apply_apply]
      rfl

lemma Sieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp [LocallySmall.{w} C] {X : C}
    (S : Sieve X) (F : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheafFor F S.arrows ↔
      Function.Bijective (fun g : _ ⟶ F ↦ S.shrinkFunctor.ι ≫ g) := by
  simp only [Presieve.IsSheafFor, Function.bijective_iff_existsUnique,
    Sieve.shrinkFunctor_ι_comp_eq_iff_isAmalgamation,
    Equiv.forall_congr_left Sieve.shrinkFunctorHomEquiv, Subtype.forall]
  exact forall₂_congr fun x hx ↦ by simp [Equiv.existsUnique_congr_right]

set_option backward.isDefEq.respectTransparency false in
def Sieve.equivSubfunctorShrinkYoneda [LocallySmall.{w} C] {X : C} :
    Sieve X ≃ Subfunctor (shrinkYoneda.{w}.obj X) where
  invFun F :=
    ⟨fun Y f ↦ shrinkYonedaObjObjEquiv.symm f ∈ F.obj (.op Y),
      fun {Y Z} f hf g ↦ by
        dsimp
        rw [shrinkYonedaObjObjEquiv_symm_comp]
        exact F.map g.op hf⟩
  toFun S := S.shrinkFunctor
  left_inv S := by simp
  right_inv F := by ext; simp

instance : J.PreservesSheafification (uliftFunctor.{max u₁ v₁, w}) := by
  -- apply J.instPreservesSheafification
  sorry

--lemma GrothendieckTopology.W_whiskerRight_uliftFunctor_iff
--    (F : A ⥤ B) {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) [J.PreservesSheafification F] :
--    J.W (Functor.whiskerRight f F) ↔ J.W f := by
--  refine ⟨fun h ↦ ?_, fun h ↦ J.W_of_preservesSheafification _ _ h⟩
--  sorry

namespace Presheaf

/--
A morphism of presheafs `f : H ⟶ K` is `J`-covering if for any `J`-sheaf `F` the induced
map `(K ⟶ F) → (H ⟶ F)` is injective.
(cf. SGA4 II 5.2 (morphisme couvrant))
-/
def covering : MorphismProperty (Cᵒᵖ ⥤ A) :=
  ObjectProperty.isHomInjective (Presheaf.IsSheaf J)

def IsCoveringFamily {X : Cᵒᵖ ⥤ A} (R : Presieve X) : Prop :=
  ObjectProperty.IsJointlyHomInjective (Presheaf.IsSheaf J) R

def IsBicoveringFamily {X : Cᵒᵖ ⥤ A} (R : Presieve X) : Prop :=
  ObjectProperty.IsJointlyLocal (Presheaf.IsSheaf J) R

variable {J}

lemma covering_of_W {H K : Cᵒᵖ ⥤ A} {f : H ⟶ K} (hf : J.W f) : covering J f :=
  fun F hF ↦ (hf F hF).injective

lemma Functor.W_map_of_adjunction_of_isContinuous (F : C ⥤ D)
    (H : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)) (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    [Functor.IsContinuous.{v} F J K] {G G' : Cᵒᵖ ⥤ A} (f : G ⟶ G') (hf : J.W f) :
    K.W (H.map f) := by
  intro U hU
  rw [adj.bijective_map_comp_iff]
  exact hf _ (F.op_comp_isSheaf_of_isSheaf _ _ _ hU)

lemma Functor.IsContinuous.of_W_map_of_adjunction [LocallySmall.{w} C] {F : C ⥤ D}
    {H : (Cᵒᵖ ⥤ Type w) ⥤ (Dᵒᵖ ⥤ Type w)} (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    (h : ∀ ⦃X : C⦄ ⦃S : Sieve X⦄, S ∈ J X → K.W (H.map <| S.shrinkFunctor.ι)) :
    Functor.IsContinuous.{w} F J K := by
  refine ⟨fun G X S hS ↦ ?_⟩
  rw [Sieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp, ← Functor.whiskeringLeft_obj_obj,
    ← adj.bijective_map_comp_iff]
  exact h hS _ G.cond

lemma asdfasdf (F : C ⥤ D) [Functor.IsContinuous.{max u₁ v₁ u₂ v₂} F J K] :
    Functor.IsContinuous.{max w u₁ v₁ u₂ v₂} F J K := by
  let H : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂ := F.op.lan
  let adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  let H' : (Cᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂ := F.op.lan
  let adj' : H' ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  apply Functor.IsContinuous.of_W_map_of_adjunction _ adj'
  intro X S hS
  have hWS : J.W (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι := by
    -- TODO: extract this into a separate lemma
    intro Z hZ
    rw [isSheaf_iff_isSheaf_of_type] at hZ
    rw [← Sieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
    apply hZ
    exact hS
  have : K.W _ := Functor.W_map_of_adjunction_of_isContinuous (J := J) K F H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS
  let e : H ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ≅
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ⋙ H' :=
    uliftFunctor.{w, max (max (max u₁ u₂) v₁) v₂}.lanCompIsoOfPreserves F.op
  sorry

lemma adfasdfasd (F : C ⥤ D)
    (H : (Cᵒᵖ ⥤ Type w) ⥤ (Dᵒᵖ ⥤ Type w)) (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    [Functor.IsContinuous.{w} F J K]
    {G : Cᵒᵖ ⥤ Type w} (R : Presieve G) (hR : IsBicoveringFamily J R) :
    IsBicoveringFamily K (R.map H) := by
  intro U hU
  have := hR _ (F.op_comp_isSheaf_of_isSheaf _ _ _ hU)
  sorry

--lemma foo {H K : Cᵒᵖ ⥤ Type w} (f : H ⟶ K) :
--    covering J f ↔
--      ∀ (X : C) (u : shrinkYoneda.{w}.obj X ⟶ K),
--        Sieve.equivSubfunctorShrinkYoneda.symm (Subfunctor.range (pullback.snd f u)) ∈ J X := by
--  refine ⟨?_, ?_⟩
--  · sorry
--  · sorry

lemma foo' [HasPullbacks A] {H K : Cᵒᵖ ⥤ A} (f : H ⟶ K) :
    J.W f ↔
      covering J f ∧ covering J (pullback.diagonal f) := by
  refine ⟨fun hf ↦ ⟨covering_of_W hf, ?_⟩, ?_⟩
  · sorry
  · sorry

end Presheaf

namespace Functor

variable {F : C ⥤ D}

lemma functorPushforward_mem [IsContinuous.{max u₂ v₂} F J K] {X : C} (S : Sieve X) (hS : S ∈ J X) :
    S.functorPushforward F ∈ K _ := by
  rw [K.mem_iff_isSheafFor_closedSieves]
  obtain ⟨S, h⟩ := S
  obtain ⟨ι, Y, f, rfl⟩ := S.exists_eq_ofArrows
  dsimp
  sorry

lemma adsfasdf' [IsContinuous.{max u₂ v₂} F J K] :
    PreservesOneHypercovers.{w} F J K := by
  have H {X : C} (R : Presieve X) (hS : Sieve.generate R ∈ J X) :
      Presieve.IsSheafFor (F.op ⋙ closedSieves K) R := by
    rw [Presieve.isSheafFor_iff_generate]
    apply IsContinuous.op_comp_isSheaf_of_types (J := J) (K := K) ⟨closedSieves K, _⟩ _ hS
    rw [isSheaf_iff_isSheaf_of_type]
    exact classifier_isSheaf _
  --let auxSieve (Y : D) : Sieve Y :=
  --  { arrows Z f := ∃ (X : C), Nonempty (Z ⟶ F.obj X)
  --    downward_closed := sorry }
  intro X E
  refine ⟨?_, ?_⟩
  · rw [K.mem_iff_isSheafFor_closedSieves]
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate]
    rw [Presieve.isSheafFor_arrows_iff]
    intro x hx
    have := H E.presieve₀ E.mem₀
    rw [Presieve.isSheafFor_arrows_iff] at this
    refine this x ?_
    intro i j Z gi gj hgij
    apply hx
    simp [← Functor.map_comp, hgij]
  · intro i j W p₁ p₂ h
    --rw [K.mem_iff_isSheafFor_closedSieves]
    --intro x hx
    --let S : Sieve W :=
    --  ⟨fun T g ↦ ∃ (X : C), Nonempty (T ⟶ F.obj X), by
    --    intro Y Z f ⟨X, ⟨p⟩⟩ g
    --    use X, g ≫ p⟩
    --have hS : S ∈ K W := sorry
    let S : Sieve W :=
      ⟨fun T g ↦ ∃ (B : C) (u : B ⟶ E.X i) (u' : B ⟶ E.X j) (b : T ⟶ F.obj B),
          b ≫ F.map u = g ≫ p₁ ∧ b ≫ F.map u' = g ≫ p₂, by
        intro Y Z f ⟨B, u, u', b, hb₁, hb₂⟩ g
        use B, u, u', g ≫ b
        simp [hb₁, hb₂]⟩
    have hS : S ∈ K W :=
      sorry
    refine GrothendieckTopology.transitive _ hS _ ?_
    intro Y f ⟨B, u, u', b, hb₁, hb₂⟩
    --intro Y f ⟨X, ⟨p⟩⟩
    have := E.sieve₁ u u'
    have := E.mem₁ _ _ u u' <| by
      sorry
    have hmem : ((E.sieve₁ u u').functorPushforward F).pullback b ∈ K Y :=
      sorry
    refine K.superset_covering ?_ hmem
    intro Z p ⟨T, w, v, ⟨k, a, ha, ha'⟩, heq⟩
    use k, v ≫ F.map a
    refine ⟨?_, ?_⟩
    · simp [← hb₁, ← Functor.map_comp, ← ha, reassoc_of% heq]
    · simp [← hb₂, ← Functor.map_comp, ← ha', reassoc_of% heq]
  --rw [K.mem_iff_isSheafFor_closedSieves]
  --have : Presieve.IsSheafFor (F.op ⋙ closedSieves K) S.arrows := by
  --  apply IsContinuous.op_comp_isSheaf_of_types (J := J) (K := K) ⟨closedSieves K, _⟩ _ hS
  --  rw [isSheaf_iff_isSheaf_of_type]
  --  exact classifier_isSheaf _

lemma adsfasdf [IsContinuous.{max u₂ v₂} F J K] {X : C} {S : Sieve X} (hS : S ∈ J X) :
    S.functorPushforward F ∈ K (F.obj X) := by
  rw [K.mem_iff_isSheafFor_closedSieves]
  have : Presieve.IsSheafFor (F.op ⋙ closedSieves K) S.arrows := by
    apply IsContinuous.op_comp_isSheaf_of_types (J := J) (K := K) ⟨closedSieves K, _⟩ _ hS
    rw [isSheaf_iff_isSheaf_of_type]
    exact classifier_isSheaf _
  sorry

end Functor

end CategoryTheory
