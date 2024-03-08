/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Galois.Decomposition
import Mathlib.CategoryTheory.Limits.FunctorCategory

/-!
# Pro-Representability of fiber functors

We show that any fiber functor is pro-representable, i.e. there exists a pro-object
`X : I ⥤ C` such that `F` is naturally isomorphic to `X ⋙ coyoneda`.

## Main results


## References

* H. W. Lenstra. Galois theory for schemes
  <https://websites.math.leidenuniv.nl/algebra/GSchemes.pdf>

-/

universe u₁ u₂ w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable (C : Type u₁) [Category.{u₂} C] [GaloisCategory C]

def GaloisObjects := { A : C | IsGalois A }

variable (F : C ⥤ FintypeCat.{u₂}) [FiberFunctor F]

variable {C}

def Idx : Type (max u₁ u₂) := (A : GaloisObjects C) × F.obj (A : C)

instance : Category.{u₂} (Idx F) where
  Hom := by
    intro ⟨A, a⟩ ⟨B, b⟩
    exact { f : (B : C) ⟶ A // F.map f b = a }
  id := by
    intro ⟨A, a⟩
    exact ⟨𝟙 (A : C), by simp⟩
  comp := by
    intro ⟨A, a⟩ ⟨B, b⟩ ⟨C, c⟩ ⟨f, hf⟩ ⟨g, hg⟩
    have h : F.map (g ≫ f) c = a := by
      simp only [F.map_comp, FintypeCat.comp_apply, hf, hg]
    exact ⟨g ≫ f, h⟩

instance : IsFilteredOrEmpty (Idx F) where
  cocone_objs := fun ⟨A, a⟩ ⟨B, b⟩ ↦ by
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_map_from_galois_of_fiber F (A ⨯ B)
      <| (fiberBinaryProductEquiv F A B).symm (a, b)
    refine ⟨⟨⟨Z, hgal⟩, z⟩, ⟨f ≫ prod.fst, ?_⟩, ⟨f ≫ prod.snd, ?_⟩, trivial⟩
    simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_fst_apply]
    simp only [F.map_comp, hfz, FintypeCat.comp_apply, fiberBinaryProductEquiv_symm_snd_apply]
  cocone_maps := fun ⟨A, a⟩ ⟨B, b⟩ ⟨f, hf⟩ ⟨g, hg⟩ ↦ by
    obtain ⟨Z, h, z, hgal, hhz⟩ := exists_map_from_galois_of_fiber F B b
    refine ⟨⟨⟨Z, hgal⟩, z⟩, ⟨h, hhz⟩, ?_⟩
    apply Subtype.ext
    apply evaluationInjective_of_isConnected F Z A z
    show F.map (h ≫ f) z = F.map (h ≫ g) z
    simp only [map_comp, FintypeCat.comp_apply, hhz, hf, hg]

def can : Idx F ⥤ Cᵒᵖ where
  obj := fun ⟨A, _⟩ ↦ ⟨A⟩
  map := fun ⟨f, _⟩ ↦ ⟨f⟩

@[simp]
lemma can_map_eq {A B : Idx F} (f : A ⟶ B) : ((can F).map f).unop = f.val :=
  rfl

def cocone : Cocone (can F ⋙ coyoneda) where
  pt := F ⋙ FintypeCat.incl
  ι := {
    app := by
      intro ⟨A, a⟩
      exact {
        app := by
          intro X (f : (A : C) ⟶ X)
          -- evaluation at a
          exact F.map f a
      }
    naturality := by
      intro ⟨A, a⟩ ⟨B, b⟩ ⟨f, hf⟩
      ext Y (g : (A : C) ⟶ Y)
      simp [hf]
  }

#check Types.FilteredColimit.isColimitOf

noncomputable def iscolimit : IsColimit (cocone F) := by
  apply evaluationJointlyReflectsColimits
  intro X
  let s : Cocone ((can F ⋙ coyoneda) ⋙ (evaluation C (Type u₂)).obj X) :=
    ((evaluation C (Type u₂)).toPrefunctor.obj X).mapCocone (cocone F)
  show IsColimit s
  apply Types.FilteredColimit.isColimitOf.{max u₁ u₂, max u₁ u₂, u₂}
    ((can F ⋙ coyoneda) ⋙ (evaluation C (Type u₂)).obj X)
    (((evaluation C (Type u₂)).obj X).mapCocone (cocone F))
  intro (x : F.obj X)
  obtain ⟨Y, i, y, h1, _, _⟩ := fiber_in_connected_component F X x
  obtain ⟨Z, f, z, hgal, hfz⟩ := exists_map_from_galois_of_fiber F Y y
  use ⟨⟨Z, hgal⟩, z⟩
  use f ≫ i
  show x = F.map (f ≫ i) z
  simp only [←h1, map_comp, FintypeCat.comp_apply, hfz]
  intro ⟨A, a⟩ ⟨B, b⟩ (u : (A : C) ⟶ X) (v : (B : C) ⟶ X) (h : F.map u a = F.map v b)
  obtain ⟨⟨⟨Z, (hgal : IsGalois Z)⟩, z⟩, ⟨f, hf⟩, ⟨g, hg⟩, _⟩ :=
    @IsFilteredOrEmpty.cocone_objs (Idx F) _ _ (⟨A, a⟩ : Idx F) (⟨B, b⟩ : Idx F)
  use ⟨⟨Z, hgal⟩, z⟩
  use ⟨f, hf⟩
  use ⟨g, hg⟩
  have : IsConnected Z := sorry
  apply evaluationInjective_of_isConnected F Z X z
  show F.map (f ≫ u) z = F.map (g ≫ v) z
  rw [map_comp, FintypeCat.comp_apply, hf, map_comp, FintypeCat.comp_apply, hg, h]

--instance (X : C) : SMul (Aut F) (F.obj X) := ⟨fun σ a => (σ.app X).hom a⟩

private noncomputable def autMap' {A B : C} [IsGalois B] (f : A ⟶ B) (a : F.obj A)
    (b : F.obj B) (σ : Aut A) : { τ : Aut B | F.map τ.hom b = F.map (σ.hom ≫ f) a } := by
  choose τ h using MulAction.surjective_smul (Aut B) b (F.map (σ.hom ≫ f) a)
  exact ⟨τ, h⟩

private noncomputable def autMap {A B : C} [IsGalois B] (f : A ⟶ B) (a : F.obj A)
    (b : F.obj B) (σ : Aut A) : Aut B := autMap' F f a b σ

@[simp]
lemma autMap_eval {A B : C} [IsGalois B] (f : A ⟶ B) (a : F.obj A) (b : F.obj B)
    (σ : Aut A) : F.map (autMap F f a b σ : Aut B).hom b = F.map (σ.hom ≫ f) a := by
  show F.map (autMap' F f a b σ : Aut B).hom b = F.map (σ.hom ≫ f) a
  let ⟨_, h⟩ := autMap' F f a b σ
  exact h

lemma autMap_surjective {A B : C} [IsGalois A] [IsGalois B] (f : A ⟶ B)
    (a : F.obj A) (b : F.obj B) : Function.Surjective (autMap F f a b) := by
  intro σ
  --have h : Nonempty (F.obj A) := nonempty_fibre_of_connected A
  obtain ⟨a', ha'⟩ := surjective_of_nonempty_fiber_of_isConnected F f (F.map σ.hom b)
  obtain ⟨τ, (hτ : F.map τ.hom a = a')⟩ := MulAction.exists_smul_eq (Aut A) a a'
  use τ
  apply evaluation_aut_injective_of_isConnected F B b
  simp only [autMap_eval, map_comp, FintypeCat.comp_apply]
  rw [hτ, ha']

lemma autMap_comp {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (a : F.obj A) (b : F.obj B)
    (h : F.map f a = b)
    (σ : Aut A) : σ.hom ≫ f = f ≫ (autMap F f a b σ).hom := by
  apply evaluationInjective_of_isConnected F A B a
  show F.map (σ.hom ≫ f) a = F.map (f ≫ (autMap F f a b σ).hom) a
  simp only [map_comp, FintypeCat.comp_apply, h, autMap_eval]

lemma autMap_mul {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (a : F.obj A) (b : F.obj B)
    (h : F.map f a = b)
    (σ τ : Aut A) : autMap F f a b (σ * τ) = autMap F f a b σ * autMap F f a b τ := by
  apply evaluation_aut_injective_of_isConnected F (B : C) b
  show F.map (autMap F f a b (σ * τ)).hom b =
    F.map (autMap F f a b σ * autMap F f a b τ).hom b
  simp only [autMap_eval]
  convert_to F.map ((τ.hom ≫ σ.hom) ≫ f) a
    = F.map ((f ≫ (autMap F f a b τ).hom) ≫ (autMap F f a b σ).hom) a
  erw [←h, Functor.map_comp]
  simp only [FintypeCat.comp_apply, autMap_eval, map_comp, Category.assoc]
  erw [←autMap_comp F f a b h τ, Category.assoc, Category.assoc,
    ←autMap_comp F f a b h σ]

noncomputable def autMapMul : {A B : (Idx F)ᵒᵖ} → (A ⟶ B) → Aut (A.1.1 : C) →* Aut (B.1.1 : C) := by
  intro ⟨⟨A, (h1 : IsGalois A)⟩, a⟩ ⟨⟨B, (h2 : IsGalois B)⟩, b⟩ ⟨f, hf⟩
  apply MonoidHom.mk'
  exact autMap_mul F f a b hf

noncomputable def autGaloisSystem : (Idx F)ᵒᵖ ⥤ Type w where
  obj := fun ⟨A, _⟩ => Aut (A : C)
  map := by
    intro ⟨A, _⟩ ⟨B, _⟩ f
    exact (autMapMul F f : Aut (A : C) → Aut (B : C))
  map_id := by
    intro ⟨⟨A, (hAgal : IsGalois A)⟩, a⟩
    ext (σ : Aut A)
    have : autMap F (𝟙 A) a a σ = σ := by
      apply evaluation_aut_injective_of_isConnected F (A : C) a
      simp only [autMap_eval F (𝟙 A) a a σ, Category.comp_id]
    exact congrArg Iso.hom this
  map_comp := by
    intro ⟨⟨A, (hAgal : IsGalois A)⟩, a⟩ ⟨⟨B, (hBgal : IsGalois B)⟩, b⟩
      ⟨⟨C, (hCgal : IsGalois C)⟩, c⟩ ⟨f, hf⟩ ⟨g, hg⟩
    ext (σ : Aut A)
    apply congrArg Iso.hom
    show autMap F (f ≫ g) a c σ = autMap F g b c (autMap F f a b σ)
    apply evaluation_aut_injective_of_isConnected F C c
    simp only [autMap_eval, map_comp, FintypeCat.comp_apply]

noncomputable def autGalois : Type w := limit (autGaloisSystem F)

noncomputable def autGaloisSystemInv : autGaloisSystem F ⟶ autGaloisSystem F where
  app := by
    intro ⟨⟨A, _⟩, _⟩
    show Aut A ⟶ Aut A
    intro σ
    exact σ⁻¹
  naturality := by
    intro ⟨A, _⟩ ⟨B, _⟩ f
    simp
    ext (σ : Aut (A : C))
    show (autMapMul F f σ)⁻¹ = autMapMul F f σ⁻¹
    simp only [_root_.map_inv]

noncomputable def autGaloisInv : autGalois F → autGalois F := lim.map (autGaloisSystemInv F)

private noncomputable def mapAutGaloisCocone (a : autGalois F) : Cocone (can F ⋙ coyoneda) := {
    pt := F ⋙ FintypeCat.incl
    ι := {
      app := by
        intro ⟨⟨A, hGal⟩, (x : F.obj A)⟩
        constructor
        swap
        intro X
        show (A ⟶ X) → F.obj X
        intro f
        let σ : Aut A := limit.π (autGaloisSystem F) ⟨⟨A, hGal⟩, x⟩ a
        exact F.map (σ.hom ≫ f) x
        intro X Y f
        ext (g : A ⟶ X)
        simp
      naturality := by
        intro ⟨⟨A, (hagal : IsGalois A)⟩, (x : F.obj A)⟩ ⟨⟨B, (hbgal : IsGalois B)⟩, (y : F.obj B)⟩ ⟨f, hf⟩
        ext X (g : A ⟶ X)
        simp
        rw [←hf]
        simp
        apply congrArg
        show (F.map (limit.π (autGaloisSystem F) ⟨⟨B, _⟩, y⟩ a).hom ≫ F.map f) y =
          (F.map f ≫ F.map (limit.π (autGaloisSystem F) ⟨⟨A, _⟩, F.map f y⟩ a).hom) y
        rw [←F.map_comp, ←F.map_comp]
        let A' : (Idx F)ᵒᵖ := ⟨⟨A, hagal⟩, F.map f y⟩
        let B' : (Idx F)ᵒᵖ := ⟨⟨B, hbgal⟩, y⟩
        let f' : B' ⟶ A' := ⟨f, rfl⟩
        have : (limit.π (autGaloisSystem F) ⟨⟨B, _⟩, y⟩ a).hom ≫ f = 
            f ≫ (limit.π (autGaloisSystem F) ⟨⟨A, _⟩, F.map f y⟩ a).hom := by
          rw [←limit.w (autGaloisSystem F) f']
          show (limit.π (autGaloisSystem F) B' a).hom ≫ f =
            f ≫ ((limit.π (autGaloisSystem F) B' ≫ autMap F f y (F.map f y)) a).hom
          rw [autMap_comp F f y (F.map f y) rfl]
          rfl
        rw [this]
    }
  }

noncomputable def mapAutGaloisEnd (a : autGalois F) : End F := by
  let u' : F ⋙ FintypeCat.incl ⟶ F ⋙ FintypeCat.incl := (iscolimit F).desc (mapAutGaloisCocone F a)
  exact {
    app := fun X x => u'.app X x
    naturality := by
      intro X Y f
      ext x
      erw [u'.naturality]
      rfl
  }

lemma mapAutGaloisEnd_autGaloisInv (σ : autGalois F) :
    mapAutGaloisEnd F σ ≫ mapAutGaloisEnd F (autGaloisInv F σ) = 𝟙 F := by
  let u : F ⟶ F := mapAutGaloisEnd F σ
  let u' : F ⟶ F := mapAutGaloisEnd F (autGaloisInv F σ)
  show u ≫ u' = 𝟙 F
  ext X x
  obtain ⟨A, f, a, hgal, hf⟩ := exists_map_from_galois_of_fiber F X x
  rw [←hf]
  have : F.map f a = (((cocone F).ι.app ⟨⟨A, hgal⟩, a⟩).app X : (A ⟶ X) → F.obj X) f := rfl
  show (mapAutGaloisEnd F (autGaloisInv F σ)).app X
    ((mapAutGaloisEnd F σ).app X (F.map f a))
    = F.map f a
  rw [this]
  simp
  let v : F ⋙ FintypeCat.incl ⟶ F ⋙ FintypeCat.incl := (iscolimit F).desc
    (mapAutGaloisCocone F σ)
  let v' : F ⋙ FintypeCat.incl ⟶ F ⋙ FintypeCat.incl := (iscolimit F).desc
    (mapAutGaloisCocone F (autGaloisInv F σ))
  let τ : Aut A := limit.π (autGaloisSystem F) ⟨⟨A, hgal⟩, a⟩ σ
  let τ' : Aut A := limit.π (autGaloisSystem F) ⟨⟨A, hgal⟩, a⟩ (autGaloisInv F σ)
  have ht : τ' = τ⁻¹ := by
    show ((lim.map (autGaloisSystemInv F)) ≫ limit.π (autGaloisSystem F) ⟨⟨A, _⟩, a⟩) σ = τ⁻¹
    erw [limMap_π]
    rfl
  have : (((cocone F).ι.app ⟨⟨A, hgal⟩, a⟩).app X ≫ v.app X) = (((cocone F).ι.app ⟨⟨A, _⟩, a⟩) ≫ v).app X := by
    rfl
  have : v.app X (((cocone F).ι.app ⟨⟨A, hgal⟩, a⟩).app X f)
    = ((cocone F).ι.app ⟨⟨A, _⟩, a⟩ ≫ (iscolimit F).desc (mapAutGaloisCocone F σ)).app X f := rfl
  show v'.app X (v.app X (((cocone F).ι.app ⟨⟨A, _⟩, a⟩).app X f)) = ((cocone F).ι.app ⟨⟨A, _⟩, a⟩).app X f
  rw [this, (iscolimit F).fac]
  simp
  show (((cocone F).ι.app ⟨⟨A, hgal⟩, a⟩ ≫ v').app X (τ.hom ≫ f)) = F.map f a
  rw [(iscolimit F).fac]
  show F.map (τ'.hom ≫ τ.hom ≫ f) a = F.map f a
  rw [ht, ←Category.assoc]
  show F.map ((τ * τ⁻¹).hom ≫ f) a = F.map f a
  rw [mul_right_inv]
  simp
  show F.map f (F.map (𝟙 A) a) = F.map f a
  simp

private lemma autGaloisInv_autGaloisInv_eq_id (σ : autGalois F) :
    autGaloisInv F (autGaloisInv F σ) = σ := by
  show (lim.map (autGaloisSystemInv F) ≫ lim.map (autGaloisSystemInv F)) σ = σ
  rw [←lim.map_comp]
  have : autGaloisSystemInv F ≫ autGaloisSystemInv F = 𝟙 (autGaloisSystem F) := rfl
  rw [this]
  simp only [lim_obj, FunctorToTypes.map_id_apply]

noncomputable def mapAutGaloisAut (σ : autGalois F) : Aut F := by
  apply CategoryTheory.Iso.mk
  exact mapAutGaloisEnd_autGaloisInv F σ
  conv => lhs; congr; rfl; rw [←autGaloisInv_autGaloisInv_eq_id F σ]
  exact mapAutGaloisEnd_autGaloisInv F (autGaloisInv F σ)

private lemma proj_surj (A : C) [inst : IsGalois A] (a : F.obj A) :
    Function.Surjective (limit.π (autGaloisSystem F) ⟨⟨A, inst⟩, a⟩) := by
  intro (σ : Aut A)
  have (i : (Idx F)ᵒᵖ) : Nonempty ((autGaloisSystem F).obj i) := by
    show Nonempty (Aut (i.1.1.1))
    constructor
    exact 1
  have (i : (Idx F)ᵒᵖ) : Finite ((autGaloisSystem F).obj i) := by
    show Finite (Aut (i.1.1.1))
    have : IsGalois i.1.1.1 := i.1.1.2
    infer_instance
  have fsur (i j : (Idx F)ᵒᵖ) (f : i ⟶ j) : Function.Surjective ((autGaloisSystem F).map f) := by
    have : IsGalois i.1.1.1 := i.1.1.2
    have : IsGalois j.1.1.1 := j.1.1.2
    exact autMap_surjective F f.1.1 i.1.2 j.1.2
  obtain ⟨s', hs⟩ := eval_section_surjective_of_surjective (autGaloisSystem F) fsur
    ⟨⟨A, inst⟩, a⟩ σ
  let s : autGalois F := (Types.limitEquivSections (autGaloisSystem F)).symm s'
  use s
  simp only [Types.limitEquivSections_symm_apply]
  exact hs

private def transitive_of_galois (X : C) [inst : IsGalois X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  constructor
  intro x y
  have : ∃ φ : Aut X, F.map φ.hom x = y := MulAction.IsPretransitive.exists_smul_eq x y
  obtain ⟨(φ : Aut X), h⟩ := this
  obtain ⟨a, ha⟩ := proj_surj F X x φ
  let σ : Aut F := mapAutGaloisAut F a
  use σ
  let f : X ⟶ X := 𝟙 X
  have hx : x = (((cocone F).ι.app ⟨⟨X, inst⟩, x⟩).app X f) := by
    show x = F.map (𝟙 X) x
    simp only [CategoryTheory.Functor.map_id, FintypeCat.id_apply]
  show ((iscolimit F).desc (mapAutGaloisCocone F a)).app X x = y
  rw [hx]
  show (((cocone F).ι.app { fst := { val := X, property := inst }, snd := x } ≫ 
      IsColimit.desc (iscolimit F) (mapAutGaloisCocone F a)).app X f) = y
  rw [(iscolimit F).fac]
  show F.map ((limit.π (autGaloisSystem F) ⟨⟨X, inst⟩, x⟩ a).hom ≫ f) x = y
  rw [ha]
  simpa

instance pretransitiveOfConnected (X : C) [IsConnected X] :
    MulAction.IsPretransitive (Aut F) (F.obj X) := by
  obtain ⟨A, f, hgal⟩ := exists_map_from_galois_of_connected F X
  have hs : Function.Surjective (F.map f) := surjective_of_nonempty_fiber_of_isConnected F f
  constructor
  intro x y
  obtain ⟨a, ha⟩ := hs x
  obtain ⟨b, hb⟩ := hs y
  have : MulAction.IsPretransitive (Aut F) (F.obj A) := transitive_of_galois F A
  obtain ⟨σ, (hσ : σ.hom.app A a = b)⟩ := MulAction.exists_smul_eq (Aut F) a b
  use σ
  rw [←ha, ←hb]
  show (F.map f ≫ σ.hom.app X) a = F.map f b
  rw [σ.hom.naturality, FintypeCat.comp_apply, hσ]
