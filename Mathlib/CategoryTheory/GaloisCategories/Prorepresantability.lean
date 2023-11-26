import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.GaloisCategories.Basic
import Mathlib.CategoryTheory.GaloisCategories.Playground
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.CategoryTheory.Limits.ConcreteCategory

universe u v w

open CategoryTheory Limits Functor

namespace Galois

variable {C : Type u} [Category.{u, u} C]

variable (F : C ⥤ FintypeCat.{u}) [PreGaloisCategory C] [FibreFunctor F]

instance (X : C) : SMul (Aut X) (F.obj X) := ⟨fun σ a => F.map σ.hom a⟩

def Idx : Type (max u u) := (A : GaloisObjects F) × F.obj (A : C)

instance : SmallCategory (Idx F) where
  Hom := by
    intro ⟨A, a⟩ ⟨B, b⟩
    exact { f : (B : C) ⟶ A // F.map f b = a }
  id := by
    intro ⟨A, a⟩
    exact ⟨𝟙 (A : C), by simp⟩
  comp := by
    intro ⟨A, a⟩ ⟨B, b⟩ ⟨C, c⟩ ⟨f, hf⟩ ⟨g, hg⟩
    have h : F.map (g ≫ f) c = a := by
      simp only [map_comp, FintypeCat.comp_apply, hf, hg]
    exact ⟨g ≫ f, h⟩

instance : IsFilteredOrEmpty (Idx F) where
  cocone_objs := by
    intro ⟨A, a⟩ ⟨B, b⟩
    let φ : F.obj (A ⨯ B) ≅ F.obj A ⨯ F.obj B := PreservesLimitPair.iso F A B
    let ψ : F.obj A ⨯ F.obj B ≅ FintypeCat.of (F.obj A × F.obj B) := FintypeCat.binaryProductIso _ _
    obtain ⟨Y, i, y, h1, _, _⟩ := fibre_in_connected_component F (A ⨯ B) (φ.inv (ψ.inv (a, b)))
    have hp1 : φ.hom ≫ prod.fst = F.map prod.fst := prodComparison_fst F
    have hp2 : prod.fst = φ.inv ≫ F.map prod.fst := (Iso.eq_inv_comp φ).mpr hp1
    have hq1 : φ.hom ≫ prod.snd = F.map prod.snd := prodComparison_snd F
    have hq2 : prod.snd = φ.inv ≫ F.map prod.snd := (Iso.eq_inv_comp φ).mpr hq1
    obtain ⟨Z, f, z, hgal, hfz⟩ := exists_map_from_galois_of_fibre F Y y
    let hf : F.map (f ≫ i ≫ prod.fst) z = a := by
      simp [hfz, h1]
      show (φ.inv ≫ F.map prod.fst) (ψ.inv (a, b)) = a
      rw [←hp2]
      simp [←FintypeCat.binaryProductIso_hom_comp_fst]
    use ⟨⟨Z, hgal⟩, z⟩
    use ⟨f ≫ i ≫ prod.fst, hf⟩
    let hg : F.map (f ≫ i ≫ prod.snd) z = b := by
      simp [hfz, h1]
      show (φ.inv ≫ F.map prod.snd) (ψ.inv (a, b)) = b
      rw [←hq2]
      simp [←FintypeCat.binaryProductIso_hom_comp_snd]
    use ⟨f ≫ i ≫ prod.snd, hg⟩
  cocone_maps := by
    intro ⟨A, a⟩ ⟨B, b⟩ ⟨f, hf⟩ ⟨g, hg⟩
    obtain ⟨Y, i, y, h1, _, _⟩ := fibre_in_connected_component F B b
    obtain ⟨Z, h, z, hgal, hhz⟩ := exists_map_from_galois_of_fibre F Y y
    use ⟨⟨Z, hgal⟩, z⟩
    have hh : F.map (h ≫ i) z = b := by simp [hhz, h1]
    use ⟨h ≫ i, hh⟩
    apply Subtype.ext
    have : ConnectedObject Z := hgal.connected
    apply evaluationInjectiveOfConnected Z A z
    show F.map ((h ≫ i) ≫ f) z = F.map ((h ≫ i) ≫ g) z
    simp only [map_comp, FintypeCat.comp_apply, hhz, h1, hf, hg]

def can : Idx F ⥤ Cᵒᵖ where
  obj := by
    intro ⟨A, _⟩
    exact ⟨A⟩
  map := by
    intro ⟨A, _⟩ ⟨B, _⟩ ⟨f, _⟩
    exact ⟨f⟩

--instance : SmallCategory (Idx F) := sorry

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

noncomputable def iscolimit : IsColimit (cocone F) := by
  apply evaluationJointlyReflectsColimits
  intro X
  apply Types.FilteredColimit.isColimitOf.{u, u} _ _
  intro (x : F.obj X)
  obtain ⟨Y, i, y, h1, _, _⟩ := fibre_in_connected_component F X x
  obtain ⟨Z, f, z, hgal, hfz⟩ := exists_map_from_galois_of_fibre F Y y
  use ⟨⟨Z, hgal⟩, z⟩
  use f ≫ i
  show x = F.map (f ≫ i) z
  simp only [←h1, map_comp, FintypeCat.comp_apply, hfz]
  intro ⟨A, a⟩ ⟨B, b⟩ (u : (A : C) ⟶ X) (v : (B : C) ⟶ X) (h : F.map u a = F.map v b)
  obtain ⟨⟨⟨Z, hgal⟩, z⟩, ⟨f, hf⟩, ⟨g, hg⟩, _⟩ :=
    @IsFilteredOrEmpty.cocone_objs (Idx F) _ _ (⟨A, a⟩ : Idx F) (⟨B, b⟩ : Idx F)
  use ⟨⟨Z, hgal⟩, z⟩
  use ⟨f, hf⟩
  use ⟨g, hg⟩
  have : ConnectedObject Z := hgal.connected
  apply evaluationInjectiveOfConnected Z X z
  show F.map (f ≫ u) z = F.map (g ≫ v) z
  rw [map_comp, FintypeCat.comp_apply, hf, map_comp, FintypeCat.comp_apply, hg, h]

instance (X : C) : SMul (Aut F) (F.obj X) := ⟨fun σ a => (σ.app X).hom a⟩

instance (X : C) [ConnectedObject X] : MulAction.IsPretransitive (Aut F) (F.obj X) := by
  constructor
  intro x y
  admit
