/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Data.Set.Lattice.Image

/-!

# Subpresheaf of types

We define the subpresheaf of a type valued presheaf.

## Main results

- `CategoryTheory.Subpresheaf` :
  A subpresheaf of a presheaf of types.

-/


universe w v u

open Opposite CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A subpresheaf of a presheaf consists of a subset of `F.obj U` for every `U`,
compatible with the restriction maps `F.map i`. -/
@[ext]
structure Subpresheaf (F : Cᵒᵖ ⥤ Type w) where
  /-- If `G` is a sub-presheaf of `F`, then the sections of `G` on `U` forms a subset of sections of
    `F` on `U`. -/
  obj : ∀ U, Set (F.obj U)
  /-- If `G` is a sub-presheaf of `F` and `i : U ⟶ V`, then for each `G`-sections on `U` `x`,
    `F i x` is in `F(V)`. -/
  map : ∀ {U V : Cᵒᵖ} (i : U ⟶ V), obj U ⊆ F.map i ⁻¹' obj V

@[deprecated (since := "2025-01-08")] alias GrothendieckTopology.Subpresheaf := Subpresheaf

variable {F F' F'' : Cᵒᵖ ⥤ Type w} (G G' : Subpresheaf F)

instance : PartialOrder (Subpresheaf F) :=
  PartialOrder.lift Subpresheaf.obj (fun _ _ => Subpresheaf.ext)

instance : CompleteLattice (Subpresheaf F) where
  sup F G :=
    { obj U := F.obj U ⊔ G.obj U
      map _ _ := by
        rintro (h|h)
        · exact Or.inl (F.map _ h)
        · exact Or.inr (G.map _ h) }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by
    rintro x (h|h)
    · exact h₁ _ h
    · exact h₂ _ h
  inf S T :=
    { obj U := S.obj U ⊓ T.obj U
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩}
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj U := sSup (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        obtain ⟨_, ⟨F, h, rfl⟩, h'⟩ := hx
        simp only [Set.sSup_eq_sUnion, Set.sUnion_image, Set.preimage_iUnion,
          Set.mem_iUnion, Set.mem_preimage, exists_prop]
        exact ⟨_, h, F.map f h'⟩ }
  le_sSup _ _ _ _ _ := by aesop
  sSup_le _ _ _ _ _ := by aesop
  sInf S :=
    { obj U := sInf (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        rintro _ ⟨F, h, rfl⟩
        exact F.map f (hx _ ⟨_, h, rfl⟩) }
  sInf_le _ _ _ _ _ := by aesop
  le_sInf _ _ _ _ _ := by aesop
  bot :=
    { obj U := ⊥
      map := by simp }
  bot_le _ _ := bot_le
  top :=
    { obj U := ⊤
      map := by simp }
  le_top _ _ := le_top

namespace Subpresheaf

lemma le_def (S T : Subpresheaf F) : S ≤ T ↔ ∀ U, S.obj U ≤ T.obj U := Iff.rfl

variable (F)

@[simp] lemma top_obj (i : Cᵒᵖ) : (⊤ : Subpresheaf F).obj i = ⊤ := rfl
@[simp] lemma bot_obj (i : Cᵒᵖ) : (⊥ : Subpresheaf F).obj i = ⊥ := rfl

variable {F}

lemma sSup_obj (S : Set (Subpresheaf F)) (U : Cᵒᵖ) :
    (sSup S).obj U = sSup (Set.image (fun T ↦ T.obj U) S) := rfl

lemma sInf_obj (S : Set (Subpresheaf F)) (U : Cᵒᵖ) :
    (sInf S).obj U = sInf (Set.image (fun T ↦ T.obj U) S) := rfl

@[simp]
lemma iSup_obj {ι : Type*} (S : ι → Subpresheaf F) (U : Cᵒᵖ) :
    (⨆ i, S i).obj U = ⋃ i, (S i).obj U := by
  simp [iSup, sSup_obj]

@[simp]
lemma iInf_obj {ι : Type*} (S : ι → Subpresheaf F) (U : Cᵒᵖ) :
    (⨅ i, S i).obj U = ⋂ i, (S i).obj U := by
  simp [iInf, sInf_obj]

@[simp]
lemma max_obj (S T : Subpresheaf F) (i : Cᵒᵖ) :
    (S ⊔ T).obj i = S.obj i ∪ T.obj i := rfl

@[simp]
lemma min_obj (S T : Subpresheaf F) (i : Cᵒᵖ) :
    (S ⊓ T).obj i = S.obj i ∩ T.obj i := rfl

lemma max_min (S₁ S₂ T : Subpresheaf F) :
    (S₁ ⊔ S₂) ⊓ T = (S₁ ⊓ T) ⊔ (S₂ ⊓ T) := by
  aesop

lemma iSup_min {ι : Type*} (S : ι → Subpresheaf F) (T : Subpresheaf F) :
    (⨆ i, S i) ⊓ T = ⨆ i, S i ⊓ T := by
  aesop

instance : Nonempty (Subpresheaf F) :=
  inferInstance

/-- The subpresheaf as a presheaf. -/
@[simps!]
def toPresheaf : Cᵒᵖ ⥤ Type w where
  obj U := G.obj U
  map := @fun _ _ i x => ⟨F.map i x, G.map i x.prop⟩
  map_id X := by
    ext ⟨x, _⟩
    dsimp
    simp only [FunctorToTypes.map_id_apply]
  map_comp := @fun X Y Z i j => by
    ext ⟨x, _⟩
    dsimp
    simp only [FunctorToTypes.map_comp_apply]

instance {U} : CoeHead (G.toPresheaf.obj U) (F.obj U) where
  coe := Subtype.val

/-- The inclusion of a subpresheaf to the original presheaf. -/
@[simps]
def ι : G.toPresheaf ⟶ F where app _ x := x

instance : Mono G.ι :=
  ⟨@fun _ _ _ e =>
    NatTrans.ext <|
      funext fun U => funext fun x => Subtype.ext <| congr_fun (congr_app e U) x⟩

/-- The inclusion of a subpresheaf to a larger subpresheaf -/
@[simps]
def homOfLe {G G' : Subpresheaf F} (h : G ≤ G') : G.toPresheaf ⟶ G'.toPresheaf where
  app U x := ⟨x, h U x.prop⟩

instance {G G' : Subpresheaf F} (h : G ≤ G') : Mono (Subpresheaf.homOfLe h) :=
  ⟨fun _ _ e =>
    NatTrans.ext <|
      funext fun U =>
        funext fun x =>
          Subtype.ext <| (congr_arg Subtype.val <| (congr_fun (congr_app e U) x :) :)⟩

@[reassoc (attr := simp)]
theorem homOfLe_ι {G G' : Subpresheaf F} (h : G ≤ G') :
    Subpresheaf.homOfLe h ≫ G'.ι = G.ι := by
  ext
  rfl

instance : IsIso (Subpresheaf.ι (⊤ : Subpresheaf F)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro X
  rw [isIso_iff_bijective]
  exact ⟨Subtype.coe_injective, fun x => ⟨⟨x, _root_.trivial⟩, rfl⟩⟩

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
theorem eq_top_iff_isIso : G = ⊤ ↔ IsIso G.ι := by
  constructor
  · rintro rfl
    infer_instance
  · intro H
    ext U x
    apply (iff_of_eq (iff_true _)).mpr
    rw [← IsIso.inv_hom_id_apply (G.ι.app U) x]
    exact ((inv (G.ι.app U)) x).2

theorem nat_trans_naturality (f : F' ⟶ G.toPresheaf) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : F'.obj U) : (f.app V (F'.map i x)).1 = F.map i (f.app U x).1 :=
  congr_arg Subtype.val (FunctorToTypes.naturality _ _ f i x)

end Subpresheaf

@[deprecated (since := "2025-01-23")] alias top_subpresheaf_obj := Subpresheaf.top_obj

end CategoryTheory
