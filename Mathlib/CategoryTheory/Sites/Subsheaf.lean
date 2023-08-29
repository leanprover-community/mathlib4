/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Tactic.CategoryTheory.Elementwise

#align_import category_theory.sites.subsheaf from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

# Subsheaf of types

We define the sub(pre)sheaf of a type valued presheaf.

## Main results

- `CategoryTheory.GrothendieckTopology.Subpresheaf` :
  A subpresheaf of a presheaf of types.
- `CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify` :
  The sheafification of a subpresheaf as a subpresheaf. Note that this is a sheaf only when the
  whole sheaf is.
- `CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify_isSheaf` :
  The sheafification is a sheaf
- `CategoryTheory.GrothendieckTopology.Subpresheaf.sheafifyLift` :
  The descent of a map into a sheaf to the sheafification.
- `CategoryTheory.GrothendieckTopology.imageSheaf` : The image sheaf of a morphism.
- `CategoryTheory.GrothendieckTopology.imageFactorization` : The image sheaf as a
  `limits.image_factorization`.
-/


universe w v u

open Opposite CategoryTheory

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

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
#align category_theory.grothendieck_topology.subpresheaf CategoryTheory.GrothendieckTopology.Subpresheaf

variable {F F' F'' : Cᵒᵖ ⥤ Type w} (G G' : Subpresheaf F)

instance : PartialOrder (Subpresheaf F) :=
  PartialOrder.lift Subpresheaf.obj Subpresheaf.ext

instance : Top (Subpresheaf F) :=
  ⟨⟨fun U => ⊤, @fun U V _ x _ => by aesop_cat⟩⟩
                                     -- 🎉 no goals

instance : Nonempty (Subpresheaf F) :=
  inferInstance

/-- The subpresheaf as a presheaf. -/
@[simps!]
def Subpresheaf.toPresheaf : Cᵒᵖ ⥤ Type w where
  obj U := G.obj U
  map := @fun U V i x => ⟨F.map i x, G.map i x.prop⟩
  map_id X := by
    ext ⟨x, _⟩
    -- ⊢ { obj := fun U => ↑(obj G U), map := fun U V i x => { val := F.map i ↑x, pro …
    dsimp
    -- ⊢ { val := F.map (𝟙 X) x, property := (_ : x ∈ F.map (𝟙 X) ⁻¹' obj G X) } = {  …
    simp only [FunctorToTypes.map_id_apply]
    -- 🎉 no goals
  map_comp := @fun X Y Z i j => by
    ext ⟨x, _⟩
    -- ⊢ { obj := fun U => ↑(obj G U), map := fun U V i x => { val := F.map i ↑x, pro …
    dsimp
    -- ⊢ { val := F.map (i ≫ j) x, property := (_ : x ∈ F.map (i ≫ j) ⁻¹' obj G Z) }  …
    simp only [FunctorToTypes.map_comp_apply]
    -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.to_presheaf CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf

instance {U} : CoeHead (G.toPresheaf.obj U) (F.obj U) where
  coe := Subtype.val

/-- The inclusion of a subpresheaf to the original presheaf. -/
@[simps]
def Subpresheaf.ι : G.toPresheaf ⟶ F where app U x := x
#align category_theory.grothendieck_topology.subpresheaf.ι CategoryTheory.GrothendieckTopology.Subpresheaf.ι

instance : Mono G.ι :=
  ⟨@fun _ f₁ f₂ e =>
    NatTrans.ext f₁ f₂ <|
      funext fun U => funext fun x => Subtype.ext <| congr_fun (congr_app e U) x⟩

/-- The inclusion of a subpresheaf to a larger subpresheaf -/
@[simps]
def Subpresheaf.homOfLe {G G' : Subpresheaf F} (h : G ≤ G') : G.toPresheaf ⟶ G'.toPresheaf
    where app U x := ⟨x, h U x.prop⟩
#align category_theory.grothendieck_topology.subpresheaf.hom_of_le CategoryTheory.GrothendieckTopology.Subpresheaf.homOfLe

instance {G G' : Subpresheaf F} (h : G ≤ G') : Mono (Subpresheaf.homOfLe h) :=
  ⟨fun f₁ f₂ e =>
    NatTrans.ext f₁ f₂ <|
      funext fun U =>
        funext fun x =>
          Subtype.ext <| (congr_arg Subtype.val <| (congr_fun (congr_app e U) x : _) : _)⟩

@[reassoc (attr := simp)]
theorem Subpresheaf.homOfLe_ι {G G' : Subpresheaf F} (h : G ≤ G') :
    Subpresheaf.homOfLe h ≫ G'.ι = G.ι := by
  ext
  -- ⊢ NatTrans.app (homOfLe h ≫ ι G') x✝ a✝ = NatTrans.app (ι G) x✝ a✝
  rfl
  -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.hom_of_le_ι CategoryTheory.GrothendieckTopology.Subpresheaf.homOfLe_ι

instance : IsIso (Subpresheaf.ι (⊤ : Subpresheaf F)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  -- ⊢ ∀ (X : Cᵒᵖ), IsIso (NatTrans.app (Subpresheaf.ι ⊤) X)
  · intro X
    -- ⊢ IsIso (NatTrans.app (Subpresheaf.ι ⊤) X)
    rw [isIso_iff_bijective]
    -- ⊢ Function.Bijective (NatTrans.app (Subpresheaf.ι ⊤) X)
    exact ⟨Subtype.coe_injective, fun x => ⟨⟨x, _root_.trivial⟩, rfl⟩⟩
    -- 🎉 no goals

theorem Subpresheaf.eq_top_iff_isIso : G = ⊤ ↔ IsIso G.ι := by
  constructor
  -- ⊢ G = ⊤ → IsIso (ι G)
  · rintro rfl
    -- ⊢ IsIso (ι ⊤)
    infer_instance
    -- 🎉 no goals
  · intro H
    -- ⊢ G = ⊤
    ext U x
    -- ⊢ x ∈ obj G U ↔ x ∈ obj ⊤ U
    apply iff_true_iff.mpr
    -- ⊢ x ∈ obj G U
    rw [← IsIso.inv_hom_id_apply (G.ι.app U) x]
    -- ⊢ ↑(NatTrans.app (ι G) U) (↑(Classical.choose (_ : ∃ inv, NatTrans.app (ι G) U …
    exact ((inv (G.ι.app U)) x).2
    -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.eq_top_iff_is_iso CategoryTheory.GrothendieckTopology.Subpresheaf.eq_top_iff_isIso

/-- If the image of a morphism falls in a subpresheaf, then the morphism factors through it. -/
@[simps!]
def Subpresheaf.lift (f : F' ⟶ F) (hf : ∀ U x, f.app U x ∈ G.obj U) : F' ⟶ G.toPresheaf where
  app U x := ⟨f.app U x, hf U x⟩
  naturality := by
    have := elementwise_of% f.naturality
    -- ⊢ ∀ ⦃X Y : Cᵒᵖ⦄ (f_1 : X ⟶ Y), F'.map f_1 ≫ (fun U x => { val := NatTrans.app  …
    intros
    -- ⊢ F'.map f✝ ≫ (fun U x => { val := NatTrans.app f U x, property := (_ : NatTra …
    refine funext fun x => Subtype.ext ?_
    -- ⊢ ↑((F'.map f✝ ≫ (fun U x => { val := NatTrans.app f U x, property := (_ : Nat …
    simp only [toPresheaf_obj, types_comp_apply]
    -- ⊢ NatTrans.app f Y✝ (F'.map f✝ x) = ↑((toPresheaf G).map f✝ { val := NatTrans. …
    exact this _ _
    -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.lift CategoryTheory.GrothendieckTopology.Subpresheaf.lift

@[reassoc (attr := simp)]
theorem Subpresheaf.lift_ι (f : F' ⟶ F) (hf : ∀ U x, f.app U x ∈ G.obj U) :
  G.lift f hf ≫ G.ι = f := by
  ext
  -- ⊢ NatTrans.app (lift G f hf ≫ ι G) x✝ a✝ = NatTrans.app f x✝ a✝
  rfl
  -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.lift_ι CategoryTheory.GrothendieckTopology.Subpresheaf.lift_ι

/-- Given a subpresheaf `G` of `F`, an `F`-section `s` on `U`, we may define a sieve of `U`
consisting of all `f : V ⟶ U` such that the restriction of `s` along `f` is in `G`. -/
@[simps]
def Subpresheaf.sieveOfSection {U : Cᵒᵖ} (s : F.obj U) : Sieve (unop U) where
  arrows V f := F.map f.op s ∈ G.obj (op V)
  downward_closed := @fun V W i hi j => by
    simp only [op_unop, op_comp, FunctorToTypes.map_comp_apply]
    -- ⊢ F.map j.op (F.map i.op s) ∈ obj G (op W)
    exact G.map _ hi
    -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.sieve_of_section CategoryTheory.GrothendieckTopology.Subpresheaf.sieveOfSection

/-- Given an `F`-section `s` on `U` and a subpresheaf `G`, we may define a family of elements in
`G` consisting of the restrictions of `s` -/
def Subpresheaf.familyOfElementsOfSection {U : Cᵒᵖ} (s : F.obj U) :
    (G.sieveOfSection s).1.FamilyOfElements G.toPresheaf := fun _ i hi => ⟨F.map i.op s, hi⟩
#align category_theory.grothendieck_topology.subpresheaf.family_of_elements_of_section CategoryTheory.GrothendieckTopology.Subpresheaf.familyOfElementsOfSection

theorem Subpresheaf.family_of_elements_compatible {U : Cᵒᵖ} (s : F.obj U) :
    (G.familyOfElementsOfSection s).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  -- ⊢ (toPresheaf G).map g₁.op (familyOfElementsOfSection G s f₁ h₁) = (toPresheaf …
  refine Subtype.ext ?_ -- port note: `ext1` does not work here
  -- ⊢ ↑((toPresheaf G).map g₁.op (familyOfElementsOfSection G s f₁ h₁)) = ↑((toPre …
  change F.map g₁.op (F.map f₁.op s) = F.map g₂.op (F.map f₂.op s)
  -- ⊢ F.map g₁.op (F.map f₁.op s) = F.map g₂.op (F.map f₂.op s)
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, e]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.family_of_elements_compatible CategoryTheory.GrothendieckTopology.Subpresheaf.family_of_elements_compatible

theorem Subpresheaf.nat_trans_naturality (f : F' ⟶ G.toPresheaf) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : F'.obj U) : (f.app V (F'.map i x)).1 = F.map i (f.app U x).1 :=
  congr_arg Subtype.val (FunctorToTypes.naturality _ _ f i x)
#align category_theory.grothendieck_topology.subpresheaf.nat_trans_naturality CategoryTheory.GrothendieckTopology.Subpresheaf.nat_trans_naturality

/-- The sheafification of a subpresheaf as a subpresheaf.
Note that this is a sheaf only when the whole presheaf is a sheaf. -/
def Subpresheaf.sheafify : Subpresheaf F where
  obj U := { s | G.sieveOfSection s ∈ J (unop U) }
  map := by
    rintro U V i s hs
    -- ⊢ s ∈ F.map i ⁻¹' (fun U => {s | sieveOfSection G s ∈ sieves J U.unop}) V
    refine' J.superset_covering _ (J.pullback_stable i.unop hs)
    -- ⊢ Sieve.pullback i.unop (sieveOfSection G s) ≤ sieveOfSection G (F.map i s)
    intro _ _ h
    -- ⊢ (sieveOfSection G (F.map i s)).arrows f✝
    dsimp at h ⊢
    -- ⊢ F.map f✝.op (F.map i s) ∈ obj G (op Y✝)
    rwa [← FunctorToTypes.map_comp_apply]
    -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.sheafify CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify

theorem Subpresheaf.le_sheafify : G ≤ G.sheafify J := by
  intro U s hs
  -- ⊢ s ∈ obj (sheafify J G) U
  change _ ∈ J _
  -- ⊢ sieveOfSection G s ∈ sieves J U.unop
  convert J.top_mem U.unop -- porting note: `U.unop` can not be inferred now
  -- ⊢ sieveOfSection G s = ⊤
  rw [eq_top_iff]
  -- ⊢ ⊤ ≤ sieveOfSection G s
  rintro V i -
  -- ⊢ (sieveOfSection G s).arrows i
  exact G.map i.op hs
  -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.le_sheafify CategoryTheory.GrothendieckTopology.Subpresheaf.le_sheafify

variable {J}

theorem Subpresheaf.eq_sheafify (h : Presieve.IsSheaf J F) (hG : Presieve.IsSheaf J G.toPresheaf) :
    G = G.sheafify J := by
  apply (G.le_sheafify J).antisymm
  -- ⊢ sheafify J G ≤ G
  intro U s hs
  -- ⊢ s ∈ obj G U
  suffices ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).1 = s by
    rw [← this]
    exact ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).2
  apply (h _ hs).isSeparatedFor.ext
  -- ⊢ ∀ ⦃Y : C⦄ ⦃f : Y ⟶ U.unop⦄, (sieveOfSection G s).arrows f → F.map f.op ↑(Pre …
  intro V i hi
  -- ⊢ F.map i.op ↑(Presieve.IsSheafFor.amalgamate (_ : Presieve.IsSheafFor (toPres …
  exact (congr_arg Subtype.val ((hG _ hs).valid_glue (G.family_of_elements_compatible s) _ hi) : _)
  -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.eq_sheafify CategoryTheory.GrothendieckTopology.Subpresheaf.eq_sheafify

theorem Subpresheaf.sheafify_isSheaf (hF : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J (G.sheafify J).toPresheaf := by
  intro U S hS x hx
  -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x t
  let S' := Sieve.bind S fun Y f hf => G.sieveOfSection (x f hf).1
  -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x t
  have := fun (V) (i : V ⟶ U) (hi : S' i) => hi
  -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x t
  -- porting note: change to explicit variable so that `choose` can find the correct
  -- dependent functions. Thus everything follows need two additional explicit variables.
  choose W i₁ i₂ hi₂ h₁ h₂ using this
  -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x t
  dsimp [-Sieve.bind_apply] at *
  -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x t
  let x'' : Presieve.FamilyOfElements F S' := fun V i hi => F.map (i₁ V i hi).op (x _ (hi₂ V i hi))
  -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x t
  have H : ∀ s, x.IsAmalgamation s ↔ x''.IsAmalgamation s.1 := by
    intro s
    constructor
    · intro H V i hi
      dsimp only [show x'' = fun V i hi => F.map (i₁ V i hi).op (x _ (hi₂ V i hi)) from rfl]
      conv_lhs => rw [← h₂ _ _ hi]
      rw [← H _ (hi₂ _ _ hi)]
      exact FunctorToTypes.map_comp_apply F (i₂ _ _ hi).op (i₁ _ _ hi).op _
    · intro H V i hi
      refine Subtype.ext ?_
      apply (hF _ (x i hi).2).isSeparatedFor.ext
      intro V' i' hi'
      have hi'' : S' (i' ≫ i) := ⟨_, _, _, hi, hi', rfl⟩
      have := H _ hi''
      rw [op_comp, F.map_comp] at this
      refine' this.trans (congr_arg Subtype.val (hx _ _ (hi₂ _ _ hi'') hi (h₂ _ _ hi'')))
  have : x''.Compatible := by
    intro V₁ V₂ V₃ g₁ g₂ g₃ g₄ S₁ S₂ e
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
    exact
      congr_arg Subtype.val
        (hx (g₁ ≫ i₁ _ _ S₁) (g₂ ≫ i₁ _ _ S₂) (hi₂ _ _ S₁) (hi₂ _ _ S₂)
        (by simp only [Category.assoc, h₂, e]))
  obtain ⟨t, ht, ht'⟩ := hF _ (J.bind_covering hS fun V i hi => (x i hi).2) _ this
  -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x t
  refine' ⟨⟨t, _⟩, (H ⟨t, _⟩).mpr ht, fun y hy => Subtype.ext (ht' _ ((H _).mp hy))⟩
  -- ⊢ t ∈ obj (sheafify J G) (op U)
  refine' J.superset_covering _ (J.bind_covering hS fun V i hi => (x i hi).2)
  -- ⊢ (Sieve.bind S.arrows fun V i hi => sieveOfSection G ↑(x i hi)) ≤ sieveOfSect …
  intro V i hi
  -- ⊢ (sieveOfSection G t).arrows i
  dsimp
  -- ⊢ F.map i.op t ∈ obj G (op V)
  rw [ht _ hi]
  -- ⊢ x'' i hi ∈ obj G (op V)
  exact h₁ _ _ hi
  -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.sheafify_is_sheaf CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify_isSheaf

theorem Subpresheaf.eq_sheafify_iff (h : Presieve.IsSheaf J F) :
    G = G.sheafify J ↔ Presieve.IsSheaf J G.toPresheaf :=
  ⟨fun e => e.symm ▸ G.sheafify_isSheaf h, G.eq_sheafify h⟩
#align category_theory.grothendieck_topology.subpresheaf.eq_sheafify_iff CategoryTheory.GrothendieckTopology.Subpresheaf.eq_sheafify_iff

theorem Subpresheaf.isSheaf_iff (h : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J G.toPresheaf ↔
      ∀ (U) (s : F.obj U), G.sieveOfSection s ∈ J (unop U) → s ∈ G.obj U := by
  rw [← G.eq_sheafify_iff h]
  -- ⊢ G = sheafify J G ↔ ∀ (U : Cᵒᵖ) (s : F.obj U), sieveOfSection G s ∈ sieves J  …
  change _ ↔ G.sheafify J ≤ G
  -- ⊢ G = sheafify J G ↔ sheafify J G ≤ G
  exact ⟨Eq.ge, (G.le_sheafify J).antisymm⟩
  -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.is_sheaf_iff CategoryTheory.GrothendieckTopology.Subpresheaf.isSheaf_iff

theorem Subpresheaf.sheafify_sheafify (h : Presieve.IsSheaf J F) :
    (G.sheafify J).sheafify J = G.sheafify J :=
  ((Subpresheaf.eq_sheafify_iff _ h).mpr <| G.sheafify_isSheaf h).symm
#align category_theory.grothendieck_topology.subpresheaf.sheafify_sheafify CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify_sheafify

/-- The lift of a presheaf morphism onto the sheafification subpresheaf.  -/
noncomputable def Subpresheaf.sheafifyLift (f : G.toPresheaf ⟶ F') (h : Presieve.IsSheaf J F') :
    (G.sheafify J).toPresheaf ⟶ F' where
  app U s := (h (G.sieveOfSection s.1) s.prop).amalgamate
    (_) ((G.family_of_elements_compatible s.1).compPresheafMap f)
  naturality := by
    intro U V i
    -- ⊢ (toPresheaf (sheafify J G)).map i ≫ (fun U s => Presieve.IsSheafFor.amalgama …
    ext s
    -- ⊢ ((toPresheaf (sheafify J G)).map i ≫ (fun U s => Presieve.IsSheafFor.amalgam …
    apply (h _ ((Subpresheaf.sheafify J G).toPresheaf.map i s).prop).isSeparatedFor.ext
    -- ⊢ ∀ ⦃Y : C⦄ ⦃f_1 : Y ⟶ V.unop⦄, (sieveOfSection G ↑((toPresheaf (sheafify J G) …
    intro W j hj
    -- ⊢ F'.map j.op (((toPresheaf (sheafify J G)).map i ≫ (fun U s => Presieve.IsShe …
    refine' (Presieve.IsSheafFor.valid_glue (h _ ((G.sheafify J).toPresheaf.map i s).2)
      ((G.family_of_elements_compatible _).compPresheafMap _) _ hj).trans _
    dsimp
    -- ⊢ Presieve.FamilyOfElements.compPresheafMap f (familyOfElementsOfSection G (F. …
    conv_rhs => rw [← FunctorToTypes.map_comp_apply]
    -- ⊢ Presieve.FamilyOfElements.compPresheafMap f (familyOfElementsOfSection G (F. …
    change _ = F'.map (j ≫ i.unop).op _
    -- ⊢ Presieve.FamilyOfElements.compPresheafMap f (familyOfElementsOfSection G (F. …
    refine' Eq.trans _ (Presieve.IsSheafFor.valid_glue (h _ s.2)
      ((G.family_of_elements_compatible s.1).compPresheafMap f) (j ≫ i.unop) _).symm
    swap -- porting note: need to swap two goals otherwise the first goal needs to be proven
    -- ⊢ (sieveOfSection G ↑s).arrows (j ≫ i.unop)
    -- inside the second goal any way
    · dsimp [Presieve.FamilyOfElements.compPresheafMap] at hj ⊢
      -- ⊢ F.map (i ≫ j.op) ↑s ∈ obj G (op W)
      rwa [FunctorToTypes.map_comp_apply]
      -- 🎉 no goals
    · dsimp [Presieve.FamilyOfElements.compPresheafMap]
      -- ⊢ NatTrans.app f (op W) (familyOfElementsOfSection G (F.map i ↑s) j hj) = NatT …
      exact congr_arg _ (Subtype.ext (FunctorToTypes.map_comp_apply _ _ _ _).symm)
      -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.sheafify_lift CategoryTheory.GrothendieckTopology.Subpresheaf.sheafifyLift

theorem Subpresheaf.to_sheafifyLift (f : G.toPresheaf ⟶ F') (h : Presieve.IsSheaf J F') :
    Subpresheaf.homOfLe (G.le_sheafify J) ≫ G.sheafifyLift f h = f := by
  ext U s
  -- ⊢ NatTrans.app (homOfLe (_ : G ≤ sheafify J G) ≫ sheafifyLift G f h) U s = Nat …
  apply (h _ ((Subpresheaf.homOfLe (G.le_sheafify J)).app U s).prop).isSeparatedFor.ext
  -- ⊢ ∀ ⦃Y : C⦄ ⦃f_1 : Y ⟶ U.unop⦄, (sieveOfSection G ↑(NatTrans.app (homOfLe (_ : …
  intro V i hi
  -- ⊢ F'.map i.op (NatTrans.app (homOfLe (_ : G ≤ sheafify J G) ≫ sheafifyLift G f …
  have := elementwise_of% f.naturality
  -- ⊢ F'.map i.op (NatTrans.app (homOfLe (_ : G ≤ sheafify J G) ≫ sheafifyLift G f …
  -- porting note: filled in some underscores where Lean3 could automatically fill.
  exact (Presieve.IsSheafFor.valid_glue (h _ ((homOfLe (_ : G ≤ sheafify J G)).app U s).2)
    ((G.family_of_elements_compatible _).compPresheafMap _) _ hi).trans (this _ _)
#align category_theory.grothendieck_topology.subpresheaf.to_sheafify_lift CategoryTheory.GrothendieckTopology.Subpresheaf.to_sheafifyLift

theorem Subpresheaf.to_sheafify_lift_unique (h : Presieve.IsSheaf J F')
    (l₁ l₂ : (G.sheafify J).toPresheaf ⟶ F')
    (e : Subpresheaf.homOfLe (G.le_sheafify J) ≫ l₁ = Subpresheaf.homOfLe (G.le_sheafify J) ≫ l₂) :
    l₁ = l₂ := by
  ext U ⟨s, hs⟩
  -- ⊢ NatTrans.app l₁ U { val := s, property := hs } = NatTrans.app l₂ U { val :=  …
  apply (h _ hs).isSeparatedFor.ext
  -- ⊢ ∀ ⦃Y : C⦄ ⦃f : Y ⟶ U.unop⦄, (sieveOfSection G s).arrows f → F'.map f.op (Nat …
  rintro V i hi
  -- ⊢ F'.map i.op (NatTrans.app l₁ U { val := s, property := hs }) = F'.map i.op ( …
  dsimp at hi
  -- ⊢ F'.map i.op (NatTrans.app l₁ U { val := s, property := hs }) = F'.map i.op ( …
  erw [← FunctorToTypes.naturality, ← FunctorToTypes.naturality]
  -- ⊢ NatTrans.app l₁ (op V) ((toPresheaf (sheafify J G)).map i.op { val := s, pro …
  exact (congr_fun (congr_app e <| op V) ⟨_, hi⟩ : _)
  -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.to_sheafify_lift_unique CategoryTheory.GrothendieckTopology.Subpresheaf.to_sheafify_lift_unique

theorem Subpresheaf.sheafify_le (h : G ≤ G') (hF : Presieve.IsSheaf J F)
    (hG' : Presieve.IsSheaf J G'.toPresheaf) : G.sheafify J ≤ G' := by
  intro U x hx
  -- ⊢ x ∈ obj G' U
  convert((G.sheafifyLift (Subpresheaf.homOfLe h) hG').app U ⟨x, hx⟩).2
  -- ⊢ x = ↑(NatTrans.app (sheafifyLift G (homOfLe h) hG') U { val := x, property : …
  apply (hF _ hx).isSeparatedFor.ext
  -- ⊢ ∀ ⦃Y : C⦄ ⦃f : Y ⟶ U.unop⦄, (sieveOfSection G x).arrows f → F.map f.op x = F …
  intro V i hi
  -- ⊢ F.map i.op x = F.map i.op ↑(NatTrans.app (sheafifyLift G (homOfLe h) hG') U  …
  have :=
    congr_arg (fun f : G.toPresheaf ⟶ G'.toPresheaf => (NatTrans.app f (op V) ⟨_, hi⟩).1)
      (G.to_sheafifyLift (Subpresheaf.homOfLe h) hG')
  convert this.symm
  -- ⊢ F.map i.op ↑(NatTrans.app (sheafifyLift G (homOfLe h) hG') U { val := x, pro …
  erw [← Subpresheaf.nat_trans_naturality]
  -- ⊢ ↑(NatTrans.app (sheafifyLift G (homOfLe h) hG') (op V) ((toPresheaf (sheafif …
  rfl
  -- 🎉 no goals
#align category_theory.grothendieck_topology.subpresheaf.sheafify_le CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify_le

section Image

/-- The image presheaf of a morphism, whose components are the set-theoretic images. -/
@[simps]
def imagePresheaf (f : F' ⟶ F) : Subpresheaf F where
  obj U := Set.range (f.app U)
  map := by
    rintro U V i _ ⟨x, rfl⟩
    -- ⊢ NatTrans.app f U x ∈ F.map i ⁻¹' (fun U => Set.range (NatTrans.app f U)) V
    have := elementwise_of% f.naturality
    -- ⊢ NatTrans.app f U x ∈ F.map i ⁻¹' (fun U => Set.range (NatTrans.app f U)) V
    exact ⟨_, this i x⟩
    -- 🎉 no goals
#align category_theory.grothendieck_topology.image_presheaf CategoryTheory.GrothendieckTopology.imagePresheaf

@[simp]
theorem top_subpresheaf_obj (U) : (⊤ : Subpresheaf F).obj U = ⊤ :=
  rfl
#align category_theory.grothendieck_topology.top_subpresheaf_obj CategoryTheory.GrothendieckTopology.top_subpresheaf_obj

@[simp]
theorem imagePresheaf_id : imagePresheaf (𝟙 F) = ⊤ := by
  ext
  -- ⊢ x✝ ∈ Subpresheaf.obj (imagePresheaf (𝟙 F)) x✝¹ ↔ x✝ ∈ Subpresheaf.obj ⊤ x✝¹
  simp
  -- 🎉 no goals
#align category_theory.grothendieck_topology.image_presheaf_id CategoryTheory.GrothendieckTopology.imagePresheaf_id

/-- A morphism factors through the image presheaf. -/
@[simps!]
def toImagePresheaf (f : F' ⟶ F) : F' ⟶ (imagePresheaf f).toPresheaf :=
  (imagePresheaf f).lift f fun _ _ => Set.mem_range_self _
#align category_theory.grothendieck_topology.to_image_presheaf CategoryTheory.GrothendieckTopology.toImagePresheaf

variable (J)

/-- A morphism factors through the sheafification of the image presheaf. -/
@[simps!]
def toImagePresheafSheafify (f : F' ⟶ F) : F' ⟶ ((imagePresheaf f).sheafify J).toPresheaf :=
  toImagePresheaf f ≫ Subpresheaf.homOfLe ((imagePresheaf f).le_sheafify J)
#align category_theory.grothendieck_topology.to_image_presheaf_sheafify CategoryTheory.GrothendieckTopology.toImagePresheafSheafify

variable {J}

@[reassoc (attr := simp)]
theorem toImagePresheaf_ι (f : F' ⟶ F) : toImagePresheaf f ≫ (imagePresheaf f).ι = f :=
  (imagePresheaf f).lift_ι _ _
#align category_theory.grothendieck_topology.to_image_presheaf_ι CategoryTheory.GrothendieckTopology.toImagePresheaf_ι

theorem imagePresheaf_comp_le (f₁ : F ⟶ F') (f₂ : F' ⟶ F'') :
    imagePresheaf (f₁ ≫ f₂) ≤ imagePresheaf f₂ := fun U _ hx => ⟨f₁.app U hx.choose, hx.choose_spec⟩
#align category_theory.grothendieck_topology.image_presheaf_comp_le CategoryTheory.GrothendieckTopology.imagePresheaf_comp_le

instance isIso_toImagePresheaf {F F' : Cᵒᵖ ⥤ TypeMax.{v, w}} (f : F ⟶ F') [hf : Mono f] :
  IsIso (toImagePresheaf f) := by
  have : ∀ (X : Cᵒᵖ), IsIso ((toImagePresheaf f).app X) := by
    intro X
    rw [isIso_iff_bijective]
    constructor
    · intro x y e
      have := (NatTrans.mono_iff_mono_app _ _).mp hf X
      rw [mono_iff_injective] at this
      exact this (congr_arg Subtype.val e : _)
    · rintro ⟨_, ⟨x, rfl⟩⟩
      exact ⟨x, rfl⟩
  apply NatIso.isIso_of_isIso_app
  -- 🎉 no goals

/-- The image sheaf of a morphism between sheaves, defined to be the sheafification of
`image_presheaf`. -/
@[simps]
def imageSheaf {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Sheaf J (Type w) :=
  ⟨((imagePresheaf f.1).sheafify J).toPresheaf, by
    rw [isSheaf_iff_isSheaf_of_type]
    -- ⊢ Presieve.IsSheaf J (Subpresheaf.toPresheaf (Subpresheaf.sheafify J (imagePre …
    apply Subpresheaf.sheafify_isSheaf
    -- ⊢ Presieve.IsSheaf J F'.val
    rw [← isSheaf_iff_isSheaf_of_type]
    -- ⊢ Presheaf.IsSheaf J F'.val
    exact F'.2⟩
    -- 🎉 no goals
#align category_theory.grothendieck_topology.image_sheaf CategoryTheory.GrothendieckTopology.imageSheaf

/-- A morphism factors through the image sheaf. -/
@[simps]
def toImageSheaf {F F' : Sheaf J (Type w)} (f : F ⟶ F') : F ⟶ imageSheaf f :=
  ⟨toImagePresheafSheafify J f.1⟩
#align category_theory.grothendieck_topology.to_image_sheaf CategoryTheory.GrothendieckTopology.toImageSheaf

/-- The inclusion of the image sheaf to the target. -/
@[simps]
def imageSheafι {F F' : Sheaf J (Type w)} (f : F ⟶ F') : imageSheaf f ⟶ F' :=
  ⟨Subpresheaf.ι _⟩
#align category_theory.grothendieck_topology.image_sheaf_ι CategoryTheory.GrothendieckTopology.imageSheafι

@[reassoc (attr := simp)]
theorem toImageSheaf_ι {F F' : Sheaf J (Type w)} (f : F ⟶ F') :
    toImageSheaf f ≫ imageSheafι f = f := by
  ext1
  -- ⊢ (toImageSheaf f ≫ imageSheafι f).val = f.val
  simp [toImagePresheafSheafify]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.to_image_sheaf_ι CategoryTheory.GrothendieckTopology.toImageSheaf_ι

instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Mono (imageSheafι f) :=
  (sheafToPresheaf J _).mono_of_mono_map
    (by
      dsimp
      -- ⊢ Mono (Subpresheaf.ι (Subpresheaf.sheafify J (imagePresheaf f.val)))
      infer_instance)
      -- 🎉 no goals

instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Epi (toImageSheaf f) := by
  refine' ⟨@fun G' g₁ g₂ e => _⟩
  -- ⊢ g₁ = g₂
  ext U ⟨s, hx⟩
  -- ⊢ NatTrans.app g₁.val U { val := s, property := hx } = NatTrans.app g₂.val U { …
  apply ((isSheaf_iff_isSheaf_of_type J _).mp G'.2 _ hx).isSeparatedFor.ext
  -- ⊢ ∀ ⦃Y : C⦄ ⦃f_1 : Y ⟶ U.unop⦄, (Subpresheaf.sieveOfSection (imagePresheaf f.v …
  rintro V i ⟨y, e'⟩
  -- ⊢ G'.val.map i.op (NatTrans.app g₁.val U { val := s, property := hx }) = G'.va …
  change (g₁.val.app _ ≫ G'.val.map _) _ = (g₂.val.app _ ≫ G'.val.map _) _
  -- ⊢ (NatTrans.app g₁.val (op U.unop) ≫ G'.val.map i.op) { val := s, property :=  …
  rw [← NatTrans.naturality, ← NatTrans.naturality]
  -- ⊢ ((imageSheaf f).val.map i.op ≫ NatTrans.app g₁.val (op V)) { val := s, prope …
  have E : (toImageSheaf f).val.app (op V) y = (imageSheaf f).val.map i.op ⟨s, hx⟩ :=
    Subtype.ext e'
  have := congr_arg (fun f : F ⟶ G' => (Sheaf.Hom.val f).app _ y) e
  -- ⊢ ((imageSheaf f).val.map i.op ≫ NatTrans.app g₁.val (op V)) { val := s, prope …
  dsimp at this ⊢
  -- ⊢ NatTrans.app g₁.val (op V) ((Subpresheaf.toPresheaf (Subpresheaf.sheafify J  …
  convert this <;> exact E.symm
  -- ⊢ (Subpresheaf.toPresheaf (Subpresheaf.sheafify J (imagePresheaf f.val))).map  …
                   -- 🎉 no goals
                   -- 🎉 no goals

/-- The mono factorization given by `image_sheaf` for a morphism. -/
def imageMonoFactorization {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Limits.MonoFactorisation f where
  I := imageSheaf f
  m := imageSheafι f
  e := toImageSheaf f
#align category_theory.grothendieck_topology.image_mono_factorization CategoryTheory.GrothendieckTopology.imageMonoFactorization

/-- The mono factorization given by `image_sheaf` for a morphism is an image. -/
noncomputable def imageFactorization {F F' : Sheaf J TypeMax.{v, u}} (f : F ⟶ F') :
    Limits.ImageFactorisation f where
  F := imageMonoFactorization f
  isImage :=
    { lift := fun I => by
        -- port note: need to specify the target category (TypeMax.{v, u}) for this to work.
        haveI M := (Sheaf.Hom.mono_iff_presheaf_mono J TypeMax.{v, u} _).mp I.m_mono
        -- ⊢ (imageMonoFactorization f).I ⟶ I.I
        haveI := isIso_toImagePresheaf I.m.1
        -- ⊢ (imageMonoFactorization f).I ⟶ I.I
        refine' ⟨Subpresheaf.homOfLe _ ≫ inv (toImagePresheaf I.m.1)⟩
        -- ⊢ Subpresheaf.sheafify J (imagePresheaf f.val) ≤ imagePresheaf I.m.val
        apply Subpresheaf.sheafify_le
        · conv_lhs => rw [← I.fac]
          -- ⊢ imagePresheaf (I.e ≫ I.m).val ≤ imagePresheaf I.m.val
          apply imagePresheaf_comp_le
          -- 🎉 no goals
        · rw [← isSheaf_iff_isSheaf_of_type]
          -- ⊢ Presheaf.IsSheaf J F'.val
          exact F'.2
          -- 🎉 no goals
        · apply Presieve.isSheaf_iso J (asIso <| toImagePresheaf I.m.1)
          -- ⊢ Presieve.IsSheaf J I.I.val
          rw [← isSheaf_iff_isSheaf_of_type]
          -- ⊢ Presheaf.IsSheaf J I.I.val
          exact I.I.2
          -- 🎉 no goals
      lift_fac := fun I => by
        ext1
        -- ⊢ ((fun I => { val := Subpresheaf.homOfLe (_ : Subpresheaf.sheafify J (imagePr …
        dsimp [imageMonoFactorization]
        -- ⊢ (Subpresheaf.homOfLe (_ : Subpresheaf.sheafify J (imagePresheaf f.val) ≤ ima …
        generalize_proofs h
        -- ⊢ (Subpresheaf.homOfLe (_ : Subpresheaf.sheafify J (imagePresheaf f.val) ≤ ima …
        rw [← Subpresheaf.homOfLe_ι h, Category.assoc]
        -- ⊢ Subpresheaf.homOfLe (_ : Subpresheaf.sheafify J (imagePresheaf f.val) ≤ imag …
        congr 1
        -- ⊢ inv (toImagePresheaf I.m.val) ≫ I.m.val = Subpresheaf.ι (imagePresheaf I.m.v …
        rw [IsIso.inv_comp_eq, toImagePresheaf_ι] }
        -- 🎉 no goals
#align category_theory.grothendieck_topology.image_factorization CategoryTheory.GrothendieckTopology.imageFactorization

instance : Limits.HasImages (Sheaf J (Type max v u)) :=
  ⟨@fun _ _ f => ⟨⟨imageFactorization f⟩⟩⟩

end Image

end CategoryTheory.GrothendieckTopology
