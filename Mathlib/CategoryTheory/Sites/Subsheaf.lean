/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Subpresheaf.Image
import Mathlib.CategoryTheory.Subpresheaf.Sieves

/-!

# Subsheaf of types

We define the sub(pre)sheaf of a type-valued presheaf.

## Main results

- `CategoryTheory.Subpresheaf` :
  A subpresheaf of a presheaf of types.
- `CategoryTheory.Subpresheaf.sheafify` :
  The sheafification of a subpresheaf as a subpresheaf. Note that this is a sheaf only when the
  whole sheaf is.
- `CategoryTheory.Subpresheaf.sheafify_isSheaf` :
  The sheafification is a sheaf
- `CategoryTheory.Subpresheaf.sheafifyLift` :
  The descent of a map into a sheaf to the sheafification.
- `CategoryTheory.GrothendieckTopology.imageSheaf` : The image sheaf of a morphism.
- `CategoryTheory.GrothendieckTopology.imageFactorization` : The image sheaf as a
  `Limits.imageFactorization`.
-/


universe w v u

open Opposite CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {F F' F'' : Cᵒᵖ ⥤ Type w} (G G' : Subpresheaf F)

/-- The sheafification of a subpresheaf as a subpresheaf.
Note that this is a sheaf only when the whole presheaf is a sheaf. -/
def Subpresheaf.sheafify : Subpresheaf F where
  obj U := { s | G.sieveOfSection s ∈ J (unop U) }
  map := by
    rintro U V i s hs
    refine J.superset_covering ?_ (J.pullback_stable i.unop hs)
    intro _ _ h
    dsimp at h ⊢
    rwa [← FunctorToTypes.map_comp_apply]

theorem Subpresheaf.le_sheafify : G ≤ G.sheafify J := by
  intro U s hs
  change _ ∈ J _
  convert J.top_mem U.unop
  rw [eq_top_iff]
  rintro V i -
  exact G.map i.op hs

variable {J}

theorem Subpresheaf.eq_sheafify (h : Presieve.IsSheaf J F) (hG : Presieve.IsSheaf J G.toPresheaf) :
    G = G.sheafify J := by
  apply (G.le_sheafify J).antisymm
  intro U s hs
  suffices ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).1 = s by
    rw [← this]
    exact ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).2
  apply (h _ hs).isSeparatedFor.ext
  intro V i hi
  exact (congr_arg Subtype.val ((hG _ hs).valid_glue (G.family_of_elements_compatible s) _ hi) :)

theorem Subpresheaf.sheafify_isSheaf (hF : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J (G.sheafify J).toPresheaf := by
  intro U S hS x hx
  let S' := Sieve.bind S fun Y f hf => G.sieveOfSection (x f hf).1
  have := fun (V) (i : V ⟶ U) (hi : S' i) => hi
  choose W i₁ i₂ hi₂ h₁ h₂ using this
  dsimp [-Sieve.bind_apply] at *
  let x'' : Presieve.FamilyOfElements F S' := fun V i hi => F.map (i₁ V i hi).op (x _ (hi₂ V i hi))
  have H : ∀ s, x.IsAmalgamation s ↔ x''.IsAmalgamation s.1 := by
    intro s
    constructor
    · intro H V i hi
      dsimp only [x'']
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
      exact this.trans (congr_arg Subtype.val (hx _ _ (hi₂ _ _ hi'') hi (h₂ _ _ hi'')))
  have : x''.Compatible := by
    intro V₁ V₂ V₃ g₁ g₂ g₃ g₄ S₁ S₂ e
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
    exact
      congr_arg Subtype.val
        (hx (g₁ ≫ i₁ _ _ S₁) (g₂ ≫ i₁ _ _ S₂) (hi₂ _ _ S₁) (hi₂ _ _ S₂)
        (by simp only [Category.assoc, h₂, e]))
  obtain ⟨t, ht, ht'⟩ := hF _ (J.bind_covering hS fun V i hi => (x i hi).2) _ this
  refine ⟨⟨t, _⟩, (H ⟨t, ?_⟩).mpr ht, fun y hy => Subtype.ext (ht' _ ((H _).mp hy))⟩
  refine J.superset_covering ?_ (J.bind_covering hS fun V i hi => (x i hi).2)
  intro V i hi
  dsimp
  rw [ht _ hi]
  exact h₁ _ _ hi

theorem Subpresheaf.eq_sheafify_iff (h : Presieve.IsSheaf J F) :
    G = G.sheafify J ↔ Presieve.IsSheaf J G.toPresheaf :=
  ⟨fun e => e.symm ▸ G.sheafify_isSheaf h, G.eq_sheafify h⟩

theorem Subpresheaf.isSheaf_iff (h : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J G.toPresheaf ↔
      ∀ (U) (s : F.obj U), G.sieveOfSection s ∈ J (unop U) → s ∈ G.obj U := by
  rw [← G.eq_sheafify_iff h]
  change _ ↔ G.sheafify J ≤ G
  exact ⟨Eq.ge, (G.le_sheafify J).antisymm⟩

theorem Subpresheaf.sheafify_sheafify (h : Presieve.IsSheaf J F) :
    (G.sheafify J).sheafify J = G.sheafify J :=
  ((Subpresheaf.eq_sheafify_iff _ h).mpr <| G.sheafify_isSheaf h).symm

/-- The lift of a presheaf morphism onto the sheafification subpresheaf. -/
noncomputable def Subpresheaf.sheafifyLift (f : G.toPresheaf ⟶ F') (h : Presieve.IsSheaf J F') :
    (G.sheafify J).toPresheaf ⟶ F' where
  app _ s := (h (G.sieveOfSection s.1) s.prop).amalgamate
    (_) ((G.family_of_elements_compatible s.1).compPresheafMap f)
  naturality := by
    intro U V i
    ext s
    apply (h _ ((Subpresheaf.sheafify J G).toPresheaf.map i s).prop).isSeparatedFor.ext
    intro W j hj
    refine (Presieve.IsSheafFor.valid_glue (h _ ((G.sheafify J).toPresheaf.map i s).2)
      ((G.family_of_elements_compatible _).compPresheafMap _) _ hj).trans ?_
    dsimp
    conv_rhs => rw [← FunctorToTypes.map_comp_apply]
    change _ = F'.map (j ≫ i.unop).op _
    refine Eq.trans ?_ (Presieve.IsSheafFor.valid_glue (h _ s.2)
      ((G.family_of_elements_compatible s.1).compPresheafMap f) (j ≫ i.unop) ?_).symm
    · dsimp [Presieve.FamilyOfElements.compPresheafMap]
      exact congr_arg _ (Subtype.ext (FunctorToTypes.map_comp_apply _ _ _ _).symm)
    · dsimp [Presieve.FamilyOfElements.compPresheafMap] at hj ⊢
      rwa [FunctorToTypes.map_comp_apply]

theorem Subpresheaf.to_sheafifyLift (f : G.toPresheaf ⟶ F') (h : Presieve.IsSheaf J F') :
    Subpresheaf.homOfLe (G.le_sheafify J) ≫ G.sheafifyLift f h = f := by
  ext U s
  apply (h _ ((Subpresheaf.homOfLe (G.le_sheafify J)).app U s).prop).isSeparatedFor.ext
  intro V i hi
  have := elementwise_of% f.naturality
  exact (Presieve.IsSheafFor.valid_glue (h _ ((homOfLe (_ : _ ≤ sheafify _ _)).app _ _).2)
    ((G.family_of_elements_compatible _).compPresheafMap _) _ _).trans (this _ _)

theorem Subpresheaf.to_sheafify_lift_unique (h : Presieve.IsSheaf J F')
    (l₁ l₂ : (G.sheafify J).toPresheaf ⟶ F')
    (e : Subpresheaf.homOfLe (G.le_sheafify J) ≫ l₁ = Subpresheaf.homOfLe (G.le_sheafify J) ≫ l₂) :
    l₁ = l₂ := by
  ext U ⟨s, hs⟩
  apply (h _ hs).isSeparatedFor.ext
  rintro V i hi
  dsimp at hi
  rw [← FunctorToTypes.naturality, ← FunctorToTypes.naturality]
  exact (congr_fun (congr_app e <| op V) ⟨_, hi⟩ :)

theorem Subpresheaf.sheafify_le (h : G ≤ G') (hF : Presieve.IsSheaf J F)
    (hG' : Presieve.IsSheaf J G'.toPresheaf) : G.sheafify J ≤ G' := by
  intro U x hx
  convert ((G.sheafifyLift (Subpresheaf.homOfLe h) hG').app U ⟨x, hx⟩).2
  apply (hF _ hx).isSeparatedFor.ext
  intro V i hi
  have :=
    congr_arg (fun f : G.toPresheaf ⟶ G'.toPresheaf => (NatTrans.app f (op V) ⟨_, hi⟩).1)
      (G.to_sheafifyLift (Subpresheaf.homOfLe h) hG')
  convert this.symm
  rw [← Subpresheaf.nat_trans_naturality]
  rfl

section Image

variable (J) in
/-- A morphism factors through the sheafification of the image presheaf. -/
@[simps!]
def Subpresheaf.toRangeSheafify (f : F' ⟶ F) : F' ⟶ ((Subpresheaf.range f).sheafify J).toPresheaf :=
  toRange f ≫ Subpresheaf.homOfLe ((range f).le_sheafify J)


/-- The image sheaf of a morphism between sheaves, defined to be the sheafification of
`image_presheaf`. -/
@[simps]
def Sheaf.image {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Sheaf J (Type w) :=
  ⟨((Subpresheaf.range f.1).sheafify J).toPresheaf, by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subpresheaf.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact F'.2⟩

/-- A morphism factors through the image sheaf. -/
@[simps]
def Sheaf.toImage {F F' : Sheaf J (Type w)} (f : F ⟶ F') : F ⟶ Sheaf.image f :=
  ⟨Subpresheaf.toRangeSheafify J f.1⟩

/-- The inclusion of the image sheaf to the target. -/
@[simps]
def Sheaf.imageι {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Sheaf.image f ⟶ F' :=
  ⟨Subpresheaf.ι _⟩


@[reassoc (attr := simp)]
theorem Sheaf.toImage_ι {F F' : Sheaf J (Type w)} (f : F ⟶ F') :
    toImage f ≫ imageι f = f := by
  ext1
  simp [Subpresheaf.toRangeSheafify]

instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Mono (Sheaf.imageι f) :=
  (sheafToPresheaf J _).mono_of_mono_map
    (by
      dsimp
      infer_instance)

instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Epi (Sheaf.toImage f) := by
  refine ⟨@fun G' g₁ g₂ e => ?_⟩
  ext U ⟨s, hx⟩
  apply ((isSheaf_iff_isSheaf_of_type J _).mp G'.2 _ hx).isSeparatedFor.ext
  rintro V i ⟨y, e'⟩
  change (g₁.val.app _ ≫ G'.val.map _) _ = (g₂.val.app _ ≫ G'.val.map _) _
  rw [← NatTrans.naturality, ← NatTrans.naturality]
  have E : (Sheaf.toImage f).val.app (op V) y = (Sheaf.image f).val.map i.op ⟨s, hx⟩ :=
    Subtype.ext e'
  have := congr_arg (fun f : F ⟶ G' => (Sheaf.Hom.val f).app _ y) e
  dsimp at this ⊢
  convert this <;> exact E.symm

/-- The mono factorization given by `image_sheaf` for a morphism. -/
def imageMonoFactorization {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Limits.MonoFactorisation f where
  I := Sheaf.image f
  m := Sheaf.imageι f
  e := Sheaf.toImage f

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
/-- The mono factorization given by `image_sheaf` for a morphism is an image. -/
noncomputable def imageFactorization {F F' : Sheaf J (Type (max v u))} (f : F ⟶ F') :
    Limits.ImageFactorisation f where
  F := imageMonoFactorization f
  isImage :=
    { lift := fun I => by
        haveI M := (Sheaf.Hom.mono_iff_presheaf_mono J (Type (max v u)) _).mp I.m_mono
        refine ⟨Subpresheaf.homOfLe ?_ ≫ inv (Subpresheaf.toRange I.m.1)⟩
        apply Subpresheaf.sheafify_le
        · conv_lhs => rw [← I.fac]
          apply Subpresheaf.range_comp_le
        · rw [← isSheaf_iff_isSheaf_of_type]
          exact F'.2
        · apply Presieve.isSheaf_iso J (asIso <| Subpresheaf.toRange I.m.1)
          rw [← isSheaf_iff_isSheaf_of_type]
          exact I.I.2
      lift_fac := fun I => by
        ext1
        dsimp [imageMonoFactorization]
        generalize_proofs h
        rw [← Subpresheaf.homOfLe_ι h, Category.assoc]
        congr 1
        rw [IsIso.inv_comp_eq, Subpresheaf.toRange_ι] }

instance : Limits.HasImages (Sheaf J (Type max v u)) :=
  ⟨fun f => ⟨⟨imageFactorization f⟩⟩⟩

end Image

end CategoryTheory
