import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Yoneda


namespace CategoryTheory

open Category Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- A morphism of presheaves `F ⟶ G` is representable if for any `X : C`, and any morphism
`g : yoneda.obj X ⟶ G`, the pullback `F ×_G yoneda.obj X` is also representable. -/
def Presheaf.representable : MorphismProperty (Cᵒᵖ ⥤ Type v) :=
  fun _ G f ↦ ∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), (pullback f g).Representable


namespace Presheaf.representable

section

variable {F G : Cᵒᵖ ⥤ Type v} {f : F ⟶ G} (hf : Presheaf.representable f)
  {Y : C} {f' : yoneda.obj Y ⟶ G} (hf' : Presheaf.representable f')
  {X : C} (g : yoneda.obj X ⟶ G) (hg : Presheaf.representable g)

/-- Let `f : F ⟶ G` be a representable morphism in the category of presheaves of types on
a category `C`. Then, for any `g : yoneda.obj X ⟶ G`, `hf.pullback g` denotes the (choice of) a
corresponding object in `C` equipped with an isomorphism between `yoneda.obj (hf.pullback g)`
and the categorical pullback of `f` and `g` in the category of presheaves. -/
noncomputable def pullback : C :=
  Functor.reprX (hF := hf g)

/-- The given isomorphism between `yoneda.obj (hf.pullback g)` and the choice of categorical
pullback of `f` and `g`-/
noncomputable def pullbackIso : yoneda.obj (hf.pullback g) ≅ Limits.pullback f g :=
  Functor.reprW (hF := hf g)

noncomputable def snd : hf.pullback g ⟶ X :=
  Yoneda.fullyFaithful.preimage ((hf.pullbackIso g).hom ≫ Limits.pullback.snd)

@[reassoc]
lemma yoneda_map_snd : yoneda.map (hf.snd g) = (hf.pullbackIso g).hom ≫ Limits.pullback.snd := by
  simp only [snd, Functor.FullyFaithful.map_preimage]

noncomputable abbrev fst_yoneda : yoneda.obj (hf.pullback g) ⟶ F :=
  (hf.pullbackIso g).hom ≫ Limits.pullback.fst

@[reassoc]
lemma condition_yoneda : hf.fst_yoneda g ≫ f = yoneda.map (hf.snd g) ≫ g := by
  simpa [yoneda_map_snd] using Limits.pullback.condition

#check IsPullback

-- pullbackConeOfLeftIso
-- pullbackConeOfRightIso

noncomputable def isPullback : IsLimit (PullbackCone.mk _ _ (hf.condition_yoneda g)) := by
  fapply IsLimit.ofIsoLimit (r:= limit.cone (Limits.cospan f g))

  sorry


--IsPullback (hf.fst_yoneda g) (yoneda.map <| hf.snd g) f g := by
  sorry



noncomputable def fst : hf'.pullback g ⟶ Y :=
  Yoneda.fullyFaithful.preimage ((hf'.pullbackIso g).hom ≫ Limits.pullback.fst)

@[reassoc]
lemma yoneda_map_fst :
    yoneda.map (hf'.fst g) = (hf'.pullbackIso g).hom ≫ Limits.pullback.fst := by
  simp only [fst, Functor.FullyFaithful.map_preimage]


@[reassoc]
lemma condition : yoneda.map (hf'.fst g) ≫ f' = yoneda.map (hf'.snd g) ≫ g := by
  simpa [yoneda_map_fst, yoneda_map_snd] using Limits.pullback.condition

variable {g}

@[ext 100]
lemma hom_ext {Z : C} {a b : Z ⟶ hf.pullback g}
    (h₁ : yoneda.map a ≫ (hf.pullbackIso g).hom ≫ pullback.fst =
      yoneda.map b ≫ (hf.pullbackIso g).hom ≫ pullback.fst)
    (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b := by
  apply yoneda.map_injective
  rw [← cancel_mono (hf.pullbackIso g).hom]
  ext1
  · simpa using h₁
  · simpa [yoneda_map_snd] using yoneda.congr_map h₂

@[ext]
lemma hom_ext' {Z : C} {a b : Z ⟶ hf'.pullback g}
    (h₁ : a ≫ hf'.fst g = b ≫ hf'.fst g)
    (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b :=
  hf'.hom_ext (by simpa [yoneda_map_fst] using yoneda.congr_map h₁) h₂

section

variable {Z : C} (i : yoneda.obj Z ⟶ F) (h : Z ⟶ X)
    (hi : i ≫ f = yoneda.map h ≫ g)

noncomputable def lift : Z ⟶ hf.pullback g :=
  Yoneda.fullyFaithful.preimage <| Limits.pullback.lift _ _ hi ≫ (hf.pullbackIso g).inv

@[reassoc (attr := simp)]
lemma lift_fst : yoneda.map (hf.lift i h hi) ≫
    (hf.pullbackIso g).hom ≫ pullback.fst = i := by simp [lift]

@[reassoc (attr := simp)]
lemma lift_snd : hf.lift i h hi ≫ hf.snd g = h :=
  yoneda.map_injective (by simp [yoneda_map_snd, lift])

end

section

variable {Z : C} (i : Z ⟶ Y) (h : Z ⟶ X) (hi : (yoneda.map i) ≫ f' = yoneda.map h ≫ g)

noncomputable def lift' : Z ⟶ hf'.pullback g := hf'.lift _ _ hi

@[reassoc (attr := simp)]
lemma lift'_fst : hf'.lift' i h hi ≫ hf'.fst g = i :=
  yoneda.map_injective (by simp [yoneda_map_fst, lift'])

@[reassoc (attr := simp)]
lemma lift'_snd : hf'.lift' i h hi ≫ hf'.snd g = h := by
  simp [lift']

end

noncomputable def symmetry : hf'.pullback g ⟶ hg.pullback f' :=
  hg.lift' (hf'.snd g) (hf'.fst g) (condition _ _).symm

@[reassoc (attr := simp)]
lemma symmetry_fst : hf'.symmetry hg ≫ hg.fst f' = hf'.snd g := by simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_snd : hf'.symmetry hg ≫ hg.snd f' = hf'.fst g := by simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_symmetry : hf'.symmetry hg ≫ hg.symmetry hf' = 𝟙 _ := by aesop_cat

@[simps]
noncomputable def symmetryIso : hf'.pullback g ≅ hg.pullback f' where
  hom := hf'.symmetry hg
  inv := hg.symmetry hf'

instance : IsIso (hf'.symmetry hg) :=
  (hf'.symmetryIso hg).isIso_hom

end

lemma yoneda_map [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    Presheaf.representable (yoneda.map f) := fun Z g ↦ by
  obtain ⟨g, rfl⟩ := yoneda.map_surjective g
  exact ⟨Limits.pullback f g, ⟨PreservesPullback.iso _ _ _⟩⟩

end Presheaf.representable

namespace MorphismProperty

variable {F G : Cᵒᵖ ⥤ Type v} (P : MorphismProperty C)

def presheaf : MorphismProperty (Cᵒᵖ ⥤ Type v) :=
  fun _ G f ↦ ∃ (hf : Presheaf.representable f), ∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), P (hf.snd g)

variable {P}

lemma presheaf.representable {f : F ⟶ G} (hf : P.presheaf f) : Presheaf.representable f :=
  hf.choose

lemma presheaf.property {f : F ⟶ G} (hf : P.presheaf f) {X : C} (g : yoneda.obj X ⟶ G) :
    P (hf.choose.snd g) :=
  hf.choose_spec g

-- this lemma is also introduced in PR #10425, this should be moved to CategoryTheory.Yoneda
/-- Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `yoneda.obj X ⟶ P` agree. -/
lemma _root_.CategoryTheory.hom_ext_yoneda {P Q : Cᵒᵖ ⥤ Type v} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (yonedaEquiv) (h _ (yonedaEquiv.symm x))

-- if P is compatible w/ isos/comps/base change, then so is `presheaf P`
-- TODO: yoneda.map f satisfies P if f does

lemma presheaf_monomorphisms_le_monomorphisms :
    (monomorphisms C).presheaf ≤ monomorphisms _ := fun F G f hf ↦ by
  suffices ∀ {X : C} {a b : yoneda.obj X ⟶ F}, a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_yoneda (fun _ _ ↦ this (by simp only [assoc, h]))⟩
  intro X a b h
  suffices hf.representable.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.representable.lift b (𝟙 X) (by simp [← h]) by
    simpa using yoneda.congr_map
      this =≫ ((hf.representable.pullbackIso (a ≫ f)).hom ≫ pullback.fst)
  have : Mono (hf.representable.snd (a ≫ f)) := hf.property (a ≫ f)
  simp only [← cancel_mono (hf.representable.snd (a ≫ f)),
    Presheaf.representable.lift_snd]

lemma presheaf_monotone {P' : MorphismProperty C} (h : P ≤ P') :
    P.presheaf ≤ P'.presheaf := fun _ _ _ hf ↦
  ⟨hf.representable, fun _ g ↦ h _ (hf.property g)⟩


end MorphismProperty

open MorphismProperty Limits

instance : IsStableUnderComposition (Presheaf.representable (C:=C)) where
  comp_mem {F G H} f g hf hg := by
    intro X h
    --let a := Limits.pullback.snd g h
    let H : pullback f (pullback.fst (f:=g) (g:=h)) ≅ pullback (f ≫ g) h :=
      pullbackRightPullbackFstIso g h f
    let a := hg.pullback h
    use hf.pullback (hg.fst_yoneda h)
    refine ⟨hf.pullbackIso (hg.fst_yoneda h) ≪≫ ?_ ≪≫ H⟩
    change pullback f ((hg.pullbackIso h).hom ≫ Limits.pullback.fst) ≅ _

    let φ := asIso <| pullback.fst (f:=(pullback.snd (f:=f) (g:=pullback.fst)))
      (g:=(hg.pullbackIso h).hom)
    refine ?_ ≪≫ φ

    -- need pullbackLeftPullback?Iso?
    sorry
    -- fapply IsPullback.isoPullback
    -- apply pullback.fst
    -- apply pullback.snd ≫ _
    -- apply (hg.pullbackIso h).hom

lemma Representable.StableUnderBaseChange :
    StableUnderBaseChange (Presheaf.representable (C:=C)) := by
  intro F G G' H f g f' g' BC hg X h
  use hg.pullback (h ≫ f)
  refine ⟨hg.pullbackIso (h ≫ f) ≪≫ ?_⟩
  --apply (pullbackAssoc _ _ _ _)

  sorry -- should be easy now if I would know the right lemma

lemma Representable.ofIsIso {F G : Cᵒᵖ ⥤ Type v} (f : F ⟶ G) [IsIso f] : Presheaf.representable f :=
  fun X g ↦ ⟨X, ⟨(asIso <| Limits.pullback.snd (f:=f) (g:=g)).symm⟩⟩

lemma isomorphisms_le : MorphismProperty.isomorphisms (Cᵒᵖ ⥤ Type v) ≤ Presheaf.representable :=
  fun _ _ f hf ↦ letI : IsIso f := hf; Representable.ofIsIso f

lemma Representable.respectsIso : RespectsIso (Presheaf.representable (C:=C)) :=
  ⟨fun _ _ hf ↦ comp_mem _ _ _ (Representable.ofIsIso _) hf,
  fun _ _ hf ↦ comp_mem _ _ _ hf <| Representable.ofIsIso _⟩


end CategoryTheory
