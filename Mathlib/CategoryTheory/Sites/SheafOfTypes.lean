/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.IsSheafFor

#align_import category_theory.sites.sheaf_of_types from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Sheaves of types on a Grothendieck topology

Defines the notion of a sheaf of types (usually called a sheaf of sets by mathematicians)
on a category equipped with a Grothendieck topology, as well as a range of equivalent
conditions useful in different situations.

In `Mathlib/CategoryTheory/Sites/IsSheafFor.lean` it is defined what it means for a presheaf to be a
sheaf *for* a particular sieve. Given a Grothendieck topology `J`, `P` is a sheaf if it is a sheaf
for every sieve in the topology. See `IsSheaf`.

In the case where the topology is generated by a basis, it suffices to check `P` is a sheaf for
every presieve in the pretopology. See `isSheaf_pretopology`.

We also provide equivalent conditions to satisfy alternate definitions given in the literature.

* Stacks: In `Equalizer.Presieve.sheaf_condition`, the sheaf condition at a presieve is shown to be
  equivalent to that of https://stacks.math.columbia.edu/tag/00VM (and combined with
  `isSheaf_pretopology`, this shows the notions of `IsSheaf` are exactly equivalent.)

  The condition of https://stacks.math.columbia.edu/tag/00Z8 is virtually identical to the
  statement of `isSheafFor_iff_yonedaSheafCondition` (since the bijection described there carries
  the same information as the unique existence.)

* Maclane-Moerdijk [MM92]: Using `compatible_iff_sieveCompatible`, the definitions of `IsSheaf`
  are equivalent. There are also alternate definitions given:
  - Sheaf for a pretopology (Prop 1): `isSheaf_pretopology` combined with `pullbackCompatible_iff`.
  - Sheaf for a pretopology as equalizer (Prop 1, bis): `Equalizer.Presieve.sheaf_condition`
    combined with the previous.

## References

* [MM92]: *Sheaves in geometry and logic*, Saunders MacLane, and Ieke Moerdijk:
  Chapter III, Section 4.
* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1.
* https://stacks.math.columbia.edu/tag/00VL (sheaves on a pretopology or site)
* https://stacks.math.columbia.edu/tag/00ZB (sheaves on a topology)

-/


universe w v u

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presieve

variable {C : Type u} [Category.{v} C]
variable {P : Cᵒᵖ ⥤ Type w}
variable {X : C}
variable (J J₂ : GrothendieckTopology C)

/-- A presheaf is separated for a topology if it is separated for every sieve in the topology. -/
def IsSeparated (P : Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ {X} (S : Sieve X), S ∈ J X → IsSeparatedFor P (S : Presieve X)
#align category_theory.presieve.is_separated CategoryTheory.Presieve.IsSeparated

/-- A presheaf is a sheaf for a topology if it is a sheaf for every sieve in the topology.

If the given topology is given by a pretopology, `isSheaf_pretopology` shows it suffices to
check the sheaf condition at presieves in the pretopology.
-/
def IsSheaf (P : Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ ⦃X⦄ (S : Sieve X), S ∈ J X → IsSheafFor P (S : Presieve X)
#align category_theory.presieve.is_sheaf CategoryTheory.Presieve.IsSheaf

theorem IsSheaf.isSheafFor {P : Cᵒᵖ ⥤ Type w} (hp : IsSheaf J P) (R : Presieve X)
    (hr : generate R ∈ J X) : IsSheafFor P R :=
  (isSheafFor_iff_generate R).2 <| hp _ hr
#align category_theory.presieve.is_sheaf.is_sheaf_for CategoryTheory.Presieve.IsSheaf.isSheafFor

theorem isSheaf_of_le (P : Cᵒᵖ ⥤ Type w) {J₁ J₂ : GrothendieckTopology C} :
    J₁ ≤ J₂ → IsSheaf J₂ P → IsSheaf J₁ P := fun h t _ S hS => t S (h _ hS)
#align category_theory.presieve.is_sheaf_of_le CategoryTheory.Presieve.isSheaf_of_le

theorem isSeparated_of_isSheaf (P : Cᵒᵖ ⥤ Type w) (h : IsSheaf J P) : IsSeparated J P :=
  fun S hS => (h S hS).isSeparatedFor
#align category_theory.presieve.is_separated_of_is_sheaf CategoryTheory.Presieve.isSeparated_of_isSheaf

/-- The property of being a sheaf is preserved by isomorphism. -/
theorem isSheaf_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (h : IsSheaf J P) : IsSheaf J P' :=
  fun _ S hS => isSheafFor_iso i (h S hS)
#align category_theory.presieve.is_sheaf_iso CategoryTheory.Presieve.isSheaf_iso

theorem isSheaf_of_yoneda {P : Cᵒᵖ ⥤ Type v}
    (h : ∀ {X} (S : Sieve X), S ∈ J X → YonedaSheafCondition P S) : IsSheaf J P := fun _ _ hS =>
  isSheafFor_iff_yonedaSheafCondition.2 (h _ hS)
#align category_theory.presieve.is_sheaf_of_yoneda CategoryTheory.Presieve.isSheaf_of_yoneda

/-- For a topology generated by a basis, it suffices to check the sheaf condition on the basis
presieves only.
-/
theorem isSheaf_pretopology [HasPullbacks C] (K : Pretopology C) :
    IsSheaf (K.toGrothendieck C) P ↔ ∀ {X : C} (R : Presieve X), R ∈ K X → IsSheafFor P R := by
  constructor
  · intro PJ X R hR
    rw [isSheafFor_iff_generate]
    apply PJ (Sieve.generate R) ⟨_, hR, le_generate R⟩
  · rintro PK X S ⟨R, hR, RS⟩
    have gRS : ⇑(generate R) ≤ S := by
      apply giGenerate.gc.monotone_u
      rwa [sets_iff_generate]
    apply isSheafFor_subsieve P gRS _
    intro Y f
    rw [← pullbackArrows_comm, ← isSheafFor_iff_generate]
    exact PK (pullbackArrows f R) (K.pullbacks f R hR)
#align category_theory.presieve.is_sheaf_pretopology CategoryTheory.Presieve.isSheaf_pretopology

/-- Any presheaf is a sheaf for the bottom (trivial) grothendieck topology. -/
theorem isSheaf_bot : IsSheaf (⊥ : GrothendieckTopology C) P := fun X => by
  simp [isSheafFor_top_sieve]
#align category_theory.presieve.is_sheaf_bot CategoryTheory.Presieve.isSheaf_bot

/--
For a presheaf of the form `yoneda.obj W`, a compatible family of elements on a sieve
is the same as a co-cone over the sieve. Constructing a co-cone from a compatible family works for
any presieve, as does constructing a family of elements from a co-cone. Showing compatibility of the
family needs the sieve condition.
Note: This is related to `CategoryTheory.Presheaf.conesEquivSieveCompatibleFamily`
 -/

def compatibleYonedaFamily_toCocone (R : Presieve X) (W : C) (x : FamilyOfElements (yoneda.obj W) R)
    (hx : FamilyOfElements.Compatible x) :
    Cocone (R.diagram) where
  pt := W
  ι :=
    { app := fun f => x f.obj.hom f.property
      naturality := by
        intro g₁ g₂ F
        simp only [Functor.id_obj, Functor.comp_obj, fullSubcategoryInclusion.obj, Over.forget_obj,
          Functor.const_obj_obj, Functor.comp_map, fullSubcategoryInclusion.map, Over.forget_map,
          Functor.const_obj_map, Category.comp_id]
        rw [← Category.id_comp (x g₁.obj.hom g₁.property)]
        apply hx
        simp only [Functor.id_obj, Over.w, Opposite.unop_op, Category.id_comp] }

def yonedaFamilyOfElements_fromCocone (R : Presieve X) (s : Cocone (diagram R)) :
    FamilyOfElements (yoneda.obj s.pt) R :=
  fun _ f hf => s.ι.app ⟨Over.mk f, hf⟩

end Presieve

namespace Sieve
open Presieve

variable {C : Type u} [Category.{v} C]
variable {X : C}

theorem yonedaFamily_fromCocone_compatible (S : Sieve X) (s : Cocone (diagram S.arrows)) :
    FamilyOfElements.Compatible <| yonedaFamilyOfElements_fromCocone S.arrows s := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hgf
  have Hs := s.ι.naturality
  simp only [Functor.id_obj, yoneda_obj_obj, Opposite.unop_op, yoneda_obj_map, Quiver.Hom.unop_op]
  dsimp [yonedaFamilyOfElements_fromCocone]
  have hgf₁ : S.arrows (g₁ ≫ f₁) := by exact Sieve.downward_closed S hf₁ g₁
  have hgf₂ : S.arrows (g₂ ≫ f₂) := by exact Sieve.downward_closed S hf₂ g₂
  let F : (Over.mk (g₁ ≫ f₁) : Over X) ⟶ (Over.mk (g₂ ≫ f₂) : Over X) := Over.homMk (𝟙 Z)
  let F₁ : (Over.mk (g₁ ≫ f₁) : Over X) ⟶ (Over.mk f₁ : Over X) := Over.homMk g₁
  let F₂ : (Over.mk (g₂ ≫ f₂) : Over X) ⟶ (Over.mk f₂ : Over X) := Over.homMk g₂
  have hF := @Hs ⟨Over.mk (g₁ ≫ f₁), hgf₁⟩ ⟨Over.mk (g₂ ≫ f₂), hgf₂⟩ F
  have hF₁ := @Hs ⟨Over.mk (g₁ ≫ f₁), hgf₁⟩ ⟨Over.mk f₁, hf₁⟩ F₁
  have hF₂ := @Hs ⟨Over.mk (g₂ ≫ f₂), hgf₂⟩ ⟨Over.mk f₂, hf₂⟩ F₂
  aesop_cat

/--
The base of a sieve `S` is a colimit of `S` iff all Yoneda-presheaves satisfy
the sheaf condition for `S`.
-/
theorem forallYonedaIsSheaf_iff_colimit (S : Sieve X) :
    (∀ W : C, Presieve.IsSheafFor (yoneda.obj W) (S : Presieve X)) ↔
      Nonempty (IsColimit S.arrows.cocone) := by
  constructor
  · intro H
    refine Nonempty.intro ?_
    exact
    { desc := fun s => H s.pt (yonedaFamilyOfElements_fromCocone S.arrows s)
        (yonedaFamily_fromCocone_compatible S s) |>.choose
      fac := by
        intro s f
        replace H := H s.pt (yonedaFamilyOfElements_fromCocone S.arrows s)
          (yonedaFamily_fromCocone_compatible S s)
        have ht := H.choose_spec.1 f.obj.hom f.property
        aesop_cat
      uniq := by
        intro s Fs HFs
        replace H := H s.pt (yonedaFamilyOfElements_fromCocone S.arrows s)
          (yonedaFamily_fromCocone_compatible S s)
        apply H.choose_spec.2 Fs
        exact fun _ f hf => HFs ⟨Over.mk f, hf⟩ }
  · intro H W x hx
    replace H := Classical.choice H
    let s := compatibleYonedaFamily_toCocone S W x hx
    use H.desc s
    constructor
    · exact fun _ f hf => (H.fac s) ⟨Over.mk f, hf⟩
    · exact fun g hg => H.uniq s g (fun ⟨⟨f, _, hom⟩, hf⟩ => hg hom hf)

end Sieve

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/-- The category of sheaves on a grothendieck topology. -/
structure SheafOfTypes (J : GrothendieckTopology C) : Type max u v (w + 1) where
  /-- the underlying presheaf -/
  val : Cᵒᵖ ⥤ Type w
  /-- the condition that the presheaf is a sheaf -/
  cond : Presieve.IsSheaf J val
set_option linter.uppercaseLean3 false in
#align category_theory.SheafOfTypes CategoryTheory.SheafOfTypes

namespace SheafOfTypes

variable {J}

/-- Morphisms between sheaves of types are just morphisms between the underlying presheaves. -/
@[ext]
structure Hom (X Y : SheafOfTypes J) where
  /-- a morphism between the underlying presheaves -/
  val : X.val ⟶ Y.val
set_option linter.uppercaseLean3 false in
#align category_theory.SheafOfTypes.hom CategoryTheory.SheafOfTypes.Hom

@[simps]
instance : Category (SheafOfTypes J) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.val ≫ g.val⟩
  id_comp _ := Hom.ext _ _ <| id_comp _
  comp_id _ := Hom.ext _ _ <| comp_id _
  assoc _ _ _ := Hom.ext _ _ <| assoc _ _ _

-- Porting note: we need to restate the ext lemma in terms of the categorical morphism
-- not just the underlying structure.
-- It would be nice if this boilerplate weren't necessary.
@[ext]
theorem Hom.ext' {X Y : SheafOfTypes J} (f g : X ⟶ Y) (w : f.val = g.val) : f = g :=
  Hom.ext f g w

-- Let's make the inhabited linter happy...
instance (X : SheafOfTypes J) : Inhabited (Hom X X) :=
  ⟨𝟙 X⟩

end SheafOfTypes

/-- The inclusion functor from sheaves to presheaves. -/
@[simps]
def sheafOfTypesToPresheaf : SheafOfTypes J ⥤ Cᵒᵖ ⥤ Type w where
  obj := SheafOfTypes.val
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl
set_option linter.uppercaseLean3 false in
#align category_theory.SheafOfTypes_to_presheaf CategoryTheory.sheafOfTypesToPresheaf

instance : (sheafOfTypesToPresheaf J).Full where preimage f := ⟨f⟩

instance : (sheafOfTypesToPresheaf J).Faithful where

/--
The category of sheaves on the bottom (trivial) grothendieck topology is equivalent to the category
of presheaves.
-/
@[simps]
def sheafOfTypesBotEquiv : SheafOfTypes (⊥ : GrothendieckTopology C) ≌ Cᵒᵖ ⥤ Type w where
  functor := sheafOfTypesToPresheaf _
  inverse :=
    { obj := fun P => ⟨P, Presieve.isSheaf_bot⟩
      map := fun f => (sheafOfTypesToPresheaf _).preimage f }
  unitIso :=
    { hom := { app := fun _ => ⟨𝟙 _⟩ }
      inv := { app := fun _ => ⟨𝟙 _⟩ } }
  counitIso := Iso.refl _
set_option linter.uppercaseLean3 false in
#align category_theory.SheafOfTypes_bot_equiv CategoryTheory.sheafOfTypesBotEquiv

instance : Inhabited (SheafOfTypes (⊥ : GrothendieckTopology C)) :=
  ⟨sheafOfTypesBotEquiv.inverse.obj ((Functor.const _).obj PUnit)⟩

end CategoryTheory
