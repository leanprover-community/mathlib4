import Mathlib.CategoryTheory.Sites.Pullback

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Limits

instance {C D E : Type*} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    PreservesFiniteLimits (F ⋙ G) := ⟨fun _ _ _ => inferInstance⟩

instance {C D E : Type*} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] :
    PreservesFiniteColimits (F ⋙ G) := ⟨fun _ _ _ => inferInstance⟩

end Limits

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] (J : GrothendieckTopology C)
  (K : GrothendieckTopology D) {L : GrothendieckTopology E}

/-- SGA 4 IV 4.9 -/
structure SitesHom where
  functor : D ⥤ C
  [isContinuous : Functor.IsContinuous functor K J]
  pullbackTypes : Sheaf K (Type w) ⥤ Sheaf J (Type w)
  adjTypes : pullbackTypes ⊣ functor.sheafPushforwardContinuous (Type w) K J
  [preservesFiniteLimits : PreservesFiniteLimits pullbackTypes]

namespace SitesHom

attribute [instance] isContinuous preservesFiniteLimits

@[simps!]
def pushforward (f : SitesHom.{w} J K) (A : Type*) [Category.{w} A] :
    Sheaf J A ⥤ Sheaf K A := f.functor.sheafPushforwardContinuous A K J

@[simps]
noncomputable def id : SitesHom J J where
  functor := 𝟭 C
  pullbackTypes := 𝟭 (Sheaf J (Type w))
  adjTypes := Adjunction.id

variable {J K}

@[simps]
def comp (f : SitesHom J K) (g : SitesHom K L) : SitesHom J L where
  functor := g.functor ⋙ f.functor
  isContinuous := Functor.isContinuous_comp g.functor f.functor L K J
  pullbackTypes := g.pullbackTypes ⋙ f.pullbackTypes
  adjTypes := g.adjTypes.comp f.adjTypes

def pushforwardComp (f : SitesHom.{w} J K) (g : SitesHom.{w} K L) (A : Type*) [Category.{w} A] :
    (f.comp g).pushforward A ≅ f.pushforward A ⋙ g.pushforward A := Iso.refl _

abbrev HasPullback (f : SitesHom.{w} J K) (A : Type*) [Category.{w} A] :=
  IsRightAdjoint (f.pushforward A)

instance (f : SitesHom.{w} J K) : f.HasPullback (Type w) where
  left := f.pullbackTypes
  adj := f.adjTypes

section

variable (f : SitesHom.{w} J K) (g : SitesHom.{w} K L)
  (A : Type*) [Category.{w} A] [f.HasPullback A] [g.HasPullback A]
  [(f.comp g).HasPullback A]

def pullback : Sheaf K A ⥤ Sheaf J A := leftAdjoint (f.pushforward A)

def adj : f.pullback A ⊣ f.pushforward A := Adjunction.ofRightAdjoint _

def pullbackComp : (f.comp g).pullback A ≅ g.pullback A ⋙ f.pullback A :=
  Adjunction.leftAdjointUniq ((f.comp g).adj A) ((g.adj A).comp (f.adj A))

end

/-- SGA 4 IV 4.9.3 -/
instance : Category (SitesHom.{w} J K) :=
  InducedCategory.category (fun f => Opposite.op f.functor)

namespace Hom

@[simp]
lemma unop_id (f : SitesHom.{w} J K) : (𝟙 f).unop = 𝟙 _ := rfl

@[simp, reassoc]
lemma unop_comp {f g h : SitesHom.{w} J K} (α : f ⟶ g) (β : g ⟶ h) :
    (α ≫ β).unop = β.unop ≫ α.unop := rfl

end Hom

variable (J K)

@[simps]
def mapPushforward (A : Type*) [Category.{w} A] :
    SitesHom.{w} J K ⥤ (Sheaf J A ⥤ Sheaf K A) where
  obj f := f.pushforward A
  map {f g} φ := { app := fun F => ⟨whiskerRight (NatTrans.op φ.unop) _⟩ }

section

variable {C' : Type v₁} [SmallCategory C'] {D' : Type v₁} [SmallCategory D']
   (G : D' ⥤ C') (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
   [Functor.IsContinuous.{v₁} G K' J'] [RepresentablyFlat G]

@[simps]
noncomputable def mk' : SitesHom.{v₁} J' K' where
  functor := G
  pullbackTypes := G.sheafPullback (Type v₁) K' J'
  adjTypes := G.sheafAdjunctionContinuous (Type v₁) K' J'

variable (A : Type u₁) [Category.{v₁} A]
  [ConcreteCategory.{v₁} A] [PreservesLimits (forget A)] [HasColimits A] [HasLimits A]
  [PreservesFilteredColimits (forget A)] [ReflectsIsomorphisms (forget A)]

noncomputable instance : (mk' G  J' K').HasPullback A where
  adj := G.sheafAdjunctionContinuous A K' J'

end

end SitesHom

end CategoryTheory
