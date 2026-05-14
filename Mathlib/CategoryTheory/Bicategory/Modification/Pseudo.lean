/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Modification.Oplax
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Modifications between transformations of pseudofunctors

In this file we define modifications of strong transformations of pseudofunctors. They are defined
similarly to modifications of transformations of oplax functors.

## Main definitions

Given two pseudofunctors `F` and `G`, we define:

* `Pseudofunctor.StrongTrans.Modification η θ` : modifications between strong transformations
  `η` and `θ` (between `F` and `G`).
* `Pseudofunctor.StrongTrans.homCategory F G` : the category structure on strong transformations
  between `F` and `G`, where the morphisms are modifications, and composition is given by vertical
  composition of modifications. Note that this a scoped instance in the `Pseudofunctor.StrongTrans`
  namespace, so you need to run `open scoped Pseudofunctor.StrongTrans` to access it.

-/

@[expose] public section

namespace CategoryTheory.Pseudofunctor

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : Pseudofunctor B C}

namespace StrongTrans

variable (η θ : F ⟶ G)

/-- A modification `Γ` between strong transformations (of pseudofunctors) `η` and `θ` consists of a
family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
structure Modification where
  /-- The underlying family of 2-morphism. -/
  app (a : B) : η.app a ⟶ θ.app a
  /-- The naturality condition. -/
  naturality {a b : B} (f : a ⟶ b) :
      F.map f ◁ app b ≫ (θ.naturality f).hom =
        (η.naturality f).hom ≫ app a ▷ G.map f := by cat_disch

attribute [reassoc (attr := simp)] Modification.naturality

variable {η θ}

namespace Modification

variable (Γ : Modification η θ)

set_option backward.isDefEq.respectTransparency false in
/-- The modification between the corresponding strong transformation of the underlying oplax
functors. -/
@[simps]
def toOplax : Oplax.StrongTrans.Modification η.toOplax θ.toOplax where
  app a := Γ.app a

instance hasCoeToOplax :
    Coe (Modification η θ) (Oplax.StrongTrans.Modification η.toOplax θ.toOplax) :=
  ⟨toOplax⟩

/-- The modification between strong transformations of pseudofunctors associated to a modification
between the underlying strong transformations of oplax functors. -/
@[simps]
def mkOfOplax (Γ : Oplax.StrongTrans.Modification η.toOplax θ.toOplax) : Modification η θ where
  app a := Γ.app a
  naturality f := Γ.naturality f

/-- Modifications between strong transformations of pseudofunctors are equivalent to modifications
between the underlying strong transformations of oplax functors. -/
@[simps]
def equivOplax : (Oplax.StrongTrans.Modification η.toOplax θ.toOplax) ≃ Modification η θ where
  toFun := mkOfOplax
  invFun := toOplax
  left_inv _ := rfl
  right_inv _ := rfl

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ (θ.naturality g).hom =
      f ◁ (η.naturality g).hom ≫ f ◁ Γ.app b ▷ G.map g :=
  Oplax.StrongTrans.Modification.whiskerLeft_naturality Γ.toOplax _ _

@[reassoc (attr := simp)]
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    F.map f ◁ Γ.app b ▷ g ≫ (α_ _ _ _).inv ≫ (θ.naturality f).hom ▷ g =
      (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ g ≫ Γ.app a ▷ G.map f ▷ g :=
  Oplax.StrongTrans.Modification.whiskerRight_naturality Γ.toOplax _ _

end

variable (η) in
/-- The identity modification. -/
@[simps]
def id : Modification η η where app a := 𝟙 (η.app a)

instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
def vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) : Modification η ι where
  app a := Γ.app a ≫ Δ.app a

end Modification

variable (η θ) in
/-- Type-alias for modifications between strong transformations of pseudofunctors. This is the type
used for the 2-homomorphisms in the bicategory of pseudofunctors. -/
@[ext]
structure Hom where
  of ::
  /-- The underlying modification of strong transformations. -/
  as : Modification η θ

/-- Category structure on the strong transformations between pseudofunctors.

Note that this a scoped instance in the `Pseudofunctor.StrongTrans` namespace. -/
@[simps!]
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id Γ := ⟨Modification.id Γ⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩

instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
lemma homCategory.ext {m n : η ⟶ θ} (w : ∀ b, m.as.app b = n.as.app b) : m = n :=
  Hom.ext <| Modification.ext <| funext w

/-- Construct a modification isomorphism between strong transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
def isoMk (app : ∀ a, η.app a ≅ θ.app a)
    (naturality : ∀ {a b} (f : a ⟶ b),
      F.map f ◁ (app b).hom ≫ (θ.naturality f).hom =
        (η.naturality f).hom ≫ (app a).hom ▷ G.map f := by cat_disch) :
    η ≅ θ where
  hom.as.app a := (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using _ ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ _

end StrongTrans

end CategoryTheory.Pseudofunctor
