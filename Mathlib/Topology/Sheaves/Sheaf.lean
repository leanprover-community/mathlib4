/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Spaces

#align_import topology.sheaves.sheaf from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category.

A presheaf on a topological space `X` is a sheaf precisely when it is a sheaf under the
grothendieck topology on `opens X`, which expands out to say: For each open cover `{ Uᵢ }` of
`U`, and a family of compatible functions `A ⟶ F(Uᵢ)` for an `A : X`, there exists a unique
gluing `A ⟶ F(U)` compatible with the restriction.

See the docstring of `TopCat.Presheaf.IsSheaf` for an explanation on the design decisions and a list
of equivalent conditions.

We provide the instance `CategoryTheory.Category (TopCat.Sheaf C X)` as the full subcategory of
presheaves, and the fully faithful functor `Sheaf.forget : TopCat.Sheaf C X ⥤ TopCat.Presheaf C X`.

-/


universe w v u

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}} (F : Presheaf C X) {ι : Type v} (U : ι → Opens X)

namespace Presheaf

/-- The sheaf condition has several different equivalent formulations.
The official definition chosen here is in terms of grothendieck topologies so that the results on
sites could be applied here easily, and this condition does not require additional constraints on
the value category.
The equivalent formulations of the sheaf condition on `presheaf C X` are as follows :

1. `TopCat.Presheaf.IsSheaf`: (the official definition)
  It is a sheaf with respect to the grothendieck topology on `opens X`, which is to say:
  For each open cover `{ Uᵢ }` of `U`, and a family of compatible functions `A ⟶ F(Uᵢ)` for an
  `A : X`, there exists a unique gluing `A ⟶ F(U)` compatible with the restriction.

2. `TopCat.Presheaf.IsSheafEqualizerProducts`: (requires `C` to have all products)
  For each open cover `{ Uᵢ }` of `U`, `F(U) ⟶ ∏ᶜ F(Uᵢ)` is the equalizer of the two morphisms
  `∏ᶜ F(Uᵢ) ⟶ ∏ᶜ F(Uᵢ ∩ Uⱼ)`.
  See `TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts`.

3. `TopCat.Presheaf.IsSheafOpensLeCover`:
  For each open cover `{ Uᵢ }` of `U`, `F(U)` is the limit of the diagram consisting of arrows
  `F(V₁) ⟶ F(V₂)` for every pair of open sets `V₁ ⊇ V₂` that are contained in some `Uᵢ`.
  See `TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`.

4. `TopCat.Presheaf.IsSheafPairwiseIntersections`:
  For each open cover `{ Uᵢ }` of `U`, `F(U)` is the limit of the diagram consisting of arrows
  from `F(Uᵢ)` and `F(Uⱼ)` to `F(Uᵢ ∩ Uⱼ)` for each pair `(i, j)`.
  See `TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections`.

The following requires `C` to be concrete and complete, and `forget C` to reflect isomorphisms and
preserve limits. This applies to most "algebraic" categories, e.g. groups, abelian groups and rings.

5. `TopCat.Presheaf.IsSheafUniqueGluing`:
  (requires `C` to be concrete and complete; `forget C` to reflect isomorphisms and preserve limits)
  For each open cover `{ Uᵢ }` of `U`, and a compatible family of elements `x : F(Uᵢ)`, there exists
  a unique gluing `x : F(U)` that restricts to the given elements.
  See `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`.

6. The underlying sheaf of types is a sheaf.
  See `TopCat.Presheaf.isSheaf_iff_isSheaf_comp` and
  `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`.
-/
nonrec def IsSheaf (F : Presheaf.{w, v, u} C X) : Prop :=
  Presheaf.IsSheaf (Opens.grothendieckTopology X) F
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf TopCat.Presheaf.IsSheaf

/-- The presheaf valued in `Unit` over any topological space is a sheaf.
-/
theorem isSheaf_unit (F : Presheaf (CategoryTheory.Discrete Unit) X) : F.IsSheaf :=
  fun x U S _ x _ => ⟨eqToHom (Subsingleton.elim _ _), by aesop_cat, fun _ => by aesop_cat⟩
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_unit TopCat.Presheaf.isSheaf_unit

theorem isSheaf_iso_iff {F G : Presheaf C X} (α : F ≅ G) : F.IsSheaf ↔ G.IsSheaf :=
  Presheaf.isSheaf_of_iso_iff α
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_iso_iff TopCat.Presheaf.isSheaf_iso_iff

/-- Transfer the sheaf condition across an isomorphism of presheaves.
-/
theorem isSheaf_of_iso {F G : Presheaf C X} (α : F ≅ G) (h : F.IsSheaf) : G.IsSheaf :=
  (isSheaf_iso_iff α).1 h
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_of_iso TopCat.Presheaf.isSheaf_of_iso

end Presheaf

variable (C X)

/-- A `TopCat.Sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
nonrec def Sheaf : Type max u v w :=
  Sheaf (Opens.grothendieckTopology X) C
set_option linter.uppercaseLean3 false in
#align Top.sheaf TopCat.Sheaf

-- Porting note: `deriving Cat` failed
instance SheafCat : Category (Sheaf C X) :=
  show Category (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C) from inferInstance

variable {C X}

/-- The underlying presheaf of a sheaf -/
abbrev Sheaf.presheaf (F : X.Sheaf C) : TopCat.Presheaf C X :=
  F.1
set_option linter.uppercaseLean3 false in
#align Top.sheaf.presheaf TopCat.Sheaf.presheaf

variable (C X)

-- Let's construct a trivial example, to keep the inhabited linter happy.
instance sheafInhabited : Inhabited (Sheaf (CategoryTheory.Discrete PUnit) X) :=
  ⟨⟨Functor.star _, Presheaf.isSheaf_unit _⟩⟩
set_option linter.uppercaseLean3 false in
#align Top.sheaf_inhabited TopCat.sheafInhabited

namespace Sheaf

/-- The forgetful functor from sheaves to presheaves.
-/
def forget : TopCat.Sheaf C X ⥤ TopCat.Presheaf C X :=
  sheafToPresheaf _ _
set_option linter.uppercaseLean3 false in
#align Top.sheaf.forget TopCat.Sheaf.forget

-- Porting note: `deriving Full` failed
instance forget_full : (forget C X).Full where
  map_surjective f := ⟨Sheaf.Hom.mk f, rfl⟩

-- Porting note: `deriving Faithful` failed
instance forgetFaithful : (forget C X).Faithful where
  map_injective := Sheaf.Hom.ext _ _

-- Note: These can be proved by simp.
theorem id_app (F : Sheaf C X) (t) : (𝟙 F : F ⟶ F).1.app t = 𝟙 _ :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top.sheaf.id_app TopCat.Sheaf.id_app

theorem comp_app {F G H : Sheaf C X} (f : F ⟶ G) (g : G ⟶ H) (t) :
    (f ≫ g).1.app t = f.1.app t ≫ g.1.app t :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top.sheaf.comp_app TopCat.Sheaf.comp_app

end Sheaf

end TopCat
