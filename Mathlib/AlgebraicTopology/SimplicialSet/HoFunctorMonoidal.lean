/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed

/-!
# The homotopy functor is monoidal

-/

universe u

open CategoryTheory MonoidalCategory Simplicial SimplicialObject.Truncated
  CartesianMonoidalCategory Limits

namespace SSet

namespace Truncated

namespace Edge

variable {X Y : Truncated.{u} 2}

/-- The external product of edges of `2`-truncated simplicial sets. -/
@[simps]
def tensor {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    Edge (X := X ⊗ Y) (x, y) (x', y') where
  edge := (e₁.edge, e₂.edge)
  src_eq := Prod.ext e₁.src_eq e₂.src_eq
  tgt_eq := Prod.ext e₁.tgt_eq e₂.tgt_eq

lemma tensor_surjective {x x' : X _⦋0⦌₂} {y y' : Y _⦋0⦌₂}
    (e : Edge (X := X ⊗ Y) (x, y) (x', y')) :
    ∃ (e₁ : Edge x x') (e₂ : Edge y y'), e₁.tensor e₂ = e :=
  ⟨e.map (fst _ _), e.map (snd _ _), rfl⟩

@[simp]
lemma id_tensor_id (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (id x).tensor (id y) = id (X := X ⊗ Y) (x, y):= rfl

/-- The external product of `CompStruct` between edges of `2`-truncated simplicial sets. -/
@[simps simplex_fst simplex_snd]
def CompStruct.tensor
    {x₀ x₁ x₂ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (hx : CompStruct e₀₁ e₁₂ e₀₂)
    {y₀ y₁ y₂ : Y _⦋0⦌₂} {e'₀₁ : Edge y₀ y₁} {e'₁₂ : Edge y₁ y₂} {e'₀₂ : Edge y₀ y₂}
    (hy : CompStruct e'₀₁ e'₁₂ e'₀₂) :
    CompStruct (e₀₁.tensor e'₀₁) (e₁₂.tensor e'₁₂) (e₀₂.tensor e'₀₂) where
  simplex := (hx.simplex, hy.simplex)
  d₂ := Prod.ext hx.d₂ hy.d₂
  d₀ := Prod.ext hx.d₀ hy.d₀
  d₁ := Prod.ext hx.d₁ hy.d₁

end Edge

namespace HomotopyCategory

lemma square {X Y : Truncated.{u} 2}
    {x₀ x₁ : X _⦋0⦌₂} (ex : Edge x₀ x₁) {y₀ y₁ : Y _⦋0⦌₂} (ey : Edge y₀ y₁) :
    homMk (ex.tensor (.id y₀)) ≫ homMk (Edge.tensor (.id x₁) ey) =
      homMk (Edge.tensor (.id x₀) ey) ≫ homMk (ex.tensor (.id y₁)) := by
  rw [homMk_comp_homMk ((Edge.CompStruct.idComp ex).tensor (Edge.CompStruct.compId ey)),
    homMk_comp_homMk ((Edge.CompStruct.compId ex).tensor (Edge.CompStruct.idComp ey))]

namespace BinaryProduct

variable {X Y : Truncated.{u} 2}

variable (X Y) in
/-- The functor `(X ⊗ Y).HomotopyCategory ⥤ X.HomotopyCategory × Y.HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
def functor : (X ⊗ Y).HomotopyCategory ⥤ X.HomotopyCategory × Y.HomotopyCategory :=
  (mapHomotopyCategory (fst _ _)).prod' (mapHomotopyCategory (snd _ _))

@[simp]
lemma functor_obj (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functor X Y).obj (mk (x, y)) = (mk x, mk y) := rfl

@[simp]
lemma functor_map {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : Y _⦋0⦌₂} (e' : Edge y₀ y₁) :
    (functor X Y).map (homMk (e.tensor e')) = (homMk e, homMk e') := rfl

variable (X Y) in
/-- The functor `X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
def curriedInverse : X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory :=
  lift (fun x ↦ lift (fun y ↦ mk (x, y)) (fun {y₀ y₁} e ↦ homMk (Edge.tensor (.id _) e)) (by simp)
    (fun {y₀ y₁ y₁ e₀₁ e₁₂ e₀₂ h} ↦ homMk_comp_homMk ((Edge.CompStruct.idCompId x).tensor h)))
    (fun {x₀ x₁} e ↦ mkNatTrans (fun y ↦ homMk (V := X ⊗ Y) (x₀ := (x₀, y))
      (x₁ := (x₁, y)) (e.tensor (.id y))) (fun y₀ y₁ e' ↦ by simp [square]))
    (by cat_disch) (fun {x₀ x₁ x₂ e₀₁ e₁₂ e₀₂} h ↦ by
      ext y
      obtain ⟨y, rfl⟩ := mk_surjective y
      simpa using homMk_comp_homMk (h.tensor (.idCompId y)))

variable (X Y) in
/-- The functor `X.HomotopyCategory × Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
def inverse : X.HomotopyCategory × Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory :=
  Functor.uncurry.obj (curriedInverse X Y)

@[simp]
lemma inverse_obj (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) : (inverse X Y).obj (mk x, mk y) = mk (x, y) := rfl

@[simp]
lemma inverse_map_mkHom_homMk_id {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (y : Y _⦋0⦌₂) :
    (inverse X Y).map (Prod.mkHom (homMk e) (𝟙 (mk y))) = homMk (e.tensor (.id y)) := rfl

@[simp]
lemma inverse_map_mkHom_id_homMk (x : X _⦋0⦌₂) {y₀ y₁ : Y _⦋0⦌₂} (e : Edge y₀ y₁) :
    (inverse X Y).map (Prod.mkHom (𝟙 (mk x)) (homMk e)) = homMk ((Edge.id x).tensor e) := rfl

lemma inverse_map_mkHom_homMk_homMkxxx {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : Y _⦋0⦌₂} (e' : Edge y₀ y₁) :
    (inverse X Y).map (Prod.mkHom (homMk e) (homMk e')) =
      homMk (e.tensor (.id y₀)) ≫ homMk ((Edge.id x₁).tensor e') := rfl

lemma inverse_map_mkHom_homMk_homMk {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : Y _⦋0⦌₂} (e' : Edge y₀ y₁) :
    (inverse X Y).map (Prod.mkHom (homMk e) (homMk e')) = homMk (e.tensor e') :=
  homMk_comp_homMk ((Edge.CompStruct.compId e).tensor (Edge.CompStruct.idComp e'))

variable (X Y) in
/-- Auxiliary definition for `equivalence`. -/
def functorCompInverseIso : functor X Y ⋙ inverse X Y ≅ 𝟭 _ :=
  mkNatIso (fun _ ↦ Iso.refl _) (by
    rintro ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ e
    obtain ⟨ex, ey, rfl⟩ := e.tensor_surjective
    dsimp
    rw [Category.comp_id, Category.id_comp, inverse_map_mkHom_homMk_homMk])

@[simp]
lemma functorCompInverseIso_hom_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functorCompInverseIso X Y).hom.app (mk (x ,y)) = 𝟙 _ := rfl

@[simp]
lemma functorCompInverseIso_inv_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functorCompInverseIso X Y).inv.app (mk (x ,y)) = 𝟙 _ := rfl

variable (X Y) in
/-- Auxiliary definition for `equivalence`. -/
def inverseCompFunctorIso : inverse X Y ⋙ functor X Y ≅ 𝟭 _ :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ Iso.refl _)
      (fun y₀ y₁ e ↦ by
        dsimp
        rw [inverse_map_mkHom_id_homMk]
        cat_disch))
      (fun x₀ x₁ e ↦ by
        ext y : 2
        obtain ⟨y, rfl⟩ := y.mk_surjective
        dsimp
        rw [inverse_map_mkHom_homMk_id]
        cat_disch))

@[simp]
lemma inverseCompFunctorIso_hom_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (inverseCompFunctorIso X Y).hom.app (mk x, mk y) = 𝟙 _ := rfl

@[simp]
lemma inverseCompFunctorIso_inv_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (inverseCompFunctorIso X Y).inv.app (mk x, mk y) = 𝟙 _ := rfl

variable (X Y)

lemma functor_comp_inverse : functor X Y ⋙ inverse X Y = 𝟭 _ :=
  Functor.ext_of_iso (functorCompInverseIso X Y) (fun _ ↦ rfl)

lemma inverse_comp_functor : inverse X Y ⋙ functor X Y = 𝟭 _ :=
  Functor.ext_of_iso (inverseCompFunctorIso X Y) (fun _ ↦ rfl)

/-- The equivalence `(X ⊗ Y).HomotopyCategory ≌ X.HomotopyCategory ⥤ Y.HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
def equivalence :
    (X ⊗ Y).HomotopyCategory ≌ X.HomotopyCategory × Y.HomotopyCategory where
  functor := functor X Y
  inverse := inverse X Y
  unitIso := (functorCompInverseIso X Y).symm
  counitIso := inverseCompFunctorIso X Y

/-- The isomorphism of categories between
`(X ⊗ Y).HomotopyCategory` and `X.HomotopyCategory ⥤ Y.HomotopyCategory`. -/
@[simps]
def iso :
    Cat.of ((X ⊗ Y).HomotopyCategory) ≅ Cat.of (X.HomotopyCategory × Y.HomotopyCategory) where
  hom := functor X Y
  inv := inverse X Y
  hom_inv_id := functor_comp_inverse X Y
  inv_hom_id := inverse_comp_functor X Y

end BinaryProduct

instance {n : ℕ} (d : (SimplexCategory.Truncated n)ᵒᵖ) :
    Unique ((𝟙_ (Truncated.{u} n)).obj d) :=
  inferInstanceAs (Unique PUnit)

/-- The homotopy category of the tensor unit of `Truncated.{u} 2` is isomorphic to
the (chosen) terminal object of `Cat`. -/
def isoTerminal : Cat.of ((𝟙_ (Truncated.{u} 2)).HomotopyCategory) ≅ Cat.chosenTerminal :=
  IsTerminal.uniqueUpToIso (isTerminal _) Cat.chosenTerminalIsTerminal

end HomotopyCategory

open HomotopyCategory.BinaryProduct in
instance : hoFunctor₂.{u}.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (HomotopyCategory.isoTerminal).symm
      μIso X Y := (iso X Y).symm
      μIso_hom_natural_left := sorry
      μIso_hom_natural_right := sorry
      left_unitality := sorry
      right_unitality := sorry
      associativity := sorry }

instance : hoFunctor.{u}.Monoidal :=
  inferInstanceAs ((truncation 2 ⋙ hoFunctor₂).Monoidal)

end Truncated

end SSet
