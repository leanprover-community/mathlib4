/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/

import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
import Mathlib.CategoryTheory.Category.ReflQuiv
import Mathlib.Combinatorics.Quiver.ReflQuiver


/-!

# The homotopy category of a simplicial set

The homotopy category of a simplicial set is defined as a quotient of the free category on its
underlying reflexive quiver (equivalently its one truncation). The quotient imposes an additional
hom relation on this free category, asserting that `f ≫ g = h` whenever `f`, `g`, and `h` are
respectively the 2nd, 0th, and 1st faces of a 2-simplex.

In fact, the associated functor

`SSet.hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ SSet.hoFunctor₂`

is defined by first restricting from simplicial sets to 2-truncated simplicial sets (throwing away
the data that is not used for the construction of the homotopy category) and then composing with an
analogously defined `SSet.hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u,u}` implemented relative to
the syntax of the 2-truncated simplex category.

In the file `Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.lean` we show the functor
`SSet.hoFunctor` to be left adjoint to the nerve by providing an analogous decomposition of the
nerve functor, made by possible by the fact that nerves of categories are 2-coskeletal, and then
composing a pair of adjunctions, which factor through the category of 2-truncated simplicial sets.
-/

namespace SSet
open CategoryTheory Category Limits Functor Opposite Simplicial Nerve
open SimplexCategory.Truncated SimplicialObject.Truncated

universe v u

section

/-- A 2-truncated simplicial set `S` has an underlying refl quiver with `S _⦋0⦌₂` as its underlying
type. -/
def OneTruncation₂ (S : SSet.Truncated 2) := S _⦋0⦌₂

/-- Abbreviations for face maps in the 2-truncated simplex category. -/
abbrev δ₂ {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) :
    (⟨⦋n⦌, hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨⦋n + 1⦌, hn'⟩ := SimplexCategory.δ i

/-- Abbreviations for degeneracy maps in the 2-truncated simplex category. -/
abbrev σ₂ {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) :
    (⟨⦋n+1⦌, hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨⦋n⦌, hn'⟩ := SimplexCategory.σ i

@[reassoc (attr := simp)]
lemma δ₂_zero_comp_σ₂_zero {n} (hn := by decide) (hn' := by decide) :
    δ₂ (n := n) 0 hn hn' ≫ σ₂ 0 hn' hn = 𝟙 _ := SimplexCategory.δ_comp_σ_self

@[reassoc]
lemma δ₂_zero_comp_σ₂_one : δ₂ (0 : Fin 3) ≫ σ₂ 1 = σ₂ 0 ≫ δ₂ 0 :=
  SimplexCategory.δ_comp_σ_of_le (i := 0) (j := 0) (Fin.zero_le _)

@[reassoc (attr := simp)]
lemma δ₂_one_comp_σ₂_zero {n} (hn := by decide) (hn' := by decide) :
    δ₂ (n := n) 1 hn hn' ≫ σ₂ 0 hn' hn = 𝟙 _ := SimplexCategory.δ_comp_σ_succ

@[reassoc (attr := simp)]
lemma δ₂_two_comp_σ₂_one : δ₂ (2 : Fin 3) ≫ σ₂ 1 = 𝟙 _ := SimplexCategory.δ_comp_σ_succ' (by decide)

@[reassoc]
lemma δ₂_two_comp_σ₂_zero : δ₂ (2 : Fin 3) ≫ σ₂ 0 = σ₂ 0 ≫ δ₂ 1 :=
  SimplexCategory.δ_comp_σ_of_gt' (by decide)

/-- The hom-types of the refl quiver underlying a simplicial set `S` are types of edges in `S _⦋1⦌₂`
together with source and target equalities. -/
@[ext]
structure OneTruncation₂.Hom {S : SSet.Truncated 2} (X Y : OneTruncation₂ S) where
  /-- An arrow in `OneTruncation₂.Hom X Y` includes the data of a 1-simplex. -/
  edge : S _⦋1⦌₂
  /-- An arrow in `OneTruncation₂.Hom X Y` includes a source equality. -/
  src_eq : S.map (δ₂ 1).op edge = X
  /-- An arrow in `OneTruncation₂.Hom X Y` includes a target equality. -/
  tgt_eq : S.map (δ₂ 0).op edge = Y

/-- A 2-truncated simplicial set `S` has an underlying refl quiver `SSet.OneTruncation₂ S`. -/
instance (S : SSet.Truncated 2) : ReflQuiver (OneTruncation₂ S) where
  Hom X Y := SSet.OneTruncation₂.Hom X Y
  id X :=
    { edge := S.map (SSet.σ₂ (n := 0) 0).op X
      src_eq := by
        simp only [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_one_comp_σ₂_zero,
          op_id, FunctorToTypes.map_id_apply]
      tgt_eq := by
        simp only [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_zero,
          op_id, FunctorToTypes.map_id_apply] }

@[simp]
lemma OneTruncation₂.id_edge {S : SSet.Truncated 2} (X : OneTruncation₂ S) :
    OneTruncation₂.Hom.edge (𝟙rq X) = S.map (SSet.σ₂ 0).op X := rfl

/-- The functor that carries a 2-truncated simplicial set to its underlying refl quiver. -/
@[simps]
def oneTruncation₂ : SSet.Truncated.{u} 2 ⥤ ReflQuiv.{u, u} where
  obj S := ReflQuiv.of (OneTruncation₂ S)
  map {S T} F := {
    obj := F.app (op ⦋0⦌₂)
    map := fun f ↦
      { edge := F.app _ f.edge
        src_eq := by rw [← FunctorToTypes.naturality, f.src_eq]
        tgt_eq := by rw [← FunctorToTypes.naturality, f.tgt_eq] }
    map_id := fun X ↦ OneTruncation₂.Hom.ext (by
      dsimp
      rw [← FunctorToTypes.naturality]) }

@[ext]
lemma OneTruncation₂.hom_ext {S : SSet.Truncated 2} {x y : OneTruncation₂ S} {f g : x ⟶ y} :
    f.edge = g.edge → f = g := OneTruncation₂.Hom.ext

@[simp]
lemma OneTruncation₂.homOfEq_edge
    {X : SSet.Truncated.{u} 2} {x₁ y₁ x₂ y₂ : OneTruncation₂ X}
    (f : x₁ ⟶ y₁) (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Quiver.homOfEq f hx hy).edge = f.edge := by
  subst hx hy
  rfl

section
variable {C : Type u} [Category.{v} C]

/-- An equivalence between the type of objects underlying a category and the type of 0-simplices in
the 2-truncated nerve. -/
@[simps]
def OneTruncation₂.nerveEquiv :
    OneTruncation₂ ((SSet.truncation 2).obj (nerve C)) ≃ C where
  toFun X := X.obj' 0
  invFun X := .mk₀ X
  left_inv _ := ComposableArrows.ext₀ rfl

/-- A hom equivalence over the function `OneTruncation₂.nerveEquiv`. -/
def OneTruncation₂.nerveHomEquiv (X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))) :
  (X ⟶ Y) ≃ (nerveEquiv X ⟶ nerveEquiv Y) where
  toFun φ := eqToHom (congr_arg ComposableArrows.left φ.src_eq.symm) ≫ φ.edge.hom ≫
      eqToHom (congr_arg ComposableArrows.left φ.tgt_eq)
  invFun f :=
    { edge := ComposableArrows.mk₁ f
      src_eq := ComposableArrows.ext₀ rfl
      tgt_eq := ComposableArrows.ext₀ rfl }
  left_inv φ := by
    ext
    exact ComposableArrows.ext₁ (congr_arg ComposableArrows.left φ.src_eq).symm
      (congr_arg ComposableArrows.left φ.tgt_eq).symm rfl
  right_inv f := by dsimp; simp only [comp_id, id_comp]; rfl

/-- The refl quiver underlying a nerve is isomorphic to the refl quiver underlying the category. -/
def OneTruncation₂.ofNerve₂ (C : Type u) [Category.{u} C] :
    ReflQuiv.of (OneTruncation₂ (nerveFunctor₂.obj (Cat.of C))) ≅ ReflQuiv.of C := by
  apply ReflQuiv.isoOfEquiv.{u,u} OneTruncation₂.nerveEquiv OneTruncation₂.nerveHomEquiv ?_
  intro X
  unfold nerveEquiv nerveHomEquiv
  simp only [Cat.of_α, op_obj, ComposableArrows.obj', Fin.zero_eta, Fin.isValue, Equiv.coe_fn_mk,
    nerveEquiv_apply, Nat.reduceAdd, id_edge, SimplexCategory.len_mk, id_eq, eqToHom_refl, comp_id,
    id_comp, ReflQuiver.id_eq_id]
  unfold nerve truncation SimplicialObject.truncation SimplexCategory.Truncated.inclusion
  -- the following was obtained by `simp?`
  simp only [ObjectProperty.ι_obj, SimplexCategory.len_mk, Nat.reduceAdd, Fin.isValue,
    SimplexCategory.toCat_map, whiskeringLeft_obj_obj, Functor.comp_map, op_obj, op_map,
    Quiver.Hom.unop_op, ObjectProperty.ι_map, ComposableArrows.whiskerLeft_map, Fin.zero_eta,
    Monotone.functor_obj, Fin.mk_one, homOfLE_leOfHom]
  show X.map (𝟙 _) = _
  rw [X.map_id]
  rfl

/-- The refl quiver underlying a nerve is naturally isomorphic to the refl quiver underlying the
category. -/
@[simps! hom_app_obj hom_app_map inv_app_obj_obj inv_app_obj_map inv_app_map]
def OneTruncation₂.ofNerve₂.natIso :
    nerveFunctor₂.{u,u} ⋙ SSet.oneTruncation₂ ≅ ReflQuiv.forget :=
  NatIso.ofComponents (fun C => OneTruncation₂.ofNerve₂ C) (by
  · intro C D F
    fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      unfold SSet.oneTruncation₂ nerveFunctor₂ SSet.truncation SimplicialObject.truncation
        nerveFunctor toReflPrefunctor
      simp only [comp_obj, whiskeringLeft_obj_obj, ReflQuiv.of_val, Functor.comp_map,
        whiskeringLeft_obj_map, whiskerLeft_app, op_obj, whiskeringRight_obj_obj, ofNerve₂,
        Cat.of_α, nerveEquiv, ComposableArrows.obj', Fin.zero_eta, Fin.isValue,
        ReflQuiv.comp_eq_comp, Nat.reduceAdd, SimplexCategory.len_mk, id_eq, op_map,
        Quiver.Hom.unop_op, nerve_map, SimplexCategory.toCat_map, ReflPrefunctor.comp_obj,
        ReflPrefunctor.comp_map]
      simp [nerveHomEquiv, ReflQuiv.isoOfEquiv, ReflQuiv.isoOfQuivIso, Quiv.isoOfEquiv])

end

section

private lemma map_map_of_eq.{w}  {C : Type u} [Category.{v} C] (V : Cᵒᵖ ⥤ Type w) {X Y Z : C}
    {α : X ⟶ Y} {β : Y ⟶ Z} {γ : X ⟶ Z} {φ} :
    α ≫ β = γ → V.map α.op (V.map β.op φ) = V.map γ.op φ := by
  rintro rfl
  simp

variable {V : SSet}

namespace Truncated

/-- The map that picks up the initial vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι0₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1

/-- The map that picks up the middle vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι1₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2

/-- The map that picks up the final vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι2₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

/-- The initial vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev0₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι0₂.op φ

/-- The middle vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev1₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι1₂.op φ

/-- The final vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev2₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι2₂.op φ

/-- The 0th face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ0₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 0

/-- The 1st face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ1₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 1

/-- The 2nd face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ2₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 2

/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
0th face of a 2-simplex. -/
def ev12₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev1₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ0₂.op φ,
    map_map_of_eq V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    map_map_of_eq V rfl⟩

/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
1st face of a 2-simplex. -/
def ev02₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev0₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ1₂.op φ, map_map_of_eq V rfl, map_map_of_eq V rfl⟩

/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
2nd face of a 2-simplex. -/
def ev01₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev0₂ φ ⟶ ev1₂ φ :=
  ⟨V.map δ2₂.op φ, map_map_of_eq V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), map_map_of_eq V rfl⟩


/-- The 2-simplices in a 2-truncated simplicial set `V` generate a hom relation on the free
category on the underlying refl quiver of `V`. -/
inductive HoRel₂ {V : SSet.Truncated 2} :
    (X Y : Cat.FreeRefl (OneTruncation₂ V)) → (f g : X ⟶ Y) → Prop
  | mk (φ : V _⦋2⦌₂) :
    HoRel₂ _ _
      (Quot.mk _ (Quiver.Hom.toPath (ev02₂ φ)))
      (Quot.mk _ ((Quiver.Hom.toPath (ev01₂ φ)).comp
        (Quiver.Hom.toPath (ev12₂ φ))))

/-- A 2-simplex whose faces are identified with certain arrows in `OneTruncation₂ V` defines
a term of type `HoRel₂` between those arrows. -/
theorem HoRel₂.mk' {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) {X₀ X₁ X₂ : OneTruncation₂ V}
    (f₀₁ : X₀ ⟶ X₁) (f₁₂ : X₁ ⟶ X₂) (f₀₂ : X₀ ⟶ X₂)
    (h₀₁ : f₀₁.edge = V.map (δ₂ 2).op φ) (h₁₂ : f₁₂.edge = V.map (δ₂ 0).op φ)
    (h₀₂ : f₀₂.edge = V.map (δ₂ 1).op φ) :
    HoRel₂ _ _ (Quot.mk _ (Quiver.Hom.toPath f₀₂))
      (Quot.mk _ ((Quiver.Hom.toPath f₀₁).comp (Quiver.Hom.toPath f₁₂))) := by
  obtain rfl : X₀ = ev0₂ φ := by
    rw [← f₀₂.src_eq, h₀₂, ← FunctorToTypes.map_comp_apply, ← op_comp]
    rfl
  obtain rfl : X₁ = ev1₂ φ := by
    rw [← f₀₁.tgt_eq, h₀₁, ← FunctorToTypes.map_comp_apply, ← op_comp]
    rfl
  obtain rfl : X₂ = ev2₂ φ := by
    rw [← f₁₂.tgt_eq, h₁₂, ← FunctorToTypes.map_comp_apply, ← op_comp]
    rfl
  obtain rfl : f₀₁ = ev01₂ φ := by ext; assumption
  obtain rfl : f₁₂ = ev12₂ φ := by ext; assumption
  obtain rfl : f₀₂ = ev02₂ φ := by ext; assumption
  constructor

/-- The type underlying the homotopy category of a 2-truncated simplicial set `V`. -/
def _root_.SSet.Truncated.HomotopyCategory (V : SSet.Truncated.{u} 2) : Type u :=
  Quotient (HoRel₂ (V := V))

instance (V : SSet.Truncated.{u} 2) : Category.{u} (V.HomotopyCategory) :=
  inferInstanceAs (Category (CategoryTheory.Quotient ..))

/-- A canonical functor from the free category on the refl quiver underlying a 2-truncated
simplicial set `V` to its homotopy category. -/
def _root_.SSet.Truncated.HomotopyCategory.quotientFunctor (V : SSet.Truncated.{u} 2) :
    Cat.FreeRefl (OneTruncation₂ V) ⥤ V.HomotopyCategory :=
  Quotient.functor _

/-- By `Quotient.lift_unique'` (not `Quotient.lift`) we have that `quotientFunctor V` is an
epimorphism. -/
theorem HomotopyCategory.lift_unique' (V : SSet.Truncated.{u} 2) {D} [Category D]
    (F₁ F₂ : V.HomotopyCategory ⥤ D)
    (h : HomotopyCategory.quotientFunctor V ⋙ F₁ = HomotopyCategory.quotientFunctor V ⋙ F₂) :
    F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.FreeRefl (OneTruncation₂ V))
    (HoRel₂ (V := V)) _ _ h

/-- A map of 2-truncated simplicial sets induces a functor between homotopy categories. -/
def mapHomotopyCategory {V W : SSet.Truncated.{u} 2} (F : V ⟶ W) :
    V.HomotopyCategory ⥤ W.HomotopyCategory :=
  CategoryTheory.Quotient.lift _
    ((oneTruncation₂ ⋙ Cat.freeRefl).map F ⋙ HomotopyCategory.quotientFunctor W)
    (by
      rintro _ _ _ _ ⟨φ⟩
      apply CategoryTheory.Quotient.sound
      apply HoRel₂.mk' (φ := F.app _ φ)
        (f₀₁ := (oneTruncation₂.map F).map (ev01₂ φ))
        (f₀₂ := (oneTruncation₂.map F).map (ev02₂ φ))
        (f₁₂ := (oneTruncation₂.map F).map (ev12₂ φ))
      all_goals
        apply FunctorToTypes.naturality)

/-- The functor that takes a 2-truncated simplicial set to its homotopy category. -/
def hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u,u} where
  obj V := Cat.of (V.HomotopyCategory)
  map {S T} F := mapHomotopyCategory F
  map_id S := by
    apply Quotient.lift_unique'
    simp [mapHomotopyCategory, Quotient.lift_spec]
    exact Eq.trans (Functor.id_comp ..) (Functor.comp_id _).symm
  map_comp {S T U} F G := by
    apply Quotient.lift_unique'
    simp [mapHomotopyCategory, SSet.Truncated.HomotopyCategory.quotientFunctor]
    rw [Quotient.lift_spec, Cat.comp_eq_comp, Cat.comp_eq_comp, ← Functor.assoc, Functor.assoc,
      Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]

theorem hoFunctor₂_naturality {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) :
    (oneTruncation₂ ⋙ Cat.freeRefl).map f ⋙ SSet.Truncated.HomotopyCategory.quotientFunctor Y =
      SSet.Truncated.HomotopyCategory.quotientFunctor X ⋙ mapHomotopyCategory f := rfl

end Truncated

/-- The functor that takes a simplicial set to its homotopy category by passing through the
2-truncation. -/
def hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ Truncated.hoFunctor₂

end

end

end SSet
