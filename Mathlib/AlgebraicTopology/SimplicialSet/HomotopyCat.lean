/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/

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

The functor `SSet.hoFunctor` is shown to be left adjoint to the nerve by providing an analogous
decomposition of the nerve functor, made by possible by the fact that nerves of categories are
2-coskeletal, and then composing a pair of adjunctions, which factor through the category of
2-truncated simplicial sets.
-/

namespace CategoryTheory
namespace SSet
open Category Limits Functor Opposite Simplicial Nerve
universe v u

section

local macro:1000 (priority := high) X:term " _[" n:term "]₂" : term =>
    `(($X : SSet.Truncated 2).obj (Opposite.op ⟨SimplexCategory.mk $n, by decide⟩))

-- FIXME why doesn't this work?
-- local notation3:1000 (priority := high) (prettyPrint := false) " _[" n "]₂" =>
--     (X : SSet.Truncated 2).obj (Opposite.op ⟨SimplexCategory.mk n, by decide⟩)

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : SimplexCategory.Truncated 2))

/-- A 2-truncated simplicial set `S` has an underlying refl quiver with `S _[0]₂` as its underlying
type. -/
def OneTruncation₂ (S : SSet.Truncated 2) := S _[0]₂

/-- Abbreviations for face maps in the 2-truncated simplex category. -/
abbrev δ₂ {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) :
    (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[n + 1], hn'⟩ := SimplexCategory.δ i

/-- Abbreviations for degeneracy maps in the 2-truncated simplex category. -/
abbrev σ₂ {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) :
    (⟨[n+1], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[n], hn'⟩ := SimplexCategory.σ i

@[reassoc (attr := simp)]
lemma δ₂_zero_comp_σ₂_zero : δ₂ (0 : Fin 2) ≫ σ₂ 0 = 𝟙 _ := SimplexCategory.δ_comp_σ_self

@[reassoc (attr := simp)]
lemma δ₂_one_comp_σ₂_zero : δ₂ (1 : Fin 2) ≫ σ₂ 0 = 𝟙 _ := SimplexCategory.δ_comp_σ_succ

/-- The source vertex of `f : S _[1]₂` for use in defining the underlying refl quiver. -/
def OneTruncation₂.src {S : SSet.Truncated 2} (f : S _[1]₂) : OneTruncation₂ S :=
  S.map (δ₂ 1).op f

/-- The target vertex of `f : S _[1]₂` for use in defining the underlying refl quiver. -/
def OneTruncation₂.tgt {S : SSet.Truncated 2} (f : S _[1]₂) : OneTruncation₂ S :=
  S.map (δ₂ 0).op f

/-- The hom-types of the refl quiver underlying a simplicial set `S` are subtypes of `S _[1]₂`. -/
@[ext]
structure OneTruncation₂.Hom {S : SSet.Truncated 2} (X Y : OneTruncation₂ S) where
  edge : S _[1]₂
  src_eq : OneTruncation₂.src edge = X
  tgt_eq : OneTruncation₂.tgt edge = Y

/-- A 2-truncated simplicial set `S` has an underlying refl quiver `SSet.OneTruncation₂ S`. -/
instance (S : SSet.Truncated 2) : ReflQuiver (OneTruncation₂ S) where
  Hom X Y := SSet.OneTruncation₂.Hom X Y
  id X := by
    refine ⟨S.map (SSet.σ₂ (n := 0) 0).op X, ?_, ?_⟩ <;>
    · change (S.map _ ≫ S.map _) X = X
      rw [← map_comp]
      rw [(_ : _ ≫ _ = 𝟙 _)]; simp
      show ({..} : Opposite _) = _; congr; dsimp [SimplexCategory.Truncated]; ext ⟨i, _⟩
      let 0 := i
      rfl

/-- The functor that carries a 2-truncated simplicial set to its underlying refl quiver. -/
def oneTruncation₂ : SSet.Truncated.{u} 2 ⥤ ReflQuiv.{u,u} where
  obj S := ReflQuiv.of (OneTruncation₂ S)
  map {S T} F := {
    obj := F.app (op [0]₂)
    map := fun f => by
      refine ⟨F.app (op [1]₂) f.edge, ?_, ?_⟩
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.src_eq
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.tgt_eq
    map_id := fun X => by
      apply OneTruncation₂.Hom.ext
      dsimp only [SimplexCategory.len_mk, id_eq, ReflQuiv.of_val, Nat.reduceAdd, Fin.isValue,
        types_comp_apply, eq_mpr_eq_cast]
      change _ = (F.app _ ≫ _) _
      rw [← F.naturality]
      rfl
  }
  map_id X := by rfl
  map_comp f g := by rfl

@[ext] lemma hom₂_ext {S : SSet.Truncated 2} {x y : OneTruncation₂ S} {f g : x ⟶ y} :
    f.edge = g.edge → f = g := OneTruncation₂.Hom.ext

section
variable {C : Type u} [Category.{v} C]

/-- An arrow `f : X ⟶ Y` in the refl quiver of a nerve induces an arrow in the category `C`. -/
def OneTruncation₂.ofNerve₂.map {X Y : OneTruncation₂ (nerveFunctor₂.obj (Cat.of C))}
    (f : X ⟶ Y) : X.left ⟶ Y.left :=
  eqToHom (congrArg (·.left) f.src_eq.symm) ≫ f.edge.hom ≫ eqToHom (congrArg (·.left) f.tgt_eq)

/-- The refl prefunctor from the refl quiver underlying a nerve to the refl quiver underlying a
category. -/
def OneTruncation₂.ofNerve₂.hom : OneTruncation₂ (nerveFunctor₂.obj (Cat.of C)) ⥤rq C where
  obj := (·.left)
  map := OneTruncation₂.ofNerve₂.map
  map_id := fun X : ComposableArrows _ 0 => by
    obtain ⟨x, rfl⟩ := X.mk₀_surjective
    simp [map]; rfl

/-- The refl prefunctor from the refl quiver underlying a category to the refl quiver underlying
a nerve. -/
def OneTruncation₂.ofNerve₂.inv : C ⥤rq OneTruncation₂ (nerveFunctor₂.obj (Cat.of C)) where
  obj := (.mk₀ ·)
  map := fun f => by
    refine ⟨.mk₁ f, ?_, ?_⟩ <;> apply ComposableArrows.ext₀ <;> simp <;> rfl
  map_id _ := by ext; apply ComposableArrows.ext₁ <;> simp <;> rfl

/-- The refl quiver underlying a nerve is isomorphic to the refl quiver underlying the category. -/
def OneTruncation₂.ofNerve₂ (C : Type u) [Category.{u} C] :
    ReflQuiv.of (OneTruncation₂ (nerveFunctor₂.obj (Cat.of C))) ≅ ReflQuiv.of C := by
  refine {
    hom := ofNerve₂.hom
    inv := ofNerve₂.inv (C := C)
    hom_inv_id := ?_
    inv_hom_id := ?_
  }
  · have H1 {X X' Y : OneTruncation₂ (nerveFunctor₂.obj (Cat.of C))}
        (f : X ⟶ Y) (h : X = X') : (Eq.rec f h : X' ⟶ Y).edge = f.edge := by cases h; rfl
    have H2 {X Y Y' : OneTruncation₂ (nerveFunctor₂.obj (Cat.of C))}
        (f : X ⟶ Y) (h : Y = Y') : (Eq.rec f h : X ⟶ Y').edge = f.edge := by cases h; rfl
    fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ ComposableArrows.ext₀ rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      apply OneTruncation₂.Hom.ext
      simp [ReflQuiv.comp_eq_comp]
      refine ((H2 _ _).trans ((H1 _ _).trans (ComposableArrows.ext₁ ?_ ?_ ?_))).symm
      · rfl
      · rfl
      · simp [ofNerve₂.inv, ofNerve₂.hom, ofNerve₂.map]; rfl
  · fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ rfl
    · intro X Y f
      simp [ReflQuiv.comp_eq_comp, ReflQuiv.id_eq_id, ofNerve₂.inv, ofNerve₂.hom, ofNerve₂.map,
        SimplexCategory.Truncated.inclusion]

/-- The refl quiver underlying a nerve is naturally isomorphic to the refl quiver underlying the
category. -/
@[simps! hom_app_obj hom_app_map inv_app_obj_obj inv_app_obj_map inv_app_map]
def OneTruncation₂.ofNerve₂.natIso :
    nerveFunctor₂.{u,u} ⋙ SSet.oneTruncation₂ ≅ ReflQuiv.forget := by
  refine NatIso.ofComponents (fun C => OneTruncation₂.ofNerve₂ C) ?nat
  · intro C D F
    fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      unfold SSet.oneTruncation₂ nerveFunctor₂ SSet.truncation SimplicialObject.truncation
        nerveFunctor mapComposableArrows toReflPrefunctor
      simp [ReflQuiv.comp_eq_comp, ofNerve₂, ofNerve₂.hom, ofNerve₂.map]

end

section

private lemma map_map_of_eq.{w}  {C : Type u} [Category.{v} C] (V : Cᵒᵖ ⥤ Type w) {X Y Z : C}
    {α : X ⟶ Y} {β : Y ⟶ Z} {γ : X ⟶ Z} {φ} :
    α ≫ β = γ → V.map α.op (V.map β.op φ) = V.map γ.op φ := by
  rintro rfl
  change (V.map _ ≫ V.map _) _ = _
  rw [← map_comp]; rfl

variable {V : SSet}

open SSet

namespace Truncated

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

/-- The map that picks up the initial vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι0₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1

/-- The map that picks up the middle vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι1₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2

/-- The map that picks up the final vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι2₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

/-- The initial vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev0₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι0₂.op φ

/-- The middle vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev1₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι1₂.op φ

/-- The final vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev2₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι2₂.op φ

/-- The 0th face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ0₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 0

/-- The 1st face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ1₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 1

/-- The 2nd face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ2₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 2

/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
0th face of a 2-simplex. -/
def ev12₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev1₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ0₂.op φ,
    map_map_of_eq V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    map_map_of_eq V rfl⟩

/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
1st face of a 2-simplex. -/
def ev02₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev0₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ1₂.op φ, map_map_of_eq V rfl, map_map_of_eq V rfl⟩

/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
2nd face of a 2-simplex. -/
def ev01₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev0₂ φ ⟶ ev1₂ φ :=
  ⟨V.map δ2₂.op φ, map_map_of_eq V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), map_map_of_eq V rfl⟩

end Truncated
open Truncated

/-- The 2-simplices in a 2-truncated simplicial set `V` generate a hom relation on the free
category on the underlying refl quiver of `V`. -/
inductive HoRel₂ {V : SSet.Truncated 2} :
    (X Y : Cat.FreeRefl (OneTruncation₂ V)) → (f g : X ⟶ Y) → Prop
  | mk (φ : V _[2]₂) :
    HoRel₂ _ _
      (Quot.mk _ (Quiver.Hom.toPath (ev02₂ φ)))
      (Quot.mk _ ((Quiver.Hom.toPath (ev01₂ φ)).comp
        (Quiver.Hom.toPath (ev12₂ φ))))

theorem HoRel₂.ext_triangle {V} (X X' Y Y' Z Z' : OneTruncation₂ V)
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : X ⟶ Z) (f' : X' ⟶ Z') (hf : f.edge = f'.edge)
    (g : X ⟶ Y) (g' : X' ⟶ Y') (hg : g.edge = g'.edge)
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (hh : h.edge = h'.edge) :
    HoRel₂ _ _
      ((Quotient.functor _).map (.cons .nil f))
      ((Quotient.functor _).map (.cons (.cons .nil g) h)) ↔
    HoRel₂ _ _
      ((Quotient.functor _).map (.cons .nil f'))
      ((Quotient.functor _).map (.cons (.cons .nil g') h')) := by
  cases hX
  cases hY
  cases hZ
  congr! <;> apply OneTruncation₂.Hom.ext <;> assumption

/-- The type underlying the homotopy category of a 2-truncated simplicial set `V`. -/
def hoFunctor₂Obj (V : SSet.Truncated.{u} 2) : Type u :=
  Quotient (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) (HoRel₂ (V := V))

instance (V : SSet.Truncated.{u} 2) : Category.{u} (SSet.hoFunctor₂Obj V) :=
  inferInstanceAs (Category (Quotient ..))

/-- A canonical functor from the free category on the refl quiver underlying a 2-truncated
simplicial set `V` to its homotopy category. -/
def hoFunctor₂Obj.quotientFunctor (V : SSet.Truncated.{u} 2) :
    Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V)) ⥤ SSet.hoFunctor₂Obj V :=
  Quotient.functor (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) (HoRel₂ (V := V))

/-- By `Quotient.lift_unique'` (not `Quotient.lift`) we have that `quotientFunctor V` is an
epimorphism. -/
theorem hoFunctor₂Obj.lift_unique' (V : SSet.Truncated.{u} 2)
    {D} [Category D] (F₁ F₂ : hoFunctor₂Obj V ⥤ D)
    (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) : F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V)))
    (HoRel₂ (V := V)) _ _ h

/-- A map of 2-truncated simplicial sets induces a functor between homotopy categories. -/
def hoFunctor₂Map {V W : SSet.Truncated.{u} 2} (F : V ⟶ W) : hoFunctor₂Obj V ⥤ hoFunctor₂Obj W :=
  Quotient.lift _
    ((by exact (oneTruncation₂ ⋙ Cat.freeRefl).map F) ⋙ hoFunctor₂Obj.quotientFunctor _)
    (fun X Y f g hfg => by
      let .mk φ := hfg
      apply Quotient.sound
      convert HoRel₂.mk (F.app (op _) φ) using 0
      apply HoRel₂.ext_triangle
      · exact congrFun (F.naturality ι0₂.op) φ
      · exact congrFun (F.naturality ι1₂.op) φ
      · exact congrFun (F.naturality ι2₂.op) φ
      · exact congrFun (F.naturality δ1₂.op) φ
      · exact congrFun (F.naturality δ2₂.op) φ
      · exact congrFun (F.naturality δ0₂.op) φ)

/-- The functor that takes a 2-truncated simplicial set to its homotopy category. -/
def hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u,u} where
  obj V := Cat.of (hoFunctor₂Obj V)
  map {S T} F := hoFunctor₂Map F
  map_id S := by
    apply Quotient.lift_unique'
    simp [hoFunctor₂Map, Quotient.lift_spec]
    exact Eq.trans (Functor.id_comp ..) (Functor.comp_id _).symm
  map_comp {S T U} F G := by
    apply Quotient.lift_unique'
    simp [hoFunctor₂Map, SSet.hoFunctor₂Obj.quotientFunctor]
    rw [Quotient.lift_spec, Cat.comp_eq_comp, Cat.comp_eq_comp, ← Functor.assoc, Functor.assoc,
      Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]

theorem hoFunctor₂_naturality {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) :
    (oneTruncation₂ ⋙ Cat.freeRefl).map f ⋙ hoFunctor₂Obj.quotientFunctor Y =
      hoFunctor₂Obj.quotientFunctor X ⋙ hoFunctor₂Map f := rfl

/-- The functor that takes a simplicial set to its homotopy category by passing through the
2-truncation. -/
def hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ hoFunctor₂

end

end

end SSet
end CategoryTheory
