/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/

import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Category.ReflQuiv
import Mathlib.Combinatorics.Quiver.ReflQuiver


/-!

# The homotopy category of a simplicial set

The homotopy category of a simplicial set is defined as a quotient of the free category on its
underlying reflexive quiver (equivalently its one truncation). The quotient imposes an additional
hom relation on this free category, asserting that `f ≫ g = h` whenever `f`, `g`, and `h` are
respectively the 2nd, 0th, and 1st faces of a 2-simplex.

In this file, we in fact define a pair of functors:

(1) `SSet.hoFunctor' : SSet.{u} ⥤ Cat.{u, u}` implements the construction described above, while

(2) `SSet.hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ SSet.hoFunctor₂` is defined by
first restricting from simplicial sets to 2-truncated simplicial sets (throwing away the data that
is not used for the construction of the homotopy category) and then composing with an analogously
defined `SSet.hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u,u}` implemented relative to the syntax of
the 2-truncated simplex category.

It should be relatively straightforward to show that these constructions agree:

def hoFunctor.ofTwoTruncation.iso (V : SSet) :
    SSet.hoFunctor₂Obj ((truncation 2).obj V) ≅ SSet.hoCat V := sorry

def hoFunctor.ofTwoTruncation.natIso :
     truncation 2 ⋙ SSet.hoFunctor₂ ≅ SSet.hoFunctor' := sorry

but we leave this for future work.

The functor `SSet.hoFunctor` is shown to be left adjoint to the nerve by providing an analogous
decomposition of the nerve functor and then composing a pair of adjunctions, which factor through
the category of 2-truncated simplicial sets.
-/

namespace CategoryTheory
open Category Limits Functor Opposite Simplicial
universe v u

section

/-- A simplicial set `S` has an underlying refl quiver with `S _[0]` as its underlying type.-/
def SSet.OneTruncation (S : SSet) := S _[0]

/-- The source vertex of `f : S _[1]` for use in defining the underlying refl quiver.-/
def SSet.OneTruncation.src {S : SSet} (f : S _[1]) : OneTruncation S := S.δ 1 f

/-- The target vertex of `f : S _[1]` for use in defining the underlying refl quiver.-/
def SSet.OneTruncation.tgt {S : SSet} (f : S _[1]) : OneTruncation S := S.δ 0 f

/-- The hom-types of the refl quiver underlying a simplicial set `S` are subtypes of `S _[1]`.-/
def SSet.OneTruncation.Hom {S : SSet} (X Y : OneTruncation S) :=
  {p : S _[1] // src p = X ∧ tgt p = Y}

/-- A simplicial set `S` has an underlying refl quiver `SSet.OneTruncation S`.-/
instance (S : SSet) : ReflQuiver (SSet.OneTruncation S) where
  Hom X Y := SSet.OneTruncation.Hom X Y
  id X := by
    refine ⟨S.σ 0 X, ?_, ?_⟩ <;> change (S.δ _ (S.σ _ _)) = X
    · apply SSet.δ_comp_σ_succ_apply 0
    · apply SSet.δ_comp_σ_self_apply 0

/-- The functor that carries a simplicial set to its underlying refl quiver.-/
def SSet.oneTruncation : SSet.{u} ⥤ ReflQuiv.{u,u} where
  obj S := ReflQuiv.of (OneTruncation S)
  map {S T} F := {
    obj := F.app (op [0])
    map := fun f => by
      refine ⟨F.app (op [1]) f.1, ?_, ?_⟩
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.2.1
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.2.2
    map_id := fun X => by
      change ({..} : Subtype _) = {..}
      congr
      change _ = (F.app _ ≫ _) _
      rw [← F.naturality]
      rfl
  }

@[ext] lemma hom_ext {S : SSet} {x y : SSet.OneTruncation S} {f g : x ⟶ y} :
    f.1 = g.1 → f = g := Subtype.ext

section
variable {C : Type u} [Category.{v} C]

theorem opstuff.{w} (V : Cᵒᵖ ⥤ Type w) {X Y Z : C} {α : X ⟶ Y} {β : Y ⟶ Z} {γ : X ⟶ Z} {φ} :
    α ≫ β = γ → V.map α.op (V.map β.op φ) = V.map γ.op φ := by
  rintro rfl
  change (V.map _ ≫ V.map _) _ = _
  rw [← map_comp]; rfl


/-- An arrow `f : X ⟶ Y` in the refl quiver of a nerve induces an arrow in the category `C`.-/
def SSet.OneTruncation.ofNerve.map {X Y : OneTruncation (nerve C)}
    (f : X ⟶ Y) : X.left ⟶ Y.left :=
  eqToHom (congrArg (·.left) f.2.1.symm) ≫ f.1.hom ≫ eqToHom (congrArg (·.left) f.2.2)

/-- The refl prefunctor from the refl quiver underlying a nerve to the refl quiver underlying a
category.-/
def SSet.OneTruncation.ofNerve.hom : OneTruncation (nerve C) ⥤rq C where
  obj := (·.left)
  map := OneTruncation.ofNerve.map
  map_id := fun X : ComposableArrows _ 0 => by
    obtain ⟨x, rfl⟩ := X.mk₀_surjective
    simp [map]; rfl

/-- The refl prefunctor from the refl quiver underlying a category to the refl quiver underlying
a nerve.-/
def SSet.OneTruncation.ofNerve.inv : C ⥤rq OneTruncation (nerve C) where
  obj := (.mk₀ ·)
  map := fun f => by
    refine ⟨.mk₁ f, ?_, ?_⟩ <;> apply ComposableArrows.ext₀ <;> simp <;> rfl
  map_id _ := by ext; apply ComposableArrows.ext₁ <;> simp <;> rfl

/-- The refl quiver underlying a nerve is isomorphic to the refl quiver underlying the category.-/
def SSet.OneTruncation.ofNerve (C : Type u) [Category.{u} C] :
    ReflQuiv.of (OneTruncation (nerve C)) ≅ ReflQuiv.of C := by
  refine {
    hom := ofNerve.hom
    inv := ofNerve.inv (C := C)
    hom_inv_id := ?_
    inv_hom_id := ?_
  }
  · have H1 {X X' Y : OneTruncation (nerve C)} (f : X ⟶ Y) (h : X = X') :
        (Eq.rec f h : X' ⟶ Y).1 = f.1 := by cases h; rfl
    have H2 {X Y Y' : OneTruncation (nerve C)} (f : X ⟶ Y) (h : Y = Y') :
        (Eq.rec f h : X ⟶ Y').1 = f.1 := by cases h; rfl
    fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ ComposableArrows.ext₀ rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      apply Subtype.ext
      simp [ReflQuiv.comp_eq_comp]
      refine ((H2 _ _).trans ((H1 _ _).trans (ComposableArrows.ext₁ ?_ ?_ ?_))).symm
      · rfl
      · rfl
      · simp [ofNerve.inv, ofNerve.hom, ofNerve.map]; rfl
  · fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ rfl
    · intro X Y f
      simp [ReflQuiv.comp_eq_comp, ReflQuiv.id_eq_id, ofNerve.inv, ofNerve.hom, ofNerve.map]

/-- The refl quiver underlying a nerve is naturally isomorphic to the refl quiver underlying the
category.-/
@[simps! hom_app_obj hom_app_map inv_app_obj_obj inv_app_obj_map inv_app_map]
def SSet.OneTruncation.ofNerve.natIso :
    nerveFunctor.{u,u} ⋙ SSet.oneTruncation ≅ ReflQuiv.forget := by
  refine NatIso.ofComponents (fun C => OneTruncation.ofNerve C) ?nat
  · intro C D F
    fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      unfold SSet.oneTruncation nerveFunctor mapComposableArrows toReflPrefunctor
      simp [ReflQuiv.comp_eq_comp, ofNerve, ofNerve.hom, ofNerve.map]

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

private def ι0 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 1 ≫ SimplexCategory.δ (n := 1) 1
private def ι1 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.δ (n := 1) 2
private def ι2 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.δ (n := 1) 1

private def ev0 {V : SSet} (φ : V _[2]) : SSet.OneTruncation V := V.map ι0.op φ
private def ev1 {V : SSet} (φ : V _[2]) : SSet.OneTruncation V := V.map ι1.op φ
private def ev2 {V : SSet} (φ : V _[2]) : SSet.OneTruncation V := V.map ι2.op φ

private def δ0 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 0
private def δ1 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 1
private def δ2 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 2

private def ev02 {V : SSet} (φ : V _[2]) : ev0 φ ⟶ ev2 φ :=
  ⟨V.map δ1.op φ, opstuff V rfl, opstuff V rfl⟩
private def ev01 {V : SSet} (φ : V _[2]) : ev0 φ ⟶ ev1 φ :=
  ⟨V.map δ2.op φ, opstuff V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), opstuff V rfl⟩
private def ev12 {V : SSet} (φ : V _[2]) : ev1 φ ⟶ ev2 φ :=
  ⟨V.map δ0.op φ,
    opstuff V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    opstuff V rfl⟩

/-- The 2-simplices in a simplicial set `V` generate a hom relation on the free category on
the underlying refl quiver of `V`.-/
inductive SSet.HoRel {V : SSet} :
    (X Y : Cat.freeRefl.obj (ReflQuiv.of (OneTruncation V))) → (f g : X ⟶ Y) → Prop
  | mk (φ : V _[2]) :
    HoRel _ _
      (Quot.mk _ (.cons .nil (ev02 φ)))
      (Quot.mk _ (.cons (.cons .nil (ev01 φ)) (ev12 φ)))

theorem SSet.HoRel.ext_triangle {V} (X X' Y Y' Z Z' : OneTruncation V)
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : X ⟶ Z) (f' : X' ⟶ Z') (hf : f.1 = f'.1)
    (g : X ⟶ Y) (g' : X' ⟶ Y') (hg : g.1 = g'.1)
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (hh : h.1 = h'.1) :
    HoRel _ _
      ((Quotient.functor _).map (.cons .nil f))
      ((Quotient.functor _).map (.cons (.cons .nil g) h)) ↔
    HoRel _ _
      ((Quotient.functor _).map (.cons .nil f'))
      ((Quotient.functor _).map (.cons (.cons .nil g') h')) := by
  cases hX
  cases hY
  cases hZ
  congr! <;> apply Subtype.ext <;> assumption

/-- The homotopy category of a simplicial set is a quotient of the free category generated by its
underlying refl quiver by the hom relation `HoRel`.-/
def SSet.hoCat (V : SSet.{u}) : Type u :=
  Quotient (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation V))) (HoRel (V := V))

instance (V : SSet.{u}) : Category.{u} (SSet.hoCat V) := inferInstanceAs (Category (Quotient ..))

/-- A map of simplicial sets induces a functor between homotopy categories.-/
def SSet.hoFunctorMap {V W : SSet.{u}} (F : V ⟶ W) : SSet.hoCat V ⥤ SSet.hoCat W :=
  Quotient.lift _ (((SSet.oneTruncation ⋙ Cat.freeRefl).map F) ⋙ Quotient.functor _)
    (fun X Y f g hfg => by
      let .mk φ := hfg
      clear f g hfg
      simp [Quot.liftOn]
      apply Quotient.sound
      convert HoRel.mk (F.app (op [2]) φ) using 0
      apply HoRel.ext_triangle
      · exact congrFun (F.naturality ι0.op) φ
      · exact congrFun (F.naturality ι1.op) φ
      · exact congrFun (F.naturality ι2.op) φ
      · exact congrFun (F.naturality δ1.op) φ
      · exact congrFun (F.naturality δ2.op) φ
      · exact congrFun (F.naturality δ0.op) φ)

/-- The functor that takes a simplicial set to its homotopy category. This should be isomorphic to
the similiarly defined `SSet.hoFunctor` below, though this has not yet been proven.-/
def SSet.hoFunctor' : SSet.{u} ⥤ Cat.{u,u} where
  obj V := Cat.of (SSet.hoCat V)
  map {S T} F := SSet.hoFunctorMap F
  map_id S := by
    apply Quotient.lift_unique'
    simp [hoFunctorMap, Quotient.lift_spec]
    exact Eq.trans (Functor.id_comp ..) (Functor.comp_id _).symm
  map_comp {S T U} F G := by
    apply Quotient.lift_unique'
    simp [hoFunctorMap]
    rw [Quotient.lift_spec, Cat.comp_eq_comp, Cat.comp_eq_comp, ← Functor.assoc, Functor.assoc,
      Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]
end
end

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
type.-/
def SSet.OneTruncation₂ (S : SSet.Truncated 2) := S _[0]₂

/-- Abbreviations for face maps in the 2-truncated simplex category.-/
abbrev SSet.δ₂ {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) :
    (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[n + 1], hn'⟩ := SimplexCategory.δ i

/-- Abbreviations for degeneracy maps in the 2-truncated simplex category.-/
abbrev SSet.σ₂ {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) :
    (⟨[n+1], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[n], hn'⟩ := SimplexCategory.σ i

/-- The source vertex of `f : S _[1]₂` for use in defining the underlying refl quiver.-/
def SSet.OneTruncation₂.src {S : SSet.Truncated 2} (f : S _[1]₂) : OneTruncation₂ S :=
  S.map (δ₂ (n := 0) 1).op f

/-- The target vertex of `f : S _[1]₂` for use in defining the underlying refl quiver.-/
def SSet.OneTruncation₂.tgt {S : SSet.Truncated 2} (f : S _[1]₂) : OneTruncation₂ S :=
  S.map (δ₂ (n := 0) 0).op f

/-- The hom-types of the refl quiver underlying a simplicial set `S` are subtypes of `S _[1]₂`.-/
def SSet.OneTruncation₂.Hom {S : SSet.Truncated 2} (X Y : OneTruncation₂ S) :=
  {p : S _[1]₂ // src p = X ∧ tgt p = Y}

/-- A 2-truncated simplicial set `S` has an underlying refl quiver `SSet.OneTruncation₂ S`.-/
instance (S : SSet.Truncated 2) : ReflQuiver (SSet.OneTruncation₂ S) where
  Hom X Y := SSet.OneTruncation₂.Hom X Y
  id X := by
    refine ⟨S.map (SSet.σ₂ (n := 0) 0).op X, ?_, ?_⟩ <;>
    · change (S.map _ ≫ S.map _) X = X
      rw [← map_comp]
      rw [(_ : _ ≫ _ = 𝟙 _)]; simp
      show ({..} : Opposite _) = _; congr; dsimp [SimplexCategory.Truncated]; ext ⟨i, _⟩
      let 0 := i
      rfl

/-- The functor that carries a 2-truncated simplicial set to its underlying refl quiver.-/
def SSet.oneTruncation₂ : SSet.Truncated.{u} 2 ⥤ ReflQuiv.{u,u} where
  obj S := ReflQuiv.of (OneTruncation₂ S)
  map {S T} F := {
    obj := F.app (op [0]₂)
    map := fun f => by
      refine ⟨F.app (op [1]₂) f.1, ?_, ?_⟩
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.2.1
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.2.2
    map_id := fun X => by
      change ({..} : Subtype _) = {..}
      congr
      change _ = (F.app _ ≫ _) _
      rw [← F.naturality]
      rfl
  }
  map_id X := by rfl
  map_comp f g := by rfl

section
variable {V : SSet}

open SSet

/-- A natural isomorphism between the underlying refl quivers of a simplicial set `V` and its
2-truncation.-/
def SSet.OneTruncation₂.ofTwoTruncationIso (V : SSet) :
    ReflQuiv.of (OneTruncation₂ ((SSet.truncation 2).obj V)) ≅ ReflQuiv.of (OneTruncation V) :=
  .refl _

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

private def ι0₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1
private def ι1₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2
private def ι2₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

private def ev0₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι0₂.op φ
private def ev1₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι1₂.op φ
private def ev2₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι2₂.op φ

private def δ1₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 1
private def δ2₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 2
private def δ0₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 0

private def ev02₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev0₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ1₂.op φ, opstuff V rfl, opstuff V rfl⟩
private def ev01₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev0₂ φ ⟶ ev1₂ φ :=
  ⟨V.map δ2₂.op φ, opstuff V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), opstuff V rfl⟩
private def ev12₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev1₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ0₂.op φ,
    opstuff V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    opstuff V rfl⟩

/-- The 2-simplices in a 2-truncated simplicial set `V` generate a hom relation on the free
category on the underlying refl quiver of `V`.-/
inductive SSet.HoRel₂ {V : SSet.Truncated 2} :
    (X Y : Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) → (f g : X ⟶ Y) → Prop
  | mk (φ : V _[2]₂) :
    HoRel₂ _ _
      (Quot.mk _ (.cons .nil (ev02₂ φ)))
      (Quot.mk _ (.cons (.cons .nil (ev01₂ φ)) (ev12₂ φ)))

theorem SSet.HoRel₂.ext_triangle {V} (X X' Y Y' Z Z' : OneTruncation₂ V)
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : X ⟶ Z) (f' : X' ⟶ Z') (hf : f.1 = f'.1)
    (g : X ⟶ Y) (g' : X' ⟶ Y') (hg : g.1 = g'.1)
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (hh : h.1 = h'.1) :
    HoRel₂ _ _
      ((Quotient.functor _).map (.cons .nil f))
      ((Quotient.functor _).map (.cons (.cons .nil g) h)) ↔
    HoRel₂ _ _
      ((Quotient.functor _).map (.cons .nil f'))
      ((Quotient.functor _).map (.cons (.cons .nil g') h')) := by
  cases hX
  cases hY
  cases hZ
  congr! <;> apply Subtype.ext <;> assumption

/-- The type underlying the homotopy category of a 2-truncated simplicial set `V`.-/
def SSet.hoFunctor₂Obj (V : SSet.Truncated.{u} 2) : Type u :=
  Quotient (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) (HoRel₂ (V := V))

instance (V : SSet.Truncated.{u} 2) : Category.{u} (SSet.hoFunctor₂Obj V) :=
  inferInstanceAs (Category (Quotient ..))

/-- A canonical functor from the free category on the refl quiver underlying a 2-truncated
simplicial set `V` to its homotopy category.-/
def SSet.hoFunctor₂Obj.quotientFunctor (V : SSet.Truncated.{u} 2) :
    Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V)) ⥤ SSet.hoFunctor₂Obj V :=
  Quotient.functor (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) (HoRel₂ (V := V))

/-- By `Quotient.lift_unique'` (not `Quotient.lift`) we have that `quotientFunctor V` is an
epimorphism.-/
theorem SSet.hoFunctor₂Obj.lift_unique' (V : SSet.Truncated.{u} 2)
    {D} [Category D] (F₁ F₂ : SSet.hoFunctor₂Obj V ⥤ D)
    (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) : F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V)))
    (HoRel₂ (V := V)) _ _ h

/-- A map of 2-truncated simplicial sets induces a functor between homotopy categories.-/
def SSet.hoFunctor₂Map {V W : SSet.Truncated.{u} 2} (F : V ⟶ W) :
    SSet.hoFunctor₂Obj V ⥤ SSet.hoFunctor₂Obj W :=
  Quotient.lift _
    ((by exact (SSet.oneTruncation₂ ⋙ Cat.freeRefl).map F) ⋙
      SSet.hoFunctor₂Obj.quotientFunctor _)
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

/-- The functor that takes a 2-truncated simplicial set to its homotopy category.-/
def SSet.hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u,u} where
  obj V := Cat.of (SSet.hoFunctor₂Obj V)
  map {S T} F := SSet.hoFunctor₂Map F
  map_id S := by
    apply Quotient.lift_unique'
    simp [hoFunctor₂Map, Quotient.lift_spec]
    exact Eq.trans (Functor.id_comp ..) (Functor.comp_id _).symm
  map_comp {S T U} F G := by
    apply Quotient.lift_unique'
    simp [hoFunctor₂Map, SSet.hoFunctor₂Obj.quotientFunctor]
    rw [Quotient.lift_spec, Cat.comp_eq_comp, Cat.comp_eq_comp, ← Functor.assoc, Functor.assoc,
      Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]

theorem SSet.hoFunctor₂_naturality {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) :
    (SSet.oneTruncation₂ ⋙ Cat.freeRefl).map f ⋙
    hoFunctor₂Obj.quotientFunctor Y =
    SSet.hoFunctor₂Obj.quotientFunctor X ⋙ hoFunctor₂Map f := rfl

/-- The functor that takes a simplicial set to its homotopy category by passing through the
2-truncation. This should be naturally isomorphic to `SSet.hoFunctor'`.-/
def SSet.hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ SSet.hoFunctor₂

end
end

end CategoryTheory
