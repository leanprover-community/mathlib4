/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Junyan Xu
-/
import Mathlib.CategoryTheory.PathCategory
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Bicategory.Free
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

#align_import category_theory.bicategory.coherence from "leanprover-community/mathlib"@"f187f1074fa1857c94589cc653c786cadc4c35ff"

/-!
# The coherence theorem for bicategories

In this file, we prove the coherence theorem for bicategories, stated in the following form: the
free bicategory over any quiver is locally thin.

The proof is almost the same as the proof of the coherence theorem for monoidal categories that
has been previously formalized in mathlib, which is based on the proof described by Ilya Beylin
and Peter Dybjer. The idea is to view a path on a quiver as a normal form of a 1-morphism in the
free bicategory on the same quiver. A normalization procedure is then described by
`normalize : Pseudofunctor (FreeBicategory B) (LocallyDiscrete (Paths B))`, which is a
pseudofunctor from the free bicategory to the locally discrete bicategory on the path category.
It turns out that this pseudofunctor is locally an equivalence of categories, and the coherence
theorem follows immediately from this fact.

## Main statements

* `locally_thin` : the free bicategory is locally thin, that is, there is at most one
  2-morphism between two fixed 1-morphisms.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
   proof of normalization for monoids][beylin1996]
-/


open Quiver (Path)

open Quiver.Path

namespace CategoryTheory

open Bicategory Category

universe v u

namespace FreeBicategory

variable {B : Type u} [Quiver.{v + 1} B]

/-- Auxiliary definition for `inclusionPath`. -/
@[simp]
def inclusionPathAux {a : B} : ∀ {b : B}, Path a b → Hom a b
  | _, nil => Hom.id a
  | _, cons p f => (inclusionPathAux p).comp (Hom.of f)
#align category_theory.free_bicategory.inclusion_path_aux CategoryTheory.FreeBicategory.inclusionPathAux

/- Porting note: Since the following instance was removed when porting
`CategoryTheory.Bicategory.Free`, we add it locally here. -/
/-- Category structure on `Hom a b`. In this file, we will use `Hom a b` for `a b : B`
(precisely, `FreeBicategory.Hom a b`) instead of the definitionally equal expression
`a ⟶ b` for `a b : FreeBicategory B`. The main reason is that we have to annoyingly write
`@Quiver.Hom (FreeBicategory B) _ a b` to get the latter expression when given `a b : B`. -/
local instance homCategory' (a b : B) : Category (Hom a b) :=
  homCategory a b

/-- The discrete category on the paths includes into the category of 1-morphisms in the free
bicategory.
-/
def inclusionPath (a b : B) : Discrete (Path.{v + 1} a b) ⥤ Hom a b :=
  Discrete.functor inclusionPathAux
#align category_theory.free_bicategory.inclusion_path CategoryTheory.FreeBicategory.inclusionPath

/-- The inclusion from the locally discrete bicategory on the path category into the free bicategory
as a prelax functor. This will be promoted to a pseudofunctor after proving the coherence theorem.
See `inclusion`.
-/
def preinclusion (B : Type u) [Quiver.{v + 1} B] :
    PrelaxFunctor (LocallyDiscrete (Paths B)) (FreeBicategory B) where
  obj a := a.as
  map := @fun a b f => (@inclusionPath B _ a.as b.as).obj f
  map₂ η := (inclusionPath _ _).map η
#align category_theory.free_bicategory.preinclusion CategoryTheory.FreeBicategory.preinclusion

@[simp]
theorem preinclusion_obj (a : B) : (preinclusion B).obj ⟨a⟩ = a :=
  rfl
#align category_theory.free_bicategory.preinclusion_obj CategoryTheory.FreeBicategory.preinclusion_obj

@[simp]
theorem preinclusion_map₂ {a b : B} (f g : Discrete (Path.{v + 1} a b)) (η : f ⟶ g) :
    (preinclusion B).map₂ η = eqToHom (congr_arg _ (Discrete.ext _ _ (Discrete.eq_of_hom η))) := by
  rcases η with ⟨⟨⟩⟩
  cases Discrete.ext _ _ (by assumption)
  convert (inclusionPath a b).map_id _
#align category_theory.free_bicategory.preinclusion_map₂ CategoryTheory.FreeBicategory.preinclusion_map₂

/-- The normalization of the composition of `p : Path a b` and `f : Hom b c`.
`p` will eventually be taken to be `nil` and we then get the normalization
of `f` alone, but the auxiliary `p` is necessary for Lean to accept the definition of
`normalizeIso` and the `whisker_left` case of `normalizeAux_congr` and `normalize_naturality`.
-/
@[simp]
def normalizeAux {a : B} : ∀ {b c : B}, Path a b → Hom b c → Path a c
  | _, _, p, Hom.of f => p.cons f
  | _, _, p, Hom.id _ => p
  | _, _, p, Hom.comp f g => normalizeAux (normalizeAux p f) g
#align category_theory.free_bicategory.normalize_aux CategoryTheory.FreeBicategory.normalizeAux

/-
We may define
```
def normalizeAux' : ∀ {a b : B}, Hom a b → Path a b
  | _, _, (Hom.of f) => f.toPath
  | _, _, (Hom.id b) => nil
  | _, _, (Hom.comp f g) => (normalizeAux' f).comp (normalizeAux' g)
```
and define `normalizeAux p f` to be `p.comp (normalizeAux' f)` and this will be
equal to the above definition, but the equality proof requires `comp_assoc`, and it
thus lacks the correct definitional property to make the definition of `normalizeIso`
typecheck.
```
example {a b c : B} (p : Path a b) (f : Hom b c) :
    normalizeAux p f = p.comp (normalizeAux' f) := by
  induction f; rfl; rfl;
  case comp _ _ _ _ _ ihf ihg => rw [normalizeAux, ihf, ihg]; apply comp_assoc
```
-/
/-- A 2-isomorphism between a partially-normalized 1-morphism in the free bicategory to the
fully-normalized 1-morphism.
-/
@[simp]
def normalizeIso {a : B} :
    ∀ {b c : B} (p : Path a b) (f : Hom b c),
      (preinclusion B).map ⟨p⟩ ≫ f ≅ (preinclusion B).map ⟨normalizeAux p f⟩
  | _, _, _, Hom.of _ => Iso.refl _
  | _, _, _, Hom.id b => ρ_ _
  | _, _, p, Hom.comp f g =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIso p f) g ≪≫ normalizeIso (normalizeAux p f) g
#align category_theory.free_bicategory.normalize_iso CategoryTheory.FreeBicategory.normalizeIso

/-- Given a 2-morphism between `f` and `g` in the free bicategory, we have the equality
`normalizeAux p f = normalizeAux p g`.
-/
theorem normalizeAux_congr {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    normalizeAux p f = normalizeAux p g := by
  rcases η with ⟨η'⟩
  apply @congr_fun _ _ fun p => normalizeAux p f
  clear p η
  induction η' with
  | vcomp _ _ _ _ => apply Eq.trans <;> assumption
  | whisker_left _ _ ih => funext; apply congr_fun ih
  | whisker_right _ _ ih => funext; apply congr_arg₂ _ (congr_fun ih _) rfl
  | _ => funext; rfl
#align category_theory.free_bicategory.normalize_aux_congr CategoryTheory.FreeBicategory.normalizeAux_congr

/-- The 2-isomorphism `normalizeIso p f` is natural in `f`. -/
theorem normalize_naturality {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    (preinclusion B).map ⟨p⟩ ◁ η ≫ (normalizeIso p g).hom =
      (normalizeIso p f).hom ≫
        (preinclusion B).map₂ (eqToHom (Discrete.ext _ _ (normalizeAux_congr p η))) := by
  rcases η with ⟨η'⟩; clear η;
  induction η' with
  | id => simp
  | vcomp η θ ihf ihg =>
    simp only [mk_vcomp, Bicategory.whiskerLeft_comp]
    slice_lhs 2 3 => rw [ihg]
    slice_lhs 1 2 => rw [ihf]
    simp
  -- p ≠ nil required! See the docstring of `normalizeAux`.
  | whisker_left _ _ ih =>
    dsimp
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ih]
    simp
  | whisker_right h η' ih =>
    dsimp
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ih, comp_whiskerRight]
    have := dcongr_arg (fun x => (normalizeIso x h).hom) (normalizeAux_congr p (Quot.mk _ η'))
    dsimp at this; simp [this]
  | _ => simp
#align category_theory.free_bicategory.normalize_naturality CategoryTheory.FreeBicategory.normalize_naturality

-- Porting note: the left-hand side is not in simp-normal form.
-- @[simp]
theorem normalizeAux_nil_comp {a b c : B} (f : Hom a b) (g : Hom b c) :
    normalizeAux nil (f.comp g) = (normalizeAux nil f).comp (normalizeAux nil g) := by
  induction g generalizing a with
  | id => rfl
  | of => rfl
  | comp g _ ihf ihg => erw [ihg (f.comp g), ihf f, ihg g, comp_assoc]
#align category_theory.free_bicategory.normalize_aux_nil_comp CategoryTheory.FreeBicategory.normalizeAux_nil_comp

/-- The normalization pseudofunctor for the free bicategory on a quiver `B`. -/
def normalize (B : Type u) [Quiver.{v + 1} B] :
    Pseudofunctor (FreeBicategory B) (LocallyDiscrete (Paths B)) where
  obj a := ⟨a⟩
  map f := ⟨normalizeAux nil f⟩
  map₂ η := eqToHom <| Discrete.ext _ _ <| normalizeAux_congr nil η
  mapId a := eqToIso <| Discrete.ext _ _ rfl
  mapComp f g := eqToIso <| Discrete.ext _ _ <| normalizeAux_nil_comp f g
#align category_theory.free_bicategory.normalize CategoryTheory.FreeBicategory.normalize

/-- Auxiliary definition for `normalizeEquiv`. -/
def normalizeUnitIso (a b : FreeBicategory B) :
    𝟭 (a ⟶ b) ≅ (normalize B).mapFunctor a b ⋙ @inclusionPath B _ a b :=
  NatIso.ofComponents (fun f => (λ_ f).symm ≪≫ normalizeIso nil f)
    (by
      intro f g η
      erw [leftUnitor_inv_naturality_assoc, assoc]
      congr 1
      exact normalize_naturality nil η)
#align category_theory.free_bicategory.normalize_unit_iso CategoryTheory.FreeBicategory.normalizeUnitIso

/-- Normalization as an equivalence of categories. -/
def normalizeEquiv (a b : B) : Hom a b ≌ Discrete (Path.{v + 1} a b) :=
  Equivalence.mk ((normalize _).mapFunctor a b) (inclusionPath a b) (normalizeUnitIso a b)
    (Discrete.natIso fun f => eqToIso (by
      induction' f with f
      induction' f with _ _ _ _ ih
      -- Porting note: `tidy` closes the goal in mathlib3 but `aesop` doesn't here.
      · rfl
      · ext1
        injection ih with ih
        conv_rhs => rw [← ih]
        rfl))
#align category_theory.free_bicategory.normalize_equiv CategoryTheory.FreeBicategory.normalizeEquiv

/-- The coherence theorem for bicategories. -/
instance locally_thin {a b : FreeBicategory B} : Quiver.IsThin (a ⟶ b) := fun _ _ =>
  ⟨fun _ _ =>
    (@normalizeEquiv B _ a b).functor.map_injective (Subsingleton.elim _ _)⟩
#align category_theory.free_bicategory.locally_thin CategoryTheory.FreeBicategory.locally_thin

/-- Auxiliary definition for `inclusion`. -/
def inclusionMapCompAux {a b : B} :
    ∀ {c : B} (f : Path a b) (g : Path b c),
      (preinclusion _).map (⟨f⟩ ≫ ⟨g⟩) ≅ (preinclusion _).map ⟨f⟩ ≫ (preinclusion _).map ⟨g⟩
  | _, f, nil => (ρ_ ((preinclusion _).map ⟨f⟩)).symm
  | _, f, cons g₁ g₂ => whiskerRightIso (inclusionMapCompAux f g₁) (Hom.of g₂) ≪≫ α_ _ _ _
#align category_theory.free_bicategory.inclusion_map_comp_aux CategoryTheory.FreeBicategory.inclusionMapCompAux

/-- The inclusion pseudofunctor from the locally discrete bicategory on the path category into the
free bicategory.
-/
def inclusion (B : Type u) [Quiver.{v + 1} B] :
    Pseudofunctor (LocallyDiscrete (Paths B)) (FreeBicategory B) :=
  { -- All the conditions for 2-morphisms are trivial thanks to the coherence theorem!
    preinclusion B with
    mapId := fun a => Iso.refl _
    mapComp := fun f g => inclusionMapCompAux f.as g.as }
#align category_theory.free_bicategory.inclusion CategoryTheory.FreeBicategory.inclusion

end FreeBicategory

end CategoryTheory
