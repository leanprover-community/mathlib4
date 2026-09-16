import Mathlib.Tactic.CategoryTheory.ToApp
import Mathlib.CategoryTheory.Bicategory.Functor.Prelax

universe w v u

namespace CategoryTheory.ToAppTest

open Bicategory Category

variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

@[to_app]
theorem whiskerLeft_hom_inv (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
    f ◁ η.hom ≫ f ◁ η.inv = 𝟙 (f ≫ g) := by
  rw [← Bicategory.whiskerLeft_comp, Iso.hom_inv_id, Bicategory.whiskerLeft_id]

example {a b c : Cat} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (X : a) :
    η.hom.toNatTrans.app (f.toFunctor.obj X) ≫ η.inv.toNatTrans.app (f.toFunctor.obj X) =
      𝟙 ((f ≫ g).toFunctor.obj X) :=
  whiskerLeft_hom_inv_app f η X

set_option backward.defeqAttrib.useBackward true in
@[to_app]
theorem pentagon_hom_hom_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv =
      (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom :=
  eq_of_inv_eq_inv (by simp)

example {a b c d e : Cat} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) (X : a) : True := by
  have hyp := pentagon_hom_hom_inv_inv_hom_app f g h i X
  guard_hyp hyp : 𝟙 (i.toFunctor.obj (h.toFunctor.obj (g.toFunctor.obj (f.toFunctor.obj X)))) =
    i.toFunctor.map (𝟙 (h.toFunctor.obj (g.toFunctor.obj (f.toFunctor.obj X))))
  trivial

@[to_app]
theorem testThm {C : Type*} [Bicategory C] (F : PrelaxFunctor B C) {a b : B} {f g : a ⟶ b}
    (η : f ⟶ g) : F.map₂ η ≫ F.map₂ (𝟙 g) = F.map₂ η := by simp

example {B : Type u_1} [Bicategory B] (F : PrelaxFunctor B Cat)
    {a b : B} {f g : a ⟶ b} (η : f ⟶ g) (X : ↑(F.obj a)) :
    (F.map₂ η).toNatTrans.app X ≫ (F.map₂ (𝟙 g)).toNatTrans.app X = (F.map₂ η).toNatTrans.app X :=
  testThm_app F η X

/-- error: `to_app` cannot specialize the bicategory B to `Cat` -/
#guard_msgs in
example {f g : a ⟶ b} (η θ : f ⟶ g) (h : η = θ) : True := to_app_of% h

abbrev BicategoryAlias (B : Type u) := Bicategory.{v, v} B

@[to_app]
theorem bicategory_alias_eq {B : Type u} [BicategoryAlias.{v} B] {a b : B}
    {f g : a ⟶ b} (η θ : f ⟶ g) (h : η = θ) : η = θ := h

example {C D : Cat} {F G : C ⟶ D} (η θ : F ⟶ G) (h : η = θ) (X : C) :
    η.toNatTrans.app X = θ.toNatTrans.app X := bicategory_alias_eq_app η θ h X

section UnbundledNatTrans

variable {C : Type u} [Category.{v} C] {D : Type u_1} [Category.{v_1} D]
variable {F G H K : C ⥤ D}

@[to_app]
theorem unbundled_eq_of_eq (η θ : F ⟶ G) (h : η = θ) : η = θ := h

example (η θ : F ⟶ G) (h : η = θ) (X : C) : True := by
  have hyp := unbundled_eq_of_eq_app η θ h X
  guard_hyp hyp : η.app X = θ.app X
  trivial

example (η θ : F ⟶ G) (h : η = θ) (X : C) : True := by
  have hyp := (to_app_of% h) X
  guard_hyp hyp : η.app X = θ.app X
  trivial

@[to_app]
theorem unbundled_comp_assoc (η : F ⟶ G) (θ : G ⟶ H) (κ : H ⟶ K) :
    (η ≫ θ) ≫ κ = η ≫ θ ≫ κ := by
  simp

example (η : F ⟶ G) (θ : G ⟶ H) (κ : H ⟶ K) (X : C) : True := by
  have hyp := unbundled_comp_assoc_app η θ κ X
  guard_hyp hyp : (η.app X ≫ θ.app X) ≫ κ.app X = η.app X ≫ θ.app X ≫ κ.app X
  trivial

section

@[implicit_reducible]
def foo (η : F ⟶ G) (θ : G ⟶ F) : F ⟶ F := η ≫ θ

@[to_app (attr := local simp)]
theorem unbundled_eq (η : F ⟶ G) (θ : G ⟶ F) : η ≫ θ = foo η θ := rfl

/--
info: CategoryTheory.ToAppTest.unbundled_eq_app.{v, u, u_1, v_1} {C : Type u} [Category.{v, u} C] {D : Type u_1}
  [Category.{v_1, u_1} D] {F G : C ⥤ D} (η : F ⟶ G) (θ : G ⟶ F) (X : C) : η.app X ≫ θ.app X = (foo η θ).app X
-/
#guard_msgs in
#check unbundled_eq_app

example (η : F ⟶ G) (θ : G ⟶ F) (X : C) : True := by
  have hyp := unbundled_eq_app η θ X
  guard_hyp hyp : η.app X ≫ θ.app X = (foo η θ).app X
  trivial

example (η : F ⟶ G) (θ : G ⟶ F) (X : C) : η.app X ≫ θ.app X = (foo η θ).app X := by
  simp

example (η : F ⟶ G) (θ : G ⟶ F) (X : C) : η.app X ≫ θ.app X = (foo η θ).app X := by
  dsimp

end

attribute [-simp] Iso.inv_hom_id Iso.inv_hom_id_app

@[to_app (attr := simp)]
theorem inv_hom_id (i : F ≅ G) : i.inv ≫ i.hom = 𝟙 _ :=
  i.inv_hom_id

/--
info: CategoryTheory.ToAppTest.inv_hom_id_app.{v, u, u_1, v_1} {C : Type u} [Category.{v, u} C] {D : Type u_1}
  [Category.{v_1, u_1} D] {F G : C ⥤ D} (i : F ≅ G) (X : C) : i.inv.app X ≫ i.hom.app X = 𝟙 (G.obj X)
-/
#guard_msgs in
#check inv_hom_id_app

example (i : F ≅ G) (X : C) : i.inv.app X ≫ i.hom.app X = 𝟙 _ := by
  simp

-- A definition that is not implicit-reducible only gives a backward-defeq lemma.
def semireducibleComp (η : F ⟶ G) (θ : G ⟶ H) : F ⟶ H := η ≫ θ

@[to_app]
theorem semireducibleComp_eq (η : F ⟶ G) (θ : G ⟶ H) :
    semireducibleComp η θ = η ≫ θ := rfl

run_cmd do
  let env ← Lean.getEnv
  unless Lean.defeqAttr.hasTag env ``unbundled_eq_app do
    throwError "Expected a defeq lemma"
  if Lean.defeqAttr.hasTag env ``semireducibleComp_eq_app then
    throwError "Unexpected defeq lemma for a semireducible definition"
  unless Lean.backwardDefeqAttr.hasTag env ``semireducibleComp_eq_app do
    throwError "Expected a backward-defeq lemma"
  if Lean.backwardDefeqAttr.hasTag env ``inv_hom_id_app then
    throwError "Unexpected backward-defeq lemma for a non-definitional equality"

set_option backward.defeqAttrib.useBackward true in
example (η : F ⟶ G) (θ : G ⟶ H) (X : C) :
    (semireducibleComp η θ).app X = η.app X ≫ θ.app X := by
  dsimp only [semireducibleComp_eq_app]

-- Simplification must preserve the equality, even when its sides become identical.
@[to_app]
theorem reflexive (η : F ⟶ G) : η = η := rfl

example (η : F ⟶ G) (X : C) : η.app X = η.app X := reflexive_app η X

-- Abbreviations and let-bound propositions are reduced before inspecting the equality.
abbrev Arrow (F G : C ⥤ D) := F ⟶ G
abbrev Same (η θ : Arrow F G) := η = θ
abbrev AllSame (η : Arrow F G) := ∀ θ, Same η θ → Same η θ

@[to_app]
theorem alias_eq (η θ : Arrow F G) (h : Same η θ) : Same η θ := h

@[to_app]
theorem forall_alias (η : Arrow F G) : AllSame η := fun _ h => h

@[to_app]
theorem let_eq (η θ : F ⟶ G) (h : η = θ) : let P := η = θ; P := h

example (η θ : F ⟶ G) (h : η = θ) (X : C) : η.app X = θ.app X := by
  have h₁ := alias_eq_app η θ h X
  have h₂ := forall_alias_app η θ h X
  have h₃ := let_eq_app η θ h X
  guard_hyp h₁ : η.app X = θ.app X
  guard_hyp h₂ : η.app X = θ.app X
  guard_hyp h₃ : η.app X = θ.app X
  exact (to_app_of% (forall_alias η)) θ h X

example (η θ : F ⟶ G) (h : η = θ) (X : C) : η.app X = θ.app X := by
  rw [to_app_of% (alias_eq _ _ h)]

@[to_app (attr := reassoc)]
theorem whisker_eq (η θ : F ⟶ G) (h : η = θ) (L : D ⥤ D) :
    Functor.whiskerRight η L = Functor.whiskerRight θ L := by rw [h]

example (η θ : F ⟶ G) (h : η = θ) (L : D ⥤ D) (X : C)
    {Y : D} (f : L.obj (G.obj X) ⟶ Y) :
    L.map (η.app X) ≫ f = L.map (θ.app X) ≫ f := whisker_eq_app_assoc η θ h L X f

end UnbundledNatTrans

-- Equations already in `Cat` do not have a quantified bicategory instance to specialize.
section BundledNatTrans

variable {C D : Cat.{v, u}} {F G H : C ⟶ D}

@[to_app]
theorem bundled_eq (η θ : F ⟶ G) (h : η = θ) : η = θ := h

example (η θ : F ⟶ G) (h : η = θ) (X : C) :
    η.toNatTrans.app X = θ.toNatTrans.app X := bundled_eq_app η θ h X

example (η θ : F ⟶ G) (h : η = θ) (X : C) :
    η.toNatTrans.app X = θ.toNatTrans.app X := (to_app_of% h) X

@[to_app]
theorem bundled_hom₂_eq (η θ : Cat.Hom₂ F G) (h : η = θ) : η = θ := h

example (η θ : Cat.Hom₂ F G) (h : η = θ) (X : C) :
    η.toNatTrans.app X = θ.toNatTrans.app X := bundled_hom₂_eq_app η θ h X

example (η : F ⟶ G) (θ : G ⟶ H) (X : C) :
    (η ≫ θ).toNatTrans.app X = η.toNatTrans.app X ≫ θ.toNatTrans.app X :=
  (to_app_of% (show η ≫ θ = η ≫ θ from rfl)) X

end BundledNatTrans

/-- error: `to_app` expects an equality -/
#guard_msgs in
example : True := to_app_of% True.intro

/-- error: `to_app` expects an equality of natural transformations or 2-morphisms -/
#guard_msgs in
example : True := to_app_of% (show 1 = 1 from rfl)

end CategoryTheory.ToAppTest
