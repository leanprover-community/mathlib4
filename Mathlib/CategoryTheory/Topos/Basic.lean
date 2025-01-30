/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Topos.Power


/-!
# Topoi

We follow Mac Lane and Moerdijk in defining a topos as a category
with a terminal object, pullbacks, a subobject classifier, and
power objects.

In this file, a "predicate" refers to any morphism into `Ω C`.

## Main definitions

* `CategoryTheory.Topos C` is a typeclass asserting that `C` is a topos.

* The namespace `CategoryTheory.Topos.Predicate` provides an API for various
  useful predicates, such as `Predicate.eq` as the equality predicate
  `B ⨯ B ⟶ Ω C`, and `Predicate.isSingleton` which is the classifier of the
  singleton map `singleton B : B ⟶ Pow B`.

## Main results

* `singleton B : B ⟶ Pow B` is a monomorphism. This is `singletonMono`.

## Notation

* If `φ` is a predicate `X ⟶ Ω C`, `⌈φ⌉` is shorthand for `Name φ`,
  which is the global element `⊤_ C ⟶ Pow X` associated to `φ`.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MLM92]

-/

namespace CategoryTheory

open Category Limits Classifier Power

universe u v

variable (C : Type u) [Category.{v} C]

/-- A category is a topos if it has a terminal object,
all pullbacks, a subobject classifier, and power objects.
-/
class Topos where
  /-- A topos has a terminal object. -/
  [has_terminal : HasTerminal C]
  /-- A topos has pullbacks. -/
  [has_pullbacks : HasPullbacks C]
  /-- A topos has a subobject classifier. -/
  [subobject_classifier : HasClassifier C]
  /-- A topos has power objects. -/
  [has_power_objects : HasPowers C]

attribute [instance] Topos.has_terminal Topos.has_pullbacks
                     Topos.subobject_classifier Topos.has_power_objects

variable [Topos C] {C}

namespace Topos

/-- A topos has (chosen) finite products. -/
noncomputable instance chosenFiniteProducts : ChosenFiniteProducts C :=
  ChosenFiniteProducts.ofFiniteProducts C
/-- A topos has binary products. -/
instance hasBinaryProducts : HasBinaryProducts C :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks C
/-- A topos has finite products. -/
instance hasFiniteProducts : HasFiniteProducts C :=
  hasFiniteProducts_of_has_binary_and_terminal
/-- A topos has equalizers, since it has pullbacks and
binary products.
-/
instance hasEqualizers : HasEqualizers C :=
  hasEqualizers_of_hasPullbacks_and_binary_products


noncomputable section

/-- The predicate on `B` which corresponds to the subobject `𝟙 B: B ⟶ B`. -/
def Predicate.true_ (B : C) : B ⟶ Ω C := terminal.from B ≫ (t C)

/--
  The equality predicate on `B ⨯ B`.
-/
def Predicate.eq (B : C) : B ⨯ B ⟶ Ω C := ClassifierOf (diag B)

/-- The lift `X ⟶ B ⨯ B` of a morphism with itself, when composed
with `predicate.eq B`, is true.
-/
lemma Predicate.lift_eq {X B : C} (b : X ⟶ B) :
    prod.lift b b ≫ Predicate.eq B = Predicate.true_ X := by
  dsimp only [eq, true_]
  rw [←prod.comp_diag b, assoc, (ClassifierComm (diag B)), ←assoc, terminal.comp_from]

/-- Two maps in a topos are equal if their lift composed with
the equality predicate on `B ⨯ B` is true.
In other words, this combined with `Predicate.lift_eq` states that
`Predicate.eq` is able to distinguish whether two morphisms are equal.
-/
lemma Predicate.eq_of_lift_eq {X B : C} {b b' : X ⟶ B}
  (comm' : prod.lift b b' ≫ Predicate.eq B = Predicate.true_ X) :
    b = b' := by
  dsimp only [eq, true_] at comm'
  let cone_lift := ClassifierCone_into (comm' := comm')
  have t : cone_lift ≫ diag _ = prod.lift b b' := ClassifierCone_into_comm (comm' := comm')
  rw [prod.comp_diag] at t
  have t₁ := congrArg (fun k ↦ k ≫ prod.fst) t
  have t₂ := congrArg (fun k ↦ k ≫ prod.snd) t
  simp at t₁
  simp at t₂
  exact t₁.symm.trans t₂

/-- The "singleton" map `B ⟶ Pow B`.
In Set, this map sends `b ∈ B` to the
singleton set containing just `b`.
-/
def singleton (B : C) : B ⟶ Pow B := (Predicate.eq B)^

/-- `singleton B : B ⟶ Pow B` is a monomorphism. -/
instance singletonMono (B : C) : Mono (singleton B) where
  right_cancellation := by
    intro X b b' h
    rw [singleton] at h
    have h₁ : prod.map (𝟙 _) (b ≫ (Predicate.eq B)^) ≫ in_ B
    = prod.map (𝟙 _) (b' ≫ (Predicate.eq B)^) ≫ in_ B :=
      congrFun (congrArg CategoryStruct.comp (congrArg (prod.map (𝟙 B)) h)) (in_ B)
    rw [prod.map_id_comp, assoc, Pow_powerizes, prod.map_id_comp, assoc, Pow_powerizes] at h₁
    have comm : (b ≫ terminal.from _) ≫ t C
    = prod.lift b (𝟙 _) ≫ prod.map (𝟙 _) b ≫ Predicate.eq _ := by
      rw [terminal.comp_from, ←assoc, prod.lift_map, comp_id,
          id_comp, Predicate.lift_eq, Predicate.true_]
    rw [terminal.comp_from, h₁, ←assoc, prod.lift_map, id_comp, comp_id] at comm
    exact Predicate.eq_of_lift_eq comm.symm

/-- The predicate on `Pow B` which picks out the subobject of "singletons".
-/
def Predicate.isSingleton (B : C) : Pow B ⟶ Ω C := χ_ (singleton B)

/-- The name ⌈φ⌉ : ⊤_ C ⟶ Pow B of a predicate `φ : B ⟶ Ω C`.
This is the global element of `Pow B` associated to a predicate
on `B`.
-/
def Name {B} (φ : B ⟶ Ω C) : ⊤_ C ⟶ Pow B := (((prod.fst) ≫ φ))^

/-- Notation for `Name`. Consistent with Mac Lane and Moerdijk's notation. -/
notation "⌈" φ "⌉" => Name φ

/-- The inverse of `Name`, sending a global element of `Pow B`
to the corresponding predicate on `B`.
-/
def Predicate.fromName {B} (φ' : ⊤_ C ⟶ Pow B) : B ⟶ Ω C :=
  (prod.lift (𝟙 B) (terminal.from B)) ≫ φ'^

/-- The condition from the definition of `Name`
as the `P_transpose` of a morphism.
-/
lemma Predicate.NameDef {B} (φ : B ⟶ Ω C) : (prod.map (𝟙 _) ⌈φ⌉) ≫ (in_ B) = (prod.fst) ≫ φ :=
  Pow_powerizes _ _

/-- The equivalence between morphisms `B ⟶ Ω C` and morphisms `⊤_ C ⟶ Pow B`,
which comes from the more general equivalence between morphisms `B ⨯ A ⟶ Ω C`
and morphisms `A ⟶ Pow B`.
-/
def Predicate.NameEquiv (B : C) : (B ⟶ Ω C) ≃ (⊤_ C ⟶ Pow B) where
  toFun := Name
  invFun := fromName
  left_inv := by
    intro φ
    dsimp [Name, fromName]
    rw [P_transpose_left_inv, ←assoc, prod.lift_fst, id_comp]
  right_inv := by
    intro φ'
    dsimp only [Name, fromName]
    have h := (Limits.prod.rightUnitor B).hom_inv_id
    dsimp at h
    rw [←assoc, h, id_comp, P_transpose_right_inv]

end
end CategoryTheory.Topos
