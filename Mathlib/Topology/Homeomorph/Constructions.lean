/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Bases -- only used for piUnique
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Miscellaneous constructions around homeomorphisms

TODO: write a doc-string here!

# Main definitions and results

* Pretty much every topological property is preserved under homeomorphisms.

-/

open Filter Function Set Topology

variable {X Y W Z : Type*}

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

-- Commutativity and associativity of the product of top. spaces, and the product with `PUnit`.
section prod

variable (X Y W Z)

/-- The product over `S ⊕ T` of a family of topological spaces
is homeomorphic to the product of (the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `Homeomorph`.
-/
def sumPiEquivProdPi (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, TopologicalSpace (A st)] :
    (Π (st : S ⊕ T), A st) ≃ₜ (Π (s : S), A (.inl s)) × (Π (t : T), A (.inr t)) where
  __ := Equiv.sumPiEquivProdPi _
  continuous_toFun := Continuous.prodMk (by fun_prop) (by fun_prop)
  continuous_invFun := continuous_pi <| by rintro (s | t) <;> simp <;> fun_prop

/-- The product `Π t : α, f t` of a family of topological spaces is homeomorphic to the
space `f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `Homeomorph`.
-/
@[simps! -fullyApplied]
def piUnique {α : Type*} [Unique α] (f : α → Type*) [∀ x, TopologicalSpace (f x)] :
    (Π t, f t) ≃ₜ f default :=
  homeomorphOfContinuousOpen (Equiv.piUnique f) (continuous_apply default) (isOpenMap_eval _)

end prod

section Distrib

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- `(Σ i, X i) × Y` is homeomorphic to `Σ i, (X i × Y)`. -/
@[simps! apply symm_apply toEquiv]
def sigmaProdDistrib : (Σ i, X i) × Y ≃ₜ Σ i, X i × Y :=
  Homeomorph.symm <|
    homeomorphOfContinuousOpen (Equiv.sigmaProdDistrib X Y).symm
      (continuous_sigma fun _ => continuous_sigmaMk.fst'.prodMk continuous_snd)
      (isOpenMap_sigma.2 fun _ => isOpenMap_sigmaMk.prodMap IsOpenMap.id)

end Distrib

/-- If `ι` has a unique element, then `ι → X` is homeomorphic to `X`. -/
@[simps! -fullyApplied]
def funUnique (ι X : Type*) [Unique ι] [TopologicalSpace X] : (ι → X) ≃ₜ X where
  toEquiv := Equiv.funUnique ι X
  continuous_toFun := continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_id

/-- A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
@[simps!]
def image (e : X ≃ₜ Y) (s : Set X) : s ≃ₜ e '' s where
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: by continuity!
  continuous_toFun := e.continuous.continuousOn.restrict_mapsTo (mapsTo_image _ _)
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).codRestrict _
  toEquiv := e.toEquiv.image s

/-- `Set.univ X` is homeomorphic to `X`. -/
@[simps! -fullyApplied]
def Set.univ (X : Type*) [TopologicalSpace X] : (univ : Set X) ≃ₜ X where
  toEquiv := Equiv.Set.univ X
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- `s ×ˢ t` is homeomorphic to `s × t`. -/
@[simps!]
def Set.prod (s : Set X) (t : Set Y) : ↥(s ×ˢ t) ≃ₜ s × t where
  toEquiv := Equiv.Set.prod s t
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: align the order of universes with `Equiv.ulift`
/-- `ULift X` is homeomorphic to `X`. -/
def ulift.{u, v} {X : Type u} [TopologicalSpace X] : ULift.{v, u} X ≃ₜ X where
  continuous_toFun := continuous_uliftDown
  continuous_invFun := continuous_uliftUp
  toEquiv := Equiv.ulift

/-- `Equiv.piCongrLeft` as a homeomorphism: this is the natural homeomorphism
`Π i, Y (e i) ≃ₜ Π j, Y j` obtained from a bijection `ι ≃ ι'`. -/
@[simps! apply toEquiv]
def piCongrLeft {ι ι' : Type*} {Y : ι' → Type*} [∀ j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') : (∀ i, Y (e i)) ≃ₜ ∀ j, Y j where
  continuous_toFun := continuous_pi <| e.forall_congr_right.mp fun i ↦ by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using continuous_apply i
  continuous_invFun := Pi.continuous_precomp' e
  toEquiv := Equiv.piCongrLeft _ e

/-- `Equiv.piCongrRight` as a homeomorphism: this is the natural homeomorphism
`Π i, Y₁ i ≃ₜ Π j, Y₂ i` obtained from homeomorphisms `Y₁ i ≃ₜ Y₂ i` for each `i`. -/
@[simps! apply toEquiv]
def piCongrRight {ι : Type*} {Y₁ Y₂ : ι → Type*} [∀ i, TopologicalSpace (Y₁ i)]
    [∀ i, TopologicalSpace (Y₂ i)] (F : ∀ i, Y₁ i ≃ₜ Y₂ i) : (∀ i, Y₁ i) ≃ₜ ∀ i, Y₂ i where
  continuous_toFun := Pi.continuous_postcomp' fun i ↦ (F i).continuous
  continuous_invFun := Pi.continuous_postcomp' fun i ↦ (F i).symm.continuous
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]
theorem piCongrRight_symm {ι : Type*} {Y₁ Y₂ : ι → Type*} [∀ i, TopologicalSpace (Y₁ i)]
    [∀ i, TopologicalSpace (Y₂ i)] (F : ∀ i, Y₁ i ≃ₜ Y₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl

/-- `Equiv.piCongr` as a homeomorphism: this is the natural homeomorphism
`Π i₁, Y₁ i ≃ₜ Π i₂, Y₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and homeomorphisms
`Y₁ i₁ ≃ₜ Y₂ (e i₁)` for each `i₁ : ι₁`. -/
@[simps! apply toEquiv]
def piCongr {ι₁ ι₂ : Type*} {Y₁ : ι₁ → Type*} {Y₂ : ι₂ → Type*}
    [∀ i₁, TopologicalSpace (Y₁ i₁)] [∀ i₂, TopologicalSpace (Y₂ i₂)]
    (e : ι₁ ≃ ι₂) (F : ∀ i₁, Y₁ i₁ ≃ₜ Y₂ (e i₁)) : (∀ i₁, Y₁ i₁) ≃ₜ ∀ i₂, Y₂ i₂ :=
  (Homeomorph.piCongrRight F).trans (Homeomorph.piCongrLeft e)

/-- Homeomorphism between dependent functions `Π i : Fin 2, X i` and `X 0 × X 1`. -/
@[simps! -fullyApplied]
def piFinTwo.{u} (X : Fin 2 → Type u) [∀ i, TopologicalSpace (X i)] : (∀ i, X i) ≃ₜ X 0 × X 1 where
  toEquiv := piFinTwoEquiv X
  continuous_toFun := (continuous_apply 0).prodMk (continuous_apply 1)
  continuous_invFun := continuous_pi <| Fin.forall_fin_two.2 ⟨continuous_fst, continuous_snd⟩

/-- Homeomorphism between `X² = Fin 2 → X` and `X × X`. -/
@[simps! -fullyApplied]
def finTwoArrow : (Fin 2 → X) ≃ₜ X × X :=
  { piFinTwo fun _ => X with toEquiv := finTwoArrowEquiv X }

/-- The natural homeomorphism `(ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)`.
`Equiv.sumArrowEquivProdArrow` as a homeomorphism. -/
@[simps!]
def sumArrowHomeomorphProdArrow {ι ι' : Type*} : (ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)  where
  toEquiv := Equiv.sumArrowEquivProdArrow _ _ _
  continuous_toFun := by
    simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_mk]
    fun_prop
  continuous_invFun := continuous_pi fun i ↦ match i with
    | .inl i => by apply (continuous_apply _).comp' continuous_fst
    | .inr i => by apply (continuous_apply _).comp' continuous_snd

private theorem _root_.Fin.appendEquiv_eq_Homeomorph (m n : ℕ) : Fin.appendEquiv m n =
    ((sumArrowHomeomorphProdArrow).symm.trans
    (piCongrLeft (Y := fun _ ↦ X) finSumFinEquiv)).toEquiv := by
  ext ⟨x1, x2⟩ l
  simp only [sumArrowHomeomorphProdArrow, Equiv.sumArrowEquivProdArrow,
    finSumFinEquiv, Fin.addCases, Fin.appendEquiv, Fin.append, Equiv.coe_fn_mk]
  by_cases h : l < m
  · simp [h]
  · simp [h]

theorem _root_.Fin.continuous_append (m n : ℕ) :
    Continuous fun (p : (Fin m → X) × (Fin n → X)) ↦ Fin.append p.1 p.2 := by
  suffices Continuous (Fin.appendEquiv m n) by exact this
  rw [Fin.appendEquiv_eq_Homeomorph]
  exact Homeomorph.continuous_toFun _

/-- The natural homeomorphism between `(Fin m → X) × (Fin n → X)` and `Fin (m + n) → X`.
`Fin.appendEquiv` as a homeomorphism -/
@[simps!]
def _root_.Fin.appendHomeomorph (m n : ℕ) : (Fin m → X) × (Fin n → X) ≃ₜ (Fin (m + n) → X) where
  toEquiv := Fin.appendEquiv m n
  continuous_toFun := Fin.continuous_append m n
  continuous_invFun := by
    rw [Fin.appendEquiv_eq_Homeomorph]
    exact Homeomorph.continuous_invFun _

@[simp]
theorem _root_.Fin.appendHomeomorph_toEquiv (m n : ℕ) :
    (Fin.appendHomeomorph (X := X) m n).toEquiv = Fin.appendEquiv m n :=
  rfl

end Homeomorph
