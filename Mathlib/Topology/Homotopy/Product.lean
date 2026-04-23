/-
Copyright (c) 2021 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.Topology.Homotopy.Path
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Product of homotopies

In this file, we introduce definitions for the product of
homotopies. We show that the products of relative homotopies
are still relative homotopies. Finally, we specialize to the case
of path homotopies, and provide the definition for the product of path classes.
We show various lemmas associated with these products, such as the fact that
path products commute with path composition, and that projection is the inverse
of products.

## Definitions
### General homotopies
- `ContinuousMap.Homotopy.pi homotopies`: Let f and g be a family of functions
  indexed on I, such that for each i ∈ I, fᵢ and gᵢ are maps from A to Xᵢ.
  Let `homotopies` be a family of homotopies from fᵢ to gᵢ for each i.
  Then `Homotopy.pi homotopies` is the canonical homotopy
  from ∏ f to ∏ g, where ∏ f is the product map from A to Πi, Xᵢ,
  and similarly for ∏ g.

- `ContinuousMap.HomotopyRel.pi homotopies`: Same as `ContinuousMap.Homotopy.pi`, but
  all homotopies are done relative to some set S ⊆ A.

- `ContinuousMap.Homotopy.prod F G` is the product of homotopies F and G,
  where F is a homotopy between f₀ and f₁, G is a homotopy between g₀ and g₁.
  The result F × G is a homotopy between (f₀ × g₀) and (f₁ × g₁).
  Again, all homotopies are done relative to S.

- `ContinuousMap.HomotopyRel.prod F G`: Same as `ContinuousMap.Homotopy.prod`, but
  all homotopies are done relative to some set S ⊆ A.

### Path products
- `Path.Homotopic.pi` The product of a family of path classes, where a path class is an equivalence
  class of paths up to path homotopy.

- `Path.Homotopic.prod` The product of two path classes.
-/

@[expose] public section


noncomputable section

namespace ContinuousMap

open ContinuousMap

section Pi

variable {I A : Type*} {X : I → Type*} [∀ i, TopologicalSpace (X i)] [TopologicalSpace A]
  {f g : ∀ i, C(A, X i)} {S : Set A}

/-- The relative product homotopy of `homotopies` between functions `f` and `g` -/
@[simps!]
def HomotopyRel.pi (homotopies : ∀ i : I, HomotopyRel (f i) (g i) S) :
    HomotopyRel (pi f) (pi g) S :=
  { Homotopy.pi fun i => (homotopies i).toHomotopy with
    prop' := by
      intro t x hx
      dsimp only [coe_mk, pi_eval, toFun_eq_coe, HomotopyWith.coe_toContinuousMap]
      simp only [funext_iff]
      intro i
      exact (homotopies i).prop' t x hx }

end Pi

section Prod

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {A : Type*} [TopologicalSpace A]
  {f₀ f₁ : C(A, α)} {g₀ g₁ : C(A, β)} {S : Set A}

/-- The product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁` and `G` takes `g₀` to `g₁` -/
@[simps]
def Homotopy.prod (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (ContinuousMap.prodMk f₀ g₀) (ContinuousMap.prodMk f₁ g₁) where
  toFun t := (F t, G t)
  map_zero_left x := by simp only [prod_eval, Homotopy.apply_zero]
  map_one_left x := by simp only [prod_eval, Homotopy.apply_one]

/-- The relative product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁` and `G` takes `g₀` to `g₁` -/
@[simps!]
def HomotopyRel.prod (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel g₀ g₁ S) :
    HomotopyRel (prodMk f₀ g₀) (prodMk f₁ g₁) S where
  toHomotopy := Homotopy.prod F.toHomotopy G.toHomotopy
  prop' t x hx := Prod.ext (F.prop' t x hx) (G.prop' t x hx)

end Prod

end ContinuousMap

namespace Path.Homotopic

local infixl:70 " ⬝ " => Quotient.trans

section Pi

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {as bs cs : ∀ i, X i}

/-- The product of a family of path homotopies. This is just a specialization of `HomotopyRel`. -/
def piHomotopy (γ₀ γ₁ : ∀ i, Path (as i) (bs i)) (H : ∀ i, Path.Homotopy (γ₀ i) (γ₁ i)) :
    Path.Homotopy (Path.pi γ₀) (Path.pi γ₁) :=
  ContinuousMap.HomotopyRel.pi H

/-- The product of a family of path homotopy classes. -/
def pi (γ : ∀ i, Path.Homotopic.Quotient (as i) (bs i)) : Path.Homotopic.Quotient as bs :=
  (_root_.Quotient.map Path.pi fun x y hxy =>
    Nonempty.map (piHomotopy x y) (Classical.nonempty_pi.mpr hxy)) (Quotient.choice γ)

theorem pi_lift (γ : ∀ i, Path (as i) (bs i)) :
    (Path.Homotopic.pi fun i => (Quotient.mk (γ i))) = Quotient.mk (Path.pi γ) := by
  simp_rw [← Quotient.mk'_eq_mk, Quotient.mk', pi, Quotient.choice_eq, Quotient.map_mk]

/-- Composition and products commute.
  This is `Path.trans_pi_eq_pi_trans` descended to path homotopy classes. -/
theorem comp_pi_eq_pi_comp (γ₀ : ∀ i, Path.Homotopic.Quotient (as i) (bs i))
    (γ₁ : ∀ i, Path.Homotopic.Quotient (bs i) (cs i)) : pi γ₀ ⬝ pi γ₁ = pi fun i ↦ γ₀ i ⬝ γ₁ i := by
  induction γ₁ using Quotient.induction_on_pi with | _ a =>
  induction γ₀ using Quotient.induction_on_pi
  simp only [Quotient.mk''_eq_mk, pi_lift]
  rw [← Path.Homotopic.Quotient.mk_trans, Path.trans_pi_eq_pi_trans, ← pi_lift]
  rfl

/-- Abbreviation for projection onto the ith coordinate. -/
abbrev proj (i : ι) (p : Path.Homotopic.Quotient as bs) : Path.Homotopic.Quotient (as i) (bs i) :=
  p.map ⟨_, continuous_apply i⟩

/-- Lemmas showing projection is the inverse of pi. -/
@[simp]
theorem proj_pi (i : ι) (paths : ∀ i, Path.Homotopic.Quotient (as i) (bs i)) :
    proj i (pi paths) = paths i := by
  induction paths using Quotient.induction_on_pi
  simp only [Quotient.mk''_eq_mk]
  rw [proj, pi_lift]
  congr

@[simp]
theorem pi_proj (p : Path.Homotopic.Quotient as bs) : (pi fun i => proj i p) = p := by
  induction p using Quotient.inductionOn
  simp_rw [Quotient.mk''_eq_mk, proj, ← Path.Homotopic.Quotient.mk_map]
  erw [pi_lift]
  congr

end Pi

section Prod

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {a₁ a₂ a₃ : α} {b₁ b₂ b₃ : β}
  {p₁ p₁' : Path a₁ a₂} {p₂ p₂' : Path b₁ b₂} (q₁ : Path.Homotopic.Quotient a₁ a₂)
  (q₂ : Path.Homotopic.Quotient b₁ b₂)

/-- The product of homotopies h₁ and h₂.
This is `HomotopyRel.prod` specialized for path homotopies. -/
def prodHomotopy (h₁ : Path.Homotopy p₁ p₁') (h₂ : Path.Homotopy p₂ p₂') :
    Path.Homotopy (p₁.prod p₂) (p₁'.prod p₂') :=
  ContinuousMap.HomotopyRel.prod h₁ h₂

/-- The product of path classes q₁ and q₂. This is `Path.prod` descended to the quotient. -/
def prod (q₁ : Path.Homotopic.Quotient a₁ a₂) (q₂ : Path.Homotopic.Quotient b₁ b₂) :
    Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂) :=
  Quotient.map₂ Path.prod (fun _ _ h₁ _ _ h₂ => Nonempty.map2 prodHomotopy h₁ h₂) q₁ q₂

variable (p₁ p₁' p₂ p₂')

theorem prod_lift : prod (Quotient.mk p₁) (Quotient.mk p₂) = Quotient.mk (p₁.prod p₂) :=
  rfl

variable (r₁ : Path.Homotopic.Quotient a₂ a₃) (r₂ : Path.Homotopic.Quotient b₂ b₃)

/-- Products commute with path composition.
This is `trans_prod_eq_prod_trans` descended to the quotient. -/
theorem comp_prod_eq_prod_comp : prod q₁ q₂ ⬝ prod r₁ r₂ = prod (q₁ ⬝ r₁) (q₂ ⬝ r₂) := by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  induction r₁, r₂ using Path.Homotopic.Quotient.ind₂
  simp only [prod_lift, ← Path.Homotopic.Quotient.mk_trans, Path.trans_prod_eq_prod_trans]

variable {c₁ c₂ : α × β}

/-- Abbreviation for projection onto the left coordinate of a path class. -/
abbrev projLeft (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁.1 c₂.1 :=
  p.map ⟨_, continuous_fst⟩

/-- Abbreviation for projection onto the right coordinate of a path class. -/
abbrev projRight (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁.2 c₂.2 :=
  p.map ⟨_, continuous_snd⟩

/-- Lemmas showing projection is the inverse of product. -/
@[simp]
theorem projLeft_prod : projLeft (prod q₁ q₂) = q₁ := by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  rw [projLeft, prod_lift, ← Path.Homotopic.Quotient.mk_map]
  congr

@[simp]
theorem projRight_prod : projRight (prod q₁ q₂) = q₂ := by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  rw [projRight, prod_lift, ← Path.Homotopic.Quotient.mk_map]
  congr

@[simp]
theorem prod_projLeft_projRight (p : Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂)) :
    prod (projLeft p) (projRight p) = p := by
  induction p using Path.Homotopic.Quotient.ind
  simp only [projLeft, projRight, ← Path.Homotopic.Quotient.mk_map]
  congr

end Prod

end Path.Homotopic
