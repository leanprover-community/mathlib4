/-
Copyright (c) 2021 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path

#align_import topology.homotopy.product from "leanprover-community/mathlib"@"6a51706df6baee825ace37c94dc9f75b64d7f035"

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


noncomputable section

namespace ContinuousMap

open ContinuousMap

section Pi

variable {I A : Type*} {X : I → Type*} [∀ i, TopologicalSpace (X i)] [TopologicalSpace A]
  {f g : ∀ i, C(A, X i)} {S : Set A}

-- Porting note: this definition is already in `Topology.Homotopy.Basic`
-- /-- The product homotopy of `homotopies` between functions `f` and `g` -/
-- @[simps]
-- def Homotopy.pi (homotopies : ∀ i, Homotopy (f i) (g i)) : Homotopy (pi f) (pi g) where
--   toFun t i := homotopies i t
--   map_zero_left t := by ext i; simp only [pi_eval, Homotopy.apply_zero]
--   map_one_left t := by ext i; simp only [pi_eval, Homotopy.apply_one]
-- #align continuous_map.homotopy.pi ContinuousMap.Homotopy.pi

/-- The relative product homotopy of `homotopies` between functions `f` and `g` -/
@[simps!]
def HomotopyRel.pi (homotopies : ∀ i : I, HomotopyRel (f i) (g i) S) :
    HomotopyRel (pi f) (pi g) S :=
  { Homotopy.pi fun i => (homotopies i).toHomotopy with
    prop' := by
      intro t x hx
      dsimp only [coe_mk, pi_eval, toFun_eq_coe, HomotopyWith.coe_toContinuousMap]
      simp only [Function.funext_iff, ← forall_and]
      intro i
      exact (homotopies i).prop' t x hx }
#align continuous_map.homotopy_rel.pi ContinuousMap.HomotopyRel.pi

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
#align continuous_map.homotopy.prod ContinuousMap.Homotopy.prod

/-- The relative product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁` and `G` takes `g₀` to `g₁` -/
@[simps!]
def HomotopyRel.prod (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel g₀ g₁ S) :
    HomotopyRel (prodMk f₀ g₀) (prodMk f₁ g₁) S where
  toHomotopy := Homotopy.prod F.toHomotopy G.toHomotopy
  prop' t x hx := Prod.ext (F.prop' t x hx) (G.prop' t x hx)
#align continuous_map.homotopy_rel.prod ContinuousMap.HomotopyRel.prod

end Prod

end ContinuousMap

namespace Path.Homotopic

attribute [local instance] Path.Homotopic.setoid

local infixl:70 " ⬝ " => Quotient.comp

section Pi

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {as bs cs : ∀ i, X i}

/-- The product of a family of path homotopies. This is just a specialization of `HomotopyRel`. -/
def piHomotopy (γ₀ γ₁ : ∀ i, Path (as i) (bs i)) (H : ∀ i, Path.Homotopy (γ₀ i) (γ₁ i)) :
    Path.Homotopy (Path.pi γ₀) (Path.pi γ₁) :=
  ContinuousMap.HomotopyRel.pi H
#align path.homotopic.pi_homotopy Path.Homotopic.piHomotopy

/-- The product of a family of path homotopy classes. -/
def pi (γ : ∀ i, Path.Homotopic.Quotient (as i) (bs i)) : Path.Homotopic.Quotient as bs :=
  (Quotient.map Path.pi fun x y hxy =>
    Nonempty.map (piHomotopy x y) (Classical.nonempty_pi.mpr hxy)) (Quotient.choice γ)
#align path.homotopic.pi Path.Homotopic.pi

theorem pi_lift (γ : ∀ i, Path (as i) (bs i)) :
    (Path.Homotopic.pi fun i => ⟦γ i⟧) = ⟦Path.pi γ⟧ := by unfold pi; simp
#align path.homotopic.pi_lift Path.Homotopic.pi_lift

/-- Composition and products commute.
  This is `Path.trans_pi_eq_pi_trans` descended to path homotopy classes. -/
theorem comp_pi_eq_pi_comp (γ₀ : ∀ i, Path.Homotopic.Quotient (as i) (bs i))
    (γ₁ : ∀ i, Path.Homotopic.Quotient (bs i) (cs i)): pi γ₀ ⬝ pi γ₁ = pi fun i => γ₀ i ⬝ γ₁ i := by
  apply Quotient.induction_on_pi (p := _) γ₁
  intro a
  apply Quotient.induction_on_pi (p := _) γ₀
  intros
  simp only [pi_lift]
  rw [← Path.Homotopic.comp_lift, Path.trans_pi_eq_pi_trans, ← pi_lift]
  rfl
#align path.homotopic.comp_pi_eq_pi_comp Path.Homotopic.comp_pi_eq_pi_comp

/-- Abbreviation for projection onto the ith coordinate. -/
abbrev proj (i : ι) (p : Path.Homotopic.Quotient as bs) : Path.Homotopic.Quotient (as i) (bs i) :=
  p.mapFn ⟨_, continuous_apply i⟩
#align path.homotopic.proj Path.Homotopic.proj

/-- Lemmas showing projection is the inverse of pi. -/
@[simp]
theorem proj_pi (i : ι) (paths : ∀ i, Path.Homotopic.Quotient (as i) (bs i)) :
    proj i (pi paths) = paths i := by
  apply Quotient.induction_on_pi (p := _) paths
  intro; unfold proj
  rw [pi_lift, ← Path.Homotopic.map_lift]
  congr
#align path.homotopic.proj_pi Path.Homotopic.proj_pi

@[simp]
theorem pi_proj (p : Path.Homotopic.Quotient as bs) : (pi fun i => proj i p) = p := by
  apply Quotient.inductionOn (motive := _) p
  intro; unfold proj
  simp_rw [← Path.Homotopic.map_lift]
  erw [pi_lift]
  congr
#align path.homotopic.pi_proj Path.Homotopic.pi_proj

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
#align path.homotopic.prod_homotopy Path.Homotopic.prodHomotopy

/-- The product of path classes q₁ and q₂. This is `Path.prod` descended to the quotient. -/
def prod (q₁ : Path.Homotopic.Quotient a₁ a₂) (q₂ : Path.Homotopic.Quotient b₁ b₂) :
    Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂) :=
  Quotient.map₂ Path.prod (fun _ _ h₁ _ _ h₂ => Nonempty.map2 prodHomotopy h₁ h₂) q₁ q₂
#align path.homotopic.prod Path.Homotopic.prod

variable (p₁ p₁' p₂ p₂')

theorem prod_lift : prod ⟦p₁⟧ ⟦p₂⟧ = ⟦p₁.prod p₂⟧ :=
  rfl
#align path.homotopic.prod_lift Path.Homotopic.prod_lift

variable (r₁ : Path.Homotopic.Quotient a₂ a₃) (r₂ : Path.Homotopic.Quotient b₂ b₃)

/-- Products commute with path composition.
    This is `trans_prod_eq_prod_trans` descended to the quotient. -/
theorem comp_prod_eq_prod_comp : prod q₁ q₂ ⬝ prod r₁ r₂ = prod (q₁ ⬝ r₁) (q₂ ⬝ r₂) := by
  apply Quotient.inductionOn₂ (motive := _) q₁ q₂
  intro a b
  apply Quotient.inductionOn₂ (motive := _) r₁ r₂
  intros
  simp only [prod_lift, ← Path.Homotopic.comp_lift, Path.trans_prod_eq_prod_trans]
#align path.homotopic.comp_prod_eq_prod_comp Path.Homotopic.comp_prod_eq_prod_comp

variable {c₁ c₂ : α × β}

/-- Abbreviation for projection onto the left coordinate of a path class. -/
abbrev projLeft (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁.1 c₂.1 :=
  p.mapFn ⟨_, continuous_fst⟩
#align path.homotopic.proj_left Path.Homotopic.projLeft

/-- Abbreviation for projection onto the right coordinate of a path class. -/
abbrev projRight (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁.2 c₂.2 :=
  p.mapFn ⟨_, continuous_snd⟩
#align path.homotopic.proj_right Path.Homotopic.projRight

/-- Lemmas showing projection is the inverse of product. -/
@[simp]
theorem projLeft_prod : projLeft (prod q₁ q₂) = q₁ := by
  apply Quotient.inductionOn₂ (motive := _) q₁ q₂
  intro p₁ p₂
  unfold projLeft
  rw [prod_lift, ← Path.Homotopic.map_lift]
  congr
#align path.homotopic.proj_left_prod Path.Homotopic.projLeft_prod

@[simp]
theorem projRight_prod : projRight (prod q₁ q₂) = q₂ := by
  apply Quotient.inductionOn₂ (motive := _) q₁ q₂
  intro p₁ p₂
  unfold projRight
  rw [prod_lift, ← Path.Homotopic.map_lift]
  congr
#align path.homotopic.proj_right_prod Path.Homotopic.projRight_prod

@[simp]
theorem prod_projLeft_projRight (p : Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂)) :
    prod (projLeft p) (projRight p) = p := by
  apply Quotient.inductionOn (motive := _) p
  intro p'
  unfold projLeft; unfold projRight
  simp only [← Path.Homotopic.map_lift, prod_lift]
  congr
#align path.homotopic.prod_proj_left_proj_right Path.Homotopic.prod_projLeft_projRight

end Prod

end Path.Homotopic
