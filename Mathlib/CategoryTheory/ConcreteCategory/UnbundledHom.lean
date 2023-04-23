/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module category_theory.concrete_category.unbundled_hom
! leanprover-community/mathlib commit f153a85a8dc0a96ce9133fed69e34df72f7f191f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom

/-!
# Category instances for structures that use unbundled homs

This file provides basic infrastructure to define concrete
categories using unbundled homs (see `class unbundled_hom`), and
define forgetful functors between them (see
`unbundled_hom.mk_has_forget₂`).
-/


universe v u

namespace CategoryTheory

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`hom_id] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`hom_comp] [] -/
/-- A class for unbundled homs used to define a category. `hom` must
take two types `α`, `β` and instances of the corresponding structures,
and return a predicate on `α → β`. -/
class UnbundledHom {c : Type u → Type u} (hom : ∀ {α β}, c α → c β → (α → β) → Prop) where
  hom_id : ∀ {α} (ia : c α), hom ia ia id
  hom_comp :
    ∀ {α β γ} {Iα : c α} {Iβ : c β} {Iγ : c γ} {g : β → γ} {f : α → β} (hg : hom Iβ Iγ g)
      (hf : hom Iα Iβ f), hom Iα Iγ (g ∘ f)
#align category_theory.unbundled_hom CategoryTheory.UnbundledHom

namespace UnbundledHom

variable (c : Type u → Type u) (hom : ∀ ⦃α β⦄, c α → c β → (α → β) → Prop) [𝒞 : UnbundledHom hom]

include 𝒞

instance bundledHom : BundledHom fun α β (Iα : c α) (Iβ : c β) => Subtype (hom Iα Iβ)
    where
  toFun _ _ _ _ := Subtype.val
  id α Iα := ⟨id, hom_id hom Iα⟩
  id_toFun := by intros <;> rfl
  comp _ _ _ _ _ _ g f := ⟨g.1 ∘ f.1, hom_comp c g.2 f.2⟩
  comp_toFun := by intros <;> rfl
  hom_ext := by intros <;> apply Subtype.eq
#align category_theory.unbundled_hom.bundled_hom CategoryTheory.UnbundledHom.bundledHom

section HasForget₂

variable {c hom} {c' : Type u → Type u} {hom' : ∀ ⦃α β⦄, c' α → c' β → (α → β) → Prop}
  [𝒞' : UnbundledHom hom']

include 𝒞'

variable (obj : ∀ ⦃α⦄, c α → c' α)
  (map : ∀ ⦃α β Iα Iβ f⦄, @hom α β Iα Iβ f → hom' (obj Iα) (obj Iβ) f)

/-- A custom constructor for forgetful functor
between concrete categories defined using `unbundled_hom`. -/
def mkHasForget₂ : HasForget₂ (Bundled c) (Bundled c') :=
  BundledHom.mkHasForget₂ obj (fun X Y f => ⟨f.val, map f.property⟩) fun _ _ _ => rfl
#align category_theory.unbundled_hom.mk_has_forget₂ CategoryTheory.UnbundledHom.mkHasForget₂

end HasForget₂

end UnbundledHom

end CategoryTheory

