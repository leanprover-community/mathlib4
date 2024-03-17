/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom

#align_import category_theory.concrete_category.unbundled_hom from "leanprover-community/mathlib"@"f153a85a8dc0a96ce9133fed69e34df72f7f191f"

/-!
# Category instances for structures that use unbundled homs

This file provides basic infrastructure to define concrete
categories using unbundled homs (see `class UnbundledHom`), and
define forgetful functors between them (see
`UnbundledHom.mkHasForget₂`).
-/


universe v u

namespace CategoryTheory

/-- A class for unbundled homs used to define a category. `hom` must
take two types `α`, `β` and instances of the corresponding structures,
and return a predicate on `α → β`. -/
class UnbundledHom {c : Type u → Type u} (hom : ∀ ⦃α β⦄, c α → c β → (α → β) → Prop) : Prop where
  hom_id : ∀ {α} (ia : c α), hom ia ia id
  hom_comp : ∀ {α β γ} {Iα : c α} {Iβ : c β} {Iγ : c γ} {g : β → γ} {f : α → β} (_ : hom Iβ Iγ g)
      (_ : hom Iα Iβ f), hom Iα Iγ (g ∘ f)
#align category_theory.unbundled_hom CategoryTheory.UnbundledHom

namespace UnbundledHom

variable (c : Type u → Type u) (hom : ∀ ⦃α β⦄, c α → c β → (α → β) → Prop) [𝒞 : UnbundledHom hom]

instance bundledHom : BundledHom fun α β (Iα : c α) (Iβ : c β) => Subtype (hom Iα Iβ) where
  toFun _ _ := Subtype.val
  id Iα := ⟨id, hom_id Iα⟩
  id_toFun _ := rfl
  comp _ _ _ g f := ⟨g.1 ∘ f.1, hom_comp g.2 f.2⟩
  comp_toFun _ _ _ _ _ := rfl
  hom_ext _ _ _ _ := Subtype.eq
#align category_theory.unbundled_hom.bundled_hom CategoryTheory.UnbundledHom.bundledHom

section HasForget₂

variable {c hom} {c' : Type u → Type u} {hom' : ∀ ⦃α β⦄, c' α → c' β → (α → β) → Prop}
  [𝒞' : UnbundledHom hom']

variable (obj : ∀ ⦃α⦄, c α → c' α)
  (map : ∀ ⦃α β Iα Iβ f⦄, @hom α β Iα Iβ f → hom' (obj Iα) (obj Iβ) f)

/-- A custom constructor for forgetful functor
between concrete categories defined using `UnbundledHom`. -/
def mkHasForget₂ : HasForget₂ (Bundled c) (Bundled c') :=
  BundledHom.mkHasForget₂ obj (fun f => ⟨f.val, map f.property⟩) fun _ => rfl
#align category_theory.unbundled_hom.mk_has_forget₂ CategoryTheory.UnbundledHom.mkHasForget₂

end HasForget₂

end UnbundledHom

end CategoryTheory
