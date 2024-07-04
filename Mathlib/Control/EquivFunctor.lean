/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Convert

#align_import control.equiv_functor from "leanprover-community/mathlib"@"d6aae1bcbd04b8de2022b9b83a5b5b10e10c777d"

/-!
# Functions functorial with respect to equivalences

An `EquivFunctor` is a function from `Type → Type` equipped with the additional data of
coherently mapping equivalences to equivalences.

In categorical language, it is an endofunctor of the "core" of the category `Type`.
-/


universe u₀ u₁ u₂ v₀ v₁ v₂

open Function

/-- An `EquivFunctor` is only functorial with respect to equivalences.

To construct an `EquivFunctor`, it suffices to supply just the function `f α → f β` from
an equivalence `α ≃ β`, and then prove the functor laws. It's then a consequence that
this function is part of an equivalence, provided by `EquivFunctor.mapEquiv`.
-/
class EquivFunctor (f : Type u₀ → Type u₁) where
  /-- The action of `f` on isomorphisms. -/
  map : ∀ {α β}, α ≃ β → f α → f β
  /-- `map` of `f` preserves the identity morphism. -/
  map_refl' : ∀ α, map (Equiv.refl α) = @id (f α) := by rfl
  /-- `map` is functorial on equivalences. -/
  map_trans' : ∀ {α β γ} (k : α ≃ β) (h : β ≃ γ), map (k.trans h) = map h ∘ map k := by rfl
#align equiv_functor EquivFunctor

attribute [simp] EquivFunctor.map_refl'

namespace EquivFunctor

section

variable (f : Type u₀ → Type u₁) [EquivFunctor f] {α β : Type u₀} (e : α ≃ β)

/-- An `EquivFunctor` in fact takes every equiv to an equiv. -/
def mapEquiv : f α ≃ f β where
  toFun := EquivFunctor.map e
  invFun := EquivFunctor.map e.symm
  left_inv x := by
    convert (congr_fun (EquivFunctor.map_trans' e e.symm) x).symm
    simp
  right_inv y := by
    convert (congr_fun (EquivFunctor.map_trans' e.symm e) y).symm
    simp
#align equiv_functor.map_equiv EquivFunctor.mapEquiv

@[simp]
theorem mapEquiv_apply (x : f α) : mapEquiv f e x = EquivFunctor.map e x :=
  rfl
#align equiv_functor.map_equiv_apply EquivFunctor.mapEquiv_apply

theorem mapEquiv_symm_apply (y : f β) : (mapEquiv f e).symm y = EquivFunctor.map e.symm y :=
  rfl
#align equiv_functor.map_equiv_symm_apply EquivFunctor.mapEquiv_symm_apply

@[simp]
theorem mapEquiv_refl (α) : mapEquiv f (Equiv.refl α) = Equiv.refl (f α) := by
 simp only [mapEquiv, map_refl', Equiv.refl_symm]; rfl
#align equiv_functor.map_equiv_refl EquivFunctor.mapEquiv_refl

@[simp]
theorem mapEquiv_symm : (mapEquiv f e).symm = mapEquiv f e.symm :=
  Equiv.ext <| mapEquiv_symm_apply f e
#align equiv_functor.map_equiv_symm EquivFunctor.mapEquiv_symm

/-- The composition of `mapEquiv`s is carried over the `EquivFunctor`.
For plain `Functor`s, this lemma is named `map_map` when applied
or `map_comp_map` when not applied.
-/
@[simp]
theorem mapEquiv_trans {γ : Type u₀} (ab : α ≃ β) (bc : β ≃ γ) :
    (mapEquiv f ab).trans (mapEquiv f bc) = mapEquiv f (ab.trans bc) :=
  Equiv.ext fun x => by simp [mapEquiv, map_trans']
#align equiv_functor.map_equiv_trans EquivFunctor.mapEquiv_trans

end

instance (priority := 100) ofLawfulFunctor (f : Type u₀ → Type u₁) [Functor f] [LawfulFunctor f] :
    EquivFunctor f where
  map {α β} e := Functor.map e
  map_refl' α := by
    ext
    apply LawfulFunctor.id_map
  map_trans' {α β γ} k h := by
    ext x
    apply LawfulFunctor.comp_map k h x
#align equiv_functor.of_is_lawful_functor EquivFunctor.ofLawfulFunctor

theorem mapEquiv.injective (f : Type u₀ → Type u₁)
    [Applicative f] [LawfulApplicative f] {α β : Type u₀}
    (h : ∀ γ, Function.Injective (pure : γ → f γ)) :
      Function.Injective (@EquivFunctor.mapEquiv f _ α β) :=
  fun e₁ e₂ H =>
    Equiv.ext fun x => h β (by simpa [EquivFunctor.map] using Equiv.congr_fun H (pure x))
#align equiv_functor.map_equiv.injective EquivFunctor.mapEquiv.injective

end EquivFunctor
