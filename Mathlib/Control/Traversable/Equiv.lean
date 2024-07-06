/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Traversable.Lemmas
import Mathlib.Logic.Equiv.Defs

#align_import control.traversable.equiv from "leanprover-community/mathlib"@"706d88f2b8fdfeb0b22796433d7a6c1a010af9f2"

/-!
# Transferring `Traversable` instances along isomorphisms

This file allows to transfer `Traversable` instances along isomorphisms.

## Main declarations

* `Equiv.map`: Turns functorially a function `α → β` into a function `t' α → t' β` using the functor
  `t` and the equivalence `Π α, t α ≃ t' α`.
* `Equiv.functor`: `Equiv.map` as a functor.
* `Equiv.traverse`: Turns traversably a function `α → m β` into a function `t' α → m (t' β)` using
  the traversable functor `t` and the equivalence `Π α, t α ≃ t' α`.
* `Equiv.traversable`: `Equiv.traverse` as a traversable functor.
* `Equiv.isLawfulTraversable`: `Equiv.traverse` as a lawful traversable functor.
-/


universe u

namespace Equiv

section Functor

-- Porting note: `parameter` doesn't seem to work yet.
variable {t t' : Type u → Type u} (eqv : ∀ α, t α ≃ t' α)
variable [Functor t]

open Functor

/-- Given a functor `t`, a function `t' : Type u → Type u`, and
equivalences `t α ≃ t' α` for all `α`, then every function `α → β` can
be mapped to a function `t' α → t' β` functorially (see
`Equiv.functor`). -/
protected def map {α β : Type u} (f : α → β) (x : t' α) : t' β :=
  eqv β <| map f ((eqv α).symm x)
#align equiv.map Equiv.map

/-- The function `Equiv.map` transfers the functoriality of `t` to
`t'` using the equivalences `eqv`.  -/
protected def functor : Functor t' where map := Equiv.map eqv
#align equiv.functor Equiv.functor

-- Porting note: `LawfulFunctor` is missing an `#align`.
variable [LawfulFunctor t]

protected theorem id_map {α : Type u} (x : t' α) : Equiv.map eqv id x = x := by
  simp [Equiv.map, id_map]
#align equiv.id_map Equiv.id_map

protected theorem comp_map {α β γ : Type u} (g : α → β) (h : β → γ) (x : t' α) :
    Equiv.map eqv (h ∘ g) x = Equiv.map eqv h (Equiv.map eqv g x) := by
  simpa [Equiv.map] using comp_map ..
#align equiv.comp_map Equiv.comp_map

protected theorem lawfulFunctor : @LawfulFunctor _ (Equiv.functor eqv) :=
  -- Porting note: why is `_inst` required here?
  let _inst := Equiv.functor eqv; {
    map_const := fun {_ _} => rfl
    id_map := Equiv.id_map eqv
    comp_map := Equiv.comp_map eqv }
#align equiv.is_lawful_functor Equiv.lawfulFunctor

protected theorem lawfulFunctor' [F : Functor t']
    (h₀ : ∀ {α β} (f : α → β), Functor.map f = Equiv.map eqv f)
    (h₁ : ∀ {α β} (f : β), Functor.mapConst f = (Equiv.map eqv ∘ Function.const α) f) :
    LawfulFunctor t' := by
  have : F = Equiv.functor eqv := by
    cases F
    dsimp [Equiv.functor]
    congr <;> ext <;> dsimp only <;> [rw [← h₀]; rw [← h₁]] <;> rfl
  subst this
  exact Equiv.lawfulFunctor eqv
#align equiv.is_lawful_functor' Equiv.lawfulFunctor'

end Functor

section Traversable

variable {t t' : Type u → Type u} (eqv : ∀ α, t α ≃ t' α)
variable [Traversable t]
variable {m : Type u → Type u} [Applicative m]
variable {α β : Type u}

/-- Like `Equiv.map`, a function `t' : Type u → Type u` can be given
the structure of a traversable functor using a traversable functor
`t'` and equivalences `t α ≃ t' α` for all α. See `Equiv.traversable`. -/
protected def traverse (f : α → m β) (x : t' α) : m (t' β) :=
  eqv β <$> traverse f ((eqv α).symm x)
#align equiv.traverse Equiv.traverse

theorem traverse_def (f : α → m β) (x : t' α) :
    Equiv.traverse eqv f x = eqv β <$> traverse f ((eqv α).symm x) :=
  rfl

/-- The function `Equiv.traverse` transfers a traversable functor
instance across the equivalences `eqv`. -/
protected def traversable : Traversable t' where
  toFunctor := Equiv.functor eqv
  traverse := Equiv.traverse eqv
#align equiv.traversable Equiv.traversable

end Traversable

section Equiv

variable {t t' : Type u → Type u} (eqv : ∀ α, t α ≃ t' α)

-- Is this to do with the fact it lives in `Type (u+1)` not `Prop`?
variable [Traversable t] [LawfulTraversable t]
variable {F G : Type u → Type u} [Applicative F] [Applicative G]
variable [LawfulApplicative F] [LawfulApplicative G]
variable (η : ApplicativeTransformation F G)
variable {α β γ : Type u}

open LawfulTraversable Functor

-- Porting note: Id.bind_eq is missing an `#align`.

protected theorem id_traverse (x : t' α) : Equiv.traverse eqv (pure : α → Id α) x = x := by
  rw [Equiv.traverse, id_traverse, Id.map_eq, apply_symm_apply]
#align equiv.id_traverse Equiv.id_traverse

protected theorem traverse_eq_map_id (f : α → β) (x : t' α) :
    Equiv.traverse eqv ((pure : β → Id β) ∘ f) x = pure (Equiv.map eqv f x) := by
  simp only [Equiv.traverse, traverse_eq_map_id, Id.map_eq, Id.pure_eq]; rfl
#align equiv.traverse_eq_map_id Equiv.traverse_eq_map_id

protected theorem comp_traverse (f : β → F γ) (g : α → G β) (x : t' α) :
    Equiv.traverse eqv (Comp.mk ∘ Functor.map f ∘ g) x =
      Comp.mk (Equiv.traverse eqv f <$> Equiv.traverse eqv g x) := by
  rw [traverse_def, comp_traverse, Comp.map_mk]
  simp only [map_map, Function.comp_def, traverse_def, symm_apply_apply]
#align equiv.comp_traverse Equiv.comp_traverse

protected theorem naturality (f : α → F β) (x : t' α) :
    η (Equiv.traverse eqv f x) = Equiv.traverse eqv (@η _ ∘ f) x := by
  simp only [Equiv.traverse, functor_norm]
#align equiv.naturality Equiv.naturality

/-- The fact that `t` is a lawful traversable functor carries over the
equivalences to `t'`, with the traversable functor structure given by
`Equiv.traversable`. -/
protected theorem isLawfulTraversable : @LawfulTraversable t' (Equiv.traversable eqv) :=
  -- Porting note: Same `_inst` local variable problem.
  let _inst := Equiv.traversable eqv; {
    toLawfulFunctor := Equiv.lawfulFunctor eqv
    id_traverse := Equiv.id_traverse eqv
    comp_traverse := Equiv.comp_traverse eqv
    traverse_eq_map_id := Equiv.traverse_eq_map_id eqv
    naturality := Equiv.naturality eqv }
#align equiv.is_lawful_traversable Equiv.isLawfulTraversable

/-- If the `Traversable t'` instance has the properties that `map`,
`map_const`, and `traverse` are equal to the ones that come from
carrying the traversable functor structure from `t` over the
equivalences, then the fact that `t` is a lawful traversable functor
carries over as well. -/
protected theorem isLawfulTraversable' [Traversable t']
    (h₀ : ∀ {α β} (f : α → β), map f = Equiv.map eqv f)
    (h₁ : ∀ {α β} (f : β), mapConst f = (Equiv.map eqv ∘ Function.const α) f)
    (h₂ : ∀ {F : Type u → Type u} [Applicative F],
      ∀ [LawfulApplicative F] {α β} (f : α → F β), traverse f = Equiv.traverse eqv f) :
    LawfulTraversable t' where
  -- we can't use the same approach as for `lawful_functor'` because
  -- h₂ needs a `LawfulApplicative` assumption
  toLawfulFunctor := Equiv.lawfulFunctor' eqv @h₀ @h₁
  id_traverse _ := by rw [h₂, Equiv.id_traverse]
  comp_traverse _ _ _ := by rw [h₂, Equiv.comp_traverse, h₂]; congr; rw [h₂]
  traverse_eq_map_id _ _ := by rw [h₂, Equiv.traverse_eq_map_id, h₀]; rfl
  naturality _ _ _ _ _ := by rw [h₂, Equiv.naturality, h₂]
#align equiv.is_lawful_traversable' Equiv.isLawfulTraversable'

end Equiv

end Equiv
