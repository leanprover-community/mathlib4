/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.UnivLE
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Types

/-!
# Universe inequalities and essential surjectivity of `uliftFunctor`.

We show `(∀ α : Type max u v, Small.{v} α) ↔ EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v)`.
-/

set_option autoImplicit true

open CategoryTheory

noncomputable section

theorem Small.ofEssSurj.{u, v} (w : EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v))
    (α : Type max u v) : Small.{v} α := by
  obtain ⟨a', ⟨m⟩⟩ := w.mem_essImage α
  exact ⟨a', ⟨(Iso.toEquiv m).symm.trans Equiv.ulift⟩⟩

instance EssSurj.ofSmall [∀ α : Type max u v, Small.{v} α] :
    EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v) where
  mem_essImage α :=
    ⟨Shrink α, ⟨Equiv.toIso (Equiv.ulift.trans (equivShrink α).symm)⟩⟩

theorem UnivLE_iff_essSurj.{u, v} :
    (∀ α : Type max u v, Small.{v} α) ↔ EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v) :=
  ⟨fun _ => EssSurj.ofSmall, fun w => Small.ofEssSurj w⟩

instance [∀ α : Type max u v, Small.{v} α] : IsEquivalence uliftFunctor.{u, v} :=
  Equivalence.ofFullyFaithfullyEssSurj uliftFunctor

def UnivLE.witness.{u, v} [∀ α : Type max u v, Small.{v} α] : Type u ⥤ Type v :=
  uliftFunctor.{v, u} ⋙ (uliftFunctor.{u, v}).inv

instance [∀ α : Type max u v, Small.{v} α] : Faithful UnivLE.witness.{u, v} :=
  inferInstanceAs <| Faithful (_ ⋙ _)

instance [∀ α : Type max u v, Small.{v} α] : Full UnivLE.witness.{u, v} :=
  inferInstanceAs <| Full (_ ⋙ _)
