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

We show `UnivLE.{u, v} ↔ EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v)`.
-/

set_option autoImplicit true

open CategoryTheory

noncomputable section

theorem UnivLE.ofEssSurj.{u, v} (w : EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v)) :
    UnivLE.{u, v} :=
  fun a => by
    obtain ⟨a', ⟨m⟩⟩ := w.mem_essImage a
    exact ⟨a', ⟨(Iso.toEquiv m).symm.trans Equiv.ulift⟩⟩

instance [UnivLE.{u, v}] : EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v) where
  mem_essImage α :=
    ⟨Shrink α, ⟨Equiv.toIso (Equiv.ulift.trans (equivShrink α).symm)⟩⟩

theorem UnivLE_iff_essSurj.{u, v} :
    UnivLE.{u, v} ↔ EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v) :=
  ⟨fun _ => inferInstance, fun w => UnivLE.ofEssSurj w⟩

instance [UnivLE.{u, v}] : IsEquivalence uliftFunctor.{u, v} :=
  Equivalence.ofFullyFaithfullyEssSurj uliftFunctor

def UnivLE.witness.{u, v} [UnivLE.{u, v}] : Type u ⥤ Type v :=
  uliftFunctor.{v, u} ⋙ (uliftFunctor.{u, v}).inv

instance [UnivLE.{u, v}] : Faithful UnivLE.witness.{u, v} :=
  inferInstanceAs <| Faithful (_ ⋙ _)

instance [UnivLE.{u, v}] : Full UnivLE.witness.{u, v} :=
  inferInstanceAs <| Full (_ ⋙ _)
