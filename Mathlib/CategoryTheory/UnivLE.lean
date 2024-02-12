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

We show `UnivLE.{max u v, v} ↔ EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v)`.
-/

set_option autoImplicit true

open CategoryTheory

noncomputable section

theorem UnivLE.ofEssSurj.{u, v} (w : EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v)) :
    UnivLE.{max u v, v} :=
  fun α ↦ by
    obtain ⟨a', ⟨m⟩⟩ := w.mem_essImage α
    exact ⟨a', ⟨(Iso.toEquiv m).symm.trans Equiv.ulift⟩⟩

instance EssSurj.ofUnivLE [UnivLE.{max u v, v}] :
    EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v) where
  mem_essImage α :=
    ⟨Shrink α, ⟨Equiv.toIso (Equiv.ulift.trans (equivShrink α).symm)⟩⟩

theorem UnivLE_iff_essSurj.{u, v} :
    UnivLE.{max u v, v} ↔ EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v) :=
  ⟨fun _ => inferInstance, fun w => UnivLE.ofEssSurj w⟩

instance [UnivLE.{max u v, v}] : IsEquivalence uliftFunctor.{u, v} :=
  Equivalence.ofFullyFaithfullyEssSurj uliftFunctor

def UnivLE.witness.{u, v} [UnivLE.{max u v, v}] : Type u ⥤ Type v :=
  uliftFunctor.{v, u} ⋙ (uliftFunctor.{u, v}).inv

instance [UnivLE.{max u v, v}] : Faithful UnivLE.witness.{u, v} :=
  inferInstanceAs <| Faithful (_ ⋙ _)

instance [UnivLE.{max u v, v}] : Full UnivLE.witness.{u, v} :=
  inferInstanceAs <| Full (_ ⋙ _)
