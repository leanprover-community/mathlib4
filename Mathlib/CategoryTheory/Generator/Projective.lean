/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Enough projectives from a projective separator in a locally small category
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

/-- A projective separator gives enough projectives.  The coproduct is indexed by `Shrink (G ⟶ X)`
so that this applies in locally small categories whose hom types are not themselves small enough for
available coproducts. -/
lemma enoughProjectives_of_projective_separator_shrink {C : Type u} [Category.{v} C]
    [LocallySmall.{w} C] (G : C) [Projective G] (hG : IsSeparator G)
    [∀ X : C, HasCoproduct (fun _ : Shrink (G ⟶ X) => G)] : EnoughProjectives C := by
  refine ⟨fun X => ⟨{
    p := ∐ fun _ : Shrink (G ⟶ X) => G,
    projective := by
      constructor
      intro E Y f e he
      have : Epi e := he
      refine ⟨Sigma.desc fun i : Shrink (G ⟶ X) =>
        Projective.factorThru (Sigma.ι (fun _ : Shrink (G ⟶ X) => G) i ≫ f) e, ?_⟩
      apply colimit.hom_ext
      intro i
      simp
    f := Sigma.desc fun i : Shrink (G ⟶ X) => (equivShrink (G ⟶ X)).symm i,
    epi := by
      constructor
      intro Y u v huv
      refine hG.def u v ?_
      intro h
      have hh := congrArg (fun e => Sigma.ι (fun _ : Shrink (G ⟶ X) => G)
        (equivShrink (G ⟶ X) h) ≫ e) huv
      simpa [Category.assoc] using hh }⟩⟩

end CategoryTheory
