import Mathlib.CategoryTheory.Localization.Monoidal
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

open CategoryTheory Localization MonoidalCategory

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

variable {C : Type*} [Category C] (J : GrothendieckTopology C) (A : Type*) [Category A]
  [MonoidalCategory A] [ConcreteCategory A]
  [HasWeakSheafify J A] [J.WEqualsLocallyBijective A]

instance : (J.W (A := A)).Monoidal where
  whiskerLeft F G₁ G₂ g h := by
    simp only [GrothendieckTopology.W, LeftBousfield.W] at h ⊢
    intro Z hZ
    constructor
    · intro a b hh
      simp at hh
      ext W w
      have hhh := congrFun ((forget A).congr_map (NatTrans.congr_app hh W))
      simp at hhh
      sorry
    · sorry
    -- rw [J.W_iff_isLocallyBijective] at *
    -- constructor
    -- · constructor
    --   intro X x y hh
    --   simp only [Monoidal.tensorObj_obj] at x y
    --   have := h.1
    --   have : ∀ (x y : G₁.obj X) (_ : g.app X x = g.app X y),
    --     Presheaf.equalizerSieve x y ∈ J.sieves X.unop := fun x y h ↦ this.1 x y h

    --   simp? [Presheaf.equalizerSieve]
    -- · sorry
  whiskerRight := sorry

noncomputable instance : MonoidalCategory (Sheaf J A) :=
    inferInstanceAs (MonoidalCategory ((LocalizedMonoidal (presheafToSheaf J A) J.W (Iso.refl _))))
