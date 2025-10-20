/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Types.Set

/-!
# Presentable objects in Type

In this file, we show that if `κ : Cardinal.{u}` is a regular cardinal,
then `X : Type u` is `κ`-presentable in the category of types iff
`HasCardinalLT X κ` holds.

-/

universe u

open CategoryTheory Limits Opposite

namespace HasCardinalLT

variable {X : Type u} (κ : Cardinal.{u}) [Fact κ.IsRegular]

lemma isCardinalPresentable (hX : HasCardinalLT X κ) :
    IsCardinalPresentable X κ where
  preservesColimitOfShape J _ _ :=
    ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨by
      have := isFiltered_of_isCardinalFiltered J κ
      refine Types.FilteredColimit.isColimitOf' _ _ (fun f ↦ ?_) (fun j f g h ↦ ?_)
      · choose j g hg using fun x ↦ Types.jointly_surjective_of_isColimit hc (f x)
        refine ⟨IsCardinalFiltered.max j hX,
          fun x ↦ F.map (IsCardinalFiltered.toMax j hX x) (g x), ?_⟩
        dsimp
        ext x
        dsimp at j g hg x ⊢
        rw [← hg]
        exact congr_fun (c.w (IsCardinalFiltered.toMax j hX x)).symm (g x)
      · choose k a hk using fun x ↦
          (Types.FilteredColimit.isColimit_eq_iff' hc _ _).1 (congr_fun h x)
        dsimp at f g h k a hk ⊢
        obtain ⟨l, b, c, hl⟩ : ∃ (l : J) (c : j ⟶ l) (b : ∀ x, k x ⟶ l),
            ∀ x, a x ≫ b x = c := by
          let φ (x : X) : j ⟶ IsCardinalFiltered.max k hX :=
            a x ≫ IsCardinalFiltered.toMax k hX x
          exact ⟨IsCardinalFiltered.coeq φ hX,
            IsCardinalFiltered.toCoeq φ hX,
            fun x ↦ IsCardinalFiltered.toMax k hX x ≫ IsCardinalFiltered.coeqHom φ hX,
            fun x ↦ by simpa [φ] using IsCardinalFiltered.coeq_condition φ hX x⟩
        exact ⟨l, b, by ext x; simp [← hl x, hk]⟩⟩⟩⟩

variable (X)

protected abbrev Set := { A : Set X // HasCardinalLT A κ }

instance : IsCardinalFiltered (HasCardinalLT.Set X κ) κ :=
  isCardinalFiltered_preorder _ _ (by
    sorry)

@[simps!]
def Set.functor : HasCardinalLT.Set X κ ⥤ Type u :=
  Monotone.functor (f := Subtype.val) (by tauto) ⋙ Set.functorToTypes (X := X)

@[simps]
def Set.cocone : Cocone (Set.functor X κ) where
  pt := X
  ι.app _ := Subtype.val

def Set.isColimitCocone : IsColimit (cocone X κ) := sorry

end HasCardinalLT

namespace CategoryTheory

namespace Types

variable {X : Type u} (κ : Cardinal.{u}) [Fact κ.IsRegular]


lemma isCardinalPresentable_iff :
    IsCardinalPresentable X κ ↔ HasCardinalLT X κ := by
  refine ⟨fun _ ↦ ?_, fun hX ↦ hX.isCardinalPresentable⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ
  obtain ⟨⟨A, hA⟩, f, hf⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (coyoneda.obj (op X))
      (HasCardinalLT.Set.isColimitCocone X κ)) (𝟙 X)
  obtain rfl : A = .univ := by
    ext x
    have := congr_fun hf x
    dsimp at f hf this
    simp only [Set.mem_univ, iff_true]
    rw [← this]
    exact (f x).2
  exact (hasCardinalLT_iff_of_equiv (Equiv.Set.univ X) _).1 hA

instance (X : Type u) : IsPresentable.{u} X := by
  obtain ⟨κ, hκ, hX⟩ := HasCardinalLT.exists_regular_cardinal.{u} X
  have : Fact κ.IsRegular := ⟨hκ⟩
  have := hX.isCardinalPresentable
  exact isPresentable_of_isCardinalPresentable X κ

end Types

end CategoryTheory
