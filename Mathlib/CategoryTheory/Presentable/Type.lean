/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Types.Set

/-!
# Presentable objects in Type

In this file, we show that if `κ : Cardinal.{u}` is a regular cardinal,
then `X : Type u` is `κ`-presentable in the category of types iff
`HasCardinalLT X κ` holds, i.e. the cardinal number of `X` is less than `κ`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite ConcreteCategory

namespace HasCardinalLT

variable (X : Type u) (κ : Cardinal.{u})

set_option backward.isDefEq.respectTransparency false in
variable {X κ} in
lemma isCardinalPresentable (hX : HasCardinalLT X κ) [Fact κ.IsRegular] :
    IsCardinalPresentable X κ where
  preservesColimitOfShape J _ _ :=
    ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨by
      have := isFiltered_of_isCardinalFiltered J κ
      refine Types.FilteredColimit.isColimitOf' _ _ (fun f ↦ ?_) (fun j f g h ↦ ?_)
      · dsimp at f
        choose j g hg using fun x ↦ Types.jointly_surjective_of_isColimit hc (f x)
        refine ⟨IsCardinalFiltered.max j hX,
          TypeCat.ofHom ⟨fun x ↦ F.map (IsCardinalFiltered.toMax j hX x) (g x)⟩, ?_⟩
        dsimp
        ext x
        dsimp at j g hg x ⊢
        rw [← hg]
        exact congr_hom (c.w (IsCardinalFiltered.toMax j hX x)).symm (g x)
      · choose k a hk using fun x ↦
          (Types.FilteredColimit.isColimit_eq_iff' hc _ _).1 (congr_hom h x)
        dsimp at f g h k a hk ⊢
        replace hk : ∀ x, F.map (a x) (f x) = F.map (a x) (g x) := by assumption
        obtain ⟨l, b, c, hl⟩ : ∃ (l : J) (c : j ⟶ l) (b : ∀ x, k x ⟶ l),
            ∀ x, a x ≫ b x = c := by
          let φ (x : X) : j ⟶ IsCardinalFiltered.max k hX :=
            a x ≫ IsCardinalFiltered.toMax k hX x
          exact ⟨IsCardinalFiltered.coeq φ hX,
            IsCardinalFiltered.toCoeq φ hX,
            fun x ↦ IsCardinalFiltered.toMax k hX x ≫ IsCardinalFiltered.coeqHom φ hX,
            fun x ↦ by simpa [φ] using IsCardinalFiltered.coeq_condition φ hX x⟩
        refine ⟨l, b, by ext x; simp [← hl x, hk]⟩⟩⟩⟩

/-- Given `X : Type u` and `κ : Cardinal.{u} X`, this is the preordered type
of subsets of `X` of cardinality `< κ`. -/
protected abbrev Set := { A : Set X // HasCardinalLT A κ }

namespace Set

instance [Fact κ.IsRegular] :
    IsCardinalFiltered (HasCardinalLT.Set X κ) κ :=
  isCardinalFiltered_preorder _ _
    (fun ι A hι ↦ ⟨⟨⋃ (i : ι), (A i).val,
      hasCardinalLT_iUnion _
        (by rwa [hasCardinalLT_iff_cardinal_mk_lt]) (fun i ↦ (A i).prop)⟩,
      le_iSup (fun i ↦ (A i).1)⟩)

instance [Fact κ.IsRegular] :
    IsFiltered (HasCardinalLT.Set X κ) :=
  isFiltered_of_isCardinalFiltered _ κ

lemma isFiltered_of_aleph0_le (hκ : Cardinal.aleph0 ≤ κ) :
    IsFiltered (HasCardinalLT.Set X κ) where
  nonempty := ⟨⟨∅, hasCardinalLT_of_finite _ _ hκ⟩⟩
  toIsFilteredOrEmpty := by
    have : IsDirectedOrder (HasCardinalLT.Set X κ) :=
      ⟨fun A B ↦ ⟨⟨A.val ∪ B.val, hasCardinalLT_union hκ A.prop B.prop⟩,
        Set.subset_union_left, Set.subset_union_right⟩⟩
    exact isFilteredOrEmpty_of_directed_le _

/-- The functor `HasCardinalLT.Set X κ ⥤ Type u` which sends a subset of `X`
of cardinality `κ` to the corresponding subtype. -/
@[simps!]
def functor : HasCardinalLT.Set X κ ⥤ Type u :=
  Monotone.functor (f := Subtype.val) (by tauto) ⋙ Set.functorToTypes (X := X)

/-- The cocone for `Set.functor X κ : HasCardinalLT.Set X κ ⥤ Type u` with point `X`. -/
@[simps]
def cocone : Cocone (Set.functor X κ) where
  pt := X
  ι.app _ := TypeCat.ofHom ⟨Subtype.val⟩

/-- Any type `X` is the (filtered) colimit of its subsets of cardinality `< κ`
when `κ` is an infinite cardinal. (This colimit is `κ`-filtered when `κ` is
a regular cardinal.) -/
noncomputable def isColimitCocone
    (hκ : Cardinal.aleph0 ≤ κ) : IsColimit (cocone X κ) := by
  have := isFiltered_of_aleph0_le X κ hκ
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) ?_
  · exact ⟨⟨{x}, hasCardinalLT_of_finite _ _ hκ⟩, ⟨x, by simp⟩, rfl⟩
  · rintro A ⟨x, hx⟩ ⟨y, hy⟩ rfl
    exact ⟨A, 𝟙 _, rfl⟩

end Set

end HasCardinalLT

namespace CategoryTheory

namespace Types

variable {X : Type u}

set_option backward.isDefEq.respectTransparency false in
lemma isCardinalPresentable_iff (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsCardinalPresentable X κ ↔ HasCardinalLT X κ := by
  refine ⟨fun _ ↦ ?_, fun hX ↦ hX.isCardinalPresentable⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ
  obtain ⟨⟨A, hA⟩, f, hf⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (coyoneda.obj (op X))
      (HasCardinalLT.Set.isColimitCocone X κ
        (Cardinal.IsRegular.aleph0_le Fact.out))) (𝟙 X)
  obtain rfl : A = .univ := by
    ext x
    have := congr_hom hf x
    dsimp at this
    rw [← this]
    simp
  exact (hasCardinalLT_iff_of_equiv (Equiv.Set.univ X) _).1 hA

instance (X : Type u) : IsPresentable.{u} X := by
  obtain ⟨κ, hκ, hX⟩ := HasCardinalLT.exists_regular_cardinal.{u} X
  have : Fact κ.IsRegular := ⟨hκ⟩
  have := hX.isCardinalPresentable
  exact isPresentable_of_isCardinalPresentable X κ

end Types

end CategoryTheory
