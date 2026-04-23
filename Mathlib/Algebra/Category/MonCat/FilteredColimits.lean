/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Algebra.Category.MonCat.Basic

/-!
# The forgetful functor from (commutative) (additive) monoids preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ MonCat`.
We then construct a monoid structure on the colimit of `F ⋙ forget MonCat` (in `Type`), thereby
showing that the forgetful functor `forget MonCat` preserves filtered colimits. Similarly for
`AddMonCat`, `CommMonCat` and `AddCommMonCat`.

-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

namespace MonCat.FilteredColimits

section

-- Porting note: mathlib 3 used `parameters` here, mainly so we can have the abbreviations `M` and
-- `M.mk` below, without passing around `F` all the time.
variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

/-- The colimit of `F ⋙ forget MonCat` in the category of types.
In the following, we will construct a monoid structure on `M`.
-/
@[to_additive
      /-- The colimit of `F ⋙ forget AddMon` in the category of types.
      In the following, we will construct an additive monoid structure on `M`. -/]
abbrev M := (F ⋙ forget MonCat).ColimitType

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive /-- The canonical projection into the colimit, as a quotient type. -/]
noncomputable abbrev M.mk : (Σ j, F.obj j) → M.{v, u} F :=
  fun x ↦ (F ⋙ forget MonCat).ιColimitType x.1 x.2

@[to_additive]
lemma M.mk_surjective (m : M.{v, u} F) :
    ∃ (j : J) (x : F.obj j), M.mk F ⟨j, x⟩ = m :=
  (F ⋙ forget MonCat).ιColimitType_jointly_surjective m

@[to_additive]
theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
    M.mk.{v, u} F x = M.mk F y :=
  Quot.eqvGen_sound _ _ <|
    Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget MonCat) x y h

@[to_additive]
lemma M.map_mk {j k : J} (f : j ⟶ k) (x : F.obj j) :
    M.mk F ⟨k, F.map f x⟩ = M.mk F ⟨j, x⟩ :=
  M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

variable [IsFiltered J]

/-- As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to define the
"one" in the colimit as the equivalence class of `⟨j₀, 1 : F.obj j₀⟩`.
-/
@[to_additive
  /-- As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to
  define the "zero" in the colimit as the equivalence class of `⟨j₀, 0 : F.obj j₀⟩`. -/]
noncomputable instance colimitOne : One (M.{v, u} F) where
  one := M.mk F ⟨IsFiltered.nonempty.some,1⟩

/-- The definition of the "one" in the colimit is independent of the chosen object of `J`.
In particular, this lemma allows us to "unfold" the definition of `colimit_one` at a custom chosen
object `j`.
-/
@[to_additive
      /-- The definition of the "zero" in the colimit is independent of the chosen object
      of `J`. In particular, this lemma allows us to "unfold" the definition of `colimit_zero` at
      a custom chosen object `j`. -/]
theorem colimit_one_eq (j : J) : (1 : M.{v, u} F) = M.mk F ⟨j, 1⟩ := by
  apply M.mk_eq
  refine ⟨max' _ j, IsFiltered.leftToMax _ j, IsFiltered.rightToMax _ j, ?_⟩
  simp

/-- The "unlifted" version of multiplication in the colimit. To multiply two dependent pairs
`⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂` (given by `IsFiltered.max`)
and multiply them there.
-/
@[to_additive
      /-- The "unlifted" version of addition in the colimit. To add two dependent pairs
      `⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂`
      (given by `IsFiltered.max`) and add them there. -/]
noncomputable def colimitMulAux (x y : Σ j, F.obj j) : M.{v, u} F :=
  M.mk F ⟨IsFiltered.max x.fst y.fst, F.map (IsFiltered.leftToMax x.1 y.1) x.2 *
    F.map (IsFiltered.rightToMax x.1 y.1) y.2⟩

/-- Multiplication in the colimit is well-defined in the left argument. -/
@[to_additive /-- Addition in the colimit is well-defined in the left argument. -/]
theorem colimitMulAux_eq_of_rel_left {x x' y : Σ j, F.obj j}
    (hxx' : Types.FilteredColimit.Rel (F ⋙ forget MonCat) x x') :
    colimitMulAux.{v, u} F x y = colimitMulAux.{v, u} F x' y := by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, x'⟩ := x'
  obtain ⟨l, f, g, hfg⟩ := hxx'
  replace hfg : F.map f x = F.map g x' := by simpa
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.leftToMax j₁ j₂) (IsFiltered.rightToMax j₁ j₂)
      (IsFiltered.rightToMax j₃ j₂) (IsFiltered.leftToMax j₃ j₂) f g
  apply M.mk_eq
  use s, α, γ
  simp_rw [map_mul, ← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp,
    ConcreteCategory.comp_apply, hfg]

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication in the colimit is well-defined in the right argument. -/
@[to_additive /-- Addition in the colimit is well-defined in the right argument. -/]
theorem colimitMulAux_eq_of_rel_right {x y y' : Σ j, F.obj j}
    (hyy' : Types.FilteredColimit.Rel (F ⋙ forget MonCat) y y') :
    colimitMulAux.{v, u} F x y = colimitMulAux.{v, u} F x y' := by
  obtain ⟨j₁, y⟩ := y; obtain ⟨j₂, x⟩ := x; obtain ⟨j₃, y'⟩ := y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk] at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.rightToMax j₂ j₁) (IsFiltered.leftToMax j₂ j₁)
      (IsFiltered.leftToMax j₂ j₃) (IsFiltered.rightToMax j₂ j₃) f g
  apply M.mk_eq
  use s, α, γ
  simp_rw [map_mul, ← comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp,
    comp_apply, hfg]

/-- Multiplication in the colimit. See also `colimitMulAux`. -/
@[to_additive /-- Addition in the colimit. See also `colimitAddAux`. -/]
noncomputable instance colimitMul : Mul (M.{v, u} F) :=
{ mul := fun x y => by
    refine Quot.lift₂ (colimitMulAux F) ?_ ?_ x y
    · intro x y y' h
      apply colimitMulAux_eq_of_rel_right
      apply Types.FilteredColimit.rel_of_colimitTypeRel
      exact h
    · intro x x' y h
      apply colimitMulAux_eq_of_rel_left
      apply Types.FilteredColimit.rel_of_colimitTypeRel
      exact h }

/-- Multiplication in the colimit is independent of the chosen "maximum" in the filtered category.
In particular, this lemma allows us to "unfold" the definition of the multiplication of `x` and `y`,
using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`.
-/
@[to_additive
      /-- Addition in the colimit is independent of the chosen "maximum" in the filtered
      category. In particular, this lemma allows us to "unfold" the definition of the addition of
      `x` and `y`, using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`. -/]
theorem colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk.{v, u} F x * M.mk F y = M.mk F ⟨k, F.map f x.2 * F.map g y.2⟩ := by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y
  obtain ⟨s, α, β, h₁, h₂⟩ := IsFiltered.bowtie (IsFiltered.leftToMax j₁ j₂) f
    (IsFiltered.rightToMax j₁ j₂) g
  refine M.mk_eq F _ _ ?_
  use s, α, β
  dsimp
  simp_rw [map_mul, ← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂]

@[to_additive]
lemma colimit_mul_mk_eq' {j : J} (x y : F.obj j) :
    M.mk.{v, u} F ⟨j, x⟩ * M.mk.{v, u} F ⟨j, y⟩ = M.mk.{v, u} F ⟨j, x * y⟩ := by
  simpa using colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)

@[to_additive]
noncomputable instance colimitMulOneClass : MulOneClass (M.{v, u} F) :=
  { colimitOne F,
    colimitMul F with
    one_mul := fun x => by
      obtain ⟨j, x, rfl⟩ := x.mk_surjective
      rw [colimit_one_eq F j, colimit_mul_mk_eq', one_mul]
    mul_one := fun x => by
      obtain ⟨j, x, rfl⟩ := x.mk_surjective
      rw [colimit_one_eq F j, colimit_mul_mk_eq', mul_one] }

@[to_additive]
noncomputable instance colimitMonoid : Monoid (M.{v, u} F) :=
  { colimitMulOneClass F with
    mul_assoc := fun x y z => by
      obtain ⟨j₁, x₁, rfl⟩ := x.mk_surjective
      obtain ⟨j₂, y₂, rfl⟩ := y.mk_surjective
      obtain ⟨j₃, z₃, rfl⟩ := z.mk_surjective
      obtain ⟨j, f₁, f₂, f₃, x, y, z, h₁, h₂, h₃⟩ :
          ∃ (j : J) (f₁ : j₁ ⟶ j) (f₂ : j₂ ⟶ j) (f₃ : j₃ ⟶ j) (x y z : F.obj j),
          F.map f₁ x₁ = x ∧ F.map f₂ y₂ = y ∧ F.map f₃ z₃ = z :=
        ⟨IsFiltered.max₃ j₁ j₂ j₃, IsFiltered.firstToMax₃ _ _ _,
          IsFiltered.secondToMax₃ _ _ _, IsFiltered.thirdToMax₃ _ _ _,
          _, _, _, rfl, rfl, rfl⟩
      simp only [← M.map_mk F f₁, ← M.map_mk F f₂, ← M.map_mk F f₃, h₁, h₂, h₃,
        colimit_mul_mk_eq', mul_assoc] }

/-- The bundled monoid giving the filtered colimit of a diagram. -/
@[to_additive
  /-- The bundled additive monoid giving the filtered colimit of a diagram. -/]
noncomputable def colimit : MonCat.{max v u} :=
  MonCat.of (M.{v, u} F)

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
@[to_additive
      /-- The additive monoid homomorphism from a given additive monoid in the diagram to the
      colimit additive monoid. -/]
noncomputable def coconeMorphism (j : J) : F.obj j ⟶ colimit F :=
  ofHom
  { toFun := (Types.TypeMax.colimitCocone.{v, max v u, v} (F ⋙ forget MonCat)).ι.app j
    map_one' := (colimit_one_eq F j).symm
    map_mul' x y := by symm; apply colimit_mul_mk_eq' }

@[to_additive (attr := simp)]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism.{v, u} F j' = coconeMorphism F j :=
  MonCat.ext fun x =>
    ConcreteCategory.congr_hom ((Types.TypeMax.colimitCocone (F ⋙ forget MonCat)).ι.naturality f) x

/-- The cocone over the proposed colimit monoid. -/
@[to_additive /-- The cocone over the proposed colimit additive monoid. -/]
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι := { app := coconeMorphism F }

set_option backward.isDefEq.respectTransparency false in
/-- Given a cocone `t` of `F`, the induced monoid homomorphism from the colimit to the cocone point.
As a function, this is simply given by the induced map of the corresponding cocone in `Type`.
The only thing left to see is that it is a monoid homomorphism.
-/
@[to_additive
      /-- Given a cocone `t` of `F`, the induced additive monoid homomorphism from the colimit
      to the cocone point. As a function, this is simply given by the induced map of the
      corresponding cocone in `Type`. The only thing left to see is that it is an additive monoid
      homomorphism. -/]
noncomputable def colimitDesc (t : Cocone F) : colimit.{v, u} F ⟶ t.pt :=
  ofHom
  { toFun := (F ⋙ forget MonCat).descColimitType
        ((F ⋙ forget MonCat).coconeTypesEquiv.symm ((forget MonCat).mapCocone t))
    map_one' := by
      simp [colimit_one_eq F IsFiltered.nonempty.some]
    map_mul' x y := by
      obtain ⟨i, x, rfl⟩ := x.mk_surjective
      obtain ⟨j, y, rfl⟩ := y.mk_surjective
      rw [colimit_mul_mk_eq F ⟨i, x⟩ ⟨j, y⟩ (max' i j) (IsFiltered.leftToMax i j)
        (IsFiltered.rightToMax i j)]
      dsimp
      rw [map_mul, t.w_apply, t.w_apply] }

/-- The proposed colimit cocone is a colimit in `MonCat`. -/
@[to_additive /-- The proposed colimit cocone is a colimit in `AddMonCat`. -/]
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) where
  desc := colimitDesc.{v, u} F
  fac t j := rfl
  uniq t m h := MonCat.ext fun y ↦ by
    obtain ⟨j, y, rfl⟩ := Functor.ιColimitType_jointly_surjective _ y
    exact ConcreteCategory.congr_hom (h j) y

@[to_additive]
instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget MonCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
    ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget MonCat.{u}))⟩
end

end MonCat.FilteredColimits

namespace CommMonCat.FilteredColimits

open MonCat.FilteredColimits (colimit_mul_mk_eq)

section

-- We use parameters here, mainly so we can have the abbreviation `M` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommMonCat.{max v u})

/-- The colimit of `F ⋙ forget₂ CommMonCat MonCat` in the category `MonCat`.
In the following, we will show that this has the structure of a _commutative_ monoid.
-/
@[to_additive
      /-- The colimit of `F ⋙ forget₂ AddCommMonCat AddMonCat` in the category `AddMonCat`. In the
      following, we will show that this has the structure of a _commutative_ additive monoid. -/]
noncomputable abbrev M : MonCat.{max v u} :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommMonCat MonCat.{max v u})

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
noncomputable instance colimitCommMonoid : CommMonoid.{max v u} (M.{v, u} F) :=
  { (M.{v, u} F) with
    mul_comm := fun x y => by
      obtain ⟨i, x, rfl⟩ := x.mk_surjective
      obtain ⟨j, y, rfl⟩ := y.mk_surjective
      let k := max' i j
      let f := IsFiltered.leftToMax i j
      let g := IsFiltered.rightToMax i j
      rw [colimit_mul_mk_eq.{v, u} (F ⋙ forget₂ CommMonCat MonCat) ⟨i, x⟩ ⟨j, y⟩ k f g,
        colimit_mul_mk_eq.{v, u} (F ⋙ forget₂ CommMonCat MonCat) ⟨j, y⟩ ⟨i, x⟩ k g f]
      dsimp
      rw [mul_comm] }

/-- The bundled commutative monoid giving the filtered colimit of a diagram. -/
@[to_additive
/-- The bundled additive commutative monoid giving the filtered colimit of a diagram. -/]
noncomputable def colimit : CommMonCat.{max v u} :=
  CommMonCat.of (M.{v, u} F)

/-- The cocone over the proposed colimit commutative monoid. -/
@[to_additive /-- The cocone over the proposed colimit additive commutative monoid. -/]
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι.app j := ofHom ((MonCat.FilteredColimits.colimitCocone.{v, u}
    (F ⋙ forget₂ CommMonCat MonCat.{max v u})).ι.app j).hom
  ι.naturality _ _ f := hom_ext <| congr_arg (MonCat.Hom.hom)
    ((MonCat.FilteredColimits.colimitCocone.{v, u}
      (F ⋙ forget₂ CommMonCat MonCat.{max v u})).ι.naturality f)

/-- The proposed colimit cocone is a colimit in `CommMonCat`. -/
@[to_additive /-- The proposed colimit cocone is a colimit in `AddCommMonCat`. -/]
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) :=
  isColimitOfReflects (forget₂ CommMonCat MonCat)
    (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _))

@[to_additive forget₂AddMonPreservesFilteredColimits]
noncomputable instance forget₂Mon_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommMonCat MonCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
    ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
      (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommMonCat MonCat.{u}))⟩

@[to_additive]
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget CommMonCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommMonCat MonCat) (forget MonCat)

end

end CommMonCat.FilteredColimits
