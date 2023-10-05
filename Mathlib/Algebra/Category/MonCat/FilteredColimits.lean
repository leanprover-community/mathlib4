/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.CategoryTheory.Limits.Types

#align_import algebra.category.Mon.filtered_colimits from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The forgetful functor from (commutative) (additive) monoids preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ MonCat`.
We then construct a monoid structure on the colimit of `F ⋙ forget MonCat` (in `Type`), thereby
showing that the forgetful functor `forget MonCat` preserves filtered colimits. Similarly for
`AddMonCat`, `CommMonCat` and `AddCommMonCat`.

-/

set_option linter.uppercaseLean3 false

universe w v u

noncomputable section

open Classical

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

namespace MonCat.FilteredColimits

section

-- Porting note: mathlib 3 used `parameters` here, mainly so we can have the abbreviations `M` and
-- `M.mk` below, without passing around `F` all the time.
variable {J : Type v} [Category.{w} J] [UnivLE.{v, u}] (F : J ⥤ MonCat.{u})

/-- The colimit of `F ⋙ forget MonCat` in the category of types.
In the following, we will construct a monoid structure on `M`.
-/
@[to_additive
      "The colimit of `F ⋙ forget AddMon` in the category of types.
      In the following, we will construct an additive monoid structure on `M`."]
abbrev M : Type u :=
  Shrink (Types.Quot (F ⋙ forget MonCat))
#align Mon.filtered_colimits.M MonCat.FilteredColimits.M
#align AddMon.filtered_colimits.M AddMonCat.FilteredColimits.M

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive "The canonical projection into the colimit, as a quotient type."]
noncomputable abbrev M.mk (x : Σ j, F.obj j) : M F :=
  (equivShrink _) ((Quot.mk (Types.Quot.Rel (F ⋙ forget MonCat))) x)
#align Mon.filtered_colimits.M.mk MonCat.FilteredColimits.M.mk
#align AddMon.filtered_colimits.M.mk AddMonCat.FilteredColimits.M.mk

@[to_additive, simp]
lemma M.equivShrink_symm_mk (x : Σ j, F.obj j) :
    (equivShrink _).symm (M.mk F x) = Quot.mk _ x := by
  apply Equiv.symm_apply_apply

@[to_additive]
lemma M.surjective_mk : Function.Surjective (M.mk F) := by
  intro x
  obtain ⟨x, rfl⟩ := (equivShrink _).surjective x
  obtain ⟨x, rfl⟩ :=  surjective_quot_mk _ x
  exact ⟨x, rfl⟩

@[to_additive]
theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
  M.mk F x = M.mk F y := by
  dsimp [mk]
  congr 1
  exact Quot.EqvGen_sound (Types.FilteredColimit.eqvGen_quot_rel_of_rel (F ⋙ forget MonCat) x y h)
#align Mon.filtered_colimits.M.mk_eq MonCat.FilteredColimits.M.mk_eq
#align AddMon.filtered_colimits.M.mk_eq AddMonCat.FilteredColimits.M.mk_eq

variable [IsFiltered J]

/-- As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to define the
"one" in the colimit as the equivalence class of `⟨j₀, 1 : F.obj j₀⟩`.
-/
@[to_additive
  "As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to
  define the \"zero\" in the colimit as the equivalence class of `⟨j₀, 0 : F.obj j₀⟩`."]
noncomputable instance colimitOne :
  One (M F) where one := M.mk F ⟨IsFiltered.Nonempty.some,1⟩
#align Mon.filtered_colimits.colimit_has_one MonCat.FilteredColimits.colimitOne
#align AddMon.filtered_colimits.colimit_has_zero AddMonCat.FilteredColimits.colimitZero

/-- The definition of the "one" in the colimit is independent of the chosen object of `J`.
In particular, this lemma allows us to "unfold" the definition of `colimit_one` at a custom chosen
object `j`.
-/
@[to_additive
      "The definition of the \"zero\" in the colimit is independent of the chosen object
      of `J`. In particular, this lemma allows us to \"unfold\" the definition of `colimit_zero` at
      a custom chosen object `j`."]
theorem colimit_one_eq (j : J) : (1 : M F) = M.mk F ⟨j, 1⟩ := by
  apply M.mk_eq
  refine' ⟨max' _ j, IsFiltered.leftToMax _ j, IsFiltered.rightToMax _ j, _⟩
  simp
#align Mon.filtered_colimits.colimit_one_eq MonCat.FilteredColimits.colimit_one_eq
#align AddMon.filtered_colimits.colimit_zero_eq AddMonCat.FilteredColimits.colimit_zero_eq

/-- The "unlifted" version of multiplication in the colimit. To multiply two dependent pairs
`⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂` (given by `IsFiltered.max`)
and multiply them there.
-/
@[to_additive
      "The \"unlifted\" version of addition in the colimit. To add two dependent pairs
      `⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂`
      (given by `IsFiltered.max`) and add them there."]
noncomputable def colimitMulAux (x y : Σ j, F.obj j) : M F :=
  M.mk F ⟨IsFiltered.max x.fst y.fst, F.map (IsFiltered.leftToMax x.1 y.1) x.2 *
    F.map (IsFiltered.rightToMax x.1 y.1) y.2⟩
#align Mon.filtered_colimits.colimit_mul_aux MonCat.FilteredColimits.colimitMulAux
#align AddMon.filtered_colimits.colimit_add_aux AddMonCat.FilteredColimits.colimitAddAux

/-- Multiplication in the colimit is well-defined in the left argument. -/
@[to_additive "Addition in the colimit is well-defined in the left argument."]
theorem colimitMulAux_eq_of_rel_left {x x' y : Σ j, F.obj j}
    (hxx' : Types.FilteredColimit.Rel.{v, u} (F ⋙ forget MonCat) x x') :
    colimitMulAux F x y = colimitMulAux F x' y := by
  cases' x with j₁ x; cases' y with j₂ y; cases' x' with j₃ x'
  obtain ⟨l, f, g, hfg⟩ := hxx'
  simp at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.leftToMax j₁ j₂) (IsFiltered.rightToMax j₁ j₂)
      (IsFiltered.rightToMax j₃ j₂) (IsFiltered.leftToMax j₃ j₂) f g
  apply M.mk_eq
  use s, α, γ
  dsimp
  simp_rw [MonoidHom.map_mul]
  -- Porting note : Lean cannot seem to use lemmas from concrete categories directly
  change (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _ =
    (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _
  simp_rw [← F.map_comp, h₁, h₂, h₃, F.map_comp]
  congr 1
  change F.map _ (F.map _ _) = F.map _ (F.map _ _)
  rw [hfg]
#align Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_left MonCat.FilteredColimits.colimitMulAux_eq_of_rel_left
#align AddMon.filtered_colimits.colimit_add_aux_eq_of_rel_left AddMonCat.FilteredColimits.colimitAddAux_eq_of_rel_left

/-- Multiplication in the colimit is well-defined in the right argument. -/
@[to_additive "Addition in the colimit is well-defined in the right argument."]
theorem colimitMulAux_eq_of_rel_right {x y y' : Σ j, F.obj j}
    (hyy' : Types.FilteredColimit.Rel.{v, u} (F ⋙ forget MonCat) y y') :
    colimitMulAux F x y = colimitMulAux F x y' := by
  cases' y with j₁ y; cases' x with j₂ x; cases' y' with j₃ y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  simp at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.rightToMax j₂ j₁) (IsFiltered.leftToMax j₂ j₁)
      (IsFiltered.leftToMax j₂ j₃) (IsFiltered.rightToMax j₂ j₃) f g
  apply M.mk_eq
  use s, α, γ
  dsimp
  simp_rw [MonoidHom.map_mul]
  -- Porting note : Lean cannot seem to use lemmas from concrete categories directly
  change (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _ =
    (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _
  simp_rw [← F.map_comp, h₁, h₂, h₃, F.map_comp]
  congr 1
  change F.map _ (F.map _ _) = F.map _ (F.map _ _)
  rw [hfg]
#align Mon.filtered_colimits.colimit_mul_aux_eq_of_rel_right MonCat.FilteredColimits.colimitMulAux_eq_of_rel_right
#align AddMon.filtered_colimits.colimit_add_aux_eq_of_rel_right AddMonCat.FilteredColimits.colimitAddAux_eq_of_rel_right

/-- Multiplication in the colimit. See also `colimitMulAux`. -/
@[to_additive "Addition in the colimit. See also `colimitAddAux`."]
noncomputable instance colimitMul : Mul (M F) where
  mul x y := by
    refine' Quot.lift₂ (fun a b => colimitMulAux F a b) _ _
      ((equivShrink (Types.Quot (F ⋙ forget MonCat))).symm x)
      ((equivShrink (Types.Quot (F ⋙ forget MonCat))).symm y)
    · intro x y y' h
      apply colimitMulAux_eq_of_rel_right
      apply Types.FilteredColimit.rel_of_quot_rel
      exact h
    · intro x x' y h
      apply colimitMulAux_eq_of_rel_left
      apply Types.FilteredColimit.rel_of_quot_rel
      exact h
#align Mon.filtered_colimits.colimit_has_mul MonCat.FilteredColimits.colimitMul
#align AddMon.filtered_colimits.colimit_has_add AddMonCat.FilteredColimits.colimitAdd

@[to_additive]
noncomputable def colimit_mul_mk_def (x y : Σ j, F.obj j) :
    M.mk F x * M.mk F y =
      M.mk F ⟨IsFiltered.max x.fst y.fst, F.map (IsFiltered.leftToMax x.1 y.1) x.2 *
        F.map (IsFiltered.rightToMax x.1 y.1) y.2⟩ := by
  dsimp [HMul.hMul, Mul.mul]
  simp only [M.equivShrink_symm_mk]
  rfl

/-- Multiplication in the colimit is independent of the chosen "maximum" in the filtered category.
In particular, this lemma allows us to "unfold" the definition of the multiplication of `x` and `y`,
using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`.
-/
@[to_additive
      "Addition in the colimit is independent of the chosen \"maximum\" in the filtered
      category. In particular, this lemma allows us to \"unfold\" the definition of the addition of
      `x` and `y`, using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`."]
theorem colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk F x * M.mk F y = M.mk F ⟨k, F.map f x.2 * F.map g y.2⟩ := by
  cases' x with j₁ x; cases' y with j₂ y
  obtain ⟨s, α, β, h₁, h₂⟩ := IsFiltered.bowtie (IsFiltered.leftToMax j₁ j₂) f
    (IsFiltered.rightToMax j₁ j₂) g
  dsimp [HMul.hMul, Mul.mul]
  simp only [M.equivShrink_symm_mk]
  apply M.mk_eq
  use s, α, β
  dsimp
  erw [MonoidHom.map_mul, MonoidHom.map_mul]
  change (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _ =
    (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _
  simp_rw [← F.map_comp, h₁, h₂]
#align Mon.filtered_colimits.colimit_mul_mk_eq MonCat.FilteredColimits.colimit_mul_mk_eq
#align AddMon.filtered_colimits.colimit_add_mk_eq AddMonCat.FilteredColimits.colimit_add_mk_eq

@[to_additive]
noncomputable instance colimitMulOneClass : MulOneClass (M F) :=
  { colimitOne F,
    colimitMul F with
    one_mul := fun x => by
      obtain ⟨⟨j, x⟩, rfl⟩ := M.surjective_mk _ x
      rw [colimit_one_eq F j, colimit_mul_mk_eq F ⟨j, 1⟩ ⟨j, x⟩ j (𝟙 j) (𝟙 j), MonoidHom.map_one,
        one_mul, F.map_id, id_apply]
    mul_one := fun x => by
      obtain ⟨⟨j, x⟩, rfl⟩ := M.surjective_mk _ x
      rw [colimit_one_eq F j, colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, 1⟩ j (𝟙 j) (𝟙 j), MonoidHom.map_one,
        mul_one, F.map_id, id_apply] }

@[to_additive]
noncomputable instance colimitMonoid : Monoid (M F) :=
  { colimitMulOneClass F with
    mul_assoc := fun x y z => by
      obtain ⟨⟨j₁, x⟩, rfl⟩ := M.surjective_mk _ x
      obtain ⟨⟨j₂, y⟩, rfl⟩ := M.surjective_mk _ y
      obtain ⟨⟨j₃, z⟩, rfl⟩ := M.surjective_mk _ z
      rw [colimit_mul_mk_eq F ⟨j₁, x⟩ ⟨j₂, y⟩ (IsFiltered.max j₁ (IsFiltered.max j₂ j₃))
        (IsFiltered.leftToMax j₁ (IsFiltered.max j₂ j₃))
        (IsFiltered.leftToMax j₂ j₃ ≫ IsFiltered.rightToMax _ _),
        colimit_mul_mk_eq F ⟨(IsFiltered.max j₁ (IsFiltered.max j₂ j₃)), _⟩ ⟨j₃, z⟩
          (IsFiltered.max j₁ (IsFiltered.max j₂ j₃)) (𝟙 _)
          (IsFiltered.rightToMax j₂ j₃ ≫ IsFiltered.rightToMax _ _),
        colimit_mul_mk_def,
        colimit_mul_mk_eq F ⟨j₁, x⟩ ⟨IsFiltered.max j₂ j₃, _⟩ _
          (IsFiltered.leftToMax _ _) (IsFiltered.rightToMax _ _)]
      congr 2
      dsimp only
      rw [F.map_id, show ∀ x, (𝟙 (F.obj (IsFiltered.max j₁ (IsFiltered.max j₂ j₃)))) x = x
        from fun _ => rfl, mul_assoc, MonoidHom.map_mul, F.map_comp, F.map_comp]
      rfl }
#align Mon.filtered_colimits.colimit_monoid MonCat.FilteredColimits.colimitMonoid
#align AddMon.filtered_colimits.colimit_add_monoid AddMonCat.FilteredColimits.colimitAddMonoid

/-- The bundled monoid giving the filtered colimit of a diagram. -/
@[to_additive
  "The bundled additive monoid giving the filtered colimit of a diagram."]
noncomputable def colimit : MonCat.{u} :=
  MonCat.of (M F)
#align Mon.filtered_colimits.colimit MonCat.FilteredColimits.colimit
#align AddMon.filtered_colimits.colimit AddMonCat.FilteredColimits.colimit

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
@[to_additive
      "The additive monoid homomorphism from a given additive monoid in the diagram to the
      colimit additive monoid."]
noncomputable def coconeMorphism (j : J) : F.obj j ⟶ colimit F where
  toFun := (Types.colimitCocone (F ⋙ forget MonCat)).ι.app j
  map_one' := (colimit_one_eq F j).symm
  map_mul' x y := by
    convert (colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 j) (𝟙 j)).symm
    rw [F.map_id]
    rfl
#align Mon.filtered_colimits.cocone_morphism MonCat.FilteredColimits.coconeMorphism
#align AddMon.filtered_colimits.cocone_morphism AddMonCat.FilteredColimits.coconeMorphism

@[to_additive (attr := simp)]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j :=
  MonoidHom.ext fun x => congr_fun ((Types.colimitCocone (F ⋙ forget MonCat)).ι.naturality f) x
#align Mon.filtered_colimits.cocone_naturality MonCat.FilteredColimits.cocone_naturality
#align AddMon.filtered_colimits.cocone_naturality AddMonCat.FilteredColimits.cocone_naturality

/-- The cocone over the proposed colimit monoid. -/
@[to_additive "The cocone over the proposed colimit additive monoid."]
noncomputable def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }
#align Mon.filtered_colimits.colimit_cocone MonCat.FilteredColimits.colimitCocone
#align AddMon.filtered_colimits.colimit_cocone AddMonCat.FilteredColimits.colimitCocone

/-- Given a cocone `t` of `F`, the induced monoid homomorphism from the colimit to the cocone point.
As a function, this is simply given by the induced map of the corresponding cocone in `Type`.
The only thing left to see is that it is a monoid homomorphism.
-/
@[to_additive
      "Given a cocone `t` of `F`, the induced additive monoid homomorphism from the colimit
      to the cocone point. As a function, this is simply given by the induced map of the
      corresponding cocone in `Type`. The only thing left to see is that it is an additive monoid
      homomorphism."]
noncomputable def colimitDesc (t : Cocone F) : colimit F ⟶ t.pt where
  toFun := (Types.colimitCoconeIsColimit (F ⋙ forget MonCat)).desc ((forget MonCat).mapCocone t)
  map_one' := by
    rw [colimit_one_eq F IsFiltered.Nonempty.some, Types.colimitCoconeIsColimit_desc_apply]
    exact MonoidHom.map_one _
  map_mul' x y := by
    obtain ⟨⟨i, x⟩, rfl⟩ := M.surjective_mk _ x
    obtain ⟨⟨j, y⟩, rfl⟩ := M.surjective_mk _ y
    rw [colimit_mul_mk_eq F ⟨i, x⟩ ⟨j, y⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j)]
    simp only [Types.colimitCoconeIsColimit_desc_apply]
    dsimp
    rw [MonoidHom.map_mul]
    congr 1 <;> apply t.w_apply
#align Mon.filtered_colimits.colimit_desc MonCat.FilteredColimits.colimitDesc
#align AddMon.filtered_colimits.colimit_desc AddMonCat.FilteredColimits.colimitDesc

/-- The proposed colimit cocone is a colimit in `MonCat`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddMon`."]
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc := colimitDesc F
  fac t j := MonoidHom.ext fun x => congr_fun ((Types.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget MonCat)).fac ((forget MonCat).mapCocone t) j) x
  uniq t m h := MonoidHom.ext fun y => congr_fun
      ((Types.colimitCoconeIsColimit (F ⋙ forget MonCat)).uniq ((forget MonCat).mapCocone t)
        ((forget MonCat).map m)
        fun j => funext fun x => FunLike.congr_fun (i := MonCat.Hom_FunLike _ _) (h j) x) y
#align Mon.filtered_colimits.colimit_cocone_is_colimit MonCat.FilteredColimits.colimitCoconeIsColimit
#align AddMon.filtered_colimits.colimit_cocone_is_colimit AddMonCat.FilteredColimits.colimitCoconeIsColimit

@[to_additive]
noncomputable instance forgetPreservesFilteredColimits :
    PreservesFilteredColimits (forget MonCat.{u}) :=
  ⟨fun J hJ1 _ => letI hJ1' : Category J := hJ1
    ⟨fun {F} => preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
      (Types.colimitCoconeIsColimit (F ⋙ forget MonCat.{u}))⟩⟩
end

end MonCat.FilteredColimits

namespace CommMonCat.FilteredColimits

open MonCat.FilteredColimits (colimit_mul_mk_eq)

section

-- We use parameters here, mainly so we can have the abbreviation `M` below, without
-- passing around `F` all the time.
variable {J : Type v} [Category.{w} J] [UnivLE.{v, u}] [IsFiltered J] (F : J ⥤ CommMonCat.{u})

/-- The colimit of `F ⋙ forget₂ CommMonCat MonCat` in the category `MonCat`.
In the following, we will show that this has the structure of a _commutative_ monoid.
-/
@[to_additive
      "The colimit of `F ⋙ forget₂ AddCommMonCat AddMonCat` in the category `AddMonCat`. In the
      following, we will show that this has the structure of a _commutative_ additive monoid."]
noncomputable abbrev M : MonCat.{u} :=
  MonCat.FilteredColimits.colimit (F ⋙ forget₂ CommMonCat MonCat.{u})
#align CommMon.filtered_colimits.M CommMonCat.FilteredColimits.M
#align AddCommMon.filtered_colimits.M AddCommMonCat.FilteredColimits.M

@[to_additive]
noncomputable instance colimitCommMonoid : CommMonoid.{u} (M F) :=
  { (M F) with
    mul_comm := fun x y => by
      obtain ⟨x, rfl⟩ := MonCat.FilteredColimits.M.surjective_mk _ x
      obtain ⟨y, rfl⟩ := MonCat.FilteredColimits.M.surjective_mk _ y
      let k := max' x.1 y.1
      let f := IsFiltered.leftToMax x.1 y.1
      let g := IsFiltered.rightToMax x.1 y.1
      rw [colimit_mul_mk_eq (F ⋙ forget₂ CommMonCat MonCat) x y k f g,
        colimit_mul_mk_eq (F ⋙ forget₂ CommMonCat MonCat) y x k g f]
      dsimp
      rw [mul_comm] }
#align CommMon.filtered_colimits.colimit_comm_monoid CommMonCat.FilteredColimits.colimitCommMonoid
#align AddCommMon.filtered_colimits.colimit_add_comm_monoid AddCommMonCat.FilteredColimits.colimitAddCommMonoid

/-- The bundled commutative monoid giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive commutative monoid giving the filtered colimit of a diagram."]
noncomputable def colimit : CommMonCat.{u} :=
  CommMonCat.of (M F)
#align CommMon.filtered_colimits.colimit CommMonCat.FilteredColimits.colimit
#align AddCommMon.filtered_colimits.colimit AddCommMonCat.FilteredColimits.colimit

/-- The cocone over the proposed colimit commutative monoid. -/
@[to_additive "The cocone over the proposed colimit additive commutative monoid."]
noncomputable def colimitCocone : Cocone F where
  pt := colimit F
  ι := { (MonCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommMonCat MonCat)).ι with }
#align CommMon.filtered_colimits.colimit_cocone CommMonCat.FilteredColimits.colimitCocone
#align AddCommMon.filtered_colimits.colimit_cocone AddCommMonCat.FilteredColimits.colimitCocone

/-- The proposed colimit cocone is a colimit in `CommMonCat`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddCommMon`."]
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc t :=
    MonCat.FilteredColimits.colimitDesc (F ⋙ forget₂ CommMonCat MonCat)
      ((forget₂ CommMonCat MonCat).mapCocone t)
  fac t j :=
    FunLike.coe_injective (i := CommMonCat.Hom_FunLike _ _) <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommMonCat)).fac
        ((forget CommMonCat).mapCocone t) j
  uniq t m h :=
    FunLike.coe_injective (i := CommMonCat.Hom_FunLike _ _) <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommMonCat)).uniq
        ((forget CommMonCat).mapCocone t)
        ((forget CommMonCat).map m) fun j => funext fun x =>
          FunLike.congr_fun (i := CommMonCat.Hom_FunLike _ _) (h j) x
#align CommMon.filtered_colimits.colimit_cocone_is_colimit CommMonCat.FilteredColimits.colimitCoconeIsColimit
#align AddCommMon.filtered_colimits.colimit_cocone_is_colimit AddCommMonCat.FilteredColimits.colimitCoconeIsColimit

@[to_additive forget₂AddMonPreservesFilteredColimits]
noncomputable instance forget₂MonPreservesFilteredColimits :
  PreservesFilteredColimits (forget₂ CommMonCat MonCat.{u}) :=
⟨fun J hJ1 _ => letI hJ3 : Category J := hJ1
  ⟨fun {F} => preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
    (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommMonCat MonCat.{u}))⟩⟩
#align CommMon.filtered_colimits.forget₂_Mon_preserves_filtered_colimits CommMonCat.FilteredColimits.forget₂MonPreservesFilteredColimits
#align AddCommMon.filtered_colimits.forget₂_AddMon_preserves_filtered_colimits AddCommMonCat.FilteredColimits.forget₂AddMonPreservesFilteredColimits

@[to_additive]
noncomputable instance forgetPreservesFilteredColimits :
    PreservesFilteredColimits (forget CommMonCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommMonCat MonCat) (forget MonCat)
#align CommMon.filtered_colimits.forget_preserves_filtered_colimits CommMonCat.FilteredColimits.forgetPreservesFilteredColimits
#align AddCommMon.filtered_colimits.forget_preserves_filtered_colimits AddCommMonCat.FilteredColimits.forgetPreservesFilteredColimits

end

end CommMonCat.FilteredColimits
