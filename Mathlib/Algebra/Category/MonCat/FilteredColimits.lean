/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.CategoryTheory.Limits.TypesFiltered

/-!
# The forgetful functor from (commutative) (additive) monoids preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ MonCat`.
We then construct a monoid structure on the colimit of `F ⋙ forget MonCat` (in `Type`), thereby
showing that the forgetful functor `forget MonCat` preserves filtered colimits. Similarly for
`AddMonCat`, `CommMonCat` and `AddCommMonCat`.

-/


universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

namespace MonCat.FilteredColimits

section

-- Porting note: mathlib 3 used `parameters` here, mainly so we can have the abbreviations `M` and
-- `M.mk` below, without passing around `F` all the time.
variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCatMax.{v, u})

/-- The colimit of `F ⋙ forget MonCat` in the category of types.
In the following, we will construct a monoid structure on `M`.
-/
@[to_additive
      "The colimit of `F ⋙ forget AddMon` in the category of types.
      In the following, we will construct an additive monoid structure on `M`."]
abbrev M :=
  Types.Quot (F ⋙ forget MonCat)

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive "The canonical projection into the colimit, as a quotient type."]
noncomputable abbrev M.mk : (Σ j, F.obj j) → M.{v, u} F :=
  Quot.mk _

@[to_additive]
theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
    M.mk.{v, u} F x = M.mk F y :=
  Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_quot_rel_of_rel (F ⋙ forget MonCat) x y h)

variable [IsFiltered J]

/-- As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to define the
"one" in the colimit as the equivalence class of `⟨j₀, 1 : F.obj j₀⟩`.
-/
@[to_additive
  "As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to
  define the \"zero\" in the colimit as the equivalence class of `⟨j₀, 0 : F.obj j₀⟩`."]
noncomputable instance colimitOne :
  One (M.{v, u} F) where one := M.mk F ⟨IsFiltered.nonempty.some,1⟩

/-- The definition of the "one" in the colimit is independent of the chosen object of `J`.
In particular, this lemma allows us to "unfold" the definition of `colimit_one` at a custom chosen
object `j`.
-/
@[to_additive
      "The definition of the \"zero\" in the colimit is independent of the chosen object
      of `J`. In particular, this lemma allows us to \"unfold\" the definition of `colimit_zero` at
      a custom chosen object `j`."]
theorem colimit_one_eq (j : J) : (1 : M.{v, u} F) = M.mk F ⟨j, 1⟩ := by
  apply M.mk_eq
  refine ⟨max' _ j, IsFiltered.leftToMax _ j, IsFiltered.rightToMax _ j, ?_⟩
  simp

/-- The "unlifted" version of multiplication in the colimit. To multiply two dependent pairs
`⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂` (given by `IsFiltered.max`)
and multiply them there.
-/
@[to_additive
      "The \"unlifted\" version of addition in the colimit. To add two dependent pairs
      `⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂`
      (given by `IsFiltered.max`) and add them there."]
noncomputable def colimitMulAux (x y : Σ j, F.obj j) : M.{v, u} F :=
  M.mk F ⟨IsFiltered.max x.fst y.fst, F.map (IsFiltered.leftToMax x.1 y.1) x.2 *
    F.map (IsFiltered.rightToMax x.1 y.1) y.2⟩

/-- Multiplication in the colimit is well-defined in the left argument. -/
@[to_additive "Addition in the colimit is well-defined in the left argument."]
theorem colimitMulAux_eq_of_rel_left {x x' y : Σ j, F.obj j}
    (hxx' : Types.FilteredColimit.Rel (F ⋙ forget MonCat) x x') :
    colimitMulAux.{v, u} F x y = colimitMulAux.{v, u} F x' y := by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, x'⟩ := x'
  obtain ⟨l, f, g, hfg⟩ := hxx'
  simp? at hfg says simp only [Functor.comp_obj, Functor.comp_map, forget_map] at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.leftToMax j₁ j₂) (IsFiltered.rightToMax j₁ j₂)
      (IsFiltered.rightToMax j₃ j₂) (IsFiltered.leftToMax j₃ j₂) f g
  apply M.mk_eq
  use s, α, γ
  dsimp
  simp_rw [MonoidHom.map_mul]
  -- Porting note: Lean cannot seem to use lemmas from concrete categories directly
  change (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _ =
    (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _
  simp_rw [← F.map_comp, h₁, h₂, h₃, F.map_comp]
  congr 1
  change F.map _ (F.map _ _) = F.map _ (F.map _ _)
  rw [hfg]

/-- Multiplication in the colimit is well-defined in the right argument. -/
@[to_additive "Addition in the colimit is well-defined in the right argument."]
theorem colimitMulAux_eq_of_rel_right {x y y' : Σ j, F.obj j}
    (hyy' : Types.FilteredColimit.Rel (F ⋙ forget MonCat) y y') :
    colimitMulAux.{v, u} F x y = colimitMulAux.{v, u} F x y' := by
  obtain ⟨j₁, y⟩ := y; obtain ⟨j₂, x⟩ := x; obtain ⟨j₃, y'⟩ := y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  simp only [Functor.comp_obj, Functor.comp_map, forget_map] at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.rightToMax j₂ j₁) (IsFiltered.leftToMax j₂ j₁)
      (IsFiltered.leftToMax j₂ j₃) (IsFiltered.rightToMax j₂ j₃) f g
  apply M.mk_eq
  use s, α, γ
  dsimp
  simp_rw [MonoidHom.map_mul]
  -- Porting note: Lean cannot seem to use lemmas from concrete categories directly
  change (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _ =
    (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _
  simp_rw [← F.map_comp, h₁, h₂, h₃, F.map_comp]
  congr 1
  change F.map _ (F.map _ _) = F.map _ (F.map _ _)
  rw [hfg]

/-- Multiplication in the colimit. See also `colimitMulAux`. -/
@[to_additive "Addition in the colimit. See also `colimitAddAux`."]
noncomputable instance colimitMul : Mul (M.{v, u} F) :=
{ mul := fun x y => by
    refine Quot.lift₂ (colimitMulAux F) ?_ ?_ x y
    · intro x y y' h
      apply colimitMulAux_eq_of_rel_right
      apply Types.FilteredColimit.rel_of_quot_rel
      exact h
    · intro x x' y h
      apply colimitMulAux_eq_of_rel_left
      apply Types.FilteredColimit.rel_of_quot_rel
      exact h }

/-- Multiplication in the colimit is independent of the chosen "maximum" in the filtered category.
In particular, this lemma allows us to "unfold" the definition of the multiplication of `x` and `y`,
using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`.
-/
@[to_additive
      "Addition in the colimit is independent of the chosen \"maximum\" in the filtered
      category. In particular, this lemma allows us to \"unfold\" the definition of the addition of
      `x` and `y`, using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`."]
theorem colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk.{v, u} F x * M.mk F y = M.mk F ⟨k, F.map f x.2 * F.map g y.2⟩ := by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y
  obtain ⟨s, α, β, h₁, h₂⟩ := IsFiltered.bowtie (IsFiltered.leftToMax j₁ j₂) f
    (IsFiltered.rightToMax j₁ j₂) g
  refine M.mk_eq F _ _ ?_
  use s, α, β
  dsimp
  simp_rw [MonoidHom.map_mul]
  -- Porting note: Lean cannot seem to use lemmas from concrete categories directly
  change (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _ =
    (F.map _ ≫ F.map _) _ * (F.map _ ≫ F.map _) _
  simp_rw [← F.map_comp, h₁, h₂]

@[to_additive]
noncomputable instance colimitMulOneClass : MulOneClass (M.{v, u} F) :=
  { colimitOne F,
    colimitMul F with
    one_mul := fun x => by
      refine Quot.inductionOn x ?_
      intro x
      obtain ⟨j, x⟩ := x
      rw [colimit_one_eq F j, colimit_mul_mk_eq F ⟨j, 1⟩ ⟨j, x⟩ j (𝟙 j) (𝟙 j), MonoidHom.map_one,
        one_mul, F.map_id]
      -- Porting note: `id_apply` does not work here, but the two sides are def-eq
      rfl
    mul_one := fun x => by
      refine Quot.inductionOn x ?_
      intro x
      obtain ⟨j, x⟩ := x
      rw [colimit_one_eq F j, colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, 1⟩ j (𝟙 j) (𝟙 j), MonoidHom.map_one,
        mul_one, F.map_id]
      -- Porting note: `id_apply` does not work here, but the two sides are def-eq
      rfl }

@[to_additive]
noncomputable instance colimitMonoid : Monoid (M.{v, u} F) :=
  { colimitMulOneClass F with
    mul_assoc := fun x y z => by
      refine Quot.induction_on₃ x y z ?_
      clear x y z
      intro x y z
      obtain ⟨j₁, x⟩ := x
      obtain ⟨j₂, y⟩ := y
      obtain ⟨j₃, z⟩ := z
      change M.mk F _ * M.mk F _ * M.mk F _ = M.mk F _ * M.mk F _
      dsimp
      rw [colimit_mul_mk_eq F ⟨j₁, x⟩ ⟨j₂, y⟩ (IsFiltered.max j₁ (IsFiltered.max j₂ j₃))
          (IsFiltered.leftToMax j₁ (IsFiltered.max j₂ j₃))
          (IsFiltered.leftToMax j₂ j₃ ≫ IsFiltered.rightToMax _ _),
        colimit_mul_mk_eq F ⟨(IsFiltered.max j₁ (IsFiltered.max j₂ j₃)), _⟩ ⟨j₃, z⟩
          (IsFiltered.max j₁ (IsFiltered.max j₂ j₃)) (𝟙 _)
          (IsFiltered.rightToMax j₂ j₃ ≫ IsFiltered.rightToMax _ _),
        colimit_mul_mk_eq.{v, u} F ⟨j₁, x⟩ ⟨IsFiltered.max j₂ j₃, _⟩ _
          (IsFiltered.leftToMax _ _) (IsFiltered.rightToMax _ _)]
      congr 2
      dsimp only
      rw [F.map_id, show ∀ x, (𝟙 (F.obj (IsFiltered.max j₁ (IsFiltered.max j₂ j₃)))) x = x
        from fun _ => rfl, mul_assoc, MonoidHom.map_mul, F.map_comp, F.map_comp]
      rfl }

/-- The bundled monoid giving the filtered colimit of a diagram. -/
@[to_additive
  "The bundled additive monoid giving the filtered colimit of a diagram."]
noncomputable def colimit : MonCat.{max v u} :=
  MonCat.of (M.{v, u} F)

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
@[to_additive
      "The additive monoid homomorphism from a given additive monoid in the diagram to the
      colimit additive monoid."]
def coconeMorphism (j : J) : F.obj j ⟶ colimit F where
  toFun := (Types.TypeMax.colimitCocone.{v, max v u, v} (F ⋙ forget MonCat)).ι.app j
  map_one' := (colimit_one_eq F j).symm
  map_mul' x y := by
    convert (colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 j) (𝟙 j)).symm
    rw [F.map_id]
    rfl

@[to_additive (attr := simp)]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism.{v, u} F j' = coconeMorphism F j :=
  MonoidHom.ext fun x =>
    congr_fun ((Types.TypeMax.colimitCocone (F ⋙ forget MonCat)).ι.naturality f) x

/-- The cocone over the proposed colimit monoid. -/
@[to_additive "The cocone over the proposed colimit additive monoid."]
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι := { app := coconeMorphism F }

/-- Given a cocone `t` of `F`, the induced monoid homomorphism from the colimit to the cocone point.
As a function, this is simply given by the induced map of the corresponding cocone in `Type`.
The only thing left to see is that it is a monoid homomorphism.
-/
@[to_additive
      "Given a cocone `t` of `F`, the induced additive monoid homomorphism from the colimit
      to the cocone point. As a function, this is simply given by the induced map of the
      corresponding cocone in `Type`. The only thing left to see is that it is an additive monoid
      homomorphism."]
def colimitDesc (t : Cocone F) : colimit.{v, u} F ⟶ t.pt where
  toFun := (Types.TypeMax.colimitCoconeIsColimit.{v, max v u, v} (F ⋙ forget MonCat)).desc
    ((forget MonCat).mapCocone t)
  map_one' := by
    rw [colimit_one_eq F IsFiltered.nonempty.some]
    exact MonoidHom.map_one _
  map_mul' x y := by
    refine Quot.induction_on₂ x y ?_
    clear x y
    intro x y
    obtain ⟨i, x⟩ := x
    obtain ⟨j, y⟩ := y
    rw [colimit_mul_mk_eq F ⟨i, x⟩ ⟨j, y⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j)]
    dsimp [Types.TypeMax.colimitCoconeIsColimit]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [MonoidHom.map_mul]
    -- Porting note: `rw` can't see through coercion is actually forgetful functor,
    -- so can't rewrite `t.w_apply`
    congr 1 <;>
    exact t.w_apply _ _

/-- The proposed colimit cocone is a colimit in `MonCat`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddMonCat`."]
def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) where
  desc := colimitDesc.{v, u} F
  fac t j := MonoidHom.ext fun x => congr_fun ((Types.TypeMax.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget MonCat)).fac ((forget MonCat).mapCocone t) j) x
  uniq t m h := MonoidHom.ext fun y => congr_fun
      ((Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget MonCat)).uniq ((forget MonCat).mapCocone t)
        ((forget MonCat).map m)
        fun j => funext fun x => DFunLike.congr_fun (i := MonCat.instFunLike _ _) (h j) x) y

@[to_additive]
instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget MonCat.{u}) :=
  ⟨fun J hJ1 _ => letI hJ1' : Category J := hJ1
    ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget MonCat.{u}))⟩⟩
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
      "The colimit of `F ⋙ forget₂ AddCommMonCat AddMonCat` in the category `AddMonCat`. In the
      following, we will show that this has the structure of a _commutative_ additive monoid."]
noncomputable abbrev M : MonCat.{max v u} :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommMonCat MonCat.{max v u})

@[to_additive]
noncomputable instance colimitCommMonoid : CommMonoid.{max v u} (M.{v, u} F) :=
  { (M.{v, u} F) with
    mul_comm := fun x y => by
      refine Quot.induction_on₂ x y ?_
      clear x y
      intro x y
      let k := max' x.1 y.1
      let f := IsFiltered.leftToMax x.1 y.1
      let g := IsFiltered.rightToMax x.1 y.1
      rw [colimit_mul_mk_eq.{v, u} (F ⋙ forget₂ CommMonCat MonCat) x y k f g,
        colimit_mul_mk_eq.{v, u} (F ⋙ forget₂ CommMonCat MonCat) y x k g f]
      dsimp
      rw [mul_comm] }

/-- The bundled commutative monoid giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive commutative monoid giving the filtered colimit of a diagram."]
noncomputable def colimit : CommMonCat.{max v u} :=
  CommMonCat.of (M.{v, u} F)

/-- The cocone over the proposed colimit commutative monoid. -/
@[to_additive "The cocone over the proposed colimit additive commutative monoid."]
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι := { (MonCat.FilteredColimits.colimitCocone.{v, u}
    (F ⋙ forget₂ CommMonCat MonCat.{max v u})).ι with }

/-- The proposed colimit cocone is a colimit in `CommMonCat`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddCommMonCat`."]
def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) where
  desc t :=
    MonCat.FilteredColimits.colimitDesc.{v, u} (F ⋙ forget₂ CommMonCat MonCat.{max v u})
      ((forget₂ CommMonCat MonCat.{max v u}).mapCocone t)
  fac t j :=
    DFunLike.coe_injective (i := CommMonCat.instFunLike _ _) <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget CommMonCat.{max v u})).fac
        ((forget CommMonCat).mapCocone t) j
  uniq t m h :=
    DFunLike.coe_injective (i := CommMonCat.instFunLike _ _) <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget CommMonCat.{max v u})).uniq
        ((forget CommMonCat.{max v u}).mapCocone t)
        ((forget CommMonCat.{max v u}).map m) fun j => funext fun x =>
          DFunLike.congr_fun (i := CommMonCat.instFunLike _ _) (h j) x

@[to_additive forget₂AddMonPreservesFilteredColimits]
noncomputable instance forget₂Mon_preservesFilteredColimits :
  PreservesFilteredColimits (forget₂ CommMonCat MonCat.{u}) :=
⟨fun J hJ1 _ => letI hJ3 : Category J := hJ1
  ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
    (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommMonCat MonCat.{u}))⟩⟩

@[to_additive]
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget CommMonCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommMonCat MonCat) (forget MonCat)

end

end CommMonCat.FilteredColimits
