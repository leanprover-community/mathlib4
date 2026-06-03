/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.Order.Category.PartOrdEmb

/-!
# The κ-accessible category of κ-directed posets

Given a regular cardinal `κ : Cardinal.{u}`, we define the
category `CardinalFilteredPoset κ` of `κ`-directed partially ordered
types (with order embeddings as morphisms). We shall show that it is
a `κ`-accessible category (TODO @joelriou).

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace PartOrdEmb

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- The property of objects in `PartOrdEmb` that are
satisfied by partially ordered types of cardinality `< κ`. -/
abbrev isCardinalFiltered : ObjectProperty PartOrdEmb.{u} :=
  fun X ↦ IsCardinalFiltered X κ

@[simp]
lemma isCardinalFiltered_iff (X : PartOrdEmb.{u}) :
    isCardinalFiltered κ X ↔ IsCardinalFiltered X κ := Iff.rfl

instance : (isCardinalFiltered κ).IsClosedUnderIsomorphisms where
  of_iso e _ := .of_equivalence κ (orderIsoOfIso e).equivalence

namespace Limits.CoconePt

variable {κ} {J : Type u} [SmallCategory J] [IsCardinalFiltered J κ]
  {F : J ⥤ PartOrdEmb.{u}} {c : Cocone (F ⋙ forget _)} (hc : IsColimit c)

lemma isCardinalFiltered_pt (hF : ∀ j, IsCardinalFiltered (F.obj j) κ) :
    haveI := isFiltered_of_isCardinalFiltered J κ
    IsCardinalFiltered (CoconePt hc) κ := by
  haveI := isFiltered_of_isCardinalFiltered J κ
  refine isCardinalFiltered_preorder _ _ (fun K f hK ↦ ?_)
  rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
  choose j₀ x₀ hx₀ using fun k ↦ Types.jointly_surjective_of_isColimit hc (f k)
  let j := IsCardinalFiltered.max j₀ hK
  let x₁ (k : K) : F.obj j := F.map (IsCardinalFiltered.toMax j₀ hK k) (x₀ k)
  have hx₁ (k : K) : c.ι.app j (x₁ k) = c.ι.app (j₀ k) (x₀ k) :=
    ConcreteCategory.congr_hom (c.w (IsCardinalFiltered.toMax j₀ hK k)) _
  refine ⟨(cocone hc).ι.app j (IsCardinalFiltered.max x₁ hK),
    fun k ↦ ?_⟩
  rw [← hx₀, ← hx₁]
  exact ((cocone hc).ι.app j).hom.monotone
    (leOfHom (IsCardinalFiltered.toMax x₁ hK k))

end Limits.CoconePt

instance (J : Type u) [SmallCategory J] [IsCardinalFiltered J κ] :
    (isCardinalFiltered κ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    have := isFiltered_of_isCardinalFiltered J κ
    rintro X ⟨p⟩
    simp only [(isCardinalFiltered κ).prop_iff_of_iso
      (p.isColimit.coconePointUniqueUpToIso
        (Limits.isColimitCocone (colimit.isColimit (p.diag ⋙ forget PartOrdEmb)))),
      isCardinalFiltered_iff]
    exact Limits.CoconePt.isCardinalFiltered_pt _ p.prop_diag_obj

end PartOrdEmb

namespace CategoryTheory

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- The category of `κ`-filtered partially ordered types,
with morphisms given by order embeddings. -/
abbrev CardinalFilteredPoset :=
  (PartOrdEmb.isCardinalFiltered κ).FullSubcategory

variable {κ}

/-- The embedding of the category of `κ`-filtered
partially ordered types in the category of partially
ordered types. -/
abbrev CardinalFilteredPoset.ι : CardinalFilteredPoset κ ⥤ PartOrdEmb :=
  ObjectProperty.ι _

namespace CardinalFilteredPoset

/-- Constructor for objects in `CardinalFilteredPoset κ`. -/
abbrev of (J : PartOrdEmb.{u}) [IsCardinalFiltered J κ] : CardinalFilteredPoset κ where
  obj := J
  property := inferInstance

instance (J : CardinalFilteredPoset κ) : IsCardinalFiltered J.obj κ := J.property

instance (J : CardinalFilteredPoset κ) : IsFiltered J.obj :=
  isFiltered_of_isCardinalFiltered _ κ

instance (J : CardinalFilteredPoset κ) : Nonempty J.obj := IsFiltered.nonempty

instance : HasCardinalFilteredColimits (CardinalFilteredPoset κ) κ where
  hasColimitsOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J κ
    infer_instance

instance (A : Type u) [SmallCategory A] [IsCardinalFiltered A κ] :
    PreservesColimitsOfShape A (forget (CardinalFilteredPoset κ)) := by
  have := isFiltered_of_isCardinalFiltered A κ
  change PreservesColimitsOfShape A (CardinalFilteredPoset.ι ⋙ forget _)
  infer_instance

instance (J : CardinalFilteredPoset κ) (κ' : Cardinal.{u}) [Fact κ'.IsRegular] :
    IsCardinalFiltered (WithTop (J.obj)) κ' :=
  isCardinalFiltered_of_hasTerminal _ _

/-- The map `CardinalFilteredPoset κ → CardinalFilteredPoset κ` which sends
a partially ordered `κ`-filtered type `J` to `WithTop J`. -/
abbrev withTop (J : CardinalFilteredPoset κ) : CardinalFilteredPoset κ :=
  .of (.of (WithTop J.obj))

section

variable {J : CardinalFilteredPoset κ} (P : Set J.obj → Prop)
  [IsDirectedOrder (Subtype P)] [Nonempty (Subtype P)]
  [∀ (S : Subtype P), IsCardinalFiltered S.val κ]

set_option backward.defeqAttrib.useBackward true in
/-- Given a predicate `P : Set J.obj → Prop` on the underlying type
of `J : CardinalFilteredPoset κ` such that all the subsets satisfying `P`
are `κ`-filtered, this is the functor `Subtype P ⥤ CardinalFilteredPoset κ`
which sends a subset `S` of `J` satisfying `P` to the induced
partially ordered type `J`, as an object in `CardinalFilteredPoset κ`. -/
@[simps!]
def functorOfPredicateSet : Subtype P ⥤ CardinalFilteredPoset κ :=
  ObjectProperty.lift _ (PartOrdEmb.functorOfPredicateSet P)
    (fun S ↦ by dsimp; infer_instance)

/-- Given a predicate `P : Set J.obj → Prop` on the underlying type
of `J : CardinalFilteredPoset κ` such that all the subsets satisfying `P`
are `κ`-filtered, this is the cocone with point `J` given
by all the inclusions of the subsets satisfying `P`. -/
@[simps]
def coconeOfPredicateSet : Cocone (functorOfPredicateSet P) where
  pt := J
  ι.app j := ObjectProperty.homMk ((PartOrdEmb.coconeOfPredicateSet P).ι.app j)

/-- Let `P` be a predicate on `Set J.obj` where `J : CardinalFilteredPoset κ`.
We assume that `Subtype P` is directed and nonempty, and that any `a : J.obj`
belongs to some `S : Set J.obj` satisfying `P`. Then, `J` is the colimit in the
category `CardinalFilteredPoset κ` of these subsets. -/
noncomputable def isColimitCoconeOfPredicateSet
    (hP : ∀ (a : J.obj), ∃ (S : Set J.obj), P S ∧ a ∈ S) :
    IsColimit (coconeOfPredicateSet P) :=
  isColimitOfReflects CardinalFilteredPoset.ι
    (PartOrdEmb.isColimitOfPredicateSet P hP)

end

section

variable (J : CardinalFilteredPoset κ)

-- `@[nolint unusedArguments]` allows to setup some instances which uses
-- the fact that `κ'` is regular.
/-- Given `J : CardinalFilteredPoset κ` and a regular cardinal `κ'`,
this is the predicate on `Set J.withTop.obj` that is satisfied by
subsets that are of cardinality `< κ'` and contain `⊤`. -/
@[nolint unusedArguments]
def PropSetWithTop (κ' : Cardinal.{u}) [Fact κ'.IsRegular]
    (S : Set J.withTop.obj) : Prop :=
  HasCardinalLT S κ' ∧ ⊤ ∈ S

variable (κ' : Cardinal.{u}) [Fact κ'.IsRegular]

instance (S : Subtype (J.PropSetWithTop κ')) : HasTerminal S :=
  IsTerminal.hasTerminal (X := ⟨⊤, S.2.2⟩)
    (IsTerminal.ofUniqueHom (fun _ ↦ homOfLE (by rw [Subtype.mk_le_mk]; exact le_top))
      (fun _ _ ↦ rfl))

instance (S : Subtype (J.PropSetWithTop κ')) : IsCardinalFiltered S κ :=
  isCardinalFiltered_of_hasTerminal _ _

instance : IsCardinalFiltered (Subtype (J.PropSetWithTop κ')) κ' :=
  isCardinalFiltered_preorder _ _ (fun K α hK ↦ by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    have hκ' : Cardinal.aleph0 ≤ κ' := Cardinal.IsRegular.aleph0_le Fact.out
    refine ⟨⟨(⋃ (k : K), α k) ∪ {⊤},
      hasCardinalLT_union hκ' (hasCardinalLT_iUnion _ hK (fun k ↦ (α k).property.left))
        (hasCardinalLT_of_finite _ _ hκ'), by simp⟩, fun k ↦ ?_⟩
    rw [Subtype.mk_le_mk]
    simp only [Set.le_eq_subset]
    exact subset_trans (Set.subset_iUnion (fun i ↦ (α i).1) k) Set.subset_union_left)

instance : IsFiltered (Subtype (J.PropSetWithTop κ')) :=
  isFiltered_of_isCardinalFiltered _ κ'

instance : IsDirectedOrder (Subtype (J.PropSetWithTop κ')) :=
  IsFiltered.isDirectedOrder _

instance : Nonempty (Subtype (J.PropSetWithTop κ')) :=
  IsFiltered.nonempty

variable {J} in
lemma propSetWithTop_pair (j : J.obj) : J.PropSetWithTop κ' {WithTop.some j, ⊤} :=
  ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out),
    Set.mem_insert_of_mem _ (by simp)⟩

lemma exists_mem_propSetWithTop (a : J.withTop.obj) :
    ∃ S, J.PropSetWithTop κ' S ∧ a ∈ S := by
  induction a with
  | some a => exact ⟨_, propSetWithTop_pair _ a, by aesop⟩
  | none => exact ⟨_, propSetWithTop_pair _ (Classical.arbitrary _), by aesop⟩

/-- If `J : CardinalFilteredPoset κ` and `κ'` is any regular cardinal,
this is a colimit cocone which exhibits `J.withTop` as the `κ'`-filtered
colimit of its subsets that are of cardinality `< κ'` and contain `⊤`. -/
abbrev coconeWithTop : Cocone (functorOfPredicateSet (J.PropSetWithTop κ')) :=
  coconeOfPredicateSet (PropSetWithTop J κ')

/-- If `J : CardinalFilteredPoset κ` and `κ'` is any regular cardinal,
then `J.withTop` is the `κ'`-filtered colimit of its subsets that are of
cardinality `< κ'` and contain `⊤`. -/
noncomputable def isColimitCoconeWithTop : IsColimit (coconeWithTop J κ') :=
  isColimitCoconeOfPredicateSet _ (fun a ↦ by
    induction a with
    | some a => exact ⟨_, propSetWithTop_pair _ a, by aesop⟩
    | none => exact ⟨_, propSetWithTop_pair _ (Classical.arbitrary _), by aesop⟩)

end

end CardinalFilteredPoset

end CategoryTheory
