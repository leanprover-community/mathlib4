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
types (with order embeddings as morphisms), and we show that it is
a `κ`-accessible category.

If `κ ≤ κ'` where `κ'` is also a regular cardinal, we characterize
the `κ'`-presentable objects of `CardinalFilteredPoset κ` as
the objects `J` such that the underlying type `J.obj` has
cardinality `< κ'`.

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
      isCardinalFiltered_iff, Limits.cocone_pt_coe]
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

lemma Hom.injective {J₁ J₂ : CardinalFilteredPoset κ} (f : J₁ ⟶ J₂) :
    Function.Injective f := f.hom.injective

lemma Hom.le_iff_le {J₁ J₂ : CardinalFilteredPoset κ} (f : J₁ ⟶ J₂) (x₁ x₂ : J₁.obj) :
    f x₁ ≤ f x₂ ↔ x₁ ≤ x₂ :=
  f.hom.hom.le_iff_le

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

variable (κ) in
/-- The property of posets in `CardinalFilteredPoset κ` that are
of cardinality `< κ` and have terminal object. -/
def hasCardinalLTWithTerminal : ObjectProperty (CardinalFilteredPoset κ) :=
  fun J ↦ HasCardinalLT J.obj κ ∧ HasTerminal J.obj

instance : ObjectProperty.EssentiallySmall.{u} (hasCardinalLTWithTerminal κ) where
  exists_small_le' := by
    obtain ⟨X, hX⟩ : ∃ (X : Type u), Cardinal.mk X = κ := ⟨κ.ord.ToType, by simp⟩
    let α : Type u := Σ (S : Set X) (_ : PartialOrder S),
      ULift.{u} (PLift (IsCardinalFiltered S κ))
    let (a : α) : PartialOrder a.1 := a.2.1
    let ι (a : α) : CardinalFilteredPoset κ :=
      { obj := .of a.1
        property := a.2.2.down.down }
    refine ⟨.ofObj ι, inferInstance, fun J ⟨hJ, _⟩ ↦ ?_⟩
    obtain ⟨f⟩ : Cardinal.mk J.obj ≤ Cardinal.mk X := by
      simpa [hX] using ((hasCardinalLT_iff_cardinal_mk_lt _ _).1 hJ).le
    let e := Equiv.ofInjective _ f.injective
    letI : PartialOrder (Set.range f) := PartialOrder.lift _ e.symm.injective
    let e' : Set.range f ≃o J.obj := { toEquiv := e.symm, map_rel_iff' := by rfl }
    exact ⟨_, ⟨⟨Set.range f, inferInstance,
      ⟨⟨IsCardinalFiltered.of_equivalence κ e'.symm.equivalence⟩⟩⟩⟩,
        ⟨CardinalFilteredPoset.ι.preimageIso (PartOrdEmb.Iso.mk (by exact e'.symm))⟩⟩

set_option backward.isDefEq.respectTransparency false in
lemma isCardinalPresentable_of_hasCardinalLT_of_le (J : CardinalFilteredPoset κ)
    {κ' : Cardinal.{u}} [Fact κ'.IsRegular] (hJ : HasCardinalLT J.obj κ') (h : κ ≤ κ') :
    IsCardinalPresentable J κ' where
  preservesColimitOfShape A _ _ := ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨by
  · have := isFiltered_of_isCardinalFiltered A κ'
    have := IsCardinalFiltered.of_le A h
    replace hc := isColimitOfPreserves (forget _) hc
    refine Types.FilteredColimit.isColimitOf' _ _ (fun f ↦ ?_) (fun j f g h ↦ ?_)
    · dsimp at f
      choose j g hg using fun (x : J.obj) ↦ Types.jointly_surjective_of_isColimit hc (f x)
      let m := IsCardinalFiltered.max j hJ
      let φ (x : J.obj) : (F.obj m).obj := F.map (IsCardinalFiltered.toMax j hJ x) (g x)
      have hφ (x : J.obj) : f x = c.ι.app _ (φ x) := by
        dsimp [φ]
        rw [← hg, ← ConcreteCategory.comp_apply, c.w]
        rfl
      refine ⟨m,
        ObjectProperty.homMk (PartOrdEmb.ofHom
          { toFun := φ
            inj' x y h := Hom.injective f (by simpa [hφ])
            map_rel_iff' {x y} := ?_ }), ?_⟩
      · simp [← Hom.le_iff_le f, hφ]
      · dsimp
        ext x
        exact (hg x).symm.trans
          (ConcreteCategory.congr_hom (c.w (IsCardinalFiltered.toMax j hJ x)).symm (g x))
    · choose k a hk using fun (x : J.obj) ↦
        (Types.FilteredColimit.isColimit_eq_iff' hc _ _).1 (ConcreteCategory.congr_hom h x)
      dsimp at f g h k a hk ⊢
      obtain ⟨l, b, c, hl⟩ : ∃ (l : A) (c : j ⟶ l) (b : ∀ x, k x ⟶ l),
          ∀ x, a x ≫ b x = c := by
        let φ (x : J.obj) : j ⟶ IsCardinalFiltered.max k hJ :=
          a x ≫ IsCardinalFiltered.toMax k hJ x
        exact ⟨IsCardinalFiltered.coeq φ hJ,
          IsCardinalFiltered.toCoeq φ hJ,
          fun x ↦ IsCardinalFiltered.toMax k hJ x ≫ IsCardinalFiltered.coeqHom φ hJ,
          fun x ↦ by simpa [φ] using IsCardinalFiltered.coeq_condition φ hJ x⟩
      refine ⟨l, b, ?_⟩
      ext x
      simpa only [← hl x, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
        PartOrdEmb.hom_comp, RelEmbedding.coe_trans, Function.comp_apply]
          using congr_arg _ (hk x)⟩⟩⟩

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

variable {κ'} in
protected lemma isCardinalPresentable_iff (h : κ ≤ κ') :
    IsCardinalPresentable J κ' ↔ HasCardinalLT J.obj κ' := by
  refine ⟨fun _ ↦ ?_, fun hJ ↦ isCardinalPresentable_of_hasCardinalLT_of_le _ hJ h⟩
  obtain ⟨X, f, hf⟩ :=
    IsCardinalPresentable.exists_hom_of_isColimit κ' (isColimitCoconeWithTop J κ')
      (ObjectProperty.homMk (PartOrdEmb.ofHom WithTop.coeOrderHom))
  replace hf : OrderEmbedding.subtype X.1 ∘ f = WithTop.coeOrderHom := by
    ext x
    exact ConcreteCategory.congr_hom hf x
  refine X.2.1.of_injective f (Function.Injective.of_comp
    (f := OrderEmbedding.subtype X.1) ?_)
  dsimp at hf ⊢
  rw [hf]
  exact WithTop.coe_injective

end

protected lemma isCardinalPresentable_iff' (J : CardinalFilteredPoset κ) :
    IsCardinalPresentable J κ ↔ HasCardinalLT J.obj κ :=
  CardinalFilteredPoset.isCardinalPresentable_iff _ (le_refl _)

section

variable (J : CardinalFilteredPoset κ)

/-- Given `J : CardinalFilteredPoset κ`, this is the predicate
on `Set J.obj` that is satisfied by subsets that are of
cardinality `< κ` and have a terminal object. -/
def PropSet (S : Set J.obj) : Prop :=
  HasCardinalLT S κ ∧ HasTerminal S

instance (S : Subtype J.PropSet) : HasTerminal S := S.prop.2

instance (S : Subtype J.PropSet) : IsCardinalFiltered S κ :=
  isCardinalFiltered_of_hasTerminal _ _

variable {J} in
lemma propSet_singleton (j : J.obj) : J.PropSet {j} :=
  ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out), by
    let : OrderTop ({j} : Set J.obj) := { top := ⟨j, rfl⟩, le_top := by simp }
    exact isTerminalTop.hasTerminal⟩

instance : IsCardinalFiltered (Subtype J.PropSet) κ :=
  isCardinalFiltered_preorder _ _ (fun K α hK ↦ by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    let t (k : K) : (α k).val := ⊤_ _
    let m := IsCardinalFiltered.max (fun k ↦ (t k).val) hK
    let S : Set J.obj := (⋃ (k : K), α k) ∪ {m}
    let : OrderTop S :=
      { top := ⟨m, by simp [S]⟩
        le_top := by
          rintro ⟨s, hs⟩
          simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_iUnion, S] at hs
          obtain rfl | ⟨k, hs⟩ := hs
          · simp
          · simp only [Subtype.mk_le_mk]
            exact leOfHom ((by exact terminal.from (C := (α k).val) ⟨_, hs⟩) ≫
              IsCardinalFiltered.toMax _ hK k) }
    refine ⟨⟨S, ?_, isTerminalTop.hasTerminal⟩, fun k ↦ ?_⟩
    · have hκ : Cardinal.aleph0 ≤ κ :=  Cardinal.IsRegular.aleph0_le Fact.out
      exact hasCardinalLT_union hκ (hasCardinalLT_iUnion _ hK (fun k ↦ (α k).2.1))
        (hasCardinalLT_of_finite _ _ hκ)
    · simp only [← Subtype.coe_le_coe, Set.le_eq_subset]
      exact subset_trans (Set.subset_iUnion_of_subset k (subset_refl _)) Set.subset_union_left )

instance : IsFiltered (Subtype J.PropSet) := isFiltered_of_isCardinalFiltered _ κ

instance : IsDirectedOrder (Subtype J.PropSet) :=
  IsFiltered.isDirectedOrder _

instance : Nonempty (Subtype J.PropSet) :=
  IsFiltered.nonempty

/-- For any object `J : CardinalFilteredPoset κ`, this is a colimit
cocone exhibiting `J` as the colimit of its subsets
that are of cardinality `< κ` and have a terminal object. -/
abbrev cocone : Cocone (functorOfPredicateSet J.PropSet) :=
  coconeOfPredicateSet J.PropSet

/-- Any object `J : CardinalFilteredPoset κ` is a colimit
of its subsets that are of cardinality `< κ` and have a terminal object. -/
noncomputable def isColimitCocone (J : CardinalFilteredPoset κ) :
    IsColimit (cocone J) :=
  isColimitCoconeOfPredicateSet _ (fun a ↦ ⟨_, propSet_singleton a, by simp⟩)

end

variable (κ) in
lemma isCardinalFilteredGenerator_hasCardinalLTWithTerminal :
    (hasCardinalLTWithTerminal κ).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := by
    rintro J ⟨_, _⟩
    rwa [isCardinalPresentable_iff, J.isCardinalPresentable_iff']
  exists_colimitsOfShape J :=
    ⟨_, inferInstance, inferInstance, ⟨{
      diag := _
      ι := _
      isColimit := isColimitCocone J
      prop_diag_obj j := j.prop }⟩⟩

instance : IsCardinalAccessibleCategory (CardinalFilteredPoset κ) κ where
  exists_generator :=
    ⟨hasCardinalLTWithTerminal κ, inferInstance,
      isCardinalFilteredGenerator_hasCardinalLTWithTerminal κ⟩

end CardinalFilteredPoset

end CategoryTheory
