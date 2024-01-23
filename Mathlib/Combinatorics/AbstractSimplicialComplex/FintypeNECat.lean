import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Order.Category.NonemptyFinLinOrd
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Topology.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Instances.NNReal


universe u v

/- The category of nonempty fintypes.-/
/- This is basically a copy-paste of Adam Topaz's FintypeCat file, adapted to nonempty finite types.-/

/-!
# The category of nonempmty finite types.

We define the category of nonempty finite types, denoted `FintypeNECat` as
(bundled) types with `Nonempty` and `Fintype` instances.

We also define `FintypeNECat.Skeleton`, the standard skeleton of `FintypeNECat` whose objects
are `Fin (n + 1)` for `n : ℕ`. We prove that the obvious inclusion functor
`FintypeNECat.Skeleton ⥤ FintypeNECat` is an equivalence of categories in
`FintypeNECat.Skeleton.equivalence`.
We prove that `FintypeNECat.Skeleton` is a skeleton of `FintypeNECat` in `FintypeNECat.isSkeleton`.
-/


open Classical

/-- A typeclass for nonempty fintypes. -/
class FintypeNE (α : Type _) extends Fintype α where
  Nonempty : Nonempty α := by infer_instance

attribute [instance] FintypeNE.Nonempty


def FintypeNE.toType (α : Type _) [FintypeNE α] : Type _ := α


instance PUnit.fintypeNE : FintypeNE PUnit where

instance Unit.fintypeNE : FintypeNE Unit where


instance Fin.fintypeNE (n : ℕ) : FintypeNE (Fin (n + 1)) where

instance ULift.fintypeNE (α : Type u) [FintypeNE α] :
    FintypeNE (ULift.{v} α) :=
  { ULift.fintype _ with }


noncomputable def FintypeNE.equivFin (α) [FintypeNE α] : α ≃ Fin ((Fintype.card α).pred + 1) := by
  rw [←Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos]
  . exact Fintype.equivFin α
  . exact Fintype.card_pos

open CategoryTheory

/-- The category of nonempty finite types. -/
def FintypeNECat :=
  Bundled FintypeNE


namespace FintypeNECat

instance : CoeSort FintypeNECat (Type _) :=
  Bundled.coeSort

/-- Construct a bundled `FintypeNECat` from the underlying type and typeclass. -/
def of (X : Type _) [FintypeNE X] : FintypeNECat :=
  Bundled.of X


instance : Inhabited FintypeNECat :=
  ⟨of PUnit⟩

instance {X : FintypeNECat} : Fintype X.1 :=
  X.2.toFintype

instance : Category FintypeNECat :=
  InducedCategory.category Bundled.α


/-- The fully faithful embedding of `FintypeNECat` into the category of types. -/
@[simps!]
def incl : FintypeNECat ⥤ Type _ :=
  inducedFunctor _

instance : Full incl := InducedCategory.full _
instance : Faithful incl := InducedCategory.faithful _

instance concreteCategoryFintypeNE : ConcreteCategory FintypeNECat :=
  ⟨incl⟩


@[simp]
theorem id_apply (X : FintypeNECat) (x : X) : (𝟙 X : X → X) x = x :=
  rfl

@[simp]
theorem comp_apply {X Y Z : FintypeNECat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl

-- porting note: added to ease automation --SMorel's note: I have no idea what this means.
@[ext]
lemma hom_ext {X Y : FintypeNECat} (f g : X ⟶ Y) (h : ∀ x, f x = g x): f = g := by
  funext
  apply h

-- See `equivEquivIso` in the root namespace for the analogue in `Type`.
/-- Equivalences between nonempty finite types are the same as isomorphisms in `FintypeNECat`. -/
@[simps]
def equivEquivIso {A B : FintypeNECat} : A.1 ≃ B.1 ≃ (A ≅ B) where
  toFun e :=
    { hom := e
      inv := e.symm }
  invFun i :=
    { toFun := i.hom
      invFun := i.inv
      left_inv := congr_fun i.hom_inv_id
      right_inv := congr_fun i.inv_hom_id }
  left_inv := by aesop_cat
  right_inv := by aesop_cat


/--
The "standard" skeleton for `FintypeNECat`. This is the full subcategory of `FintypeNECat`
spanned by objects of the form `ULift (Fin (n + 1_)` for `n : ℕ`. We parametrize the objects
of `FintypeNE.Skeleton` directly as `ULift ℕ`, as the type `ULift (Fin (m + 1)) ≃ ULift (Fin (n + 1))`
is nonempty if and only if `n = m`. Specifying universes, `Skeleton : Type u` is a small
skeletal category equivalent to `FintypeNE.{u}`.
-/
def Skeleton : Type u :=
  ULift ℕ

namespace Skeleton

/-- Given any natural number `n`, this creates the associated object of `FintypeNE.Skeleton`. -/
def mk : ℕ → Skeleton :=
  ULift.up

instance : Inhabited Skeleton :=
  ⟨mk 0⟩

/-- Given any object of `FintypeNE.Skeleton`, this returns the associated natural number. -/
def len : Skeleton → ℕ :=
  ULift.down

@[ext]
theorem ext (X Y : Skeleton) : X.len = Y.len → X = Y :=
  ULift.ext _ _

instance : SmallCategory Skeleton.{u} where
  Hom X Y := ULift.{u} (Fin (X.len + 1)) → ULift.{u} (Fin (Y.len + 1))
  id _ := id
  comp f g := g ∘ f
  id_comp := by tauto
  comp_id := by tauto
  assoc := by tauto

theorem is_skeletal : Skeletal Skeleton.{u} := fun X Y ⟨h⟩ =>
  ext _ _ <|
   Nat.succ_injective <|
    Fin.equiv_iff_eq.mp <|
      Nonempty.intro <|
        { toFun := fun x => (h.hom ⟨x⟩).down
          invFun := fun x => (h.inv ⟨x⟩).down
          left_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.hom ≫ h.inv) _).down = _
            simp
            rfl
          right_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.inv ≫ h.hom) _).down = _
            simp
            rfl }


/-- The canonical fully faithful embedding of `FintypeNE.Skeleton` into `FintypeNECat`. -/
def incl : Skeleton.{u} ⥤ FintypeNECat.{u} where
  obj X := FintypeNECat.of (ULift (Fin (X.len + 1)))
  map f := f

instance : Full incl where preimage f := f

instance : Faithful incl where


instance : EssSurj incl :=
  EssSurj.mk fun X =>
    let F := @FintypeNE.equivFin X.1 X.2
    ⟨mk (Fintype.card X).pred,
      Nonempty.intro
        { hom := F.symm ∘ ULift.down
          inv := ULift.up ∘ F }⟩

noncomputable instance : IsEquivalence incl :=
  Equivalence.ofFullyFaithfullyEssSurj _

/-- The equivalence between `Fintype.Skeleton` and `FintypeNE`. -/
noncomputable def equivalence : Skeleton ≌ FintypeNECat :=
  incl.asEquivalence


@[simp]
theorem incl_mk_nat_card (n : ℕ) : Fintype.card (incl.obj (mk n)) = n + 1 := by
  convert Finset.card_fin (n+1)
  apply Fintype.ofEquiv_card

end Skeleton

/-- `FintypeNE.Skeleton` is a skeleton of `FintypeNE`. -/
noncomputable def isSkeleton : IsSkeletonOf FintypeNECat Skeleton Skeleton.incl where
  skel := Skeleton.is_skeletal
  eqv := by infer_instance



/- We define the geometric realization, sending an object S of FintypeNECat to the topological simplex on S.-/

noncomputable section

open BigOperators CategoryTheory NNReal

attribute [local instance] CategoryTheory.ConcreteCategory.hasCoeToSort
    CategoryTheory.ConcreteCategory.instFunLike

def toTopObj (S : FintypeNECat) := {f : S.1 → ℝ≥0 | ∑ i, f i = 1}

/-
instance (S : FintypeNECat) : CoeFun S.toTopObj fun _ => S.1 → ℝ≥0 :=
  ⟨fun f => (f : S.1 → ℝ≥0)⟩
-/


@[ext]
theorem toTopObj.ext {S : FintypeNECat} (f g : S.toTopObj) : (f : S → ℝ≥0) = g → f = g :=
  Subtype.ext

def toTopMap {S T : FintypeNECat} (f : S ⟶ T) : S.toTopObj → T.toTopObj := fun g =>
  ⟨fun i => ∑ j in Finset.univ.filter fun k => f k = i, g.1 j, by
    simp only [Finset.sum_congr, toTopObj, Set.mem_setOf]
    rw [← Finset.sum_biUnion]
    have hg := g.2
    dsimp [toTopObj] at hg
    convert hg
    · simp [Finset.eq_univ_iff_forall]
    · intro i _ j _ h
      rw [Function.onFun, disjoint_iff_inf_le]
      intro e he
      simp only [Finset.bot_eq_empty, Finset.not_mem_empty]
      apply h
      simp only [Finset.mem_univ, forall_true_left,
        ge_iff_le, Finset.le_eq_subset, Finset.inf_eq_inter, Finset.mem_inter,
        Finset.mem_filter, true_and] at he
      rw [← he.1, he.2]⟩

@[simp]
theorem coe_toTopMap {S T : FintypeNECat} (f : S ⟶ T) (g : S.toTopObj) (i : T) :
    (toTopMap f g).1 i = ∑ j in Finset.univ.filter fun k => f k = i, g.1 j :=
  rfl


@[continuity]
theorem continuous_toTopMap {S T : FintypeNECat} (f : S ⟶ T) : Continuous (FintypeNECat.toTopMap f) := by
  refine' Continuous.subtype_mk (continuous_pi fun i => _) _
  dsimp only [coe_toTopMap]
  exact continuous_finset_sum _ (fun j _ => (continuous_apply _).comp continuous_subtype_val)



/-- The functor associating the topological simplex on the set of vertices `S` to `S : FintypeNECat`. -/
@[simps]
def toTop : FintypeNECat.{u} ⥤ TopCat.{u} where
  obj S := TopCat.of S.toTopObj
  map f := ⟨toTopMap f, by continuity⟩
  map_id := by
    intro Δ
    ext f
    apply toTopObj.ext
    funext i
    change (Finset.univ.filter fun k => k = i).sum _ = _
    simp [Finset.sum_filter, CategoryTheory.id_apply]
  map_comp := fun f g => by
    ext h
    apply toTopObj.ext
    funext i
    dsimp
    rw [CategoryTheory.comp_apply]
    erw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, ContinuousMap.coe_mk]
    simp only [coe_toTopMap]
    erw [← Finset.sum_biUnion]
    · apply Finset.sum_congr
      · exact Finset.ext (fun j => ⟨fun hj => by simpa using hj, fun hj => by simpa using hj⟩)
      · tauto
    · intro j _ k _ h
      rw [Function.onFun, disjoint_iff_inf_le]
      intro e he
      simp only [Finset.bot_eq_empty, Finset.not_mem_empty]
      apply h
      simp only [Finset.mem_univ, forall_true_left,
        ge_iff_le, Finset.le_eq_subset, Finset.inf_eq_inter, Finset.mem_inter,
        Finset.mem_filter, true_and] at he
      rw [← he.1, he.2]

end


end FintypeNECat
