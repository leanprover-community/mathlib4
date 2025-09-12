/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.SetTheory.ZFC.Ordinal

/-!
# ZFC classes

Classes in set theory are usually defined as collections of elements satisfying some property.
Here, however, we define `Class` as `Set ZFSet` to derive many instances automatically,
most of them being the lifting of set operations to classes. The usual definition is then
definitionally equal to ours.

## Main definitions

* `Class`: Defined as `Set ZFSet`.
* `Class.iota`: Definite description operator.
* `ZFSet.isOrdinal_notMem_univ`: The Burali-Forti paradox. Ordinals form a proper class.
-/


universe u

/-- The collection of all classes.
We define `Class` as `Set ZFSet`, as this allows us to get many instances automatically. However, in
practice, we treat it as (the definitionally equal) `ZFSet → Prop`. This means, the preferred way to
state that `x : ZFSet` belongs to `A : Class` is to write `A x`. -/
@[pp_with_univ]
def Class :=
  Set ZFSet deriving HasSubset, EmptyCollection, Nonempty, Union, Inter, HasCompl, SDiff

instance : Insert ZFSet Class :=
  ⟨Set.insert⟩

namespace Class

-- Porting note: this used to be a `deriving HasSep Set` instance,
-- it should probably be turned into notation.
/-- `{x ∈ A | p x}` is the class of elements in `A` satisfying `p` -/
protected def sep (p : ZFSet → Prop) (A : Class) : Class :=
  {y | A y ∧ p y}

@[ext]
theorem ext {x y : Class.{u}} : (∀ z : ZFSet.{u}, x z ↔ y z) → x = y :=
  Set.ext

/-- Coerce a ZFC set into a class -/
@[coe]
def ofSet (x : ZFSet.{u}) : Class.{u} :=
  { y | y ∈ x }

instance : Coe ZFSet Class :=
  ⟨ofSet⟩

/-- The universal class -/
def univ : Class :=
  Set.univ

/-- Assert that `A` is a ZFC set satisfying `B` -/
def ToSet (B : Class.{u}) (A : Class.{u}) : Prop :=
  ∃ x : ZFSet, ↑x = A ∧ B x

/-- `A ∈ B` if `A` is a ZFC set which satisfies `B` -/
protected def Mem (B A : Class.{u}) : Prop :=
  ToSet.{u} B A

instance : Membership Class Class :=
  ⟨Class.Mem⟩

theorem mem_def (A B : Class.{u}) : A ∈ B ↔ ∃ x : ZFSet, ↑x = A ∧ B x :=
  Iff.rfl

@[simp]
theorem notMem_empty (x : Class.{u}) : x ∉ (∅ : Class.{u}) := fun ⟨_, _, h⟩ => h

@[deprecated (since := "2025-05-23")] alias not_mem_empty := notMem_empty

@[simp]
theorem not_empty_hom (x : ZFSet.{u}) : ¬(∅ : Class.{u}) x :=
  id

@[simp]
theorem mem_univ {A : Class.{u}} : A ∈ univ.{u} ↔ ∃ x : ZFSet.{u}, ↑x = A :=
  exists_congr fun _ => iff_of_eq (and_true _)

@[simp]
theorem mem_univ_hom (x : ZFSet.{u}) : univ.{u} x :=
  trivial

theorem eq_univ_iff_forall {A : Class.{u}} : A = univ ↔ ∀ x : ZFSet, A x :=
  Set.eq_univ_iff_forall

theorem eq_univ_of_forall {A : Class.{u}} : (∀ x : ZFSet, A x) → A = univ :=
  Set.eq_univ_of_forall

theorem mem_wf : @WellFounded Class.{u} (· ∈ ·) :=
  ⟨by
    have H : ∀ x : ZFSet.{u}, @Acc Class.{u} (· ∈ ·) ↑x := by
      refine fun a => ZFSet.inductionOn a fun x IH => ⟨_, ?_⟩
      rintro A ⟨z, rfl, hz⟩
      exact IH z hz
    refine fun A => ⟨A, ?_⟩
    rintro B ⟨x, rfl, _⟩
    exact H x⟩

instance : IsWellFounded Class (· ∈ ·) :=
  ⟨mem_wf⟩

instance : WellFoundedRelation Class :=
  ⟨_, mem_wf⟩

theorem mem_asymm {x y : Class} : x ∈ y → y ∉ x :=
  asymm_of (· ∈ ·)

theorem mem_irrefl (x : Class) : x ∉ x :=
  irrefl_of (· ∈ ·) x

/-- **There is no universal set.**
This is stated as `univ ∉ univ`, meaning that `univ` (the class of all sets) is proper (does not
belong to the class of all sets). -/
theorem univ_notMem_univ : univ ∉ univ :=
  mem_irrefl _

@[deprecated (since := "2025-05-23")] alias univ_not_mem_univ := univ_notMem_univ

/-- Convert a conglomerate (a collection of classes) into a class -/
def congToClass (x : Set Class.{u}) : Class.{u} :=
  { y | ↑y ∈ x }

@[simp]
theorem congToClass_empty : congToClass ∅ = ∅ := by
  rfl

/-- Convert a class into a conglomerate (a collection of classes) -/
def classToCong (x : Class.{u}) : Set Class.{u} :=
  { y | y ∈ x }

@[simp]
theorem classToCong_empty : classToCong ∅ = ∅ := by
  simp [classToCong]

/-- The power class of a class is the class of all subclasses that are ZFC sets -/
def powerset (x : Class) : Class :=
  congToClass (Set.powerset x)

/-- The union of a class is the class of all members of ZFC sets in the class. Uses `⋃₀` notation,
scoped under the `Class` namespace. -/
def sUnion (x : Class) : Class :=
  ⋃₀ classToCong x

@[inherit_doc]
scoped prefix:110 "⋃₀ " => Class.sUnion

/-- The intersection of a class is the class of all members of ZFC sets in the class .
Uses `⋂₀` notation, scoped under the `Class` namespace. -/
def sInter (x : Class) : Class :=
  ⋂₀ classToCong x

@[inherit_doc]
scoped prefix:110 "⋂₀ " => Class.sInter

theorem ofSet.inj {x y : ZFSet.{u}} (h : (x : Class.{u}) = y) : x = y :=
  ZFSet.ext fun z => by
    change (x : Class.{u}) z ↔ (y : Class.{u}) z
    rw [h]

@[simp]
theorem toSet_of_ZFSet (A : Class.{u}) (x : ZFSet.{u}) : ToSet A x ↔ A x :=
  ⟨fun ⟨y, yx, py⟩ => by rwa [ofSet.inj yx] at py, fun px => ⟨x, rfl, px⟩⟩

@[simp, norm_cast]
theorem coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x ∈ A ↔ A x :=
  toSet_of_ZFSet _ _

@[simp]
theorem coe_apply {x y : ZFSet.{u}} : (y : Class.{u}) x ↔ x ∈ y :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_subset (x y : ZFSet.{u}) : (x : Class.{u}) ⊆ y ↔ x ⊆ y :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_sep (p : Class.{u}) (x : ZFSet.{u}) :
    (ZFSet.sep p x : Class) = { y ∈ x | p y } :=
  ext fun _ => ZFSet.mem_sep

@[simp, norm_cast]
theorem coe_empty : ↑(∅ : ZFSet.{u}) = (∅ : Class.{u}) :=
  ext fun y => iff_false _ ▸ ZFSet.notMem_empty y

@[simp, norm_cast]
theorem coe_insert (x y : ZFSet.{u}) : ↑(insert x y) = @insert ZFSet.{u} Class.{u} _ x y :=
  ext fun _ => ZFSet.mem_insert_iff

@[simp, norm_cast]
theorem coe_union (x y : ZFSet.{u}) : ↑(x ∪ y) = (x : Class.{u}) ∪ y :=
  ext fun _ => ZFSet.mem_union

@[simp, norm_cast]
theorem coe_inter (x y : ZFSet.{u}) : ↑(x ∩ y) = (x : Class.{u}) ∩ y :=
  ext fun _ => ZFSet.mem_inter

@[simp, norm_cast]
theorem coe_diff (x y : ZFSet.{u}) : ↑(x \ y) = (x : Class.{u}) \ y :=
  ext fun _ => ZFSet.mem_diff

@[simp, norm_cast]
theorem coe_powerset (x : ZFSet.{u}) : ↑x.powerset = powerset.{u} x :=
  ext fun _ => ZFSet.mem_powerset

@[simp]
theorem powerset_apply {A : Class.{u}} {x : ZFSet.{u}} : powerset A x ↔ ↑x ⊆ A :=
  Iff.rfl

@[simp]
theorem sUnion_apply {x : Class} {y : ZFSet} : (⋃₀ x) y ↔ ∃ z : ZFSet, x z ∧ y ∈ z := by
  constructor
  · rintro ⟨-, ⟨z, rfl, hxz⟩, hyz⟩
    exact ⟨z, hxz, hyz⟩
  · exact fun ⟨z, hxz, hyz⟩ => ⟨_, coe_mem.2 hxz, hyz⟩

open scoped ZFSet in
@[simp, norm_cast]
theorem coe_sUnion (x : ZFSet.{u}) : ↑(⋃₀ x : ZFSet) = ⋃₀ (x : Class.{u}) :=
  ext fun y =>
    ZFSet.mem_sUnion.trans (sUnion_apply.trans <| by rfl).symm

@[simp]
theorem mem_sUnion {x y : Class.{u}} : y ∈ ⋃₀ x ↔ ∃ z, z ∈ x ∧ y ∈ z := by
  constructor
  · rintro ⟨w, rfl, z, hzx, hwz⟩
    exact ⟨z, hzx, coe_mem.2 hwz⟩
  · rintro ⟨w, hwx, z, rfl, hwz⟩
    exact ⟨z, rfl, w, hwx, hwz⟩

theorem sInter_apply {x : Class.{u}} {y : ZFSet.{u}} : (⋂₀ x) y ↔ ∀ z : ZFSet.{u}, x z → y ∈ z := by
  refine ⟨fun hxy z hxz => hxy _ ⟨z, rfl, hxz⟩, ?_⟩
  rintro H - ⟨z, rfl, hxz⟩
  exact H _ hxz

open scoped ZFSet in
@[simp, norm_cast]
theorem coe_sInter {x : ZFSet.{u}} (h : x.Nonempty) : ↑(⋂₀ x : ZFSet) = ⋂₀ (x : Class.{u}) :=
  Set.ext fun _ => (ZFSet.mem_sInter h).trans sInter_apply.symm

theorem mem_of_mem_sInter {x y z : Class} (hy : y ∈ ⋂₀ x) (hz : z ∈ x) : y ∈ z := by
  obtain ⟨w, rfl, hw⟩ := hy
  exact coe_mem.2 (hw z hz)

theorem mem_sInter {x y : Class.{u}} (h : x.Nonempty) : y ∈ ⋂₀ x ↔ ∀ z, z ∈ x → y ∈ z := by
  refine ⟨fun hy z => mem_of_mem_sInter hy, fun H => ?_⟩
  simp_rw [mem_def, sInter_apply]
  obtain ⟨z, hz⟩ := h
  obtain ⟨y, rfl, _⟩ := H z (coe_mem.2 hz)
  refine ⟨y, rfl, fun w hxw => ?_⟩
  simpa only [coe_mem, coe_apply] using H w (coe_mem.2 hxw)

@[simp]
theorem sUnion_empty : ⋃₀ (∅ : Class.{u}) = (∅ : Class.{u}) := by
  ext
  simp

@[simp]
theorem sInter_empty : ⋂₀ (∅ : Class.{u}) = univ := by
  rw [sInter, classToCong_empty, Set.sInter_empty, univ]

/-- An induction principle for sets. If every subset of a class is a member, then the class is
  universal. -/
theorem eq_univ_of_powerset_subset {A : Class} (hA : powerset A ⊆ A) : A = univ :=
  eq_univ_of_forall
    (by
      by_contra! hnA
      exact
        WellFounded.min_mem ZFSet.mem_wf _ hnA
          (hA fun x hx =>
            Classical.not_not.1 fun hB =>
              WellFounded.not_lt_min ZFSet.mem_wf _ hnA hB <| coe_apply.1 hx))

/-- The definite description operator, which is `{x}` if `{y | A y} = {x}` and `∅` otherwise. -/
def iota (A : Class) : Class :=
  ⋃₀ ({ x | ∀ y, A y ↔ y = x } : Class)

theorem iota_val (A : Class) (x : ZFSet) (H : ∀ y, A y ↔ y = x) : iota A = ↑x :=
  ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by rwa [← (H x').1 <| (h x').2 rfl], fun yx =>
      ⟨_, ⟨x, rfl, H⟩, yx⟩⟩

/-- Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `Class → Set` function. -/
theorem iota_ex (A) : iota.{u} A ∈ univ.{u} :=
  mem_univ.2 <|
    Or.elim (Classical.em <| ∃ x, ∀ y, A y ↔ y = x) (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val A x h⟩)
      fun hn =>
      ⟨∅, ext fun _ => coe_empty.symm ▸ ⟨False.rec, fun ⟨_, ⟨x, rfl, H⟩, _⟩ => hn ⟨x, H⟩⟩⟩

/-- Function value -/
def fval (F A : Class.{u}) : Class.{u} :=
  iota fun y => ToSet (fun x => F (ZFSet.pair x y)) A

@[inherit_doc]
infixl:100 " ′ " => fval

theorem fval_ex (F A : Class.{u}) : F ′ A ∈ univ.{u} :=
  iota_ex _

end Class

namespace ZFSet

@[simp]
theorem map_fval {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}}
    (h : y ∈ x) : (ZFSet.map f x ′ y : Class.{u}) = f y :=
  Class.iota_val _ _ fun z => by
    rw [Class.toSet_of_ZFSet, Class.coe_apply, mem_map]
    exact
      ⟨fun ⟨w, _, pr⟩ => by
        let ⟨wy, fw⟩ := ZFSet.pair_injective pr
        rw [← fw, wy], fun e => by
        subst e
        exact ⟨_, h, rfl⟩⟩

variable (x : ZFSet.{u})

/-- A choice function on the class of nonempty ZFC sets. -/
noncomputable def choice : ZFSet :=
  @map (fun y => Classical.epsilon fun z => z ∈ y) (Classical.allZFSetDefinable _) x

theorem choice_mem_aux (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y ∈ x) :
    (Classical.epsilon fun z : ZFSet.{u} => z ∈ y) ∈ y :=
  (@Classical.epsilon_spec _ fun z : ZFSet.{u} => z ∈ y) <|
    by_contradiction fun n => h <| by rwa [← (eq_empty y).2 fun z zx => n ⟨z, zx⟩]

theorem choice_isFunc (h : ∅ ∉ x) : IsFunc x (⋃₀ x) (choice x) :=
  (@map_isFunc _ (Classical.allZFSetDefinable _) _ _).2 fun y yx =>
    mem_sUnion.2 ⟨y, yx, choice_mem_aux x h y yx⟩

theorem choice_mem (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y ∈ x) :
    (choice x ′ y : Class.{u}) ∈ (y : Class.{u}) := by
  delta choice
  rw [@map_fval _ (Classical.allZFSetDefinable _) x y yx, Class.coe_mem, Class.coe_apply]
  exact choice_mem_aux x h y yx

private lemma toSet_equiv_aux {s : Set ZFSet.{u}} (hs : Small.{u} s) :
    (mk <| PSet.mk (Shrink s) fun x ↦ ((equivShrink s).symm x).1.out).toSet = s := by
  ext x
  rw [mem_toSet, ← mk_out x, mk_mem_iff, mk_out]
  refine ⟨?_, fun xs ↦ ⟨equivShrink s (Subtype.mk x xs), ?_⟩⟩
  · rintro ⟨b, h2⟩
    rw [← ZFSet.eq, ZFSet.mk_out] at h2
    simp [h2]
  · simp [PSet.Equiv.refl]

/-- `ZFSet.toSet` as an equivalence. -/
@[simps apply_coe]
noncomputable def toSet_equiv : ZFSet.{u} ≃ {s : Set ZFSet.{u} // Small.{u, u+1} s} where
  toFun x := ⟨x.toSet, x.small_toSet⟩
  invFun := fun ⟨s, _⟩ ↦ mk <| PSet.mk (Shrink s) fun x ↦ ((equivShrink.{u, u + 1} s).symm x).1.out
  left_inv := Function.rightInverse_of_injective_of_leftInverse (by intro _ _; simp)
    fun s ↦ Subtype.coe_injective <| toSet_equiv_aux s.2
  right_inv s := Subtype.coe_injective <| toSet_equiv_aux s.2

/-- The **Burali-Forti paradox**: ordinals form a proper class. -/
theorem isOrdinal_notMem_univ : IsOrdinal ∉ Class.univ.{u} := by
  rintro ⟨x, hx, -⟩
  suffices IsOrdinal x by
    apply Class.mem_irrefl x
    rwa [Class.coe_mem, hx]
  refine ⟨fun y hy z hz ↦ ?_, fun hyz hzw hwx ↦ ?_⟩ <;> rw [← Class.coe_apply, hx] at *
  exacts [hy.mem hz, hwx.mem_trans hyz hzw]

@[deprecated (since := "2025-05-23")] alias isOrdinal_not_mem_univ := isOrdinal_notMem_univ

end ZFSet
