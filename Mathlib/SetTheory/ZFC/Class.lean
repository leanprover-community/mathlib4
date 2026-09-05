/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.SetTheory.ZFC.Ordinal

/-!
# ZFC classes

Classes in set theory are usually defined as collections of elements satisfying some property.
Here, however, we define `Class` as `Set ZFSet` to derive many instances automatically,
most of them being the lifting of set operations to classes. The usual definition is then
equivalent to ours.

## Main definitions

* `Class`: Defined as `Set ZFSet`.
* `Class.iota`: Definite description operator.
* `ZFSet.isOrdinal_notMem_univ`: The Burali-Forti paradox. Ordinals form a proper class.
-/

@[expose] public section


universe u

/-- The collection of all classes.
We define `Class` as `Set ZFSet`, as this allows us to get many instances automatically, and to
freely mix `x ∈ A` (for `x : ZFSet`, `A : Class`) with the coercion `Class.ofSet`. -/
@[pp_with_univ, use_set_notation_for_order]
abbrev Class := Set ZFSet

instance : Insert ZFSet Class :=
  ⟨Set.insert⟩

namespace Class

/-- Coerce a ZFC set into a class -/
@[coe]
def ofSet (x : ZFSet.{u}) : Class.{u} :=
  { y | y ∈ x }

instance : Coe ZFSet Class :=
  ⟨ofSet⟩

/-- The universal class -/
def univ : Class :=
  Set.univ

instance : Top Class := ⟨univ⟩

deriving instance CompleteLattice for Class

/-- `A ∈ B` if `A` is a ZFC set which satisfies `B`.

Deliberately spelled `Class.Mem A B` rather than `A ∈ B`: `Class` is reducibly `Set ZFSet`, so a
`Membership Class Class` instance would compete with `Set`'s own `Membership ZFSet (Set ZFSet)`
instance for the (`outParam`) element type, and since `ZFSet` coerces into `Class`, `x ∈ A` (for
`x : ZFSet`, `A : Class`) would become genuinely ambiguous between the two. -/
protected def Mem (A B : Class.{u}) : Prop :=
  ∃ x : ZFSet, ↑x = A ∧ x ∈ B

theorem mem_def (A B : Class.{u}) : Class.Mem A B ↔ ∃ x : ZFSet, ↑x = A ∧ x ∈ B :=
  Iff.rfl

theorem ofSet.inj {x y : ZFSet.{u}} (h : (x : Class.{u}) = y) : x = y :=
  ZFSet.ext fun z => Set.ext_iff.1 h z

@[simp, norm_cast]
theorem mem_coe {x y : ZFSet.{u}} : x ∈ (y : Class.{u}) ↔ x ∈ y :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_mem {x : ZFSet.{u}} {A : Class.{u}} : Class.Mem (x : Class.{u}) A ↔ x ∈ A :=
  ⟨fun ⟨y, yx, py⟩ => by rwa [ofSet.inj yx] at py, fun px => ⟨x, rfl, px⟩⟩

@[ext]
theorem ext {x y : Class.{u}} (h : ∀ z : ZFSet.{u}, z ∈ x ↔ z ∈ y) : x = y :=
  Set.ext h

-- Porting note: this used to be a `deriving HasSep Set` instance,
-- it should probably be turned into notation.
/-- `{x ∈ A | p x}` is the class of elements in `A` satisfying `p` -/
protected def sep (p : ZFSet → Prop) (A : Class) : Class :=
  {y | Class.Mem ↑y A ∧ p y}

@[simp]
theorem notMem_empty (x : Class.{u}) : ¬ Class.Mem x (∅ : Class.{u}) := fun ⟨_, _, h⟩ => h

@[simp]
theorem not_empty_hom (x : ZFSet.{u}) : x ∉ (∅ : Class.{u}) :=
  id

@[simp]
theorem mem_univ {A : Class.{u}} : Class.Mem A univ.{u} ↔ ∃ x : ZFSet.{u}, ↑x = A :=
  exists_congr fun _ => iff_of_eq (and_true _)

@[simp]
theorem mem_univ_hom (x : ZFSet.{u}) : x ∈ univ.{u} :=
  trivial

theorem eq_univ_iff_forall {A : Class.{u}} : A = univ ↔ ∀ x : ZFSet, x ∈ A :=
  Set.eq_univ_iff_forall

theorem eq_univ_of_forall {A : Class.{u}} : (∀ x : ZFSet, x ∈ A) → A = univ :=
  Set.eq_univ_of_forall

theorem mem_wf : @WellFounded Class.{u} Class.Mem :=
  ⟨by
    have H : ∀ x : ZFSet.{u}, @Acc Class.{u} Class.Mem ↑x := by
      refine fun a => ZFSet.inductionOn a fun x IH => ⟨_, ?_⟩
      rintro A ⟨z, rfl, hz⟩
      exact IH z hz
    refine fun A => ⟨A, ?_⟩
    rintro B ⟨x, rfl, _⟩
    exact H x⟩

instance : IsWellFounded Class Class.Mem :=
  ⟨mem_wf⟩

instance : WellFoundedRelation Class :=
  ⟨_, mem_wf⟩

theorem mem_asymm {x y : Class} : Class.Mem x y → ¬ Class.Mem y x :=
  asymm_of Class.Mem

theorem mem_irrefl (x : Class) : ¬ Class.Mem x x :=
  irrefl_of Class.Mem x

/-- **There is no universal set.**
This is stated as `¬ Class.Mem univ univ`, meaning that `univ` (the class of all sets) is proper
(does not belong to the class of all sets). -/
theorem univ_notMem_univ : ¬ Class.Mem univ univ :=
  mem_irrefl _

/-- Convert a conglomerate (a collection of classes) into a class -/
def congToClass (x : Set Class.{u}) : Class.{u} :=
  { y | ↑y ∈ x }

@[simp]
theorem congToClass_empty : congToClass ∅ = ∅ := by
  rfl

/-- Convert a class into a conglomerate (a collection of classes) -/
def classToCong (x : Class.{u}) : Set Class.{u} :=
  { y | Class.Mem y x }

@[simp]
theorem classToCong_empty : classToCong ∅ = ∅ := by
  simp [classToCong, notMem_empty]

/-- The power class of a class is the class of all subclasses that are ZFC sets -/
def powerset (x : Class) : Class :=
  congToClass (Set.powerset x)

/-- The union of a class is the class of all members of ZFC sets in the class. Uses `⋃₀` notation,
scoped under the `Class` namespace. -/
def sUnion (x : Class) : Class :=
  sSup (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋃₀ " => Class.sUnion

/-- The intersection of a class is the class of all members of ZFC sets in the class .
Uses `⋂₀` notation, scoped under the `Class` namespace. -/
def sInter (x : Class) : Class :=
  sInf (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋂₀ " => Class.sInter

@[simp, norm_cast]
theorem coe_subset (x y : ZFSet.{u}) : (x : Class.{u}) ⊆ y ↔ x ⊆ y :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_sep (p : ZFSet.{u} → Prop) (x : ZFSet.{u}) :
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
theorem coe_sdiff (x y : ZFSet.{u}) : ↑(x \ y) = (x : Class.{u}) \ y :=
  ext fun _ => ZFSet.mem_sdiff

@[deprecated (since := "2026-06-03")] alias coe_diff := coe_sdiff

@[simp, norm_cast]
theorem coe_powerset (x : ZFSet.{u}) : ↑x.powerset = powerset.{u} x :=
  ext fun _ => ZFSet.mem_powerset

@[simp]
theorem mem_powerset {A : Class.{u}} {x : ZFSet.{u}} : x ∈ powerset A ↔ ↑x ⊆ A :=
  Iff.rfl

@[simp]
theorem mem_sUnion_of_zfset {x : Class.{u}} {y : ZFSet.{u}} :
    y ∈ ⋃₀ x ↔ ∃ z : ZFSet, z ∈ x ∧ y ∈ z := by
  constructor
  · rintro ⟨-, ⟨z, rfl, hxz⟩, hyz⟩
    exact ⟨z, hxz, hyz⟩
  · exact fun ⟨z, hxz, hyz⟩ => ⟨_, coe_mem.2 hxz, hyz⟩

open scoped ZFSet in
@[simp, norm_cast]
theorem coe_sUnion (x : ZFSet.{u}) : ↑(⋃₀ x : ZFSet) = ⋃₀ (x : Class.{u}) :=
  ext fun y =>
    ZFSet.mem_sUnion.trans (mem_sUnion_of_zfset.trans <| by rfl).symm

@[simp]
theorem mem_sUnion {x y : Class.{u}} : Class.Mem y (⋃₀ x) ↔ ∃ z, Class.Mem z x ∧ Class.Mem y z := by
  constructor
  · rintro ⟨w, rfl, z, hzx, hwz⟩
    exact ⟨z, hzx, coe_mem.2 hwz⟩
  · rintro ⟨w, hwx, z, rfl, hwz⟩
    exact ⟨z, rfl, w, hwx, hwz⟩

theorem mem_sInter_of_zfset {x : Class.{u}} {y : ZFSet.{u}} :
    y ∈ ⋂₀ x ↔ ∀ z : ZFSet.{u}, z ∈ x → y ∈ z := by
  refine ⟨fun hxy z hxz => hxy _ ⟨z, rfl, hxz⟩, ?_⟩
  rintro H - ⟨z, rfl, hxz⟩
  exact H _ hxz

open scoped ZFSet in
@[simp, norm_cast]
theorem coe_sInter {x : ZFSet.{u}} (h : x.Nonempty) : ↑(⋂₀ x : ZFSet) = ⋂₀ (x : Class.{u}) :=
  ext fun _ => (ZFSet.mem_sInter h).trans mem_sInter_of_zfset.symm

theorem mem_of_mem_sInter {x y z : Class} (hy : Class.Mem y (⋂₀ x)) (hz : Class.Mem z x) :
    Class.Mem y z := by
  obtain ⟨w, rfl, hw⟩ := hy
  exact coe_mem.2 (hw z hz)

theorem mem_sInter {x y : Class.{u}} (h : x.Nonempty) :
    Class.Mem y (⋂₀ x) ↔ ∀ z, Class.Mem z x → Class.Mem y z := by
  refine ⟨fun hy z => mem_of_mem_sInter hy, fun H => ?_⟩
  simp_rw [mem_def, mem_sInter_of_zfset]
  obtain ⟨z, hz⟩ := h
  obtain ⟨y, rfl, _⟩ := H z (coe_mem.2 hz)
  refine ⟨y, rfl, fun w hxw => ?_⟩
  simpa only [coe_mem, mem_coe] using H w (coe_mem.2 hxw)

@[simp]
theorem sUnion_empty : ⋃₀ (∅ : Class.{u}) = (∅ : Class.{u}) := by
  ext
  simp

@[simp]
theorem sInter_empty : ⋂₀ (∅ : Class.{u}) = univ := by
  simp [sInter, Top.top, univ]

/-- An induction principle for sets. If every subset of a class is a member, then the class is
  universal. -/
theorem eq_univ_of_powerset_subset {A : Class} (hA : powerset A ⊆ A) : A = univ :=
  eq_univ_of_forall
    (by
      by_contra! hnA
      exact
        WellFounded.min_mem ZFSet.mem_wf {x | x ∉ A} hnA
          (hA fun x hx =>
            Classical.not_not.1 fun hB =>
              WellFounded.not_lt_min ZFSet.mem_wf {x | x ∉ A} hB <|
                mem_coe.1 hx))

/-- The definite description operator, which is `{x}` if `A = {x}` and `∅` otherwise. -/
def iota (A : Class) : Class :=
  ⋃₀ ({ x | ∀ y : ZFSet, Class.Mem ↑y A ↔ y = x } : Class)

theorem iota_val (A : Class) (x : ZFSet) (H : ∀ y : ZFSet, Class.Mem ↑y A ↔ y = x) :
    iota A = ↑x :=
  ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by rwa [← (H x').1 <| (h x').2 rfl], fun yx =>
      ⟨_, ⟨x, rfl, H⟩, yx⟩⟩

/-- Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `Class → Set` function. -/
theorem iota_ex (A) : Class.Mem (iota.{u} A) univ.{u} :=
  mem_univ.2 <|
    Or.elim (Classical.em <| ∃ x : ZFSet, ∀ y : ZFSet, Class.Mem ↑y A ↔ y = x)
      (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val A x h⟩) fun hn =>
      ⟨∅, ext fun _ => coe_empty.symm ▸ ⟨False.rec, fun ⟨_, ⟨x, rfl, H⟩, _⟩ => hn ⟨x, H⟩⟩⟩

/-- Function value -/
def fval (F A : Class.{u}) : Class.{u} :=
  iota {y | Class.Mem A {x | Class.Mem ↑(ZFSet.pair x y) F}}

@[inherit_doc]
infixl:100 " ′ " => fval

theorem fval_ex (F A : Class.{u}) : Class.Mem (F ′ A) univ.{u} :=
  iota_ex _

end Class

namespace ZFSet

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem map_fval {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}}
    (h : y ∈ x) : (ZFSet.map f x ′ y : Class.{u}) = f y :=
  Class.iota_val _ _ fun z => by
    simp only [Class.coe_mem, Set.mem_ofPred_eq, Class.mem_coe, mem_map]
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
    Class.Mem (choice x ′ y : Class.{u}) (y : Class.{u}) := by
  delta choice
  rw [@map_fval _ (Classical.allZFSetDefinable _) x y yx, Class.coe_mem, Class.mem_coe]
  exact choice_mem_aux x h y yx

private lemma coe_equiv_aux {s : Set ZFSet.{u}} (hs : Small.{u} s) :
    (mk <| PSet.mk (Shrink s) fun x ↦ ((equivShrink s).symm x).1.out) = s := by
  ext x
  rw [SetLike.mem_coe, ← mk_out x, mk_mem_iff, mk_out]
  refine ⟨?_, fun xs ↦ ⟨equivShrink s (Subtype.mk x xs), ?_⟩⟩
  · rintro ⟨b, h2⟩
    rw [← ZFSet.eq, ZFSet.mk_out] at h2
    simp [h2]
  · simp [PSet.Equiv.refl]

/-- `SetLike.coe` as an equivalence. -/
@[simps apply_coe]
noncomputable def coeEquiv : ZFSet.{u} ≃ {s : Set ZFSet.{u} // Small.{u, u+1} s} where
  toFun x := ⟨x, x.small_coe⟩
  invFun := fun ⟨s, _⟩ ↦ mk <| PSet.mk (Shrink s) fun x ↦ ((equivShrink.{u, u + 1} s).symm x).1.out
  left_inv := private Function.rightInverse_of_injective_of_leftInverse (by intro _ _; simp)
    fun s ↦ Subtype.coe_injective <| coe_equiv_aux s.2
  right_inv s := private Subtype.coe_injective <| coe_equiv_aux s.2

/-- The **Burali-Forti paradox**: ordinals form a proper class. -/
theorem isOrdinal_notMem_univ : ¬ Class.Mem {x | IsOrdinal x} Class.univ.{u} := by
  rintro ⟨x, hx, -⟩
  suffices IsOrdinal x by
    apply Class.mem_irrefl (x : Class.{u})
    rwa [Class.coe_mem, hx, Set.mem_ofPred_eq]
  refine ⟨fun y hy z hz ↦ ?_, fun hyz hzw hwx ↦ ?_⟩ <;>
    rw [← Class.mem_coe, hx, Set.mem_ofPred_eq] at *
  exacts [hy.mem hz, hwx.mem_trans hyz hzw]

end ZFSet
