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
We model this by defining `ZFClass` as `Set ZFSet`.

## Main definitions

* `ZFClass`: Defined as `Set ZFSet`.
* `ZFClass.iota`: Definite description operator.
* `ZFSet.isOrdinal_notCMem_univ`: The Burali-Forti paradox. Ordinals form a proper class.
-/

@[expose] public section

universe u

/-- The collection of all classes.

Since the `A ∈ B` notation expects the type of `A` to be determined uniquely by the type of `B`,
we cannot allow both `A : ZFSet` and `A : ZFClass` for `B : ZFClass`. We give the `A ∈ B` notation
to the first and spell the second as `A ∈ᶜ B`. -/
@[pp_with_univ] abbrev ZFClass := Set ZFSet

namespace ZFClass
variable {A B C : ZFClass.{u}} {x y : ZFSet.{u}}

/-- Membership of classes. `A ∈ᶜ B` if `A` is a ZFC set which satisfies `B`.

Note that the `A ∈ B` notation is already taken for the case where `A : ZFSet` instead
(the `OutParam` in `CMem` forces the type of `A` to be uniquely inferrable from the type of `B`). -/
protected def CMem (A B : ZFClass.{u}) : Prop :=
  ∃ x : ZFSet, ↑x = A ∧ x ∈ B

@[inherit_doc]
scoped notation:50 A:50 " ∈ᶜ " B:50 => ZFClass.CMem A B

/-- Negated membership of classes, see `ZFClass.CMem`. -/
scoped notation:50 A:50 " ∉ᶜ " B:50 => ¬ ZFClass.CMem A B

/-- Coerce a ZFC set into a class -/
@[coe]
def ofSet (x : ZFSet.{u}) : ZFClass.{u} := {y | y ∈ x}

instance : Coe ZFSet ZFClass := ⟨ofSet⟩

@[simp, norm_cast] lemma mem_ofSet : x ∈ (y : ZFClass) ↔ x ∈ y := .rfl

lemma ofSet_injective : ofSet.Injective := fun _x _y h ↦ ZFSet.ext <| Set.ext_iff.1 h

@[simp] lemma ofSet_inj : ofSet x = ofSet y ↔ x = y := ofSet_injective.eq_iff

@[simp, norm_cast] lemma ofSet_cmem : x ∈ᶜ A ↔ x ∈ A := by simp [ZFClass.CMem]

@[simp] lemma not_cmem_empty : A ∉ᶜ ∅ := by simp [ZFClass.CMem]

@[simp] lemma cmem_univ : A ∈ᶜ .univ ↔ ∃ x : ZFSet.{u}, ↑x = A := by simp [ZFClass.CMem]

lemma cmem_wf : WellFounded ZFClass.CMem.{u} := by
  refine ⟨fun A ↦ ⟨A, ?_⟩⟩
  rintro B ⟨x, rfl, _⟩
  refine x.inductionOn fun x IH => ⟨_, ?_⟩
  rintro A ⟨z, rfl, hz⟩
  exact IH z hz

instance : IsWellFounded ZFClass (· ∈ᶜ ·) := ⟨cmem_wf⟩

instance : WellFoundedRelation ZFClass := ⟨_, cmem_wf⟩

lemma cmem_asymm : A ∈ᶜ B → B ∉ᶜ A := asymm_of ZFClass.CMem

lemma cmem_irrefl : A ∉ᶜ A := irrefl_of _ _

/-- **There is no universal set.**
This is stated as `univ ∉ᶜ univ`, meaning that `univ` (the class of all sets) is proper
(does not belong to the class of all sets). -/
lemma univ_notCMem_univ : (.univ : ZFClass) ∉ᶜ .univ := cmem_irrefl

/-- Convert a conglomerate (a collection of classes) into a class -/
def congToClass (x : Set ZFClass.{u}) : ZFClass.{u} := ofSet ⁻¹' x

/-- Convert a class into a conglomerate (a collection of classes) -/
def classToCong (x : ZFClass.{u}) : Set ZFClass.{u} := {y | y ∈ᶜ x}

@[simp] lemma congToClass_empty : congToClass ∅ = ∅ := by rfl
@[simp] lemma classToCong_empty : classToCong ∅ = ∅ := by simp [classToCong]

/-- The power class of a class is the class of all subclasses that are ZFC sets -/
def powerset (x : ZFClass) : ZFClass := congToClass (Set.powerset x)

/-- The union of a class is the class of all members of ZFC sets in the class. Uses `⋃₀` notation,
scoped under the `ZFClass` namespace. -/
def sUnion (x : ZFClass) : ZFClass := sSup (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋃₀ " => ZFClass.sUnion

/-- The intersection of a class is the class of all members of ZFC sets in the class .
Uses `⋂₀` notation, scoped under the `ZFClass` namespace. -/
def sInter (x : ZFClass) : ZFClass := sInf (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋂₀ " => ZFClass.sInter

@[simp, norm_cast]
lemma ofSet_subset : (x : ZFClass.{u}) ⊆ y ↔ x ⊆ y := .rfl

@[simp, norm_cast]
lemma ofSet_sep (p : ZFSet.{u} → Prop) (x : ZFSet.{u}) : x.sep p = {y ∈ x | p y} := by ext; simp

@[simp, norm_cast]
lemma ofSet_empty : ↑(∅ : ZFSet.{u}) = (∅ : ZFClass) := by ext; simp

@[simp, norm_cast]
lemma ofSet_insert (x y : ZFSet.{u}) : ↑(insert x y) = insert x (y : ZFClass) := by ext; simp

@[simp, norm_cast]
lemma ofSet_union (x y : ZFSet.{u}) : ↑(x ∪ y) = (x : ZFClass) ∪ y := by ext; simp

@[simp, norm_cast]
lemma ofSet_inter (x y : ZFSet.{u}) : ↑(x ∩ y) = (x : ZFClass) ∩ y := by ext; simp

@[simp, norm_cast]
lemma ofSet_sdiff (x y : ZFSet.{u}) : ↑(x \ y) = (x : ZFClass) \ y := by ext; simp

@[simp]
lemma mem_powerset : x ∈ powerset A ↔ ↑x ⊆ A := .rfl

@[simp, norm_cast]
lemma ofSet_powerset (x : ZFSet.{u}) : ↑x.powerset = powerset.{u} x := by ext; simp

@[simp] lemma mem_sUnion : y ∈ ⋃₀ A ↔ ∃ z : ZFSet, z ∈ A ∧ y ∈ z := by
  simp [sUnion, classToCong, ZFClass.CMem]

open scoped ZFSet in
@[simp, norm_cast]
lemma ofSet_sUnion (x : ZFSet.{u}) : ↑(⋃₀ x : ZFSet) = ⋃₀ (x : ZFClass.{u}) := by ext; simp

@[simp] lemma cmem_sUnion : B ∈ᶜ ⋃₀ A ↔ ∃ C, C ∈ᶜ A ∧ B ∈ᶜ C := by
  simp [sUnion, ZFClass.CMem, classToCong]; grind

lemma mem_sInter : y ∈ ⋂₀ A ↔ ∀ z ∈ A, y ∈ z := by
  simp +contextual [sInter, ZFClass.CMem, classToCong, eq_comm]; grind

open scoped ZFSet in
@[simp, norm_cast]
lemma ofSet_sInter (h : x.Nonempty) : ↑(⋂₀ x : ZFSet) = ⋂₀ (x : ZFClass.{u}) := by
  ext; simp [ZFSet.mem_sInter h, mem_sInter]

lemma cmem_of_cmem_sInter (hy : B ∈ᶜ ⋂₀ A) (hz : C ∈ᶜ A) : B ∈ᶜ C := by
  obtain ⟨w, rfl, hw⟩ := hy
  exact ofSet_cmem.2 (hw C hz)

lemma cmem_sInter (h : A.Nonempty) : B ∈ᶜ ⋂₀ A ↔ ∀ z, z ∈ᶜ A → B ∈ᶜ z := by
  refine ⟨fun hy z ↦ cmem_of_cmem_sInter hy, fun H ↦ ?_⟩
  simp_rw [ZFClass.CMem]
  obtain ⟨z, hz⟩ := h
  obtain ⟨y, rfl, _⟩ := H z (ofSet_cmem.2 hz)
  refine ⟨y, rfl, fun w hxw => ?_⟩
  simpa only [ofSet_cmem, mem_ofSet] using H w hxw

@[simp] lemma sUnion_empty : ⋃₀ (∅ : ZFClass.{u}) = ∅ := by ext; simp [sUnion, classToCong]

@[simp] lemma sInter_empty : ⋂₀ (∅ : ZFClass.{u}) = .univ := by ext; simp [sInter]

/-- An induction principle for sets. If every subset of a class is a member, then the class is
universal. -/
lemma eq_univ_of_powerset_subset (hA : powerset A ⊆ A) : A = .univ := by
  rw [Set.eq_univ_iff_forall]
  by_contra! hnA
  refine WellFounded.min_mem ZFSet.mem_wf {x | x ∉ A} hnA <| hA fun x hx ↦ ?_
  by_contra hB
  exact WellFounded.not_lt_min ZFSet.mem_wf {x | x ∉ A} hB <| mem_ofSet.1 hx

/-- The definite description operator, which is `{x}` if `A = {x}` and `∅` otherwise. -/
def iota (A : ZFClass) : ZFClass := ⋃₀ {x : ZFSet | ∀ y : ZFSet, ↑y ∈ᶜ A ↔ y = x}

lemma iota_val (A : ZFClass) (x : ZFSet) (H : ∀ y : ZFSet, ↑y ∈ᶜ A ↔ y = x) : iota A = ↑x :=
  Set.ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by rwa [← (H x').1 <| (h x').2 rfl], fun yx =>
      ⟨_, ⟨x, rfl, H⟩, yx⟩⟩

/-- Unlike the other set constructors, the `iota` definite descriptor is a set for any set input,
but not constructively so, so there is no associated `ZFClass → Set` function. -/
lemma iota_ex (A) : iota.{u} A ∈ᶜ .univ :=
  cmem_univ.2 <|
    Or.elim (Classical.em <| ∃ x : ZFSet, ∀ y : ZFSet, ↑y ∈ᶜ A ↔ y = x)
      (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val A x h⟩) fun hn =>
      ⟨∅, Set.ext fun _ => ofSet_empty.symm ▸ ⟨False.rec, fun ⟨_, ⟨x, rfl, H⟩, _⟩ => hn ⟨x, H⟩⟩⟩

/-- Function value -/
def fval (F A : ZFClass.{u}) : ZFClass.{u} := iota {y | A ∈ᶜ {x | ↑(ZFSet.pair x y) ∈ᶜ F}}

@[inherit_doc]
infixl:100 " ′ " => fval

lemma fval_ex (F A : ZFClass.{u}) : F ′ A ∈ᶜ .univ := iota_ex _

end ZFClass

/-- `Class` has been renamed to `ZFClass`. -/
@[deprecated ZFClass (since := "2026-09-05")]
abbrev Class := ZFClass

instance : Insert ZFSet Class :=
  ⟨Set.insert⟩

namespace Class

open scoped ZFClass

/-- `{x ∈ A | p x}` is the class of elements in `A` satisfying `p` -/
@[deprecated "no direct replacement" (since := "2026-09-05")]
protected def sep (p : ZFSet → Prop) (A : Class) : Class :=
  {y | A y ∧ p y}

@[deprecated Set.ext (since := "2026-09-05")]
theorem ext {x y : Class.{u}} : (∀ z : ZFSet.{u}, x z ↔ y z) → x = y :=
  Set.ext

/-- Coerce a ZFC set into a class -/
@[deprecated ZFClass.ofSet (since := "2026-09-05")]
def ofSet (x : ZFSet.{u}) : Class.{u} :=
  ZFClass.ofSet x

instance : Coe ZFSet Class :=
  inferInstance

/-- The universal class -/
@[deprecated Set.univ (since := "2026-09-05")]
def univ : Class :=
  Set.univ

instance : Top Class := ⟨univ⟩

instance : CompleteLattice Class := inferInstance

/-- Assert that `A` is a ZFC set satisfying `B` -/
@[deprecated ZFClass.CMem (since := "2026-09-05")]
def ToSet (B : Class.{u}) (A : Class.{u}) : Prop :=
  ∃ x : ZFSet, ↑x = A ∧ B x

/-- `A ∈ B` if `A` is a ZFC set which satisfies `B` -/
@[deprecated ZFClass.CMem (since := "2026-09-05")]
protected def Mem (B A : Class.{u}) : Prop :=
  ToSet.{u} B A

instance : Membership Class Class :=
  ⟨Class.Mem⟩

@[deprecated ZFClass.CMem (since := "2026-09-05")]
theorem mem_def (A B : Class.{u}) : A ∈ B ↔ ∃ x : ZFSet, ↑x = A ∧ B x :=
  Iff.rfl

@[deprecated ZFClass.not_cmem_empty (since := "2026-09-05")]
theorem notMem_empty (x : Class.{u}) : x ∉ (∅ : Class.{u}) := fun ⟨_, _, h⟩ => h

@[deprecated Set.notMem_empty (since := "2026-09-05")]
theorem not_empty_hom (x : ZFSet.{u}) : ¬(∅ : Class.{u}) x :=
  id

@[deprecated ZFClass.cmem_univ (since := "2026-09-05")]
theorem mem_univ {A : Class.{u}} : A ∈ univ.{u} ↔ ∃ x : ZFSet.{u}, ↑x = A :=
  exists_congr fun _ => iff_of_eq (and_true _)

@[deprecated Set.mem_univ (since := "2026-09-05")]
theorem mem_univ_hom (x : ZFSet.{u}) : univ.{u} x :=
  trivial

@[deprecated Set.eq_univ_iff_forall (since := "2026-09-05")]
theorem eq_univ_iff_forall {A : Class.{u}} : A = univ ↔ ∀ x : ZFSet, A x :=
  Set.eq_univ_iff_forall

@[deprecated Set.eq_univ_of_forall (since := "2026-09-05")]
theorem eq_univ_of_forall {A : Class.{u}} : (∀ x : ZFSet, A x) → A = univ :=
  Set.eq_univ_of_forall

@[deprecated ZFClass.cmem_wf (since := "2026-09-05")]
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

@[deprecated ZFClass.cmem_asymm (since := "2026-09-05")]
theorem mem_asymm {x y : Class} : x ∈ y → y ∉ x :=
  asymm_of (· ∈ ·)

@[deprecated ZFClass.cmem_irrefl (since := "2026-09-05")]
theorem mem_irrefl (x : Class) : x ∉ x :=
  irrefl_of (· ∈ ·) x

/-- **There is no universal set.**
This is stated as `univ ∉ univ`, meaning that `univ` (the class of all sets) is proper (does not
belong to the class of all sets). -/
@[deprecated ZFClass.univ_notCMem_univ (since := "2026-09-05")]
theorem univ_notMem_univ : univ ∉ univ :=
  mem_irrefl _

/-- Convert a conglomerate (a collection of classes) into a class -/
@[deprecated ZFClass.congToClass (since := "2026-09-05")]
def congToClass (x : Set Class.{u}) : Class.{u} :=
  ZFClass.congToClass x

@[deprecated ZFClass.congToClass_empty (since := "2026-09-05")]
theorem congToClass_empty : congToClass ∅ = ∅ := by
  rfl

/-- Convert a class into a conglomerate (a collection of classes) -/
@[deprecated ZFClass.classToCong (since := "2026-09-05")]
def classToCong (x : Class.{u}) : Set Class.{u} :=
  ZFClass.classToCong x

@[deprecated ZFClass.classToCong_empty (since := "2026-09-05")]
theorem classToCong_empty : classToCong ∅ = ∅ := by
  simp [classToCong]

/-- The power class of a class is the class of all subclasses that are ZFC sets -/
@[deprecated ZFClass.powerset (since := "2026-09-05")]
def powerset (x : Class) : Class :=
  ZFClass.powerset x

/-- The union of a class is the class of all members of ZFC sets in the class. -/
@[deprecated ZFClass.sUnion (since := "2026-09-05")]
def sUnion (x : Class) : Class :=
  ZFClass.sUnion x

/-- The intersection of a class is the class of all members of ZFC sets in the class. -/
@[deprecated ZFClass.sInter (since := "2026-09-05")]
def sInter (x : Class) : Class :=
  ZFClass.sInter x

@[deprecated ZFClass.ofSet_injective (since := "2026-09-05")]
theorem ofSet.inj {x y : ZFSet.{u}} (h : (x : Class.{u}) = y) : x = y :=
  ZFSet.ext fun z => by
    change (x : Class.{u}) z ↔ (y : Class.{u}) z
    rw [h]

@[deprecated ZFClass.ofSet_cmem (since := "2026-09-05")]
theorem toSet_of_ZFSet (A : Class.{u}) (x : ZFSet.{u}) : ToSet A x ↔ A x :=
  ⟨fun ⟨y, yx, py⟩ => by rwa [ofSet.inj yx] at py, fun px => ⟨x, rfl, px⟩⟩

@[deprecated ZFClass.mem_ofSet (since := "2026-09-05")]
theorem coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x ∈ A ↔ A x :=
  toSet_of_ZFSet _ _

@[deprecated ZFClass.mem_ofSet (since := "2026-09-05")]
theorem coe_apply {x y : ZFSet.{u}} : (y : Class.{u}) x ↔ x ∈ y :=
  Iff.rfl

@[deprecated ZFClass.ofSet_subset (since := "2026-09-05")]
theorem coe_subset (x y : ZFSet.{u}) : (x : Class.{u}) ⊆ y ↔ x ⊆ y :=
  Iff.rfl

@[deprecated ZFClass.ofSet_sep (since := "2026-09-05")]
theorem coe_sep (p : Class.{u}) (x : ZFSet.{u}) :
    (ZFSet.sep p x : Class) = { y ∈ x | p y } :=
  ext fun _ => ZFSet.mem_sep

@[deprecated ZFClass.ofSet_empty (since := "2026-09-05")]
theorem coe_empty : ↑(∅ : ZFSet.{u}) = (∅ : Class.{u}) :=
  ext fun y => iff_false _ ▸ ZFSet.notMem_empty y

@[deprecated ZFClass.ofSet_insert (since := "2026-09-05")]
theorem coe_insert (x y : ZFSet.{u}) : ↑(insert x y) = @insert ZFSet.{u} Class.{u} _ x y :=
  ext fun _ => ZFSet.mem_insert_iff

@[deprecated ZFClass.ofSet_union (since := "2026-09-05")]
theorem coe_union (x y : ZFSet.{u}) : ↑(x ∪ y) = (x : Class.{u}) ∪ y :=
  ext fun _ => ZFSet.mem_union

@[deprecated ZFClass.ofSet_inter (since := "2026-09-05")]
theorem coe_inter (x y : ZFSet.{u}) : ↑(x ∩ y) = (x : Class.{u}) ∩ y :=
  ext fun _ => ZFSet.mem_inter

@[deprecated ZFClass.ofSet_sdiff (since := "2026-09-05")]
theorem coe_sdiff (x y : ZFSet.{u}) : ↑(x \ y) = (x : Class.{u}) \ y :=
  ext fun _ => ZFSet.mem_sdiff

@[deprecated (since := "2026-06-03")] alias coe_diff := coe_sdiff

@[deprecated ZFClass.ofSet_powerset (since := "2026-09-05")]
theorem coe_powerset (x : ZFSet.{u}) : ↑x.powerset = powerset.{u} x :=
  ext fun _ => ZFSet.mem_powerset

@[deprecated ZFClass.mem_powerset (since := "2026-09-05")]
theorem powerset_apply {A : Class.{u}} {x : ZFSet.{u}} : powerset A x ↔ ↑x ⊆ A :=
  Iff.rfl

@[deprecated ZFClass.mem_sUnion (since := "2026-09-05")]
theorem sUnion_apply {x : Class} {y : ZFSet} : (⋃₀ x) y ↔ ∃ z : ZFSet, x z ∧ y ∈ z := by
  constructor
  · rintro ⟨-, ⟨z, rfl, hxz⟩, hyz⟩
    exact ⟨z, hxz, hyz⟩
  · exact fun ⟨z, hxz, hyz⟩ => ⟨_, coe_mem.2 hxz, hyz⟩

open scoped ZFSet in
@[deprecated ZFClass.ofSet_sUnion (since := "2026-09-05")]
theorem coe_sUnion (x : ZFSet.{u}) : ↑(⋃₀ x : ZFSet) = ⋃₀ (x : Class.{u}) :=
  ext fun y =>
    ZFSet.mem_sUnion.trans (sUnion_apply.trans <| by rfl).symm

@[deprecated ZFClass.cmem_sUnion (since := "2026-09-05")]
theorem mem_sUnion {x y : Class.{u}} : y ∈ ⋃₀ x ↔ ∃ z, z ∈ x ∧ y ∈ z := by
  constructor
  · rintro ⟨w, rfl, z, hzx, hwz⟩
    exact ⟨z, hzx, coe_mem.2 hwz⟩
  · rintro ⟨w, hwx, z, rfl, hwz⟩
    exact ⟨z, rfl, w, hwx, hwz⟩

@[deprecated ZFClass.mem_sInter (since := "2026-09-05")]
theorem sInter_apply {x : Class.{u}} {y : ZFSet.{u}} : (⋂₀ x) y ↔ ∀ z : ZFSet.{u}, x z → y ∈ z := by
  refine ⟨fun hxy z hxz => hxy _ ⟨z, rfl, hxz⟩, ?_⟩
  rintro H - ⟨z, rfl, hxz⟩
  exact H _ hxz

open scoped ZFSet in
@[deprecated ZFClass.ofSet_sInter (since := "2026-09-05")]
theorem coe_sInter {x : ZFSet.{u}} (h : x.Nonempty) : ↑(⋂₀ x : ZFSet) = ⋂₀ (x : Class.{u}) :=
  Set.ext fun _ => (ZFSet.mem_sInter h).trans sInter_apply.symm

@[deprecated ZFClass.cmem_of_cmem_sInter (since := "2026-09-05")]
theorem mem_of_mem_sInter {x y z : Class} (hy : y ∈ ⋂₀ x) (hz : z ∈ x) : y ∈ z := by
  obtain ⟨w, rfl, hw⟩ := hy
  exact coe_mem.2 (hw z hz)

@[deprecated ZFClass.cmem_sInter (since := "2026-09-05")]
theorem mem_sInter {x y : Class.{u}} (h : x.Nonempty) : y ∈ ⋂₀ x ↔ ∀ z, z ∈ x → y ∈ z := by
  refine ⟨fun hy z => mem_of_mem_sInter hy, fun H => ?_⟩
  simp_rw [mem_def, sInter_apply]
  obtain ⟨z, hz⟩ := h
  obtain ⟨y, rfl, _⟩ := H z (coe_mem.2 hz)
  refine ⟨y, rfl, fun w hxw => ?_⟩
  simpa only [coe_mem, coe_apply] using H w (coe_mem.2 hxw)

@[deprecated ZFClass.sUnion_empty (since := "2026-09-05")]
theorem sUnion_empty : ⋃₀ (∅ : Class.{u}) = (∅ : Class.{u}) := by
  ext
  simp

@[deprecated ZFClass.sInter_empty (since := "2026-09-05")]
theorem sInter_empty : ⋂₀ (∅ : Class.{u}) = univ := by
  simp [univ]

/-- An induction principle for sets. If every subset of a class is a member, then the class is
  universal. -/
@[deprecated ZFClass.eq_univ_of_powerset_subset (since := "2026-09-05")]
theorem eq_univ_of_powerset_subset {A : Class} (hA : powerset A ⊆ A) : A = univ :=
  eq_univ_of_forall
    (by
      by_contra! hnA
      exact
        WellFounded.min_mem ZFSet.mem_wf _ hnA
          (hA fun x hx =>
            Classical.not_not.1 fun hB =>
              WellFounded.not_lt_min ZFSet.mem_wf _ hB <| coe_apply.1 hx))

/-- The definite description operator, which is `{x}` if `{y | A y} = {x}` and `∅` otherwise. -/
@[deprecated ZFClass.iota (since := "2026-09-05")]
def iota (A : Class) : Class :=
  ⋃₀ ({ x | ∀ y, A y ↔ y = x } : Class)

@[deprecated ZFClass.iota_val (since := "2026-09-05")]
theorem iota_val (A : Class) (x : ZFSet) (H : ∀ y, A y ↔ y = x) : iota A = ↑x :=
  ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by rwa [← (H x').1 <| (h x').2 rfl], fun yx =>
      ⟨_, ⟨x, rfl, H⟩, yx⟩⟩

/-- Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `Class → Set` function. -/
@[deprecated ZFClass.iota_ex (since := "2026-09-05")]
theorem iota_ex (A) : iota.{u} A ∈ univ.{u} :=
  mem_univ.2 <|
    Or.elim (Classical.em <| ∃ x, ∀ y, A y ↔ y = x) (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val A x h⟩)
      fun hn =>
      ⟨∅, ext fun _ => coe_empty.symm ▸ ⟨False.rec, fun ⟨_, ⟨x, rfl, H⟩, _⟩ => hn ⟨x, H⟩⟩⟩

/-- Function value -/
@[deprecated ZFClass.fval (since := "2026-09-05")]
def fval (F A : Class.{u}) : Class.{u} :=
  iota fun y => ToSet (fun x => F (ZFSet.pair x y)) A

@[deprecated ZFClass.fval_ex (since := "2026-09-05")]
theorem fval_ex (F A : Class.{u}) : F.fval A ∈ univ.{u} :=
  iota_ex _

end Class

open scoped ZFClass

namespace ZFSet

variable {x y : ZFSet.{u}}

@[simp]
lemma map_fval {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f] (h : y ∈ x) :
    (ZFSet.map f x ′ y : ZFClass.{u}) = f y :=
  ZFClass.iota_val _ _ fun z => by
    simp only [ZFClass.ofSet_cmem, Set.mem_ofPred_eq, ZFClass.mem_ofSet, mem_map]
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

lemma choice_mem_aux (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y ∈ x) :
    (Classical.epsilon fun z : ZFSet.{u} => z ∈ y) ∈ y :=
  (@Classical.epsilon_spec _ fun z : ZFSet.{u} => z ∈ y) <|
    by_contradiction fun n => h <| by rwa [← (eq_empty y).2 fun z zx => n ⟨z, zx⟩]

lemma choice_isFunc (h : ∅ ∉ x) : IsFunc x (⋃₀ x) (choice x) :=
  (@map_isFunc _ (Classical.allZFSetDefinable _) _ _).2 fun y yx =>
    mem_sUnion.2 ⟨y, yx, choice_mem_aux x h y yx⟩

lemma choice_cmem (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y ∈ x) : choice x ′ y ∈ᶜ y := by
  delta choice
  rw [@map_fval x y _ (Classical.allZFSetDefinable _) yx, ZFClass.ofSet_cmem, ZFClass.mem_ofSet]
  exact choice_mem_aux x h y yx

private lemma ofSet_equiv_aux {s : Set ZFSet.{u}} (hs : Small.{u} s) :
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
    fun s ↦ Subtype.coe_injective <| ofSet_equiv_aux s.2
  right_inv s := private Subtype.coe_injective <| ofSet_equiv_aux s.2

/-- The **Burali-Forti paradox**: ordinals form a proper class. -/
lemma isOrdinal_notCMem_univ : {x | IsOrdinal x} ∉ᶜ (.univ : ZFClass.{u}) := by
  rintro ⟨x, hx, -⟩
  suffices IsOrdinal x by
    apply ZFClass.cmem_irrefl (A := (x : ZFClass.{u}))
    rwa [ZFClass.ofSet_cmem, hx, Set.mem_ofPred_eq]
  refine ⟨fun y hy z hz ↦ ?_, fun hyz hzw hwx ↦ ?_⟩ <;>
    rw [← ZFClass.mem_ofSet, hx, Set.mem_ofPred_eq] at *
  exacts [hy.mem hz, hwx.mem_trans hyz hzw]

end ZFSet
