/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.OmegaCompletePartialOrder

/-! # Saturation of a submonoid

We define a submonoid `s` to be saturated if `x * y ∈ s → x ∈ s ∧ y ∈ s`. The type of all
saturated submonoids forms a complete lattice. For a given submonoid `s` we construct the saturation
of `s` as the smallest saturated submonoid containing `s`, which when the underlying type is a
commutative monoid, is given by the formula `{x : M | ∃ y : M, x * y ∈ s}`.

Saturated submonoids are used in the context of localisations.

We also define the type of saturated submonoids, and endow on it the structure of a complete
lattice.

## Main Definitions

* `Submonoid.MulSaturated`: the condition `x * y ∈ s ↔ x ∈ s ∧ y ∈ s`. Not to be confused with
  `Submonoid.PowSaturated`.
* `SaturatedSubmonoid`: the type of `Submonoid` satisfying `MulSaturated`. It is a complete lattice.
* `Submonoid.saturation`: the smallest saturated submonoid containing a given submonoid.

-/

@[expose] public section

namespace Submonoid

/-- Given a submonoid `s` of `M`, we say that `s` is **saturated** if it satisfies
`x * y ∈ s → x ∈ s ∧ y ∈ s`.

It is called `MulSaturated` here to be distinguished from `Submonoid.PowSaturated` or
`AddSubmonoid.NSMulSaturated`, which is also called "saturated" in the literature. -/
@[to_additive
/-- Given an additive submonoid `s` of `M`, we say that `s` is **saturated** if it satisfies
`x + y ∈ s → x ∈ s ∧ y ∈ s`.

It is called `AddSaturated` here to be distinguished from `Submonoid.PowSaturated` or
`AddSubmonoid.NSMulSaturated`, which is also called "saturated" in the literature. -/]
def MulSaturated {M : Type*} [MulOneClass M] (s : Submonoid M) : Prop :=
  ∀ ⦃x y⦄, x * y ∈ s → x ∈ s ∧ y ∈ s

namespace MulSaturated
variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

include h in
@[to_additive]
theorem mul_mem_iff {x y : M} : x * y ∈ s ↔ x ∈ s ∧ y ∈ s :=
  ⟨@h _ _, and_imp.mpr mul_mem⟩

@[to_additive]
theorem top : MulSaturated (⊤ : Submonoid M) := fun _ _ _ ↦ ⟨trivial, trivial⟩

include h₁ h₂ in
@[to_additive]
theorem inf : MulSaturated (s₁ ⊓ s₂) :=
  fun _ _ hxy ↦ ⟨⟨(h₁ hxy.1).1, (h₂ hxy.2).1⟩, (h₁ hxy.1).2, (h₂ hxy.2).2⟩

@[to_additive]
theorem sInf {f : Set (Submonoid M)} (hf : ∀ s ∈ f, s.MulSaturated) :
    (sInf f).MulSaturated := fun _ _ hxy ↦ by
  simp_rw [mem_sInf] at hxy ⊢
  exact ⟨fun s hs ↦ (hf s hs <| hxy s hs).1, fun s hs ↦ (hf s hs <| hxy s hs).2⟩

@[to_additive]
theorem iInf {ι : Sort*} {f : ι → Submonoid M} (hf : ∀ i, (f i).MulSaturated) :
    (iInf f).MulSaturated :=
  sInf <| Set.forall_mem_range.mpr hf

/-- If `M` is commutative, we only need to check the left condition `x ∈ s`. -/
@[to_additive /-- If `M` is commutative, we only need to check the left condition `x ∈ s`. -/]
theorem of_left {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → x ∈ s) : s.MulSaturated :=
  fun x y hxy ↦ ⟨h hxy, h <| mul_comm x y ▸ hxy⟩

/-- If `M` is commutative, we only need to check the right condition `y ∈ s`. -/
@[to_additive /-- If `M` is commutative, we only need to check the right condition `y ∈ s`. -/]
theorem of_right {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → y ∈ s) : s.MulSaturated :=
  of_left fun x y ↦ mul_comm x y ▸ @h y x

end MulSaturated

end Submonoid

-- automatic generation failed
/-- A saturated additive submonoid is a submonoid `s` that satisfies `x + y ∈ s → x ∈ s ∧ y ∈ s`. -/
structure SaturatedAddSubmonoid (M : Type*) [AddZeroClass M] extends AddSubmonoid M where
  addSaturated : toAddSubmonoid.AddSaturated

/-- A saturated submonoid is a submonoid `s` that satisfies `x * y ∈ s → x ∈ s ∧ y ∈ s`. -/
@[to_additive] structure SaturatedSubmonoid (M : Type*) [MulOneClass M] extends Submonoid M where
  mulSaturated : toSubmonoid.MulSaturated

namespace SaturatedSubmonoid
variable {M : Type*} [MulOneClass M]

attribute [simp] mulSaturated SaturatedAddSubmonoid.addSaturated

@[to_additive]
theorem toSubmonoid_injective : (toSubmonoid (M := M)).Injective :=
  fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ eq ↦ by congr

@[to_additive (attr := ext)]
lemma ext {s₁ s₂ : SaturatedSubmonoid M} (h : s₁.toSubmonoid = s₂.toSubmonoid) : s₁ = s₂ :=
  toSubmonoid_injective h

variable (M) in
@[to_additive]
instance : SetLike (SaturatedSubmonoid M) M where
  coe := (·.carrier)
  coe_injective' _ _ h := toSubmonoid_injective <| SetLike.coe_injective h

@[to_additive]
instance : PartialOrder (SaturatedSubmonoid M) := .ofSetLike ..

@[to_additive]
lemma ext' {s₁ s₂ : SaturatedSubmonoid M} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
  SetLike.ext h

variable (M) in
@[to_additive]
instance : SubmonoidClass (SaturatedSubmonoid M) M where
  mul_mem {s} := s.mul_mem
  one_mem {s} := s.one_mem

@[to_additive (attr := simp)]
lemma mem_toSubmonoid {s : SaturatedSubmonoid M} {x : M} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[to_additive]
instance : Top (SaturatedSubmonoid M) where
  top := { (⊤ : Submonoid M) with mulSaturated := .top }

@[to_additive (attr := simp)]
theorem mem_top {x : M} : x ∈ (⊤ : SaturatedSubmonoid M) := trivial

variable (M) in
@[to_additive]
instance : Min (SaturatedSubmonoid M) where
  min s₁ s₂ := { s₁.toSubmonoid ⊓ s₂.toSubmonoid with mulSaturated := .inf s₁.2 s₂.2 }

variable (M) in
@[to_additive]
instance : InfSet (SaturatedSubmonoid M) where
  sInf f :=
  { carrier := ⋂ s ∈ f, s
    mul_mem' hx hy := by rw [Set.mem_iInter₂] at *; exact fun s hs ↦ mul_mem (hx s hs) (hy s hs)
    one_mem' := Set.mem_iInter₂.mpr fun _ _ ↦ one_mem _
    mulSaturated := by
      convert Submonoid.MulSaturated.sInf (f := toSubmonoid '' f) (by simp)
      ext; simp [Submonoid.mem_sInf] }

@[to_additive]
theorem mem_sInf {f : Set (SaturatedSubmonoid M)} {x : M} : x ∈ sInf f ↔ ∀ s ∈ f, x ∈ s :=
  Set.mem_iInter₂

variable (M) in
@[to_additive]
instance : CompleteSemilatticeInf (SaturatedSubmonoid M) where
  isGLB_sInf _ := .of_image SetLike.coe_subset_coe isGLB_biInf

end SaturatedSubmonoid

namespace Submonoid

/-- The saturation of a submonoid `s` is the intersection of all saturated submonoids that contain
`s`.

If `M` is a commutative monoid, then this is `{x : M | ∃ y : M, x * y ∈ s}`. -/
@[to_additive
/-- The saturation of an additive submonoid `s` is the intersection of all saturated submonoids
that contain `s`.

If `M` is a commutative additive monoid, then this is `{x : M | ∃ y : M, x + y ∈ s}`. -/]
def saturation {M : Type*} [MulOneClass M] (s : Submonoid M) : SaturatedSubmonoid M :=
  sInf {t | s ≤ t.toSubmonoid}

variable {M : Type*}

section MulOneClass
variable [MulOneClass M]

variable (M) in
@[to_additive]
theorem gc_saturation : GaloisConnection (saturation (M := M)) (·.toSubmonoid) := fun _ _ ↦
  ⟨fun ih _ hx ↦ ih <| SaturatedSubmonoid.mem_sInf.mpr fun _ ht ↦ ht hx,
  fun ih _ hx ↦ SaturatedSubmonoid.mem_sInf.mp hx _ ih⟩

variable (M) in
/-- `saturation` forms a `GaloisInsertion` with the forgetful functor
`SaturatedSubmonoid.toSubmonoid`. -/
@[to_additive
/-- `saturation` forms a `GaloisInsertion` with the forgetful functor
`SaturatedAddSubmonoid.toAddSubmonoid`. -/]
def giSaturation : GaloisInsertion (saturation (M := M)) (·.toSubmonoid) where
  choice s hs := { s with mulSaturated := le_antisymm ((gc_saturation M).le_u_l s) hs ▸ by simp }
  gc := gc_saturation M
  le_l_u s := (gc_saturation M).le_u_l s.toSubmonoid
  choice_eq s h := le_antisymm ((gc_saturation M).le_u_l s) h

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

@[to_additive]
theorem saturation_le_iff_le : a.saturation ≤ b ↔ a ≤ b.toSubmonoid := gc_saturation ..

@[to_additive]
alias ⟨_, saturation_le_of_le⟩ := saturation_le_iff_le

@[to_additive]
theorem le_toSubmonoid_saturation : a ≤ a.saturation.toSubmonoid := (gc_saturation M).le_u_l a

@[to_additive (attr := simp)]
theorem saturation_toSubmonoid : b.saturation = b := (giSaturation M).l_u_eq b

@[to_additive (attr := elab_as_elim)]
theorem saturation_induction {s : Submonoid M}
    {p : (x : M) → x ∈ s.saturation → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (le_toSubmonoid_saturation hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (of_mul : ∀ (x y) (hxy : x * y ∈ s.saturation),
      p (x * y) hxy → p x (s.saturation.2 hxy).1 ∧ p y (s.saturation.2 hxy).2)
    {x : M} (hx : x ∈ s.saturation) : p x hx := by
  let s' : SaturatedSubmonoid M :=
  { carrier := { x | ∃ hx, p x hx }
    one_mem' := ⟨_ , mem 1 <| one_mem s⟩
    mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩
    mulSaturated := fun x y ⟨_, hpxy⟩ ↦ ⟨⟨_, (of_mul _ _ _ hpxy).1⟩, ⟨_, (of_mul _ _ _ hpxy).2⟩⟩ }
  exact SaturatedSubmonoid.mem_sInf.mp hx s' (fun _ h ↦ ⟨_, mem _ h⟩) |>.2

end MulOneClass

section CommMonoid
variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

@[to_additive]
theorem mem_saturation_iff : x ∈ s.saturation ↔ ∃ y, x * y ∈ s := by
  refine ⟨fun h ↦ ?_, fun ⟨y, hxy⟩ ↦ (s.saturation.2 <| le_toSubmonoid_saturation hxy).1⟩
  induction h using saturation_induction with
  | mem _ hx => exact ⟨1, by simpa⟩
  | mul _ _ _ _ ih₁ ih₂ =>
    exact ih₁.elim fun y₁ h₁ ↦ ih₂.elim fun y₂ h₂ ↦
      ⟨y₁ * y₂, by rw [mul_mul_mul_comm]; exact mul_mem h₁ h₂⟩
  | of_mul x₁ x₂ _ ih =>
    exact ih.elim fun y h ↦ ⟨⟨x₂ * y, by rwa [← mul_assoc]⟩,
      ⟨x₁ * y, by rwa [mul_left_comm, ← mul_assoc]⟩⟩

@[to_additive]
theorem mem_saturation_iff' : x ∈ s.saturation ↔ ∃ y, y * x ∈ s := by
  simp_rw [mem_saturation_iff, mul_comm x]

theorem mem_saturation_iff_exists_dvd : x ∈ s.saturation ↔ ∃ m ∈ s, x ∣ m := by
  simp_rw [dvd_def, existsAndEq, and_true, mem_saturation_iff]

end CommMonoid

end Submonoid

namespace SaturatedSubmonoid

@[to_additive]
instance (M : Type*) [MulOneClass M] :
    CompleteLattice (SaturatedSubmonoid M) :=
  { (inferInstance : PartialOrder (SaturatedSubmonoid M)),
    (inferInstance : Top (SaturatedSubmonoid M)),
    (inferInstance : Min (SaturatedSubmonoid M)),
    (inferInstance : CompleteSemilatticeInf (SaturatedSubmonoid M)),
    (Submonoid.giSaturation M).liftCompleteLattice with }

variable {M : Type*}

section MulOneClass
variable [MulOneClass M]

@[to_additive]
theorem bot_def : (⊥ : SaturatedSubmonoid M) = Submonoid.saturation ⊥ := rfl

@[to_additive]
theorem sup_def {s₁ s₂ : SaturatedSubmonoid M} :
    s₁ ⊔ s₂ = (s₁.toSubmonoid ⊔ s₂.toSubmonoid).saturation := rfl

@[to_additive]
theorem sSup_def {f : Set (SaturatedSubmonoid M)} :
    sSup f = (sSup (toSubmonoid '' f)).saturation := rfl

@[to_additive]
theorem iSup_def {ι : Sort*} {f : ι → SaturatedSubmonoid M} :
    iSup f = (⨆ i, (f i).toSubmonoid).saturation :=
  (Submonoid.giSaturation M).l_iSup_u f |>.symm

end MulOneClass

section CommMonoid
variable [CommMonoid M]

@[to_additive]
theorem mem_bot_iff {x : M} : x ∈ (⊥ : SaturatedSubmonoid M) ↔ IsUnit x := by
  simp_rw [bot_def, Submonoid.mem_saturation_iff, Submonoid.mem_bot, isUnit_iff_exists_inv]

end CommMonoid

end SaturatedSubmonoid

namespace Submonoid
variable {M : Type*} [MulOneClass M]

@[to_additive (attr := simp)]
theorem saturation_bot : (⊥ : Submonoid M).saturation = ⊥ := (gc_saturation M).l_bot

@[to_additive (attr := simp)]
theorem saturation_top : (⊤ : Submonoid M).saturation = ⊤ := (giSaturation M).l_top

@[to_additive (attr := simp)]
theorem saturation_sup {s₁ s₂ : Submonoid M} :
    (s₁ ⊔ s₂).saturation = s₁.saturation ⊔ s₂.saturation := (gc_saturation M).l_sup

-- note that it does not preserve inf:
-- if s₁ = {6 ^ n | n : ℕ} and s₂ = {15 ^ n | n : ℕ} then
-- (s₁ ⊓ s₂).saturation = {1} and
-- s₁.saturation ⊓ s₂.saturation = {3 ^ n | n : ℕ}

@[to_additive (attr := simp)]
theorem saturation_sSup {f : Set (Submonoid M)} :
    (sSup f).saturation = ⨆ s ∈ f, s.saturation := (gc_saturation M).l_sSup

@[to_additive (attr := simp)]
theorem saturation_iSup {ι : Sort*} {f : ι → Submonoid M} :
    (iSup f).saturation = ⨆ i, (f i).saturation := (gc_saturation M).l_iSup

end Submonoid
