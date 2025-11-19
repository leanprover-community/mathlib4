/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.OmegaCompletePartialOrder

/-! # Saturation of a submonoid

For a submonoid `s` of a commutative monoid `M`, we construct the saturation of `s`, which is
`{x : M | ∃ y : M, x * y ∈ s}`, called `Submonoid.saturation s`.

It is used in the context of localisations.

We also define the type of saturated submonoids, and endows on it the structure of a complete
lattice, when the underlying type is a commutative monoid.

## Main Definitions

* `Submonoid.IsSaturated`: the condition `x * y ∈ s ↔ x ∈ s ∧ y ∈ s`. Not to be confused with
  `AddSubgroup.Saturated`.
* `SaturatedSubmonoid`: the type of `Submonoid` satisfying `IsSaturated`. It is a complete lattice.
* `Submonoid.Saturation`: the smallest saturated submonoid containing a given submonoid.

-/

namespace Submonoid

/-- A saturated submonoid is `s` that satisfies `x * y ∈ s ↔ x ∈ s ∧ y ∈ s`.

Not to be confused with `AddSubgroup.Saturated`. -/
def IsSaturated {M : Type*} [MulOneClass M] (s : Submonoid M) : Prop :=
  ∀ ⦃x y⦄, x * y ∈ s → x ∈ s ∧ y ∈ s

namespace IsSaturated
variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.IsSaturated) (h₁ : s₁.IsSaturated) (h₂ : s₂.IsSaturated)

include h in
theorem mul_mem_iff {x y : M} : x * y ∈ s ↔ x ∈ s ∧ y ∈ s :=
  ⟨@h _ _, and_imp.mpr mul_mem⟩

theorem top : IsSaturated (⊤ : Submonoid M) := fun _ _ _ ↦ ⟨trivial, trivial⟩

include h₁ h₂ in
theorem inf : IsSaturated (s₁ ⊓ s₂) :=
  fun _ _ hxy ↦ ⟨⟨(h₁ hxy.1).1, (h₂ hxy.2).1⟩, (h₁ hxy.1).2, (h₂ hxy.2).2⟩

theorem sInf {f : Set (Submonoid M)} (hf : ∀ s ∈ f, s.IsSaturated) :
    (sInf f).IsSaturated := fun _ _ hxy ↦ by
  simp_rw [mem_sInf] at hxy ⊢
  exact ⟨fun s hs ↦ (hf s hs <| hxy s hs).1, fun s hs ↦ (hf s hs <| hxy s hs).2⟩

theorem iInf {ι : Sort*} {f : ι → Submonoid M} (hf : ∀ i, (f i).IsSaturated) :
    (iInf f).IsSaturated :=
  sInf <| Set.forall_mem_range.mpr hf

/-- If `M` is commutative, we only need to check the left condition `x ∈ s`. -/
theorem of_left {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → x ∈ s) : s.IsSaturated :=
  fun x y hxy ↦ ⟨h hxy, h <| mul_comm x y ▸ hxy⟩

/-- If `M` is commutative, we only need to check the right condition `y ∈ s`. -/
theorem of_right {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → y ∈ s) : s.IsSaturated :=
  of_left fun x y ↦ mul_comm x y ▸ @h y x

end IsSaturated

end Submonoid

/-- A saturated submonoid is a submonoid `s` that satisfies `x * y ∈ s ↔ x ∈ s ∧ y ∈ s`. -/
structure SaturatedSubmonoid (M : Type*) [MulOneClass M] extends Submonoid M where
  isSaturated : toSubmonoid.IsSaturated

namespace SaturatedSubmonoid
variable {M : Type*} [MulOneClass M]

attribute [simp] isSaturated

theorem toSubmonoid_injective : (toSubmonoid (M := M)).Injective :=
  fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ eq ↦ by congr

@[ext] lemma ext {s₁ s₂ : SaturatedSubmonoid M} (h : s₁.toSubmonoid = s₂.toSubmonoid) : s₁ = s₂ :=
  toSubmonoid_injective h

variable (M) in
instance instSetLike : SetLike (SaturatedSubmonoid M) M where
  coe := (·.carrier)
  coe_injective' _ _ h := toSubmonoid_injective <| SetLike.coe_injective h

lemma ext' {s₁ s₂ : SaturatedSubmonoid M} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
  SetLike.ext h

variable (M) in
instance instSubmonoidClass : SubmonoidClass (SaturatedSubmonoid M) M where
  mul_mem {s} := s.mul_mem
  one_mem {s} := s.one_mem

@[simp] lemma mem_toSubmonoid {s : SaturatedSubmonoid M} {x : M} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

instance : Top (SaturatedSubmonoid M) where
  top := { (⊤ : Submonoid M) with isSaturated := .top }

@[simp]
theorem mem_top {x : M} : x ∈ (⊤ : SaturatedSubmonoid M) := trivial

variable (M) in
instance : Min (SaturatedSubmonoid M) where
  min s₁ s₂ := { s₁.toSubmonoid ⊓ s₂.toSubmonoid with isSaturated := .inf s₁.2 s₂.2 }

variable (M) in
instance : InfSet (SaturatedSubmonoid M) where
  sInf f :=
  { carrier := ⋂ s ∈ f, s
    mul_mem' hx hy := by rw [Set.mem_iInter₂] at *; exact fun s hs ↦ mul_mem (hx s hs) (hy s hs)
    one_mem' := Set.mem_iInter₂.mpr fun _ _ ↦ one_mem _
    isSaturated := by
      convert Submonoid.IsSaturated.sInf (f := toSubmonoid '' f) (by simp)
      ext; simp [Submonoid.mem_sInf] }

theorem mem_sInf {f : Set (SaturatedSubmonoid M)} {x : M} : x ∈ sInf f ↔ ∀ s ∈ f, x ∈ s :=
  Set.mem_iInter₂

variable (M) in
instance : CompleteSemilatticeInf (SaturatedSubmonoid M) where
  sInf_le f s hs x hx := mem_sInf.1 hx s hs
  le_sInf f s ih x hx := mem_sInf.2 <| by tauto

/-- The smallest saturated submonoid is that of invertible elements. -/
instance (M : Type*) [CommMonoid M] : Bot (SaturatedSubmonoid M) where
  bot :=
  { carrier := {x | IsUnit x}
    mul_mem' := IsUnit.mul
    one_mem' := isUnit_one
    isSaturated _ _ h := ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩ }

instance (M : Type*) [CommMonoid M] : OrderBot (SaturatedSubmonoid M) where
  bot_le s _ hx := let ⟨_, hy⟩ := hx.exists_right_inv; (s.2 <| hy ▸ one_mem _).1

@[simp]
theorem mem_bot {M : Type*} [CommMonoid M] {x : M} : x ∈ (⊥ : SaturatedSubmonoid M) ↔ IsUnit x :=
  Iff.rfl

end SaturatedSubmonoid

namespace Submonoid

/-- The saturation of a submonoid `s` is a saturated submonoid, defined to be
`{x : M | ∃ y : M, x * y ∈ s}`. -/
def saturation {M : Type*} [CommMonoid M] (s : Submonoid M) : SaturatedSubmonoid M where
  carrier := {x | ∃ y, x * y ∈ s}
  mul_mem' := fun ⟨y₁, h₁⟩ ⟨y₂, h₂⟩ ↦ ⟨y₁ * y₂, by rw [mul_mul_mul_comm]; exact mul_mem h₁ h₂⟩
  one_mem' := ⟨1, by rw [one_mul]; exact one_mem _⟩
  isSaturated := .of_left fun _ z ⟨y, h⟩ ↦ ⟨z * y, by rwa [← mul_assoc]⟩

variable {M : Type*} [CommMonoid M]

section
variable {s : Submonoid M} {x : M}

theorem mem_saturation_iff : x ∈ s.saturation ↔ ∃ y, x * y ∈ s := Iff.rfl

theorem mem_saturation_iff' : x ∈ s.saturation ↔ ∃ y, y * x ∈ s := by
  simp_rw [mem_saturation_iff, mul_comm x]

theorem mem_saturation_iff_exists_dvd : x ∈ s.saturation ↔ ∃ m ∈ s, x ∣ m := by
  simp_rw [dvd_def, existsAndEq, and_true, mem_saturation_iff]

end

variable (M) in
theorem gc_saturation : GaloisConnection (saturation (M := M)) (·.toSubmonoid) :=
  fun a b ↦ ⟨fun ih x hx ↦ ih ⟨1, by rwa [mul_one]⟩, fun ih x ⟨y, h⟩ ↦ (b.2 <| ih h).1⟩

variable (M) in
/-- `saturation` forms a `GaloisInsertion` with the forgetful functor
`SaturatedSubmonoid.toSubmonoid`. -/
def giSaturation : GaloisInsertion (saturation (M := M)) (·.toSubmonoid) where
  choice s hs := { s with isSaturated := .of_left fun _ y hxy ↦ hs ⟨y, hxy⟩ }
  gc := gc_saturation M
  le_l_u s := (gc_saturation M).le_u_l s.toSubmonoid
  choice_eq s h := le_antisymm ((gc_saturation M).le_u_l s) h

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

theorem saturation_le_iff_le : a.saturation ≤ b ↔ a ≤ b.toSubmonoid := gc_saturation ..
alias ⟨_, saturation_le_of_le⟩ := saturation_le_iff_le

theorem le_toSubmonoid_saturation : a ≤ a.saturation.toSubmonoid := (gc_saturation M).le_u_l a

@[simp]
theorem saturation_toSubmonoid : b.saturation = b := (giSaturation M).l_u_eq b

end Submonoid

namespace SaturatedSubmonoid

instance instCompleteLattice (M : Type*) [CommMonoid M] :
    CompleteLattice (SaturatedSubmonoid M) :=
  { inferInstanceAs (PartialOrder (SaturatedSubmonoid M)),
    inferInstanceAs (OrderBot (SaturatedSubmonoid M)),
    inferInstanceAs (Top (SaturatedSubmonoid M)),
    inferInstanceAs (Min (SaturatedSubmonoid M)),
    inferInstanceAs (CompleteSemilatticeInf (SaturatedSubmonoid M)),
    (Submonoid.giSaturation M).liftCompleteLattice with }

variable {M : Type*} [CommMonoid M]

theorem sup_def {s₁ s₂ : SaturatedSubmonoid M} :
    s₁ ⊔ s₂ = (s₁.toSubmonoid ⊔ s₂.toSubmonoid).saturation := rfl

theorem sSup_def {f : Set (SaturatedSubmonoid M)} :
    sSup f = (sSup (toSubmonoid '' f)).saturation := rfl

theorem iSup_def {ι : Sort*} {f : ι → SaturatedSubmonoid M} :
    iSup f = (⨆ i, (f i).toSubmonoid).saturation :=
  (Submonoid.giSaturation M).l_iSup_u f |>.symm

end SaturatedSubmonoid

namespace Submonoid
variable {M : Type*} [CommMonoid M]

@[simp] theorem saturation_bot : (⊥ : Submonoid M).saturation = ⊥ := (gc_saturation M).l_bot
@[simp] theorem saturation_top : (⊤ : Submonoid M).saturation = ⊤ := (giSaturation M).l_top

@[simp] theorem saturation_sup {s₁ s₂ : Submonoid M} :
    (s₁ ⊔ s₂).saturation = s₁.saturation ⊔ s₂.saturation := (gc_saturation M).l_sup

-- note that it does not preserve inf:
-- if s₁ = {6 ^ n | n : ℕ} and s₂ = {15 ^ n | n : ℕ} then
-- (s₁ ⊓ s₂).saturation = {1} and
-- s₁.saturation ⊓ s₂.saturation = {3 ^ n | n : ℕ}

@[simp] theorem saturation_sSup {f : Set (Submonoid M)} :
    (sSup f).saturation = ⨆ s ∈ f, s.saturation := (gc_saturation M).l_sSup

@[simp] theorem saturation_iSup {ι : Sort*} {f : ι → Submonoid M} :
    (iSup f).saturation = ⨆ i, (f i).saturation := (gc_saturation M).l_iSup

end Submonoid
