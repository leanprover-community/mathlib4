/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Rowett, Kim Morrison, Johan Commelin, Mario Carneiro,
  Michael Howes
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Deprecated.Submonoid

/-!
# Unbundled subgroups (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines unbundled multiplicative and additive subgroups. Instead of using this file,
please use `Subgroup G` and `AddSubgroup A`, defined in `Mathlib.Algebra.Group.Subgroup.Basic`.

## Main definitions

`IsAddSubgroup (S : Set A)` : the predicate that `S` is the underlying subset of an additive
subgroup of `A`. The bundled variant `AddSubgroup A` should be used in preference to this.

`IsSubgroup (S : Set G)` : the predicate that `S` is the underlying subset of a subgroup
of `G`. The bundled variant `Subgroup G` should be used in preference to this.

## Tags

subgroup, subgroups, IsSubgroup
-/


open Set Function

variable {G : Type*} {H : Type*} {A : Type*} {a a₁ a₂ b c : G}

section Group

variable [Group G] [AddGroup A]

/-- `s` is an additive subgroup: a set containing 0 and closed under addition and negation. -/
structure IsAddSubgroup (s : Set A) extends IsAddSubmonoid s : Prop where
  /-- The proposition that `s` is closed under negation. -/
  neg_mem {a} : a ∈ s → -a ∈ s

/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
@[to_additive]
structure IsSubgroup (s : Set G) extends IsSubmonoid s : Prop where
  /-- The proposition that `s` is closed under inverse. -/
  inv_mem {a} : a ∈ s → a⁻¹ ∈ s

@[to_additive]
theorem IsSubgroup.div_mem {s : Set G} (hs : IsSubgroup s) {x y : G} (hx : x ∈ s) (hy : y ∈ s) :
    x / y ∈ s := by simpa only [div_eq_mul_inv] using hs.mul_mem hx (hs.inv_mem hy)

theorem Additive.isAddSubgroup {s : Set G} (hs : IsSubgroup s) : @IsAddSubgroup (Additive G) _ s :=
  @IsAddSubgroup.mk (Additive G) _ _ (Additive.isAddSubmonoid hs.toIsSubmonoid) hs.inv_mem

theorem Additive.isAddSubgroup_iff {s : Set G} : @IsAddSubgroup (Additive G) _ s ↔ IsSubgroup s :=
  ⟨by rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact @IsSubgroup.mk G _ _ ⟨h₁, @h₂⟩ @h₃, fun h =>
    Additive.isAddSubgroup h⟩

theorem Multiplicative.isSubgroup {s : Set A} (hs : IsAddSubgroup s) :
    @IsSubgroup (Multiplicative A) _ s :=
  @IsSubgroup.mk (Multiplicative A) _ _ (Multiplicative.isSubmonoid hs.toIsAddSubmonoid) hs.neg_mem

theorem Multiplicative.isSubgroup_iff {s : Set A} :
    @IsSubgroup (Multiplicative A) _ s ↔ IsAddSubgroup s :=
  ⟨by rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact @IsAddSubgroup.mk A _ _ ⟨h₁, @h₂⟩ @h₃, fun h =>
    Multiplicative.isSubgroup h⟩

@[to_additive of_add_neg]
theorem IsSubgroup.of_div (s : Set G) (one_mem : (1 : G) ∈ s)
    (div_mem : ∀ {a b : G}, a ∈ s → b ∈ s → a * b⁻¹ ∈ s) : IsSubgroup s :=
  have inv_mem : ∀ a, a ∈ s → a⁻¹ ∈ s := fun a ha => by
    have : 1 * a⁻¹ ∈ s := div_mem one_mem ha
    convert this using 1
    rw [one_mul]
  { inv_mem := inv_mem _
    mul_mem := fun {a b} ha hb => by
      have : a * b⁻¹⁻¹ ∈ s := div_mem ha (inv_mem b hb)
      convert this
      rw [inv_inv]
    one_mem }

theorem IsAddSubgroup.of_sub (s : Set A) (zero_mem : (0 : A) ∈ s)
    (sub_mem : ∀ {a b : A}, a ∈ s → b ∈ s → a - b ∈ s) : IsAddSubgroup s :=
  IsAddSubgroup.of_add_neg s zero_mem fun {x y} hx hy => by
    simpa only [sub_eq_add_neg] using sub_mem hx hy

@[to_additive]
theorem IsSubgroup.inter {s₁ s₂ : Set G} (hs₁ : IsSubgroup s₁) (hs₂ : IsSubgroup s₂) :
    IsSubgroup (s₁ ∩ s₂) :=
  { IsSubmonoid.inter hs₁.toIsSubmonoid hs₂.toIsSubmonoid with
    inv_mem := fun hx => ⟨hs₁.inv_mem hx.1, hs₂.inv_mem hx.2⟩ }

@[to_additive]
theorem IsSubgroup.iInter {ι : Sort*} {s : ι → Set G} (hs : ∀ y : ι, IsSubgroup (s y)) :
    IsSubgroup (Set.iInter s) :=
  { IsSubmonoid.iInter fun y => (hs y).toIsSubmonoid with
    inv_mem := fun h =>
      Set.mem_iInter.2 fun y => IsSubgroup.inv_mem (hs _) (Set.mem_iInter.1 h y) }

@[to_additive]
theorem isSubgroup_iUnion_of_directed {ι : Type*} [Nonempty ι] {s : ι → Set G}
    (hs : ∀ i, IsSubgroup (s i)) (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
    IsSubgroup (⋃ i, s i) :=
  { inv_mem := fun ha =>
      let ⟨i, hi⟩ := Set.mem_iUnion.1 ha
      Set.mem_iUnion.2 ⟨i, (hs i).inv_mem hi⟩
    toIsSubmonoid := isSubmonoid_iUnion_of_directed (fun i => (hs i).toIsSubmonoid) directed }

end Group

namespace IsSubgroup

open IsSubmonoid

variable [Group G] {s : Set G} (hs : IsSubgroup s)
include hs

@[to_additive]
theorem inv_mem_iff : a⁻¹ ∈ s ↔ a ∈ s :=
  ⟨fun h => by simpa using hs.inv_mem h, inv_mem hs⟩

@[to_additive]
theorem mul_mem_cancel_right (h : a ∈ s) : b * a ∈ s ↔ b ∈ s :=
  ⟨fun hba => by simpa using hs.mul_mem hba (hs.inv_mem h), fun hb => hs.mul_mem hb h⟩

@[to_additive]
theorem mul_mem_cancel_left (h : a ∈ s) : a * b ∈ s ↔ b ∈ s :=
  ⟨fun hab => by simpa using hs.mul_mem (hs.inv_mem h) hab, hs.mul_mem h⟩

end IsSubgroup

/-- `IsNormalAddSubgroup (s : Set A)` expresses the fact that `s` is a normal additive subgroup
of the additive group `A`. Important: the preferred way to say this in Lean is via bundled
subgroups `S : AddSubgroup A` and `hs : S.normal`, and not via this structure. -/
structure IsNormalAddSubgroup [AddGroup A] (s : Set A) extends IsAddSubgroup s : Prop where
  /-- The proposition that `s` is closed under (additive) conjugation. -/
  normal : ∀ n ∈ s, ∀ g : A, g + n + -g ∈ s

/-- `IsNormalSubgroup (s : Set G)` expresses the fact that `s` is a normal subgroup
of the group `G`. Important: the preferred way to say this in Lean is via bundled
subgroups `S : Subgroup G` and not via this structure. -/
@[to_additive]
structure IsNormalSubgroup [Group G] (s : Set G) extends IsSubgroup s : Prop where
  /-- The proposition that `s` is closed under conjugation. -/
  normal : ∀ n ∈ s, ∀ g : G, g * n * g⁻¹ ∈ s

@[to_additive]
theorem isNormalSubgroup_of_commGroup [CommGroup G] {s : Set G} (hs : IsSubgroup s) :
    IsNormalSubgroup s :=
  { hs with normal := fun n hn g => by rwa [mul_right_comm, mul_inv_cancel, one_mul] }

theorem Additive.isNormalAddSubgroup [Group G] {s : Set G} (hs : IsNormalSubgroup s) :
    @IsNormalAddSubgroup (Additive G) _ s :=
  @IsNormalAddSubgroup.mk (Additive G) _ _ (Additive.isAddSubgroup hs.toIsSubgroup)
    (@IsNormalSubgroup.normal _ ‹Group (Additive G)› _ hs)
    -- Porting note: Lean needs help synthesising

theorem Additive.isNormalAddSubgroup_iff [Group G] {s : Set G} :
    @IsNormalAddSubgroup (Additive G) _ s ↔ IsNormalSubgroup s :=
  ⟨by rintro ⟨h₁, h₂⟩; exact @IsNormalSubgroup.mk G _ _ (Additive.isAddSubgroup_iff.1 h₁) @h₂,
    fun h => Additive.isNormalAddSubgroup h⟩

theorem Multiplicative.isNormalSubgroup [AddGroup A] {s : Set A} (hs : IsNormalAddSubgroup s) :
    @IsNormalSubgroup (Multiplicative A) _ s :=
  @IsNormalSubgroup.mk (Multiplicative A) _ _ (Multiplicative.isSubgroup hs.toIsAddSubgroup)
    (@IsNormalAddSubgroup.normal _ ‹AddGroup (Multiplicative A)› _ hs)

theorem Multiplicative.isNormalSubgroup_iff [AddGroup A] {s : Set A} :
    @IsNormalSubgroup (Multiplicative A) _ s ↔ IsNormalAddSubgroup s :=
  ⟨by
    rintro ⟨h₁, h₂⟩
    exact @IsNormalAddSubgroup.mk A _ _ (Multiplicative.isSubgroup_iff.1 h₁) @h₂,
    fun h => Multiplicative.isNormalSubgroup h⟩

namespace IsSubgroup

variable [Group G]

-- Normal subgroup properties
@[to_additive]
theorem mem_norm_comm {s : Set G} (hs : IsNormalSubgroup s) {a b : G} (hab : a * b ∈ s) :
    b * a ∈ s := by
  simpa using (hs.normal (a * b) hab a⁻¹)

@[to_additive]
theorem mem_norm_comm_iff {s : Set G} (hs : IsNormalSubgroup s) {a b : G} : a * b ∈ s ↔ b * a ∈ s :=
  ⟨mem_norm_comm hs, mem_norm_comm hs⟩

/-- The trivial subgroup -/
@[to_additive "the trivial additive subgroup"]
def trivial (G : Type*) [Group G] : Set G :=
  {1}

@[to_additive (attr := simp)]
theorem mem_trivial {g : G} : g ∈ trivial G ↔ g = 1 :=
  mem_singleton_iff

@[to_additive]
theorem trivial_normal : IsNormalSubgroup (trivial G) := by refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> simp

@[to_additive]
theorem eq_trivial_iff {s : Set G} (hs : IsSubgroup s) : s = trivial G ↔ ∀ x ∈ s, x = (1 : G) := by
  simp only [Set.ext_iff, IsSubgroup.mem_trivial]
  exact ⟨fun h x => (h x).1, fun h x => ⟨h x, fun hx => hx.symm ▸ hs.toIsSubmonoid.one_mem⟩⟩

@[to_additive]
theorem univ_subgroup : IsNormalSubgroup (@univ G) := by refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> simp

/-- The underlying set of the center of a group. -/
@[to_additive addCenter "The underlying set of the center of an additive group."]
def center (G : Type*) [Group G] : Set G :=
  { z | ∀ g, g * z = z * g }

@[to_additive mem_add_center]
theorem mem_center {a : G} : a ∈ center G ↔ ∀ g, g * a = a * g :=
  Iff.rfl

@[to_additive add_center_normal]
theorem center_normal : IsNormalSubgroup (center G) :=
  { one_mem := by simp [center]
    mul_mem := fun ha hb g => by
      rw [← mul_assoc, mem_center.2 ha g, mul_assoc, mem_center.2 hb g, ← mul_assoc]
    inv_mem := fun {a} ha g =>
      calc
        g * a⁻¹ = a⁻¹ * (g * a) * a⁻¹ := by simp [ha g]
        _ = a⁻¹ * g := by rw [← mul_assoc, mul_assoc]; simp
    normal := fun n ha g h =>
      calc
        h * (g * n * g⁻¹) = h * n := by simp [ha g, mul_assoc]
        _ = g * g⁻¹ * n * h := by rw [ha h]; simp
        _ = g * n * g⁻¹ * h := by rw [mul_assoc g, ha g⁻¹, ← mul_assoc]
         }

/-- The underlying set of the normalizer of a subset `S : Set G` of a group `G`. That is,
  the elements `g : G` such that `g * S * g⁻¹ = S`. -/
@[to_additive addNormalizer
      "The underlying set of the normalizer of a subset `S : Set A` of an
      additive group `A`. That is, the elements `a : A` such that `a + S - a = S`."]
def normalizer (s : Set G) : Set G :=
  { g : G | ∀ n, n ∈ s ↔ g * n * g⁻¹ ∈ s }

@[to_additive]
theorem normalizer_isSubgroup (s : Set G) : IsSubgroup (normalizer s) :=
  { one_mem := by simp [normalizer]
    mul_mem := fun {a b}
      (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s) (hb : ∀ n, n ∈ s ↔ b * n * b⁻¹ ∈ s) n =>
      by rw [mul_inv_rev, ← mul_assoc, mul_assoc a, mul_assoc a, ← ha, ← hb]
    inv_mem := fun {a} (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s) n => by
      rw [ha (a⁻¹ * n * a⁻¹⁻¹)]; simp [mul_assoc] }

@[to_additive subset_add_normalizer]
theorem subset_normalizer {s : Set G} (hs : IsSubgroup s) : s ⊆ normalizer s := fun g hg n => by
  rw [IsSubgroup.mul_mem_cancel_right hs ((IsSubgroup.inv_mem_iff hs).2 hg),
    IsSubgroup.mul_mem_cancel_left hs hg]

end IsSubgroup

-- Homomorphism subgroups
namespace IsGroupHom

open IsSubmonoid IsSubgroup

/-- `ker f : Set G` is the underlying subset of the kernel of a map `G → H`. -/
@[to_additive "`ker f : Set A` is the underlying subset of the kernel of a map `A → B`"]
def ker [Group H] (f : G → H) : Set G :=
  preimage f (trivial H)

@[to_additive]
theorem mem_ker [Group H] (f : G → H) {x : G} : x ∈ ker f ↔ f x = 1 :=
  mem_trivial

variable [Group G] [Group H]

@[to_additive]
theorem one_ker_inv {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f (a * b⁻¹) = 1) :
    f a = f b := by
  rw [hf.map_mul, hf.map_inv] at h
  rw [← inv_inv (f b), eq_inv_of_mul_eq_one_left h]

@[to_additive]
theorem one_ker_inv' {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f (a⁻¹ * b) = 1) :
    f a = f b := by
  rw [hf.map_mul, hf.map_inv] at h
  apply inv_injective
  rw [eq_inv_of_mul_eq_one_left h]

@[to_additive]
theorem inv_ker_one {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f a = f b) :
    f (a * b⁻¹) = 1 := by
  have : f a * (f b)⁻¹ = 1 := by rw [h, mul_inv_cancel]
  rwa [← hf.map_inv, ← hf.map_mul] at this

@[to_additive]
theorem inv_ker_one' {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f a = f b) :
    f (a⁻¹ * b) = 1 := by
  have : (f a)⁻¹ * f b = 1 := by rw [h, inv_mul_cancel]
  rwa [← hf.map_inv, ← hf.map_mul] at this

@[to_additive]
theorem one_iff_ker_inv {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ f (a * b⁻¹) = 1 :=
  ⟨hf.inv_ker_one, hf.one_ker_inv⟩

@[to_additive]
theorem one_iff_ker_inv' {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ f (a⁻¹ * b) = 1 :=
  ⟨hf.inv_ker_one', hf.one_ker_inv'⟩

@[to_additive]
theorem inv_iff_ker {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ a * b⁻¹ ∈ ker f := by
  rw [mem_ker]; exact one_iff_ker_inv hf _ _

@[to_additive]
theorem inv_iff_ker' {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ a⁻¹ * b ∈ ker f := by
  rw [mem_ker]; exact one_iff_ker_inv' hf _ _

@[to_additive]
theorem image_subgroup {f : G → H} (hf : IsGroupHom f) {s : Set G} (hs : IsSubgroup s) :
    IsSubgroup (f '' s) :=
  { mul_mem := fun {a₁ a₂} ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩ =>
      ⟨b₁ * b₂, hs.mul_mem hb₁ hb₂, by simp [eq₁, eq₂, hf.map_mul]⟩
    one_mem := ⟨1, hs.toIsSubmonoid.one_mem, hf.map_one⟩
    inv_mem := fun {a} ⟨b, hb, Eq⟩ =>
      ⟨b⁻¹, hs.inv_mem hb, by
        rw [hf.map_inv]
        simp [*]⟩ }

@[to_additive]
theorem range_subgroup {f : G → H} (hf : IsGroupHom f) : IsSubgroup (Set.range f) :=
  @Set.image_univ _ _ f ▸ hf.image_subgroup univ_subgroup.toIsSubgroup

attribute [local simp] IsSubmonoid.one_mem IsSubgroup.inv_mem
  IsSubmonoid.mul_mem IsNormalSubgroup.normal

@[to_additive]
theorem preimage {f : G → H} (hf : IsGroupHom f) {s : Set H} (hs : IsSubgroup s) :
    IsSubgroup (f ⁻¹' s) where
  one_mem := by simp [hf.map_one, hs.one_mem]
  mul_mem := by simp_all [hf.map_mul, hs.mul_mem]
  inv_mem := by simp_all [hf.map_inv]

@[to_additive]
theorem preimage_normal {f : G → H} (hf : IsGroupHom f) {s : Set H} (hs : IsNormalSubgroup s) :
    IsNormalSubgroup (f ⁻¹' s) :=
  { one_mem := by simp [hf.map_one, hs.toIsSubgroup.one_mem]
    mul_mem := by simp (config := { contextual := true }) [hf.map_mul, hs.toIsSubgroup.mul_mem]
    inv_mem := by simp (config := { contextual := true }) [hf.map_inv, hs.toIsSubgroup.inv_mem]
    normal := by simp (config := { contextual := true }) [hs.normal, hf.map_mul, hf.map_inv] }

@[to_additive]
theorem isNormalSubgroup_ker {f : G → H} (hf : IsGroupHom f) : IsNormalSubgroup (ker f) :=
  hf.preimage_normal trivial_normal

@[to_additive]
theorem injective_of_trivial_ker {f : G → H} (hf : IsGroupHom f) (h : ker f = trivial G) :
    Function.Injective f := by
  intro a₁ a₂ hfa
  simp [Set.ext_iff, ker, IsSubgroup.trivial] at h
  have ha : a₁ * a₂⁻¹ = 1 := by rw [← h]; exact hf.inv_ker_one hfa
  rw [eq_inv_of_mul_eq_one_left ha, inv_inv a₂]

@[to_additive]
theorem trivial_ker_of_injective {f : G → H} (hf : IsGroupHom f) (h : Function.Injective f) :
    ker f = trivial G :=
  Set.ext fun x =>
    Iff.intro
      (fun hx => by
        suffices f x = f 1 by simpa using h this
        simp [hf.map_one]; rwa [mem_ker] at hx)
      (by simp (config := { contextual := true }) [mem_ker, hf.map_one])

@[to_additive]
theorem injective_iff_trivial_ker {f : G → H} (hf : IsGroupHom f) :
    Function.Injective f ↔ ker f = trivial G :=
  ⟨hf.trivial_ker_of_injective, hf.injective_of_trivial_ker⟩

@[to_additive]
theorem trivial_ker_iff_eq_one {f : G → H} (hf : IsGroupHom f) :
    ker f = trivial G ↔ ∀ x, f x = 1 → x = 1 := by
  rw [Set.ext_iff]
  simpa [ker] using ⟨fun h x hx => (h x).1 hx, fun h x => ⟨h x, fun hx => by rw [hx, hf.map_one]⟩⟩

end IsGroupHom

namespace AddGroup

variable [AddGroup A]

/-- If `A` is an additive group and `s : Set A`, then `InClosure s : Set A` is the underlying
subset of the subgroup generated by `s`. -/
inductive InClosure (s : Set A) : A → Prop
  | basic {a : A} : a ∈ s → InClosure s a
  | zero : InClosure s 0
  | neg {a : A} : InClosure s a → InClosure s (-a)
  | add {a b : A} : InClosure s a → InClosure s b → InClosure s (a + b)

end AddGroup

namespace Group

open IsSubmonoid IsSubgroup

variable [Group G] {s : Set G}

/-- If `G` is a group and `s : Set G`, then `InClosure s : Set G` is the underlying
subset of the subgroup generated by `s`. -/
@[to_additive]
inductive InClosure (s : Set G) : G → Prop
  | basic {a : G} : a ∈ s → InClosure s a
  | one : InClosure s 1
  | inv {a : G} : InClosure s a → InClosure s a⁻¹
  | mul {a b : G} : InClosure s a → InClosure s b → InClosure s (a * b)

/-- `Group.closure s` is the subgroup generated by `s`, i.e. the smallest subgroup containing `s`.
-/
@[to_additive
  "`AddGroup.closure s` is the additive subgroup generated by `s`, i.e., the
  smallest additive subgroup containing `s`."]
def closure (s : Set G) : Set G :=
  { a | InClosure s a }

@[to_additive]
theorem mem_closure {a : G} : a ∈ s → a ∈ closure s :=
  InClosure.basic

@[to_additive]
theorem closure.isSubgroup (s : Set G) : IsSubgroup (closure s) :=
  { one_mem := InClosure.one
    mul_mem := InClosure.mul
    inv_mem := InClosure.inv }

@[to_additive]
theorem subset_closure {s : Set G} : s ⊆ closure s := fun _ => mem_closure

@[to_additive]
theorem closure_subset {s t : Set G} (ht : IsSubgroup t) (h : s ⊆ t) : closure s ⊆ t := fun a ha =>
  by induction ha <;> simp [h _, *, ht.one_mem, ht.mul_mem, IsSubgroup.inv_mem_iff]

@[to_additive]
theorem closure_subset_iff {s t : Set G} (ht : IsSubgroup t) : closure s ⊆ t ↔ s ⊆ t :=
  ⟨fun h _ ha => h (mem_closure ha), fun h _ ha => closure_subset ht h ha⟩

@[to_additive]
theorem closure_mono {s t : Set G} (h : s ⊆ t) : closure s ⊆ closure t :=
  closure_subset (closure.isSubgroup _) <| Set.Subset.trans h subset_closure

@[to_additive (attr := simp)]
theorem closure_subgroup {s : Set G} (hs : IsSubgroup s) : closure s = s :=
  Set.Subset.antisymm (closure_subset hs <| Set.Subset.refl s) subset_closure

@[to_additive]
theorem exists_list_of_mem_closure {s : Set G} {a : G} (h : a ∈ closure s) :
    ∃ l : List G, (∀ x ∈ l, x ∈ s ∨ x⁻¹ ∈ s) ∧ l.prod = a :=
  InClosure.recOn h
    (fun {x} hxs => ⟨[x], List.forall_mem_singleton.2 <| Or.inl hxs, List.prod_singleton⟩)
    ⟨[], List.forall_mem_nil _, rfl⟩
    (fun {x} _ ⟨L, HL1, HL2⟩ =>
      ⟨L.reverse.map Inv.inv, fun x hx =>
        let ⟨y, hy1, hy2⟩ := List.exists_of_mem_map hx
        hy2 ▸ Or.imp id (by rw [inv_inv]; exact id) (HL1 _ <| List.mem_reverse.1 hy1).symm,
        HL2 ▸
          List.recOn L inv_one.symm fun hd tl ih => by
            rw [List.reverse_cons, List.map_append, List.prod_append, ih, List.map_singleton,
              List.prod_cons, List.prod_nil, mul_one, List.prod_cons, mul_inv_rev]⟩)
    fun {x y} _ _ ⟨L1, HL1, HL2⟩ ⟨L2, HL3, HL4⟩ =>
    ⟨L1 ++ L2, List.forall_mem_append.2 ⟨HL1, HL3⟩, by rw [List.prod_append, HL2, HL4]⟩

@[to_additive]
theorem image_closure [Group H] {f : G → H} (hf : IsGroupHom f) (s : Set G) :
    f '' closure s = closure (f '' s) :=
  le_antisymm
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact InClosure.recOn hx
        (by intros _ ha; exact subset_closure (mem_image_of_mem f ha))
        (by
          rw [hf.map_one]
          apply IsSubmonoid.one_mem (closure.isSubgroup _).toIsSubmonoid)
        (by
          intros _ _
          rw [hf.map_inv]
          apply IsSubgroup.inv_mem (closure.isSubgroup _))
        (by
          intros _ _ _ _ ha hb
          rw [hf.map_mul]
          exact (closure.isSubgroup (f '' s)).toIsSubmonoid.mul_mem ha hb))
    (closure_subset (hf.image_subgroup <| closure.isSubgroup _) <|
      Set.image_subset _ subset_closure)

@[to_additive]
theorem mclosure_subset {s : Set G} : Monoid.Closure s ⊆ closure s :=
  Monoid.closure_subset (closure.isSubgroup _).toIsSubmonoid <| subset_closure

@[to_additive]
theorem mclosure_inv_subset {s : Set G} : Monoid.Closure (Inv.inv ⁻¹' s) ⊆ closure s :=
  Monoid.closure_subset (closure.isSubgroup _).toIsSubmonoid fun x hx =>
    inv_inv x ▸ ((closure.isSubgroup _).inv_mem <| subset_closure hx)

@[to_additive]
theorem closure_eq_mclosure {s : Set G} : closure s = Monoid.Closure (s ∪ Inv.inv ⁻¹' s) :=
  Set.Subset.antisymm
    (@closure_subset _ _ _ (Monoid.Closure (s ∪ Inv.inv ⁻¹' s))
      { one_mem := (Monoid.closure.isSubmonoid _).one_mem
        mul_mem := (Monoid.closure.isSubmonoid _).mul_mem
        inv_mem := fun hx =>
          Monoid.InClosure.recOn hx
            (fun {x} hx =>
              Or.casesOn hx
                (fun hx =>
                  Monoid.subset_closure <| Or.inr <| show x⁻¹⁻¹ ∈ s from (inv_inv x).symm ▸ hx)
                fun hx => Monoid.subset_closure <| Or.inl hx)
            ((@inv_one G _).symm ▸ IsSubmonoid.one_mem (Monoid.closure.isSubmonoid _))
            fun {x y} _ _ ihx ihy =>
            (mul_inv_rev x y).symm ▸ IsSubmonoid.mul_mem (Monoid.closure.isSubmonoid _) ihy ihx }
      (Set.Subset.trans Set.subset_union_left Monoid.subset_closure))
    (Monoid.closure_subset (closure.isSubgroup _).toIsSubmonoid <|
      Set.union_subset subset_closure fun x hx =>
        inv_inv x ▸ (IsSubgroup.inv_mem (closure.isSubgroup _) <| subset_closure hx))

@[to_additive]
theorem mem_closure_union_iff {G : Type*} [CommGroup G] {s t : Set G} {x : G} :
    x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y * z = x := by
  simp only [closure_eq_mclosure, Monoid.mem_closure_union_iff, exists_prop, preimage_union]
  constructor
  · rintro ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, hys, _, hzs, rfl⟩, _, ⟨_, hyt, _, hzt, rfl⟩, ?_⟩
    rw [mul_assoc, mul_assoc, mul_left_comm zs]
  · rintro ⟨_, ⟨ys, hys, zs, hzs, rfl⟩, _, ⟨yt, hyt, zt, hzt, rfl⟩, rfl⟩
    refine ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, ?_⟩
    rw [mul_assoc, mul_assoc, mul_left_comm yt]

end Group

namespace IsSubgroup

variable [Group G]

@[to_additive]
theorem trivial_eq_closure : trivial G = Group.closure ∅ :=
  Subset.antisymm (by simp [Set.subset_def, (Group.closure.isSubgroup _).one_mem])
    (Group.closure_subset trivial_normal.toIsSubgroup <| by simp)

end IsSubgroup

/- The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/
namespace Group

variable {s : Set G} [Group G]

theorem conjugatesOf_subset {t : Set G} (ht : IsNormalSubgroup t) {a : G} (h : a ∈ t) :
    conjugatesOf a ⊆ t := fun x hc => by
  obtain ⟨c, w⟩ := isConj_iff.1 hc
  have H := IsNormalSubgroup.normal ht a h c
  rwa [← w]

theorem conjugatesOfSet_subset' {s t : Set G} (ht : IsNormalSubgroup t) (h : s ⊆ t) :
    conjugatesOfSet s ⊆ t :=
  Set.iUnion₂_subset fun _ H => conjugatesOf_subset ht (h H)

/-- The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/
def normalClosure (s : Set G) : Set G :=
  closure (conjugatesOfSet s)

theorem conjugatesOfSet_subset_normalClosure : conjugatesOfSet s ⊆ normalClosure s :=
  subset_closure

theorem subset_normalClosure : s ⊆ normalClosure s :=
  Set.Subset.trans subset_conjugatesOfSet conjugatesOfSet_subset_normalClosure

/-- The normal closure of a set is a subgroup. -/
theorem normalClosure.isSubgroup (s : Set G) : IsSubgroup (normalClosure s) :=
  closure.isSubgroup (conjugatesOfSet s)

/-- The normal closure of s is a normal subgroup. -/
theorem normalClosure.is_normal : IsNormalSubgroup (normalClosure s) :=
  { normalClosure.isSubgroup _ with
    normal := fun n h g => by
      induction' h with x hx x hx ihx x y hx hy ihx ihy
      · exact conjugatesOfSet_subset_normalClosure (conj_mem_conjugatesOfSet hx)
      · simpa using (normalClosure.isSubgroup s).one_mem
      · rw [← conj_inv]
        exact (normalClosure.isSubgroup _).inv_mem ihx
      · rw [← conj_mul]
        exact (normalClosure.isSubgroup _).toIsSubmonoid.mul_mem ihx ihy }

/-- The normal closure of s is the smallest normal subgroup containing s. -/
theorem normalClosure_subset {s t : Set G} (ht : IsNormalSubgroup t) (h : s ⊆ t) :
    normalClosure s ⊆ t := fun a w => by
  induction w with
  | basic hx => exact conjugatesOfSet_subset' ht h <| hx
  | one => exact ht.toIsSubgroup.toIsSubmonoid.one_mem
  | inv _ ihx => exact ht.toIsSubgroup.inv_mem ihx
  | mul _ _ ihx ihy => exact ht.toIsSubgroup.toIsSubmonoid.mul_mem ihx ihy

theorem normalClosure_subset_iff {s t : Set G} (ht : IsNormalSubgroup t) :
    s ⊆ t ↔ normalClosure s ⊆ t :=
  ⟨normalClosure_subset ht, Set.Subset.trans subset_normalClosure⟩

theorem normalClosure_mono {s t : Set G} : s ⊆ t → normalClosure s ⊆ normalClosure t := fun h =>
  normalClosure_subset normalClosure.is_normal (Set.Subset.trans h subset_normalClosure)

end Group

/-- Create a bundled subgroup from a set `s` and `[IsSubgroup s]`. -/
@[to_additive "Create a bundled additive subgroup from a set `s` and `[IsAddSubgroup s]`."]
def Subgroup.of [Group G] {s : Set G} (h : IsSubgroup s) : Subgroup G where
  carrier := s
  one_mem' := h.1.1
  mul_mem' := h.1.2
  inv_mem' := h.2

@[to_additive]
theorem Subgroup.isSubgroup [Group G] (K : Subgroup G) : IsSubgroup (K : Set G) :=
  { one_mem := K.one_mem'
    mul_mem := K.mul_mem'
    inv_mem := K.inv_mem' }

-- this will never fire if it's an instance
@[to_additive]
theorem Subgroup.of_normal [Group G] (s : Set G) (h : IsSubgroup s) (n : IsNormalSubgroup s) :
    Subgroup.Normal (Subgroup.of h) :=
  { conj_mem := n.normal }
