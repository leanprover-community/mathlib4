/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Rowett, Scott Morrison, Johan Commelin, Mario Carneiro,
  Michael Howes

! This file was ported from Lean 3 source module deprecated.subgroup
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.Deprecated.Submonoid

/-!
# Unbundled subgroups (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines unbundled multiplicative and additive subgroups. Instead of using this file,
please use `subgroup G` and `add_subgroup A`, defined in `group_theory.subgroup.basic`.

## Main definitions

`is_add_subgroup (S : set A)` : the predicate that `S` is the underlying subset of an additive
subgroup of `A`. The bundled variant `add_subgroup A` should be used in preference to this.

`is_subgroup (S : set G)` : the predicate that `S` is the underlying subset of a subgroup
of `G`. The bundled variant `subgroup G` should be used in preference to this.

## Tags

subgroup, subgroups, is_subgroup
-/


open Set Function

variable {G : Type _} {H : Type _} {A : Type _} {a a₁ a₂ b c : G}

section Group

variable [Group G] [AddGroup A]

/-- `s` is an additive subgroup: a set containing 0 and closed under addition and negation. -/
structure IsAddSubgroup (s : Set A) extends IsAddSubmonoid s : Prop where
  neg_mem {a} : a ∈ s → -a ∈ s
#align is_add_subgroup IsAddSubgroup

/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
@[to_additive]
structure IsSubgroup (s : Set G) extends IsSubmonoid s : Prop where
  inv_mem {a} : a ∈ s → a⁻¹ ∈ s
#align is_subgroup IsSubgroup

@[to_additive]
theorem IsSubgroup.div_mem {s : Set G} (hs : IsSubgroup s) {x y : G} (hx : x ∈ s) (hy : y ∈ s) :
    x / y ∈ s := by simpa only [div_eq_mul_inv] using hs.mul_mem hx (hs.inv_mem hy)
#align is_subgroup.div_mem IsSubgroup.div_mem

theorem Additive.is_add_subgroup {s : Set G} (hs : IsSubgroup s) :
    @IsAddSubgroup (Additive G) _ s :=
  (@IsAddSubgroup.mk (Additive G) _ _ (Additive.is_add_submonoid hs.to_is_submonoid)) fun _ =>
    hs.inv_mem
#align additive.is_add_subgroup Additive.is_add_subgroup

theorem Additive.is_add_subgroup_iff {s : Set G} : @IsAddSubgroup (Additive G) _ s ↔ IsSubgroup s :=
  ⟨by rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact @IsSubgroup.mk G _ _ ⟨h₁, @h₂⟩ @h₃, fun h =>
    Additive.is_add_subgroup h⟩
#align additive.is_add_subgroup_iff Additive.is_add_subgroup_iff

theorem Multiplicative.is_subgroup {s : Set A} (hs : IsAddSubgroup s) :
    @IsSubgroup (Multiplicative A) _ s :=
  (@IsSubgroup.mk (Multiplicative A) _ _ (Multiplicative.is_submonoid hs.to_is_add_submonoid))
    fun _ => hs.neg_mem
#align multiplicative.is_subgroup Multiplicative.is_subgroup

theorem Multiplicative.is_subgroup_iff {s : Set A} :
    @IsSubgroup (Multiplicative A) _ s ↔ IsAddSubgroup s :=
  ⟨by rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact @IsAddSubgroup.mk A _ _ ⟨h₁, @h₂⟩ @h₃, fun h =>
    Multiplicative.is_subgroup h⟩
#align multiplicative.is_subgroup_iff Multiplicative.is_subgroup_iff

@[to_additive ofAdd_neg]
theorem IsSubgroup.of_div (s : Set G) (one_mem : (1 : G) ∈ s)
    (div_mem : ∀ {a b : G}, a ∈ s → b ∈ s → a * b⁻¹ ∈ s) : IsSubgroup s :=
  have inv_mem : ∀ a, a ∈ s → a⁻¹ ∈ s := fun a ha =>
    by
    have : 1 * a⁻¹ ∈ s := div_mem one_mem ha
    simpa
  { inv_mem
    mul_mem := fun a b ha hb =>
      by
      have : a * b⁻¹⁻¹ ∈ s := div_mem ha (inv_mem b hb)
      simpa
    one_mem }
#align is_subgroup.of_div IsSubgroup.of_div

theorem IsAddSubgroup.of_sub (s : Set A) (zero_mem : (0 : A) ∈ s)
    (sub_mem : ∀ {a b : A}, a ∈ s → b ∈ s → a - b ∈ s) : IsAddSubgroup s :=
  IsAddSubgroup.of_add_neg s zero_mem fun x y hx hy => by
    simpa only [sub_eq_add_neg] using sub_mem hx hy
#align is_add_subgroup.of_sub IsAddSubgroup.of_sub

@[to_additive]
theorem IsSubgroup.inter {s₁ s₂ : Set G} (hs₁ : IsSubgroup s₁) (hs₂ : IsSubgroup s₂) :
    IsSubgroup (s₁ ∩ s₂) :=
  { IsSubmonoid.inter hs₁.to_is_submonoid hs₂.to_is_submonoid with
    inv_mem := fun x hx => ⟨hs₁.inv_mem hx.1, hs₂.inv_mem hx.2⟩ }
#align is_subgroup.inter IsSubgroup.inter

@[to_additive]
theorem IsSubgroup.Inter {ι : Sort _} {s : ι → Set G} (hs : ∀ y : ι, IsSubgroup (s y)) :
    IsSubgroup (Set.interᵢ s) :=
  { IsSubmonoid.Inter fun y => (hs y).to_is_submonoid with
    inv_mem := fun x h =>
      Set.mem_interᵢ.2 fun y => IsSubgroup.inv_mem (hs _) (Set.mem_interᵢ.1 h y) }
#align is_subgroup.Inter IsSubgroup.Inter

@[to_additive]
theorem is_subgroup_Union_of_directed {ι : Type _} [hι : Nonempty ι] {s : ι → Set G}
    (hs : ∀ i, IsSubgroup (s i)) (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
    IsSubgroup (⋃ i, s i) :=
  { inv_mem := fun a ha =>
      let ⟨i, hi⟩ := Set.mem_unionᵢ.1 ha
      Set.mem_unionᵢ.2 ⟨i, (hs i).inv_mem hi⟩
    to_is_submonoid := is_submonoid_Union_of_directed (fun i => (hs i).to_is_submonoid) Directed }
#align is_subgroup_Union_of_directed is_subgroup_Union_of_directed

end Group

namespace IsSubgroup

open IsSubmonoid

variable [Group G] {s : Set G} (hs : IsSubgroup s)

include hs

@[to_additive]
theorem inv_mem_iff : a⁻¹ ∈ s ↔ a ∈ s :=
  ⟨fun h => by simpa using hs.inv_mem h, inv_mem hs⟩
#align is_subgroup.inv_mem_iff IsSubgroup.inv_mem_iff

@[to_additive]
theorem mul_mem_cancel_right (h : a ∈ s) : b * a ∈ s ↔ b ∈ s :=
  ⟨fun hba => by simpa using hs.mul_mem hba (hs.inv_mem h), fun hb => hs.mul_mem hb h⟩
#align is_subgroup.mul_mem_cancel_right IsSubgroup.mul_mem_cancel_right

@[to_additive]
theorem mul_mem_cancel_left (h : a ∈ s) : a * b ∈ s ↔ b ∈ s :=
  ⟨fun hab => by simpa using hs.mul_mem (hs.inv_mem h) hab, hs.mul_mem h⟩
#align is_subgroup.mul_mem_cancel_left IsSubgroup.mul_mem_cancel_left

end IsSubgroup

/-- `is_normal_add_subgroup (s : set A)` expresses the fact that `s` is a normal additive subgroup
of the additive group `A`. Important: the preferred way to say this in Lean is via bundled
subgroups `S : add_subgroup A` and `hs : S.normal`, and not via this structure. -/
structure IsNormalAddSubgroup [AddGroup A] (s : Set A) extends IsAddSubgroup s : Prop where
  Normal : ∀ n ∈ s, ∀ g : A, g + n + -g ∈ s
#align is_normal_add_subgroup IsNormalAddSubgroup

/-- `is_normal_subgroup (s : set G)` expresses the fact that `s` is a normal subgroup
of the group `G`. Important: the preferred way to say this in Lean is via bundled
subgroups `S : subgroup G` and not via this structure. -/
@[to_additive]
structure IsNormalSubgroup [Group G] (s : Set G) extends IsSubgroup s : Prop where
  Normal : ∀ n ∈ s, ∀ g : G, g * n * g⁻¹ ∈ s
#align is_normal_subgroup IsNormalSubgroup

@[to_additive]
theorem is_normal_subgroup_of_comm_group [CommGroup G] {s : Set G} (hs : IsSubgroup s) :
    IsNormalSubgroup s :=
  { hs with Normal := fun n hn g => by rwa [mul_right_comm, mul_right_inv, one_mul] }
#align is_normal_subgroup_of_comm_group is_normal_subgroup_of_comm_group

theorem Additive.is_normal_add_subgroup [Group G] {s : Set G} (hs : IsNormalSubgroup s) :
    @IsNormalAddSubgroup (Additive G) _ s :=
  @IsNormalAddSubgroup.mk (Additive G) _ _ (Additive.is_add_subgroup hs.to_is_subgroup)
    (IsNormalSubgroup.normal hs)
#align additive.is_normal_add_subgroup Additive.is_normal_add_subgroup

theorem Additive.is_normal_add_subgroup_iff [Group G] {s : Set G} :
    @IsNormalAddSubgroup (Additive G) _ s ↔ IsNormalSubgroup s :=
  ⟨by rintro ⟨h₁, h₂⟩ <;> exact @IsNormalSubgroup.mk G _ _ (Additive.is_add_subgroup_iff.1 h₁) @h₂,
    fun h => Additive.is_normal_add_subgroup h⟩
#align additive.is_normal_add_subgroup_iff Additive.is_normal_add_subgroup_iff

theorem Multiplicative.is_normal_subgroup [AddGroup A] {s : Set A} (hs : IsNormalAddSubgroup s) :
    @IsNormalSubgroup (Multiplicative A) _ s :=
  @IsNormalSubgroup.mk (Multiplicative A) _ _ (Multiplicative.is_subgroup hs.to_is_add_subgroup)
    (IsNormalAddSubgroup.normal hs)
#align multiplicative.is_normal_subgroup Multiplicative.is_normal_subgroup

theorem Multiplicative.is_normal_subgroup_iff [AddGroup A] {s : Set A} :
    @IsNormalSubgroup (Multiplicative A) _ s ↔ IsNormalAddSubgroup s :=
  ⟨by
    rintro ⟨h₁, h₂⟩ <;>
      exact @IsNormalAddSubgroup.mk A _ _ (Multiplicative.is_subgroup_iff.1 h₁) @h₂,
    fun h => Multiplicative.is_normal_subgroup h⟩
#align multiplicative.is_normal_subgroup_iff Multiplicative.is_normal_subgroup_iff

namespace IsSubgroup

variable [Group G]

-- Normal subgroup properties
@[to_additive]
theorem mem_norm_comm {s : Set G} (hs : IsNormalSubgroup s) {a b : G} (hab : a * b ∈ s) :
    b * a ∈ s := by
  have h : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ s := hs.Normal (a * b) hab a⁻¹
  simp at h <;> exact h
#align is_subgroup.mem_norm_comm IsSubgroup.mem_norm_comm

@[to_additive]
theorem mem_norm_comm_iff {s : Set G} (hs : IsNormalSubgroup s) {a b : G} : a * b ∈ s ↔ b * a ∈ s :=
  ⟨mem_norm_comm hs, mem_norm_comm hs⟩
#align is_subgroup.mem_norm_comm_iff IsSubgroup.mem_norm_comm_iff

/-- The trivial subgroup -/
@[to_additive "the trivial additive subgroup"]
def trivial (G : Type _) [Group G] : Set G :=
  {1}
#align is_subgroup.trivial IsSubgroup.trivial

@[simp, to_additive]
theorem mem_trivial {g : G} : g ∈ trivial G ↔ g = 1 :=
  mem_singleton_iff
#align is_subgroup.mem_trivial IsSubgroup.mem_trivial

@[to_additive]
theorem trivial_normal : IsNormalSubgroup (trivial G) := by
  refine' { .. } <;> simp (config := { contextual := true }) [trivial]
#align is_subgroup.trivial_normal IsSubgroup.trivial_normal

@[to_additive]
theorem eq_trivial_iff {s : Set G} (hs : IsSubgroup s) : s = trivial G ↔ ∀ x ∈ s, x = (1 : G) := by
  simp only [Set.ext_iff, IsSubgroup.mem_trivial] <;>
    exact ⟨fun h x => (h x).1, fun h x => ⟨h x, fun hx => hx.symm ▸ hs.to_is_submonoid.one_mem⟩⟩
#align is_subgroup.eq_trivial_iff IsSubgroup.eq_trivial_iff

@[to_additive]
theorem univ_subgroup : IsNormalSubgroup (@univ G) := by refine' { .. } <;> simp
#align is_subgroup.univ_subgroup IsSubgroup.univ_subgroup

/-- The underlying set of the center of a group. -/
@[to_additive add_center "The underlying set of the center of an additive group."]
def center (G : Type _) [Group G] : Set G :=
  { z | ∀ g, g * z = z * g }
#align is_subgroup.center IsSubgroup.center

@[to_additive mem_add_center]
theorem mem_center {a : G} : a ∈ center G ↔ ∀ g, g * a = a * g :=
  Iff.rfl
#align is_subgroup.mem_center IsSubgroup.mem_center

@[to_additive add_center_normal]
theorem center_normal : IsNormalSubgroup (center G) :=
  { one_mem := by simp [center]
    mul_mem := fun a b ha hb g => by
      rw [← mul_assoc, mem_center.2 ha g, mul_assoc, mem_center.2 hb g, ← mul_assoc]
    inv_mem := fun a ha g =>
      calc
        g * a⁻¹ = a⁻¹ * (g * a) * a⁻¹ := by simp [ha g]
        _ = a⁻¹ * g := by rw [← mul_assoc, mul_assoc] <;> simp
        
    Normal := fun n ha g h =>
      calc
        h * (g * n * g⁻¹) = h * n := by simp [ha g, mul_assoc]
        _ = g * g⁻¹ * n * h := by rw [ha h] <;> simp
        _ = g * n * g⁻¹ * h := by rw [mul_assoc g, ha g⁻¹, ← mul_assoc]
         }
#align is_subgroup.center_normal IsSubgroup.center_normal

/-- The underlying set of the normalizer of a subset `S : set G` of a group `G`. That is,
  the elements `g : G` such that `g * S * g⁻¹ = S`. -/
@[to_additive add_normalizer
      "The underlying set of the normalizer of a subset `S : set A` of an\n  additive group `A`. That is, the elements `a : A` such that `a + S - a = S`."]
def normalizer (s : Set G) : Set G :=
  { g : G | ∀ n, n ∈ s ↔ g * n * g⁻¹ ∈ s }
#align is_subgroup.normalizer IsSubgroup.normalizer

@[to_additive]
theorem normalizer_is_subgroup (s : Set G) : IsSubgroup (normalizer s) :=
  { one_mem := by simp [normalizer]
    mul_mem := fun a b (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s) (hb : ∀ n, n ∈ s ↔ b * n * b⁻¹ ∈ s) n =>
      by rw [mul_inv_rev, ← mul_assoc, mul_assoc a, mul_assoc a, ← ha, ← hb]
    inv_mem := fun a (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s) n => by
      rw [ha (a⁻¹ * n * a⁻¹⁻¹)] <;> simp [mul_assoc] }
#align is_subgroup.normalizer_is_subgroup IsSubgroup.normalizer_is_subgroup

@[to_additive subset_add_normalizer]
theorem subset_normalizer {s : Set G} (hs : IsSubgroup s) : s ⊆ normalizer s := fun g hg n => by
  rw [IsSubgroup.mul_mem_cancel_right hs ((IsSubgroup.inv_mem_iff hs).2 hg),
    IsSubgroup.mul_mem_cancel_left hs hg]
#align is_subgroup.subset_normalizer IsSubgroup.subset_normalizer

end IsSubgroup

-- Homomorphism subgroups
namespace IsGroupHom

open IsSubmonoid IsSubgroup

/-- `ker f : set G` is the underlying subset of the kernel of a map `G → H`. -/
@[to_additive "`ker f : set A` is the underlying subset of the kernel of a map `A → B`"]
def ker [Group H] (f : G → H) : Set G :=
  preimage f (trivial H)
#align is_group_hom.ker IsGroupHom.ker

@[to_additive]
theorem mem_ker [Group H] (f : G → H) {x : G} : x ∈ ker f ↔ f x = 1 :=
  mem_trivial
#align is_group_hom.mem_ker IsGroupHom.mem_ker

variable [Group G] [Group H]

@[to_additive]
theorem one_ker_inv {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f (a * b⁻¹) = 1) : f a = f b :=
  by
  rw [hf.map_mul, hf.map_inv] at h
  rw [← inv_inv (f b), eq_inv_of_mul_eq_one_left h]
#align is_group_hom.one_ker_inv IsGroupHom.one_ker_inv

@[to_additive]
theorem one_ker_inv' {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f (a⁻¹ * b) = 1) : f a = f b :=
  by
  rw [hf.map_mul, hf.map_inv] at h
  apply inv_injective
  rw [eq_inv_of_mul_eq_one_left h]
#align is_group_hom.one_ker_inv' IsGroupHom.one_ker_inv'

@[to_additive]
theorem inv_ker_one {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f a = f b) : f (a * b⁻¹) = 1 :=
  by
  have : f a * (f b)⁻¹ = 1 := by rw [h, mul_right_inv]
  rwa [← hf.map_inv, ← hf.map_mul] at this
#align is_group_hom.inv_ker_one IsGroupHom.inv_ker_one

@[to_additive]
theorem inv_ker_one' {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f a = f b) : f (a⁻¹ * b) = 1 :=
  by
  have : (f a)⁻¹ * f b = 1 := by rw [h, mul_left_inv]
  rwa [← hf.map_inv, ← hf.map_mul] at this
#align is_group_hom.inv_ker_one' IsGroupHom.inv_ker_one'

@[to_additive]
theorem one_iff_ker_inv {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ f (a * b⁻¹) = 1 :=
  ⟨hf.inv_ker_one, hf.one_ker_inv⟩
#align is_group_hom.one_iff_ker_inv IsGroupHom.one_iff_ker_inv

@[to_additive]
theorem one_iff_ker_inv' {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ f (a⁻¹ * b) = 1 :=
  ⟨hf.inv_ker_one', hf.one_ker_inv'⟩
#align is_group_hom.one_iff_ker_inv' IsGroupHom.one_iff_ker_inv'

@[to_additive]
theorem inv_iff_ker {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ a * b⁻¹ ∈ ker f := by
  rw [mem_ker] <;> exact one_iff_ker_inv hf _ _
#align is_group_hom.inv_iff_ker IsGroupHom.inv_iff_ker

@[to_additive]
theorem inv_iff_ker' {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ a⁻¹ * b ∈ ker f := by
  rw [mem_ker] <;> exact one_iff_ker_inv' hf _ _
#align is_group_hom.inv_iff_ker' IsGroupHom.inv_iff_ker'

@[to_additive]
theorem image_subgroup {f : G → H} (hf : IsGroupHom f) {s : Set G} (hs : IsSubgroup s) :
    IsSubgroup (f '' s) :=
  { mul_mem := fun a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩ =>
      ⟨b₁ * b₂, hs.mul_mem hb₁ hb₂, by simp [eq₁, eq₂, hf.map_mul]⟩
    one_mem := ⟨1, hs.to_is_submonoid.one_mem, hf.map_one⟩
    inv_mem := fun a ⟨b, hb, Eq⟩ =>
      ⟨b⁻¹, hs.inv_mem hb, by
        rw [hf.map_inv]
        simp [*]⟩ }
#align is_group_hom.image_subgroup IsGroupHom.image_subgroup

@[to_additive]
theorem range_subgroup {f : G → H} (hf : IsGroupHom f) : IsSubgroup (Set.range f) :=
  @Set.image_univ _ _ f ▸ hf.image_subgroup univ_subgroup.to_is_subgroup
#align is_group_hom.range_subgroup IsGroupHom.range_subgroup

attribute [local simp] one_mem inv_mem mul_mem IsNormalSubgroup.normal

@[to_additive]
theorem preimage {f : G → H} (hf : IsGroupHom f) {s : Set H} (hs : IsSubgroup s) :
    IsSubgroup (f ⁻¹' s) := by
  refine' { .. } <;>
    simp (config := { contextual := true }) [hs.one_mem, hs.mul_mem, hs.inv_mem, hf.map_mul,
      hf.map_one, hf.map_inv, InvMemClass.inv_mem]
#align is_group_hom.preimage IsGroupHom.preimage

@[to_additive]
theorem preimage_normal {f : G → H} (hf : IsGroupHom f) {s : Set H} (hs : IsNormalSubgroup s) :
    IsNormalSubgroup (f ⁻¹' s) :=
  { one_mem := by simp [hf.map_one, hs.to_is_subgroup.one_mem]
    mul_mem := by simp (config := { contextual := true }) [hf.map_mul, hs.to_is_subgroup.mul_mem]
    inv_mem := by simp (config := { contextual := true }) [hf.map_inv, hs.to_is_subgroup.inv_mem]
    Normal := by simp (config := { contextual := true }) [hs.normal, hf.map_mul, hf.map_inv] }
#align is_group_hom.preimage_normal IsGroupHom.preimage_normal

@[to_additive]
theorem is_normal_subgroup_ker {f : G → H} (hf : IsGroupHom f) : IsNormalSubgroup (ker f) :=
  hf.preimage_normal trivial_normal
#align is_group_hom.is_normal_subgroup_ker IsGroupHom.is_normal_subgroup_ker

@[to_additive]
theorem injective_of_trivial_ker {f : G → H} (hf : IsGroupHom f) (h : ker f = trivial G) :
    Function.Injective f := by
  intro a₁ a₂ hfa
  simp [ext_iff, ker, IsSubgroup.trivial] at h
  have ha : a₁ * a₂⁻¹ = 1 := by rw [← h] <;> exact hf.inv_ker_one hfa
  rw [eq_inv_of_mul_eq_one_left ha, inv_inv a₂]
#align is_group_hom.injective_of_trivial_ker IsGroupHom.injective_of_trivial_ker

@[to_additive]
theorem trivial_ker_of_injective {f : G → H} (hf : IsGroupHom f) (h : Function.Injective f) :
    ker f = trivial G :=
  Set.ext fun x =>
    Iff.intro
      (fun hx => by
        suffices f x = f 1 by simpa using h this
        simp [hf.map_one] <;> rwa [mem_ker] at hx)
      (by simp (config := { contextual := true }) [mem_ker, hf.map_one])
#align is_group_hom.trivial_ker_of_injective IsGroupHom.trivial_ker_of_injective

@[to_additive]
theorem injective_iff_trivial_ker {f : G → H} (hf : IsGroupHom f) :
    Function.Injective f ↔ ker f = trivial G :=
  ⟨hf.trivial_ker_of_injective, hf.injective_of_trivial_ker⟩
#align is_group_hom.injective_iff_trivial_ker IsGroupHom.injective_iff_trivial_ker

@[to_additive]
theorem trivial_ker_iff_eq_one {f : G → H} (hf : IsGroupHom f) :
    ker f = trivial G ↔ ∀ x, f x = 1 → x = 1 := by
  rw [Set.ext_iff] <;> simp [ker] <;>
    exact ⟨fun h x hx => (h x).1 hx, fun h x => ⟨h x, fun hx => by rw [hx, hf.map_one]⟩⟩
#align is_group_hom.trivial_ker_iff_eq_one IsGroupHom.trivial_ker_iff_eq_one

end IsGroupHom

namespace AddGroup

variable [AddGroup A]

/-- If `A` is an additive group and `s : set A`, then `in_closure s : set A` is the underlying
subset of the subgroup generated by `s`. -/
inductive InClosure (s : Set A) : A → Prop
  | basic {a : A} : a ∈ s → in_closure a
  | zero : in_closure 0
  | neg {a : A} : in_closure a → in_closure (-a)
  | add {a b : A} : in_closure a → in_closure b → in_closure (a + b)
#align add_group.in_closure AddGroup.InClosure

end AddGroup

namespace Group

open IsSubmonoid IsSubgroup

variable [Group G] {s : Set G}

/-- If `G` is a group and `s : set G`, then `in_closure s : set G` is the underlying
subset of the subgroup generated by `s`. -/
@[to_additive]
inductive InClosure (s : Set G) : G → Prop
  | basic {a : G} : a ∈ s → in_closure a
  | one : in_closure 1
  | inv {a : G} : in_closure a → in_closure a⁻¹
  | mul {a b : G} : in_closure a → in_closure b → in_closure (a * b)
#align group.in_closure Group.InClosure

/-- `group.closure s` is the subgroup generated by `s`, i.e. the smallest subgroup containg `s`. -/
@[to_additive
      "`add_group.closure s` is the additive subgroup generated by `s`, i.e., the\n  smallest additive subgroup containing `s`."]
def closure (s : Set G) : Set G :=
  { a | InClosure s a }
#align group.closure Group.closure

@[to_additive]
theorem mem_closure {a : G} : a ∈ s → a ∈ closure s :=
  in_closure.basic
#align group.mem_closure Group.mem_closure

@[to_additive]
theorem closure.is_subgroup (s : Set G) : IsSubgroup (closure s) :=
  { one_mem := InClosure.one
    mul_mem := fun a b => InClosure.mul
    inv_mem := fun a => InClosure.inv }
#align group.closure.is_subgroup Group.closure.is_subgroup

@[to_additive]
theorem subset_closure {s : Set G} : s ⊆ closure s := fun a => mem_closure
#align group.subset_closure Group.subset_closure

@[to_additive]
theorem closure_subset {s t : Set G} (ht : IsSubgroup t) (h : s ⊆ t) : closure s ⊆ t := fun a ha =>
  by induction ha <;> simp [h _, *, ht.one_mem, ht.mul_mem, IsSubgroup.inv_mem_iff]
#align group.closure_subset Group.closure_subset

@[to_additive]
theorem closure_subset_iff {s t : Set G} (ht : IsSubgroup t) : closure s ⊆ t ↔ s ⊆ t :=
  ⟨fun h b ha => h (mem_closure ha), fun h b ha => closure_subset ht h ha⟩
#align group.closure_subset_iff Group.closure_subset_iff

@[to_additive]
theorem closure_mono {s t : Set G} (h : s ⊆ t) : closure s ⊆ closure t :=
  closure_subset (closure.is_subgroup _) <| Set.Subset.trans h subset_closure
#align group.closure_mono Group.closure_mono

@[simp, to_additive]
theorem closure_subgroup {s : Set G} (hs : IsSubgroup s) : closure s = s :=
  Set.Subset.antisymm (closure_subset hs <| Set.Subset.refl s) subset_closure
#align group.closure_subgroup Group.closure_subgroup

@[to_additive]
theorem exists_list_of_mem_closure {s : Set G} {a : G} (h : a ∈ closure s) :
    ∃ l : List G, (∀ x ∈ l, x ∈ s ∨ x⁻¹ ∈ s) ∧ l.Prod = a :=
  InClosure.rec_on h (fun x hxs => ⟨[x], List.forall_mem_singleton.2 <| Or.inl hxs, one_mul _⟩)
    ⟨[], List.forall_mem_nil _, rfl⟩
    (fun x _ ⟨L, HL1, HL2⟩ =>
      ⟨L.reverse.map Inv.inv, fun x hx =>
        let ⟨y, hy1, hy2⟩ := List.exists_of_mem_map hx
        hy2 ▸ Or.imp id (by rw [inv_inv] <;> exact id) (HL1 _ <| List.mem_reverse.1 hy1).symm,
        HL2 ▸
          List.recOn L inv_one.symm fun hd tl ih => by
            rw [List.reverse_cons, List.map_append, List.prod_append, ih, List.map_singleton,
              List.prod_cons, List.prod_nil, mul_one, List.prod_cons, mul_inv_rev]⟩)
    fun x y hx hy ⟨L1, HL1, HL2⟩ ⟨L2, HL3, HL4⟩ =>
    ⟨L1 ++ L2, List.forall_mem_append.2 ⟨HL1, HL3⟩, by rw [List.prod_append, HL2, HL4]⟩
#align group.exists_list_of_mem_closure Group.exists_list_of_mem_closure

@[to_additive]
theorem image_closure [Group H] {f : G → H} (hf : IsGroupHom f) (s : Set G) :
    f '' closure s = closure (f '' s) :=
  le_antisymm
    (by
      rintro _ ⟨x, hx, rfl⟩
      apply in_closure.rec_on hx <;> intros
      · solve_by_elim [subset_closure, Set.mem_image_of_mem]
      · rw [hf.to_is_monoid_hom.map_one]
        apply IsSubmonoid.one_mem (closure.is_subgroup _).to_is_submonoid
      · rw [hf.map_inv]
        apply IsSubgroup.inv_mem (closure.is_subgroup _)
        assumption
      · rw [hf.to_is_monoid_hom.map_mul]
        solve_by_elim [IsSubmonoid.mul_mem (closure.is_subgroup _).to_is_submonoid] )
    (closure_subset (hf.image_subgroup <| closure.is_subgroup _) <|
      Set.image_subset _ subset_closure)
#align group.image_closure Group.image_closure

@[to_additive]
theorem mclosure_subset {s : Set G} : Monoid.closure s ⊆ closure s :=
  Monoid.closure_subset (closure.is_subgroup _).to_is_submonoid <| subset_closure
#align group.mclosure_subset Group.mclosure_subset

@[to_additive]
theorem mclosure_inv_subset {s : Set G} : Monoid.closure (Inv.inv ⁻¹' s) ⊆ closure s :=
  (Monoid.closure_subset (closure.is_subgroup _).to_is_submonoid) fun x hx =>
    inv_inv x ▸ ((closure.is_subgroup _).inv_mem <| subset_closure hx)
#align group.mclosure_inv_subset Group.mclosure_inv_subset

@[to_additive]
theorem closure_eq_mclosure {s : Set G} : closure s = Monoid.closure (s ∪ Inv.inv ⁻¹' s) :=
  Set.Subset.antisymm
    (@closure_subset _ _ _ (Monoid.closure (s ∪ Inv.inv ⁻¹' s))
      { one_mem := (Monoid.closure.is_submonoid _).one_mem
        mul_mem := fun _ _ => (Monoid.closure.is_submonoid _).mul_mem
        inv_mem := fun x hx =>
          Monoid.InClosure.rec_on hx
            (fun x hx =>
              Or.cases_on hx
                (fun hx =>
                  Monoid.subset_closure <| Or.inr <| show x⁻¹⁻¹ ∈ s from (inv_inv x).symm ▸ hx)
                fun hx => Monoid.subset_closure <| Or.inl hx)
            ((@inv_one G _).symm ▸ IsSubmonoid.one_mem (Monoid.closure.is_submonoid _))
            fun x y hx hy ihx ihy =>
            (mul_inv_rev x y).symm ▸ IsSubmonoid.mul_mem (Monoid.closure.is_submonoid _) ihy ihx }
      (Set.Subset.trans (Set.subset_union_left _ _) Monoid.subset_closure))
    (Monoid.closure_subset (closure.is_subgroup _).to_is_submonoid <|
      (Set.union_subset subset_closure) fun x hx =>
        inv_inv x ▸ (IsSubgroup.inv_mem (closure.is_subgroup _) <| subset_closure hx))
#align group.closure_eq_mclosure Group.closure_eq_mclosure

@[to_additive]
theorem mem_closure_union_iff {G : Type _} [CommGroup G] {s t : Set G} {x : G} :
    x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y * z = x :=
  by
  simp only [closure_eq_mclosure, Monoid.mem_closure_union_iff, exists_prop, preimage_union];
  constructor
  · rintro ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, rfl⟩
    refine' ⟨_, ⟨_, hys, _, hzs, rfl⟩, _, ⟨_, hyt, _, hzt, rfl⟩, _⟩
    rw [mul_assoc, mul_assoc, mul_left_comm zs]
  · rintro ⟨_, ⟨ys, hys, zs, hzs, rfl⟩, _, ⟨yt, hyt, zt, hzt, rfl⟩, rfl⟩
    refine' ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, _⟩
    rw [mul_assoc, mul_assoc, mul_left_comm yt]
#align group.mem_closure_union_iff Group.mem_closure_union_iff

end Group

namespace IsSubgroup

variable [Group G]

@[to_additive]
theorem trivial_eq_closure : trivial G = Group.closure ∅ :=
  Subset.antisymm (by simp [Set.subset_def, (Group.closure.is_subgroup _).one_mem])
    (Group.closure_subset trivial_normal.to_is_subgroup <| by simp)
#align is_subgroup.trivial_eq_closure IsSubgroup.trivial_eq_closure

end IsSubgroup

/-The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/
namespace Group

variable {s : Set G} [Group G]

theorem conjugates_of_subset {t : Set G} (ht : IsNormalSubgroup t) {a : G} (h : a ∈ t) :
    conjugatesOf a ⊆ t := fun x hc =>
  by
  obtain ⟨c, w⟩ := isConj_iff.1 hc
  have H := IsNormalSubgroup.normal ht a h c
  rwa [← w]
#align group.conjugates_of_subset Group.conjugates_of_subset

theorem conjugates_of_set_subset' {s t : Set G} (ht : IsNormalSubgroup t) (h : s ⊆ t) :
    conjugatesOfSet s ⊆ t :=
  Set.unionᵢ₂_subset fun x H => conjugates_of_subset ht (h H)
#align group.conjugates_of_set_subset' Group.conjugates_of_set_subset'

/-- The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/
def normalClosure (s : Set G) : Set G :=
  closure (conjugatesOfSet s)
#align group.normal_closure Group.normalClosure

theorem conjugates_of_set_subset_normal_closure : conjugatesOfSet s ⊆ normalClosure s :=
  subset_closure
#align group.conjugates_of_set_subset_normal_closure Group.conjugates_of_set_subset_normal_closure

theorem subset_normal_closure : s ⊆ normalClosure s :=
  Set.Subset.trans subset_conjugates_of_set conjugates_of_set_subset_normal_closure
#align group.subset_normal_closure Group.subset_normal_closure

/-- The normal closure of a set is a subgroup. -/
theorem normalClosure.is_subgroup (s : Set G) : IsSubgroup (normalClosure s) :=
  closure.is_subgroup (conjugatesOfSet s)
#align group.normal_closure.is_subgroup Group.normalClosure.is_subgroup

/-- The normal closure of s is a normal subgroup. -/
theorem normalClosure.is_normal : IsNormalSubgroup (normalClosure s) :=
  { normalClosure.is_subgroup _ with
    Normal := fun n h g => by
      induction' h with x hx x hx ihx x y hx hy ihx ihy
      · exact conjugates_of_set_subset_normal_closure (conj_mem_conjugates_of_set hx)
      · simpa using (normal_closure.is_subgroup s).one_mem
      · rw [← conj_inv]
        exact (normal_closure.is_subgroup _).inv_mem ihx
      · rw [← conj_mul]
        exact (normal_closure.is_subgroup _).to_is_submonoid.mul_mem ihx ihy }
#align group.normal_closure.is_normal Group.normalClosure.is_normal

/-- The normal closure of s is the smallest normal subgroup containing s. -/
theorem normal_closure_subset {s t : Set G} (ht : IsNormalSubgroup t) (h : s ⊆ t) :
    normalClosure s ⊆ t := fun a w =>
  by
  induction' w with x hx x hx ihx x y hx hy ihx ihy
  · exact conjugates_of_set_subset' ht h <| hx
  · exact ht.to_is_subgroup.to_is_submonoid.one_mem
  · exact ht.to_is_subgroup.inv_mem ihx
  · exact ht.to_is_subgroup.to_is_submonoid.mul_mem ihx ihy
#align group.normal_closure_subset Group.normal_closure_subset

theorem normal_closure_subset_iff {s t : Set G} (ht : IsNormalSubgroup t) :
    s ⊆ t ↔ normalClosure s ⊆ t :=
  ⟨normal_closure_subset ht, Set.Subset.trans subset_normal_closure⟩
#align group.normal_closure_subset_iff Group.normal_closure_subset_iff

theorem normal_closure_mono {s t : Set G} : s ⊆ t → normalClosure s ⊆ normalClosure t := fun h =>
  normal_closure_subset normalClosure.is_normal (Set.Subset.trans h subset_normal_closure)
#align group.normal_closure_mono Group.normal_closure_mono

end Group

/-- Create a bundled subgroup from a set `s` and `[is_subgroup s]`. -/
@[to_additive "Create a bundled additive subgroup from a set `s` and `[is_add_subgroup s]`."]
def Subgroup.of [Group G] {s : Set G} (h : IsSubgroup s) : Subgroup G
    where
  carrier := s
  one_mem' := h.1.1
  mul_mem' _ _ := h.1.2
  inv_mem' _ := h.2
#align subgroup.of Subgroup.of

@[to_additive]
theorem Subgroup.is_subgroup [Group G] (K : Subgroup G) : IsSubgroup (K : Set G) :=
  { one_mem := K.one_mem'
    mul_mem := fun _ _ => K.mul_mem'
    inv_mem := fun _ => K.inv_mem' }
#align subgroup.is_subgroup Subgroup.is_subgroup

-- this will never fire if it's an instance
@[to_additive]
theorem Subgroup.of_normal [Group G] (s : Set G) (h : IsSubgroup s) (n : IsNormalSubgroup s) :
    Subgroup.Normal (Subgroup.of h) :=
  { conj_mem := n.Normal }
#align subgroup.of_normal Subgroup.of_normal

