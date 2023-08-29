/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Antichain
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Set.Intervals.Basic

#align_import order.minimal from "leanprover-community/mathlib"@"59694bd07f0a39c5beccba34bd9f413a160782bf"

/-!
# Minimal/maximal elements of a set

This file defines minimal and maximal of a set with respect to an arbitrary relation.

## Main declarations

* `maximals r s`: Maximal elements of `s` with respect to `r`.
* `minimals r s`: Minimal elements of `s` with respect to `r`.

## TODO

Do we need a `Finset` version?
-/

set_option autoImplicit true


open Function Set

variable {α : Type*} (r r₁ r₂ : α → α → Prop) (s t : Set α) (a b : α)

/-- Turns a set into an antichain by keeping only the "maximal" elements. -/
def maximals : Set α :=
  { a ∈ s | ∀ ⦃b⦄, b ∈ s → r a b → r b a }
#align maximals maximals

/-- Turns a set into an antichain by keeping only the "minimal" elements. -/
def minimals : Set α :=
  { a ∈ s | ∀ ⦃b⦄, b ∈ s → r b a → r a b }
#align minimals minimals

theorem maximals_subset : maximals r s ⊆ s :=
  sep_subset _ _
#align maximals_subset maximals_subset

theorem minimals_subset : minimals r s ⊆ s :=
  sep_subset _ _
#align minimals_subset minimals_subset

@[simp]
theorem maximals_empty : maximals r ∅ = ∅ :=
  sep_empty _
#align maximals_empty maximals_empty

@[simp]
theorem minimals_empty : minimals r ∅ = ∅ :=
  sep_empty _
#align minimals_empty minimals_empty

@[simp]
theorem maximals_singleton : maximals r {a} = {a} :=
  (maximals_subset _ _).antisymm <|
    singleton_subset_iff.2 <|
      ⟨rfl, by
        rintro b (rfl : b = a)
        -- ⊢ r b b → r b b
        exact id⟩
        -- 🎉 no goals
#align maximals_singleton maximals_singleton

@[simp]
theorem minimals_singleton : minimals r {a} = {a} :=
  maximals_singleton _ _
#align minimals_singleton minimals_singleton

theorem maximals_swap : maximals (swap r) s = minimals r s :=
  rfl
#align maximals_swap maximals_swap

theorem minimals_swap : minimals (swap r) s = maximals r s :=
  rfl
#align minimals_swap minimals_swap

section IsAntisymm

variable {r s t a b} [IsAntisymm α r]

theorem eq_of_mem_maximals (ha : a ∈ maximals r s) (hb : b ∈ s) (h : r a b) : a = b :=
  antisymm h <| ha.2 hb h
#align eq_of_mem_maximals eq_of_mem_maximals

theorem eq_of_mem_minimals (ha : a ∈ minimals r s) (hb : b ∈ s) (h : r b a) : a = b :=
  antisymm (ha.2 hb h) h
#align eq_of_mem_minimals eq_of_mem_minimals

theorem mem_maximals_iff : x ∈ maximals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r x y → x = y := by
  simp only [maximals, Set.mem_sep_iff, and_congr_right_iff]
  -- ⊢ x ∈ s → ((∀ ⦃b : α⦄, b ∈ s → r x b → r b x) ↔ ∀ ⦃y : α⦄, y ∈ s → r x y → x = …
  refine' fun _ ↦ ⟨fun h y hys hxy ↦ antisymm hxy (h hys hxy), fun h y hys hxy ↦ _⟩
  -- ⊢ r y x
  convert hxy <;> rw [h hys hxy]
  -- ⊢ y = x
                  -- 🎉 no goals
                  -- 🎉 no goals

theorem mem_maximals_setOf_iff : x ∈ maximals r (setOf P) ↔ P x ∧ ∀ ⦃y⦄, P y → r x y → x = y :=
  mem_maximals_iff

theorem mem_minimals_iff : x ∈ minimals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r y x → x = y :=
  @mem_maximals_iff _ _ _ (IsAntisymm.swap r) _

theorem mem_minimals_setOf_iff : x ∈ minimals r (setOf P) ↔ P x ∧ ∀ ⦃y⦄, P y → r y x → x = y :=
  mem_minimals_iff

/-- This theorem can't be used to rewrite without specifying `rlt`, since `rlt` would have to be
  guessed. See `mem_minimals_iff_forall_ssubset_not_mem` and `mem_minimals_iff_forall_lt_not_mem`
  for `⊆` and `≤` versions.  -/
theorem mem_minimals_iff_forall_lt_not_mem' (rlt : α → α → Prop) [IsNonstrictStrictOrder α r rlt] :
    x ∈ minimals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, rlt y x → y ∉ s := by
  simp [minimals, right_iff_left_not_left_of r rlt, not_imp_not, imp.swap (a := _ ∈ _)]
  -- 🎉 no goals

theorem mem_maximals_iff_forall_lt_not_mem' (rlt : α → α → Prop) [IsNonstrictStrictOrder α r rlt] :
    x ∈ maximals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, rlt x y → y ∉ s := by
  simp [maximals, right_iff_left_not_left_of r rlt, not_imp_not, imp.swap (a := _ ∈ _)]
  -- 🎉 no goals

theorem minimals_eq_minimals_of_subset_of_forall [IsTrans α r] (hts : t ⊆ s)
    (h : ∀ x ∈ s, ∃ y ∈ t, r y x) : minimals r s = minimals r t := by
  refine Set.ext fun a ↦ ⟨fun ⟨has, hmin⟩ ↦ ⟨?_,fun b hbt ↦ hmin (hts hbt)⟩,
    fun ⟨hat, hmin⟩ ↦ ⟨hts hat, fun b hbs hba ↦ ?_⟩⟩
  · obtain ⟨a', ha', haa'⟩ := h _ has
    -- ⊢ a ∈ t
    rwa [antisymm (hmin (hts ha') haa') haa']
    -- 🎉 no goals
  obtain ⟨b', hb't, hb'b⟩ := h b hbs
  -- ⊢ r a b
  rwa [antisymm (hmin hb't (Trans.trans hb'b hba)) (Trans.trans hb'b hba)]
  -- 🎉 no goals

theorem maximals_eq_maximals_of_subset_of_forall [IsTrans α r] (hts : t ⊆ s)
    (h : ∀ x ∈ s, ∃ y ∈ t, r x y) : maximals r s = maximals r t :=
  @minimals_eq_minimals_of_subset_of_forall _ _ _ _ (IsAntisymm.swap r) (IsTrans.swap r) hts h

variable (r s)

theorem maximals_antichain : IsAntichain r (maximals r s) := fun _a ha _b hb hab h =>
  hab <| eq_of_mem_maximals ha hb.1 h
#align maximals_antichain maximals_antichain

theorem minimals_antichain : IsAntichain r (minimals r s) :=
  haveI := IsAntisymm.swap r
  (maximals_antichain _ _).swap
#align minimals_antichain minimals_antichain

end IsAntisymm

theorem mem_minimals_iff_forall_ssubset_not_mem (s : Set (Set α)) :
    x ∈ minimals (· ⊆ ·) s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ⊂ x → y ∉ s :=
  mem_minimals_iff_forall_lt_not_mem' (· ⊂ ·)

theorem mem_minimals_iff_forall_lt_not_mem [PartialOrder α] {s : Set α} :
    x ∈ minimals (· ≤ ·) s ↔ x ∈ s ∧ ∀ ⦃y⦄, y < x → y ∉ s :=
  mem_minimals_iff_forall_lt_not_mem' (· < ·)

theorem mem_maximals_iff_forall_ssubset_not_mem {s : Set (Set α)} :
    x ∈ maximals (· ⊆ ·) s ↔ x ∈ s ∧ ∀ ⦃y⦄, x ⊂ y → y ∉ s :=
  mem_maximals_iff_forall_lt_not_mem' (· ⊂ ·)

theorem mem_maximals_iff_forall_lt_not_mem [PartialOrder α] {s : Set α} :
    x ∈ maximals (· ≤ ·) s ↔ x ∈ s ∧ ∀ ⦃y⦄, x < y → y ∉ s :=
  mem_maximals_iff_forall_lt_not_mem' (· < ·)

-- porting note: new theorem
theorem maximals_of_symm [IsSymm α r] : maximals r s = s :=
  sep_eq_self_iff_mem_true.2 <| fun _ _ _ _ => symm

-- porting note: new theorem
theorem minimals_of_symm [IsSymm α r] : minimals r s = s :=
  sep_eq_self_iff_mem_true.2 <| fun _ _ _ _ => symm

theorem maximals_eq_minimals [IsSymm α r] : maximals r s = minimals r s := by
  rw [minimals_of_symm, maximals_of_symm]
  -- 🎉 no goals
#align maximals_eq_minimals maximals_eq_minimals

variable {r r₁ r₂ s t a}

-- porting note: todo: use `h.induction_on`
theorem Set.Subsingleton.maximals_eq (h : s.Subsingleton) : maximals r s = s := by
  rcases h.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
  -- ⊢ maximals r ∅ = ∅
  exacts [minimals_empty _, maximals_singleton _ _]
  -- 🎉 no goals
#align set.subsingleton.maximals_eq Set.Subsingleton.maximals_eq

theorem Set.Subsingleton.minimals_eq (h : s.Subsingleton) : minimals r s = s :=
  h.maximals_eq
#align set.subsingleton.minimals_eq Set.Subsingleton.minimals_eq

theorem maximals_mono [IsAntisymm α r₂] (h : ∀ a b, r₁ a b → r₂ a b) :
    maximals r₂ s ⊆ maximals r₁ s := fun a ha =>
  ⟨ha.1, fun b hb hab => by
    have := eq_of_mem_maximals ha hb (h _ _ hab)
    -- ⊢ r₁ b a
    subst this
    -- ⊢ r₁ a a
    exact hab⟩
    -- 🎉 no goals
#align maximals_mono maximals_mono

theorem minimals_mono [IsAntisymm α r₂] (h : ∀ a b, r₁ a b → r₂ a b) :
    minimals r₂ s ⊆ minimals r₁ s := fun a ha =>
  ⟨ha.1, fun b hb hab => by
    have := eq_of_mem_minimals ha hb (h _ _ hab)
    -- ⊢ r₁ a b
    subst this
    -- ⊢ r₁ a a
    exact hab⟩
    -- 🎉 no goals
#align minimals_mono minimals_mono

theorem maximals_union : maximals r (s ∪ t) ⊆ maximals r s ∪ maximals r t := by
  intro a ha
  -- ⊢ a ∈ maximals r s ∪ maximals r t
  obtain h | h := ha.1
  -- ⊢ a ∈ maximals r s ∪ maximals r t
  · exact Or.inl ⟨h, fun b hb => ha.2 <| Or.inl hb⟩
    -- 🎉 no goals
  · exact Or.inr ⟨h, fun b hb => ha.2 <| Or.inr hb⟩
    -- 🎉 no goals
#align maximals_union maximals_union

theorem minimals_union : minimals r (s ∪ t) ⊆ minimals r s ∪ minimals r t :=
  maximals_union
#align minimals_union minimals_union

theorem maximals_inter_subset : maximals r s ∩ t ⊆ maximals r (s ∩ t) := fun _a ha =>
  ⟨⟨ha.1.1, ha.2⟩, fun _b hb => ha.1.2 hb.1⟩
#align maximals_inter_subset maximals_inter_subset

theorem minimals_inter_subset : minimals r s ∩ t ⊆ minimals r (s ∩ t) :=
  maximals_inter_subset
#align minimals_inter_subset minimals_inter_subset

theorem inter_maximals_subset : s ∩ maximals r t ⊆ maximals r (s ∩ t) := fun _a ha =>
  ⟨⟨ha.1, ha.2.1⟩, fun _b hb => ha.2.2 hb.2⟩
#align inter_maximals_subset inter_maximals_subset

theorem inter_minimals_subset : s ∩ minimals r t ⊆ minimals r (s ∩ t) :=
  inter_maximals_subset
#align inter_minimals_subset inter_minimals_subset

theorem IsAntichain.maximals_eq (h : IsAntichain r s) : maximals r s = s :=
  (maximals_subset _ _).antisymm fun a ha =>
    ⟨ha, fun b hb hab => by
      obtain rfl := h.eq ha hb hab
      -- ⊢ r a a
      exact hab⟩
      -- 🎉 no goals
#align is_antichain.maximals_eq IsAntichain.maximals_eq

theorem IsAntichain.minimals_eq (h : IsAntichain r s) : minimals r s = s :=
  h.flip.maximals_eq
#align is_antichain.minimals_eq IsAntichain.minimals_eq

@[simp]
theorem maximals_idem : maximals r (maximals r s) = maximals r s :=
  (maximals_subset _ _).antisymm fun _a ha => ⟨ha, fun _b hb => ha.2 hb.1⟩
#align maximals_idem maximals_idem

@[simp]
theorem minimals_idem : minimals r (minimals r s) = minimals r s :=
  maximals_idem
#align minimals_idem minimals_idem

/-- If `maximals r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
theorem IsAntichain.max_maximals (ht : IsAntichain r t) (h : maximals r s ⊆ t)
    (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ maximals r s, r b a) : maximals r s = t := by
  refine' h.antisymm fun a ha => _
  -- ⊢ a ∈ maximals r s
  obtain ⟨b, hb, hr⟩ := hs ha
  -- ⊢ a ∈ maximals r s
  rwa [of_not_not fun hab => ht (h hb) ha (Ne.symm hab) hr]
  -- 🎉 no goals
#align is_antichain.max_maximals IsAntichain.max_maximals

/-- If `minimals r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
theorem IsAntichain.max_minimals (ht : IsAntichain r t) (h : minimals r s ⊆ t)
    (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ minimals r s, r a b) : minimals r s = t := by
  refine' h.antisymm fun a ha => _
  -- ⊢ a ∈ minimals r s
  obtain ⟨b, hb, hr⟩ := hs ha
  -- ⊢ a ∈ minimals r s
  rwa [of_not_not fun hab => ht ha (h hb) hab hr]
  -- 🎉 no goals
#align is_antichain.max_minimals IsAntichain.max_minimals

variable [PartialOrder α]

theorem IsLeast.mem_minimals (h : IsLeast s a) : a ∈ minimals (· ≤ ·) s :=
  ⟨h.1, fun _b hb _ => h.2 hb⟩
#align is_least.mem_minimals IsLeast.mem_minimals

theorem IsGreatest.mem_maximals (h : IsGreatest s a) : a ∈ maximals (· ≤ ·) s :=
  ⟨h.1, fun _b hb _ => h.2 hb⟩
#align is_greatest.mem_maximals IsGreatest.mem_maximals

theorem IsLeast.minimals_eq (h : IsLeast s a) : minimals (· ≤ ·) s = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨h.mem_minimals, fun _b hb => eq_of_mem_minimals hb h.1 <| h.2 hb.1⟩
#align is_least.minimals_eq IsLeast.minimals_eq

theorem IsGreatest.maximals_eq (h : IsGreatest s a) : maximals (· ≤ ·) s = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨h.mem_maximals, fun _b hb => eq_of_mem_maximals hb h.1 <| h.2 hb.1⟩
#align is_greatest.maximals_eq IsGreatest.maximals_eq

theorem IsAntichain.minimals_upperClosure (hs : IsAntichain (· ≤ ·) s) :
    minimals (· ≤ ·) (upperClosure s : Set α) = s :=
  hs.max_minimals
    (fun a ⟨⟨b, hb, hba⟩, _⟩ => by rwa [eq_of_mem_minimals ‹a ∈ _› (subset_upperClosure hb) hba])
                                   -- 🎉 no goals
    fun a ha =>
    ⟨a, ⟨subset_upperClosure ha, fun b ⟨c, hc, hcb⟩ hba => by rwa [hs.eq' ha hc (hcb.trans hba)]⟩,
                                                              -- 🎉 no goals
      le_rfl⟩
#align is_antichain.minimals_upper_closure IsAntichain.minimals_upperClosure

theorem IsAntichain.maximals_lowerClosure (hs : IsAntichain (· ≤ ·) s) :
    maximals (· ≤ ·) (lowerClosure s : Set α) = s :=
  hs.to_dual.minimals_upperClosure
#align is_antichain.maximals_lower_closure IsAntichain.maximals_lowerClosure

section Image

variable {f : α → β} {r : α → α → Prop} {s : β → β → Prop}

theorem minimals_image_of_rel_iff_rel (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) :
    minimals s (f '' x) = f '' (minimals r x) := by
  ext a
  -- ⊢ a ∈ minimals s (f '' x) ↔ a ∈ f '' minimals r x
  simp only [minimals, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  -- ⊢ a ∈ {a | (∃ x_1, x_1 ∈ x ∧ f x_1 = a) ∧ ∀ (a_1 : α), a_1 ∈ x → s (f a_1) a → …
  constructor
  -- ⊢ a ∈ {a | (∃ x_1, x_1 ∈ x ∧ f x_1 = a) ∧ ∀ (a_1 : α), a_1 ∈ x → s (f a_1) a → …
  · rintro ⟨⟨a, ha, rfl⟩ , h⟩
    -- ⊢ ∃ x_1, x_1 ∈ {a | a ∈ x ∧ ∀ ⦃b : α⦄, b ∈ x → r b a → r a b} ∧ f x_1 = f a
    exact ⟨a, ⟨ha, fun y hy hya ↦ (hf ha hy).mpr (h _ hy ((hf hy ha).mp hya))⟩, rfl⟩
    -- 🎉 no goals
  rintro ⟨a,⟨⟨ha,h⟩,rfl⟩⟩
  -- ⊢ f a ∈ {a | (∃ x_1, x_1 ∈ x ∧ f x_1 = a) ∧ ∀ (a_1 : α), a_1 ∈ x → s (f a_1) a …
  exact ⟨⟨_, ha, rfl⟩, fun y hy hya ↦ (hf ha hy).mp (h hy ((hf hy ha).mpr hya))⟩
  -- 🎉 no goals

theorem maximals_image_of_rel_iff_rel_on
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) :
    maximals s (f '' x) = f '' (maximals r x) :=
  minimals_image_of_rel_iff_rel (fun _ _ a_1 a_2 ↦ hf a_2 a_1)

theorem RelEmbedding.minimals_image_eq (f : r ↪r s) (x : Set α) :
    minimals s (f '' x) = f '' (minimals r x) := by
  rw [minimals_image_of_rel_iff_rel]; simp [f.map_rel_iff]
  -- ⊢ ∀ ⦃a a' : α⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (↑f a) (↑f a'))
                                      -- 🎉 no goals

theorem RelEmbedding.maximals_image_eq (f : r ↪r s) (x : Set α) :
    maximals s (f '' x) = f '' (maximals r x) :=
  (f.swap).minimals_image_eq x

theorem inter_minimals_preimage_inter_eq_of_rel_iff_rel_on
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (y : Set β) :
    x ∩ f ⁻¹' (minimals s ((f '' x) ∩ y)) = minimals r (x ∩ f ⁻¹' y) := by
  ext a
  -- ⊢ a ∈ x ∩ f ⁻¹' minimals s (f '' x ∩ y) ↔ a ∈ minimals r (x ∩ f ⁻¹' y)
  simp only [minimals, mem_inter_iff, mem_image, and_imp, forall_exists_index,
    forall_apply_eq_imp_iff₂, preimage_setOf_eq, mem_setOf_eq, mem_preimage]
  exact ⟨fun ⟨hax,⟨_,hay⟩,h2⟩ ↦ ⟨⟨hax, hay⟩, fun a₁ ha₁ ha₁y ha₁a ↦
          (hf hax ha₁).mpr (h2 _ ha₁ ha₁y ((hf ha₁ hax).mp ha₁a))⟩ ,
        fun ⟨⟨hax,hay⟩,h⟩ ↦ ⟨hax, ⟨⟨_, hax, rfl⟩, hay⟩, fun a' ha' ha'y hsa' ↦
          (hf hax ha').mp (h ha' ha'y ((hf ha' hax).mpr hsa'))⟩⟩

theorem inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (hy : y ⊆ f '' x) :
    x ∩ f ⁻¹' (minimals s y) = minimals r (x ∩ f ⁻¹' y) := by
  rw [←inter_eq_self_of_subset_right hy, inter_minimals_preimage_inter_eq_of_rel_iff_rel_on hf,
    preimage_inter, ←inter_assoc, inter_eq_self_of_subset_left (subset_preimage_image f x)]

theorem RelEmbedding.inter_preimage_minimals_eq (f : r ↪r s) (x : Set α) (y : Set β) :
    x ∩ f⁻¹' (minimals s ((f '' x) ∩ y)) = minimals r (x ∩ f ⁻¹' y) :=
  inter_minimals_preimage_inter_eq_of_rel_iff_rel_on (by simp [f.map_rel_iff]) y
                                                         -- 🎉 no goals

theorem RelEmbedding.inter_preimage_minimals_eq_of_subset (f : r ↪r s) (h : y ⊆ f '' x) :
    x ∩ f ⁻¹' (minimals s y) = minimals r (x ∩ f ⁻¹' y) := by
  rw [inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset _ h]; simp [f.map_rel_iff]
  -- ⊢ ∀ ⦃a a' : α⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (↑f a) (↑f a'))
                                                                   -- 🎉 no goals

theorem RelEmbedding.minimals_preimage_eq (f : r ↪r s) (y : Set β) :
  minimals r (f ⁻¹' y) = f ⁻¹' minimals s (y ∩ range f) := by
  convert (f.inter_preimage_minimals_eq univ y).symm; simp [univ_inter]; simp [inter_comm]
  -- ⊢ ↑f ⁻¹' y = univ ∩ ↑f ⁻¹' y
                                                      -- ⊢ ↑f ⁻¹' minimals s (y ∩ range ↑f) = univ ∩ ↑f ⁻¹' minimals s (↑f '' univ ∩ y)
                                                                         -- 🎉 no goals

theorem inter_maximals_preimage_inter_eq_of_rel_iff_rel_on
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (y : Set β) :
    x ∩ f ⁻¹' (maximals s ((f '' x) ∩ y)) = maximals r (x ∩ f ⁻¹' y) := by
  apply inter_minimals_preimage_inter_eq_of_rel_iff_rel_on
  -- ⊢ ∀ ⦃a a' : α⦄, a ∈ x → a' ∈ x → (r a' a ↔ s (f a') (f a))
  exact fun _ _ a b ↦ hf b a
  -- 🎉 no goals

theorem inter_preimage_maximals_eq_of_rel_iff_rel_on_of_subset
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (hy : y ⊆ f '' x) :
    x ∩ f ⁻¹' (maximals s y) = maximals r (x ∩ f ⁻¹' y) := by
  apply inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset _ hy
  -- ⊢ ∀ ⦃a a' : α⦄, a ∈ x → a' ∈ x → (r a' a ↔ s (f a') (f a))
  exact fun _ _ a b ↦ hf b a
  -- 🎉 no goals

theorem RelEmbedding.inter_preimage_maximals_eq (f : r ↪r s) (x : Set α) (y : Set β) :
    x ∩ f⁻¹' (maximals s ((f '' x) ∩ y)) = maximals r (x ∩ f ⁻¹' y) :=
  inter_minimals_preimage_inter_eq_of_rel_iff_rel_on (by simp [f.map_rel_iff]) y
                                                         -- 🎉 no goals

theorem RelEmbedding.inter_preimage_maximals_eq_of_subset (f : r ↪r s) (h : y ⊆ f '' x) :
    x ∩ f ⁻¹' (maximals s y) = maximals r (x ∩ f ⁻¹' y) := by
  rw [inter_preimage_maximals_eq_of_rel_iff_rel_on_of_subset _ h]; simp [f.map_rel_iff]
  -- ⊢ ∀ ⦃a a' : α⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (↑f a) (↑f a'))
                                                                   -- 🎉 no goals

theorem RelEmbedding.maximals_preimage_eq (f : r ↪r s) (y : Set β) :
    maximals r (f ⁻¹' y) = f ⁻¹' maximals s (y ∩ range f) := by
  convert (f.inter_preimage_maximals_eq univ y).symm; simp [univ_inter]; simp [inter_comm]
  -- ⊢ ↑f ⁻¹' y = univ ∩ ↑f ⁻¹' y
                                                      -- ⊢ ↑f ⁻¹' maximals s (y ∩ range ↑f) = univ ∩ ↑f ⁻¹' maximals s (↑f '' univ ∩ y)
                                                                         -- 🎉 no goals

end Image

section Interval

variable [PartialOrder α] {a b : α}

@[simp] theorem maximals_Iic (a : α) : maximals (· ≤ ·) (Iic a) = {a} :=
  Set.ext fun _ ↦ ⟨fun h ↦ h.1.antisymm (h.2 rfl.le h.1),
    fun h ↦ ⟨h.trans_le rfl.le, fun _ hba _ ↦ le_trans hba h.symm.le⟩⟩

@[simp] theorem minimals_Ici (a : α) : minimals (· ≤ ·) (Ici a) = {a} :=
  maximals_Iic (α := αᵒᵈ) a

theorem maximals_Icc (hab : a ≤ b) : maximals (· ≤ ·) (Icc a b) = {b} :=
  Set.ext fun x ↦ ⟨fun h ↦ h.1.2.antisymm (h.2 ⟨hab, rfl.le⟩ h.1.2),
    fun (h : x = b) ↦ ⟨⟨hab.trans_eq h.symm, h.le⟩, fun _ hy _ ↦ hy.2.trans_eq h.symm⟩⟩

theorem minimals_Icc (hab : a ≤ b) : minimals (· ≤ ·) (Icc a b) = {a} := by
  simp_rw [Icc, and_comm (a := (a ≤ _))]; exact maximals_Icc (α := αᵒᵈ) hab
  -- ⊢ minimals (fun x x_1 => x ≤ x_1) {x | x ≤ b ∧ a ≤ x} = {a}
                                          -- 🎉 no goals

theorem maximals_Ioc (hab : a < b) : maximals (· ≤ ·) (Ioc a b) = {b} :=
  Set.ext fun x ↦ ⟨fun h ↦ h.1.2.antisymm (h.2 ⟨hab, rfl.le⟩ h.1.2),
    fun (h : x = b) ↦ ⟨⟨hab.trans_eq h.symm, h.le⟩, fun _ hy _ ↦ hy.2.trans_eq h.symm⟩⟩

theorem minimals_Ico (hab : a < b) : minimals (· ≤ ·) (Ico a b) = {a} := by
  simp_rw [Ico, and_comm (a := _ ≤ _)]; exact maximals_Ioc (α := αᵒᵈ) hab
  -- ⊢ minimals (fun x x_1 => x ≤ x_1) {x | x < b ∧ a ≤ x} = {a}
                                        -- 🎉 no goals

end Interval
