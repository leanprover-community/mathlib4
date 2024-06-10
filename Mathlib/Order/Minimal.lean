/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Antichain
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.RelIso.Set

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
        exact id⟩
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

set_option autoImplicit true

theorem mem_maximals_iff : x ∈ maximals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r x y → x = y := by
  simp only [maximals, Set.mem_sep_iff, and_congr_right_iff]
  refine fun _ ↦ ⟨fun h y hys hxy ↦ antisymm hxy (h hys hxy), fun h y hys hxy ↦ ?_⟩
  convert hxy <;> rw [h hys hxy]

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

theorem mem_maximals_iff_forall_lt_not_mem' (rlt : α → α → Prop) [IsNonstrictStrictOrder α r rlt] :
    x ∈ maximals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, rlt x y → y ∉ s := by
  simp [maximals, right_iff_left_not_left_of r rlt, not_imp_not, imp.swap (a := _ ∈ _)]

theorem minimals_eq_minimals_of_subset_of_forall [IsTrans α r] (hts : t ⊆ s)
    (h : ∀ x ∈ s, ∃ y ∈ t, r y x) : minimals r s = minimals r t := by
  refine Set.ext fun a ↦ ⟨fun ⟨has, hmin⟩ ↦ ⟨?_,fun b hbt ↦ hmin (hts hbt)⟩,
    fun ⟨hat, hmin⟩ ↦ ⟨hts hat, fun b hbs hba ↦ ?_⟩⟩
  · obtain ⟨a', ha', haa'⟩ := h _ has
    rwa [antisymm (hmin (hts ha') haa') haa']
  obtain ⟨b', hb't, hb'b⟩ := h b hbs
  rwa [antisymm (hmin hb't (Trans.trans hb'b hba)) (Trans.trans hb'b hba)]

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

set_option autoImplicit true

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

-- Porting note (#10756): new theorem
theorem maximals_of_symm [IsSymm α r] : maximals r s = s :=
  sep_eq_self_iff_mem_true.2 fun _ _ _ _ => symm

-- Porting note (#10756): new theorem
theorem minimals_of_symm [IsSymm α r] : minimals r s = s :=
  sep_eq_self_iff_mem_true.2 fun _ _ _ _ => symm

theorem maximals_eq_minimals [IsSymm α r] : maximals r s = minimals r s := by
  rw [minimals_of_symm, maximals_of_symm]
#align maximals_eq_minimals maximals_eq_minimals

variable {r r₁ r₂ s t a}

-- Porting note (#11215): TODO: use `h.induction_on`
theorem Set.Subsingleton.maximals_eq (h : s.Subsingleton) : maximals r s = s := by
  rcases h.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
  exacts [minimals_empty _, maximals_singleton _ _]
#align set.subsingleton.maximals_eq Set.Subsingleton.maximals_eq

theorem Set.Subsingleton.minimals_eq (h : s.Subsingleton) : minimals r s = s :=
  h.maximals_eq
#align set.subsingleton.minimals_eq Set.Subsingleton.minimals_eq

theorem maximals_mono [IsAntisymm α r₂] (h : ∀ a b, r₁ a b → r₂ a b) :
    maximals r₂ s ⊆ maximals r₁ s := fun a ha =>
  ⟨ha.1, fun b hb hab => by
    have := eq_of_mem_maximals ha hb (h _ _ hab)
    subst this
    exact hab⟩
#align maximals_mono maximals_mono

theorem minimals_mono [IsAntisymm α r₂] (h : ∀ a b, r₁ a b → r₂ a b) :
    minimals r₂ s ⊆ minimals r₁ s := fun a ha =>
  ⟨ha.1, fun b hb hab => by
    have := eq_of_mem_minimals ha hb (h _ _ hab)
    subst this
    exact hab⟩
#align minimals_mono minimals_mono

theorem maximals_union : maximals r (s ∪ t) ⊆ maximals r s ∪ maximals r t := by
  intro a ha
  obtain h | h := ha.1
  · exact Or.inl ⟨h, fun b hb => ha.2 <| Or.inl hb⟩
  · exact Or.inr ⟨h, fun b hb => ha.2 <| Or.inr hb⟩
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
      exact hab⟩
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
  refine h.antisymm fun a ha => ?_
  obtain ⟨b, hb, hr⟩ := hs ha
  rwa [of_not_not fun hab => ht (h hb) ha (Ne.symm hab) hr]
#align is_antichain.max_maximals IsAntichain.max_maximals

/-- If `minimals r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
theorem IsAntichain.max_minimals (ht : IsAntichain r t) (h : minimals r s ⊆ t)
    (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ minimals r s, r a b) : minimals r s = t := by
  refine h.antisymm fun a ha => ?_
  obtain ⟨b, hb, hr⟩ := hs ha
  rwa [of_not_not fun hab => ht ha (h hb) hab hr]
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
    fun a ha =>
    ⟨a, ⟨subset_upperClosure ha, fun b ⟨c, hc, hcb⟩ hba => by rwa [hs.eq' ha hc (hcb.trans hba)]⟩,
      le_rfl⟩
#align is_antichain.minimals_upper_closure IsAntichain.minimals_upperClosure

theorem IsAntichain.maximals_lowerClosure (hs : IsAntichain (· ≤ ·) s) :
    maximals (· ≤ ·) (lowerClosure s : Set α) = s :=
  hs.to_dual.minimals_upperClosure
#align is_antichain.maximals_lower_closure IsAntichain.maximals_lowerClosure

section Image

variable {f : α → β} {r : α → α → Prop} {s : β → β → Prop}

section
variable {x : Set α} (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) {a : α}

theorem map_mem_minimals (ha : a ∈ minimals r x) : f a ∈ minimals s (f '' x) :=
  ⟨⟨a, ha.1, rfl⟩, by rintro _ ⟨a', h', rfl⟩; rw [← hf ha.1 h', ← hf h' ha.1]; exact ha.2 h'⟩

theorem map_mem_maximals (ha : a ∈ maximals r x) : f a ∈ maximals s (f '' x) :=
  map_mem_minimals (fun _ _ h₁ h₂ ↦ by exact hf h₂ h₁) ha

theorem map_mem_minimals_iff (ha : a ∈ x) : f a ∈ minimals s (f '' x) ↔ a ∈ minimals r x :=
  ⟨fun ⟨_, hmin⟩ ↦ ⟨ha, fun a' h' ↦ by
    simpa only [hf h' ha, hf ha h'] using hmin ⟨a', h', rfl⟩⟩, map_mem_minimals hf⟩

theorem map_mem_maximals_iff (ha : a ∈ x) : f a ∈ maximals s (f '' x) ↔ a ∈ maximals r x :=
  map_mem_minimals_iff (fun _ _ h₁ h₂ ↦ by exact hf h₂ h₁) ha

theorem image_minimals_of_rel_iff_rel : f '' minimals r x = minimals s (f '' x) := by
  ext b; refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨a, ha, rfl⟩; exact map_mem_minimals hf ha
  · obtain ⟨a, ha, rfl⟩ := h.1; exact ⟨a, (map_mem_minimals_iff hf ha).mp h, rfl⟩

theorem image_maximals_of_rel_iff_rel : f '' maximals r x = maximals s (f '' x) :=
  image_minimals_of_rel_iff_rel fun _ _ h₁ h₂ ↦ hf h₂ h₁

end

theorem RelEmbedding.image_minimals_eq (f : r ↪r s) (x : Set α) :
    f '' minimals r x = minimals s (f '' x) := by
  rw [image_minimals_of_rel_iff_rel]; simp [f.map_rel_iff]

theorem RelEmbedding.image_maximals_eq (f : r ↪r s) (x : Set α) :
    f '' maximals r x = maximals s (f '' x) :=
  f.swap.image_minimals_eq x

section

variable [LE α] [LE β] {s : Set α} {t : Set β}

theorem image_minimals_univ :
    Subtype.val '' minimals (· ≤ ·) (univ : Set s) = minimals (· ≤ ·) s := by
  rw [image_minimals_of_rel_iff_rel, image_univ, Subtype.range_val]; intros; rfl

theorem image_maximals_univ :
    Subtype.val '' maximals (· ≤ ·) (univ : Set s) = maximals (· ≤ ·) s :=
  image_minimals_univ (α := αᵒᵈ)

nonrec theorem OrderIso.map_mem_minimals (f : s ≃o t) {x : α}
    (hx : x ∈ minimals (· ≤ ·) s) : (f ⟨x, hx.1⟩).val ∈ minimals (· ≤ ·) t := by
  rw [← image_minimals_univ] at hx
  obtain ⟨x, h, rfl⟩ := hx
  convert map_mem_minimals (f := Subtype.val ∘ f) (fun _ _ _ _ ↦ f.map_rel_iff.symm) h
  rw [image_comp, image_univ, f.range_eq, image_univ, Subtype.range_val]

theorem OrderIso.map_mem_maximals (f : s ≃o t) {x : α}
    (hx : x ∈ maximals (· ≤ ·) s) : (f ⟨x, hx.1⟩).val ∈ maximals (· ≤ ·) t :=
  (show OrderDual.ofDual ⁻¹' s ≃o OrderDual.ofDual ⁻¹' t from f.dual).map_mem_minimals hx

/-- If two sets are order isomorphic, their minimals are also order isomorphic. -/
def OrderIso.mapMinimals (f : s ≃o t) : minimals (· ≤ ·) s ≃o minimals (· ≤ ·) t where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_mem_minimals x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_mem_minimals x.2⟩
  left_inv x := Subtype.ext (by apply congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩)
  right_inv x := Subtype.ext (by apply congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩)
  map_rel_iff' {_ _} := f.map_rel_iff

/-- If two sets are order isomorphic, their maximals are also order isomorphic. -/
def OrderIso.mapMaximals (f : s ≃o t) : maximals (· ≤ ·) s ≃o maximals (· ≤ ·) t where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_mem_maximals x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_mem_maximals x.2⟩
  __ := (show OrderDual.ofDual ⁻¹' s ≃o OrderDual.ofDual ⁻¹' t from f.dual).mapMinimals
  -- defeq abuse to fill in the proof fields.
  -- If OrderDual ever becomes a structure, just copy the last three lines from OrderIso.mapMinimals

open OrderDual in
/-- If two sets are antitonically order isomorphic, their minimals are too. -/
def OrderIso.minimalsIsoMaximals (f : s ≃o tᵒᵈ) :
    minimals (· ≤ ·) s ≃o (maximals (· ≤ ·) t)ᵒᵈ where
  toFun x := toDual ⟨↑(ofDual (f ⟨x, x.2.1⟩)), (show s ≃o ofDual ⁻¹' t from f).map_mem_minimals x.2⟩
  invFun x := ⟨f.symm (toDual ⟨_, (ofDual x).2.1⟩),
    (show ofDual ⁻¹' t ≃o s from f.symm).map_mem_minimals x.2⟩
  __ := (show s ≃o ofDual⁻¹' t from f).mapMinimals

open OrderDual in
/-- If two sets are antitonically order isomorphic, their minimals are too. -/
def OrderIso.maximalsIsoMinimals (f : s ≃o tᵒᵈ) :
    maximals (· ≤ ·) s ≃o (minimals (· ≤ ·) t)ᵒᵈ where
  toFun x := toDual ⟨↑(ofDual (f ⟨x, x.2.1⟩)), (show s ≃o ofDual ⁻¹' t from f).map_mem_maximals x.2⟩
  invFun x := ⟨f.symm (toDual ⟨_, (ofDual x).2.1⟩),
    (show ofDual ⁻¹' t ≃o s from f.symm).map_mem_maximals x.2⟩
  __ := (show s ≃o ofDual⁻¹' t from f).mapMaximals

end

theorem inter_minimals_preimage_inter_eq_of_rel_iff_rel_on
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (y : Set β) :
    x ∩ f ⁻¹' (minimals s ((f '' x) ∩ y)) = minimals r (x ∩ f ⁻¹' y) := by
  ext a
  simp only [minimals, mem_inter_iff, mem_image, and_imp, forall_exists_index,
    forall_apply_eq_imp_iff₂, preimage_setOf_eq, mem_setOf_eq, mem_preimage]
  exact ⟨fun ⟨hax,⟨_,hay⟩,h2⟩ ↦ ⟨⟨hax, hay⟩, fun a₁ ha₁ ha₁y ha₁a ↦
          (hf hax ha₁).mpr (h2 _ ha₁ ha₁y ((hf ha₁ hax).mp ha₁a))⟩ ,
        fun ⟨⟨hax,hay⟩,h⟩ ↦ ⟨hax, ⟨⟨_, hax, rfl⟩, hay⟩, fun a' ha' ha'y hsa' ↦
          (hf hax ha').mp (h ha' ha'y ((hf ha' hax).mpr hsa'))⟩⟩

theorem inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (hy : y ⊆ f '' x) :
    x ∩ f ⁻¹' (minimals s y) = minimals r (x ∩ f ⁻¹' y) := by
  rw [← inter_eq_self_of_subset_right hy, inter_minimals_preimage_inter_eq_of_rel_iff_rel_on hf,
    preimage_inter, ← inter_assoc, inter_eq_self_of_subset_left (subset_preimage_image f x)]

theorem RelEmbedding.inter_preimage_minimals_eq (f : r ↪r s) (x : Set α) (y : Set β) :
    x ∩ f⁻¹' (minimals s ((f '' x) ∩ y)) = minimals r (x ∩ f ⁻¹' y) :=
  inter_minimals_preimage_inter_eq_of_rel_iff_rel_on (by simp [f.map_rel_iff]) y

theorem RelEmbedding.inter_preimage_minimals_eq_of_subset (f : r ↪r s) (h : y ⊆ f '' x) :
    x ∩ f ⁻¹' (minimals s y) = minimals r (x ∩ f ⁻¹' y) := by
  rw [inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset _ h]; simp [f.map_rel_iff]

theorem RelEmbedding.minimals_preimage_eq (f : r ↪r s) (y : Set β) :
    minimals r (f ⁻¹' y) = f ⁻¹' minimals s (y ∩ range f) := by
  convert (f.inter_preimage_minimals_eq univ y).symm
  · simp [univ_inter]
  · simp [inter_comm]

theorem RelIso.minimals_preimage_eq (f : r ≃r s) (y : Set β) :
    minimals r (f ⁻¹' y) = f ⁻¹' (minimals s y) := by
  convert f.toRelEmbedding.minimals_preimage_eq y; simp

theorem RelIso.maximals_preimage_eq (f : r ≃r s) (y : Set β) :
    maximals r (f ⁻¹' y) = f ⁻¹' (maximals s y) :=
  f.swap.minimals_preimage_eq y

theorem inter_maximals_preimage_inter_eq_of_rel_iff_rel_on
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (y : Set β) :
    x ∩ f ⁻¹' (maximals s ((f '' x) ∩ y)) = maximals r (x ∩ f ⁻¹' y) := by
  apply inter_minimals_preimage_inter_eq_of_rel_iff_rel_on
  exact fun _ _ a b ↦ hf b a

theorem inter_preimage_maximals_eq_of_rel_iff_rel_on_of_subset
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (hy : y ⊆ f '' x) :
    x ∩ f ⁻¹' (maximals s y) = maximals r (x ∩ f ⁻¹' y) := by
  apply inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset _ hy
  exact fun _ _ a b ↦ hf b a

theorem RelEmbedding.inter_preimage_maximals_eq (f : r ↪r s) (x : Set α) (y : Set β) :
    x ∩ f⁻¹' (maximals s ((f '' x) ∩ y)) = maximals r (x ∩ f ⁻¹' y) :=
  inter_minimals_preimage_inter_eq_of_rel_iff_rel_on (by simp [f.map_rel_iff]) y

theorem RelEmbedding.inter_preimage_maximals_eq_of_subset (f : r ↪r s) (h : y ⊆ f '' x) :
    x ∩ f ⁻¹' (maximals s y) = maximals r (x ∩ f ⁻¹' y) := by
  rw [inter_preimage_maximals_eq_of_rel_iff_rel_on_of_subset _ h]; simp [f.map_rel_iff]

theorem RelEmbedding.maximals_preimage_eq (f : r ↪r s) (y : Set β) :
    maximals r (f ⁻¹' y) = f ⁻¹' maximals s (y ∩ range f) := by
  convert (f.inter_preimage_maximals_eq univ y).symm
  · simp [univ_inter]
  · simp [inter_comm]

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

theorem maximals_Ioc (hab : a < b) : maximals (· ≤ ·) (Ioc a b) = {b} :=
  Set.ext fun x ↦ ⟨fun h ↦ h.1.2.antisymm (h.2 ⟨hab, rfl.le⟩ h.1.2),
    fun (h : x = b) ↦ ⟨⟨hab.trans_eq h.symm, h.le⟩, fun _ hy _ ↦ hy.2.trans_eq h.symm⟩⟩

theorem minimals_Ico (hab : a < b) : minimals (· ≤ ·) (Ico a b) = {a} := by
  simp_rw [Ico, and_comm (a := _ ≤ _)]; exact maximals_Ioc (α := αᵒᵈ) hab

end Interval
