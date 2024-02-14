import Mathlib

set_option autoImplicit false

variable {α β : Type*}
variable {ι ι' : Sort*}

namespace Set

open Function

/-! ## `image_subset_iff` -/

/-- Without `subset_range_of_surjective`, `image_preimage_eq` and `image_subset_iff`
create a simp confluence issue. -/
example {f : α → β} (s t : Set β) (h : Surjective f) :
    f '' (f ⁻¹' s) ⊆ t ↔ f '' (f ⁻¹' s) ⊆ t := by
  conv =>
    congr
    · simp [h, -image_preimage_eq, -subset_range_of_surjective]
    · simp [h, -image_subset_iff, -subset_range_of_surjective]
  fail_if_success simpa [h, -subset_range_of_surjective]
  simp [h]

/-- Without `Nonempty.subset_preimage_const`, `Nonempty.image_const` and `image_subset_iff`
create a simp confluence issue. -/
example {s : Set α} (hs : Set.Nonempty s) (t : Set β) (a : β) :
    (fun _ => a) '' s ⊆ t ↔ (fun _ => a) '' s ⊆ t := by
  conv =>
    congr
    · simp [hs, -Nonempty.image_const, -Nonempty.subset_preimage_const]
    · simp [hs, -image_subset_iff, -Nonempty.subset_preimage_const]
  fail_if_success simpa [hs, -Nonempty.subset_preimage_const]
  simp [hs]

/-- Without `preimage_eq_univ_iff`, `image_univ` and `image_subset_iff`
create a simp confluence issue. -/
example {f : α → β} (s) : f '' univ ⊆ s ↔ f '' univ ⊆ s := by
  conv =>
    congr
    · simp [-image_univ, -preimage_eq_univ_iff]
    · simp [-image_subset_iff, -preimage_eq_univ_iff]
  fail_if_success simpa [-preimage_eq_univ_iff]
  simp

end Set

/-! ## `Set.mem_range` -/

namespace EquivLike

variable {E : Type*} [EquivLike E ι ι']

/-- Without `memRange_congr_left'`, `range_comp` and `Set.mem_range`
create a simp confluence issue. -/
example (f : ι' → α) (e : E) (x : α) :
    x ∈ Set.range (f ∘ ⇑e) ↔ x ∈ Set.range (f ∘ ⇑e) := by
  conv =>
    congr
    · simp [-range_comp, -memRange_congr_left']
    · simp [-Set.mem_range, -memRange_congr_left']
  fail_if_success simpa [-memRange_congr_left']
  simp

end EquivLike

namespace Quotient

variable {ι : Sort*}

/-- Without `exists_rep`, `Set.range_quotient_mk` and `Set.mem_range`
create a simp confluence issue. -/
example [s : Setoid α] {q : Quotient s} : q ∈ Set.range (⟦·⟧) ↔ q ∈ Set.range (⟦·⟧) := by
  conv =>
    congr
    · simp [-Set.range_quotient_mk, -Quotient.exists_rep]
    · simp [-Set.mem_range, -Quotient.exists_rep]
  fail_if_success simpa [-Quotient.exists_rep]
  simp

/-- Without `exists_rep'`, `Set.range_quotient_mk'` and `Set.mem_range`
create a simp confluence issue. -/
example {s : Setoid α} {q : Quotient s} : q ∈ Set.range Quotient.mk' ↔ q ∈ Set.range Quotient.mk' := by
  conv =>
    congr
    · simp [-Set.range_quotient_mk', -exists_rep']
    · simp [-Set.mem_range, -exists_rep']
  fail_if_success simpa [-exists_rep']
  simp

/-- Without `exists_rep''`, `Set.Quotient.range_mk''` and `Set.mem_range`
create a simp confluence issue. -/
example {s : Setoid α} {q : Quotient s} : q ∈ Set.range Quotient.mk'' ↔ q ∈ Set.range Quotient.mk'' := by
  conv =>
    congr
    · simp [-Set.Quotient.range_mk'', -exists_rep'']
    · simp [-Set.mem_range, -exists_rep'']
  fail_if_success simpa [-exists_rep'']
  simp

/-- Without `exists_lift_iff`, `Set.range_quotient_lift` and `Set.mem_range`
create a simp confluence issue. -/
example {f : ι → α} [s : Setoid ι] (hf : ∀ a b, a ≈ b → f a = f b) (x : α) :
    x ∈ Set.range (Quotient.lift f hf) ↔ x ∈ Set.range (Quotient.lift f hf) := by
  conv =>
    congr
    · simp [-Set.range_quotient_lift, -exists_lift_iff]
    · simp [-Set.mem_range, -exists_lift_iff]
  fail_if_success simpa [-exists_lift_iff]
  simp

/-- Without `exists_liftOn_iff`, `Set.range_quotient_lift_on'` and `Set.mem_range`
create a simp confluence issue. -/
example {f : ι → α} {s : Setoid ι} (hf : ∀ a b, Setoid.r a b → f a = f b) (x : α) :
    x ∈ Set.range (Quotient.liftOn' · f hf) ↔ x ∈ Set.range (Quotient.liftOn' · f hf) := by
  conv =>
    congr
    · simp [-Set.range_quotient_lift_on', -exists_liftOn'_iff]
    · simp [-Set.mem_range, -exists_liftOn'_iff]
  fail_if_success simpa [-exists_liftOn_iff]
  simp

end Quotient

namespace Quot

/-- Without `exists_lift_iff`, `Set.range_quot_lift` and `Set.mem_range`
create a simp confluence issue. -/
example {f : ι → α} {r : ι → ι → Prop} (hf : ∀ (x y : ι), r x y → f x = f y) (x : α) :
    x ∈ Set.range (Quot.lift f hf) ↔ x ∈ Set.range (Quot.lift f hf) := by
  conv =>
    congr
    · simp [-Set.range_quot_lift, -exists_lift_iff]
    · simp [-Set.mem_range, -exists_lift_iff]
  fail_if_success simpa [-exists_lift_iff]
  simp

end Quot

namespace Option

/-- Without `eq_none_or_exists_some_eq`, `Set.insert_none_range_some` and `Set.mem_range`
create a simp confluence issue. -/
example (x : Option α) :
    x ∈ insert none (Set.range some) ↔ x ∈ insert none (Set.range some) := by
  conv =>
    congr
    · simp [-Set.insert_none_range_some, -eq_none_or_exists_some_eq]
    · simp [-Set.mem_range, -eq_none_or_exists_some_eq]
  fail_if_success simpa [-eq_none_or_exists_some_eq]
  simp

/-- Without `forall_not_some_eq_iff_eq_none`, `Set.compl_range_some` and `Set.mem_range`
create a simp confluence issue. -/
example (α : Type*) (x : Option α) : x ∈ (Set.range some)ᶜ ↔ x ∈ (Set.range some)ᶜ := by
  conv =>
    congr
    · simp [-Set.compl_range_some, -forall_not_some_eq_iff_eq_none]
    · simp [-Set.mem_range, -forall_not_some_eq_iff_eq_none]
  fail_if_success simpa [-forall_not_some_eq_iff_eq_none]
  simp

/-- Without `ne_none_of_some_eq_iff_true`, `Set.range_some_inter_none` and `Set.mem_range`
create a simp confluence issue. -/
example (α : Type*) (x : Option α) : x ∈ Set.range some ∩ {none} ↔ x ∈ Set.range some ∩ {none} := by
  conv =>
    congr
    · simp [-Set.range_some_inter_none, -ne_none_of_some_eq_iff_true]
    · simp [-Set.mem_range, -ne_none_of_some_eq_iff_true]
  fail_if_success simpa [-ne_none_of_some_eq_iff_true]
  simp

end Option

namespace Sum

/-- Without `forall_inl_ne_iff`, `Set.compl_range_inl` and `Set.mem_range`
create a simp confluence issue. -/
example (x : α ⊕ β) : x ∈ (Set.range Sum.inl)ᶜ ↔ x ∈ (Set.range Sum.inl)ᶜ := by
  conv =>
    congr
    · simp [-Set.compl_range_inl, -forall_inl_ne_iff]
    · simp [-Set.mem_range, -forall_inl_ne_iff]
  fail_if_success simpa [-forall_inl_ne_iff]
  simp

/-- Without `forall_inr_ne_iff`, `Set.compl_range_inr` and `Set.mem_range`
create a simp confluence issue. -/
example (x : α ⊕ β) : x ∈ (Set.range Sum.inr)ᶜ ↔ x ∈ (Set.range Sum.inr)ᶜ := by
  conv =>
    congr
    · simp [-Set.compl_range_inr, -forall_inr_ne_iff]
    · simp [-Set.mem_range, -forall_inr_ne_iff]
  fail_if_success simpa [-forall_inr_ne_iff]
  simp

/-- Without `exists_inl_eq_or_exists_inr_eq`, `Set.range_inl_union_range_inr` and `Set.mem_range`
create a simp confluence issue. -/
example (x : α ⊕ β) :
    x ∈ Set.range Sum.inl ∪ Set.range Sum.inr ↔ x ∈ Set.range Sum.inl ∪ Set.range Sum.inr := by
  conv =>
    congr
    · simp [-Set.range_inl_union_range_inr, -exists_inl_eq_or_exists_inr_eq]
    · simp [-Set.mem_range, -exists_inl_eq_or_exists_inr_eq]
  fail_if_success simpa [-exists_inl_eq_or_exists_inr_eq]
  simp

/-- Without `exists_inr_eq_or_exists_inl_eq`, `Set.range_inr_union_range_inl` and `Set.mem_range`
create a simp confluence issue. -/
example (x : α ⊕ β) :
    x ∈ Set.range Sum.inr ∪ Set.range Sum.inl ↔ x ∈ Set.range Sum.inr ∪ Set.range Sum.inl := by
  conv =>
    congr
    · simp [-Set.range_inr_union_range_inl, -exists_inr_eq_or_exists_inl_eq]
    · simp [-Set.mem_range, -exists_inr_eq_or_exists_inl_eq]
  fail_if_success simpa [-exists_inr_eq_or_exists_inl_eq]
  simp

/-- Without `exists_inl_eq_of_inl_eq_iff_true`, `Set.range_inl_inter_range_inr` and `Set.mem_range`
create a simp confluence issue. -/
example (x : α ⊕ β) : x ∉ Set.range Sum.inl ∩ Set.range Sum.inr ↔ x ∉ Set.range Sum.inl ∩ Set.range Sum.inr := by
  conv =>
    congr
    · simp [-Set.range_inl_inter_range_inr, -exists_inl_eq_of_inl_eq_iff_true]
    · simp [-Set.mem_range, -exists_inl_eq_of_inl_eq_iff_true]
  fail_if_success simpa [-exists_inl_eq_of_inl_eq_iff_true]
  simp

/-- Without `exists_inr_eq_of_inr_eq_iff_true`, `Set.range_inr_inter_range_inl` and `Set.mem_range`
create a simp confluence issue. -/
example (x : α ⊕ β) : x ∉ Set.range Sum.inr ∩ Set.range Sum.inl ↔ x ∉ Set.range Sum.inr ∩ Set.range Sum.inl := by
  conv =>
    congr
    · simp [-Set.range_inr_inter_range_inl, -exists_inr_eq_of_inr_eq_iff_true]
    · simp [-Set.mem_range, -exists_inr_eq_of_inr_eq_iff_true]
  fail_if_success simpa [-exists_inr_eq_of_inr_eq_iff_true]
  simp

end Sum

namespace Function

variable {α : ι → Type*} [∀ i, Nonempty (α i)]

@[simp]
theorem exists_apply_eq (i : ι) (x : α i) :
    ∃ (f : (i' : ι) → α i'), f i = x := by
  rw [← Set.mem_range, Set.range_eval]
  exact Set.mem_univ x

/-- Without `exists_apply_eq`, `Set.range_eval` and `Set.mem_range`
create a simp confluence issue. -/
example {α : ι → Type*} [inst : ∀ (i : ι), Nonempty (α i)] (i : ι) (x : α i) :
    x ∈ Set.range (Function.eval i : ((i' : ι) → α i') → α i) ↔ x ∈ Set.range (Function.eval i : ((i' : ι) → α i') → α i) := by
  conv =>
    congr
    · simp [-Set.range_eval, -exists_apply_eq]
    · simp [-Set.mem_range, -exists_apply_eq]
  fail_if_success simpa [-exists_apply_eq]
  simp

end Function

section Semiring

/-- Without `exists_two_mul_eq_iff_even`, `range_two_mul` and `Set.mem_range`
create a simp confluence issue. -/
example (α : Type*) [Semiring α] (x : α) :
    x ∈ Set.range (2 * ·) ↔ x ∈ Set.range (2 * ·) := by
  conv =>
    congr
    · simp [-range_two_mul, -exists_two_mul_eq_iff_even]
    · simp [-Set.mem_range, -exists_two_mul_eq_iff_even]
  fail_if_success simpa [-exists_two_mul_eq_iff_even]
  simp

/-- Without `exists_two_mul_add_one_eq_iff_odd`, `range_two_mul_add_one` and `Set.mem_range`
create a simp confluence issue. -/
example (α : Type*) [Semiring α] (x : α) :
    x ∈ Set.range (2 * · + 1) ↔ x ∈ Set.range (2 * · + 1) := by
  conv =>
    congr
    · simp [-range_two_mul_add_one, -exists_two_mul_add_one_eq_iff_odd]
    · simp [-Set.mem_range, -exists_two_mul_add_one_eq_iff_odd]
  fail_if_success simpa [-exists_two_mul_add_one_eq_iff_odd]
  simp

end Semiring

namespace Fin

/-- Without `exists_castLE_eq_iff`, `range_castLE` and `Set.mem_range`
create a simp confluence issue. -/
example {n : ℕ} {k : ℕ} (h : n ≤ k) (x : Fin k):
    x ∈ Set.range (castLE h) ↔ x ∈ Set.range (castLE h) := by
  conv =>
    congr
    · simp [-range_castLE, -exists_castLE_eq_iff]
    · simp [-Set.mem_range, -exists_castLE_eq_iff]
  fail_if_success simpa [-exists_castLE_eq_iff]
  simp

/-- Without `exists_castSucc_eq_iff`, `range_castSucc` and `Set.mem_range`
create a simp confluence issue. -/
example {n : ℕ} (x : Fin (n + 1)):
    x ∈ Set.range castSucc ↔ x ∈ Set.range castSucc := by
  conv =>
    congr
    · simp [-range_castSucc, -exists_castSucc_eq_iff]
    · simp [-Set.mem_range, -exists_castSucc_eq_iff]
  fail_if_success simpa [-exists_castSucc_eq_iff]
  simp

end Fin

namespace List

/-- Without `exists_getD_eq`, `Set.range_list_getD` and `Set.mem_range`
create a simp confluence issue. -/
example (l : List α) (d : α) (x : α):
    x ∈ Set.range (List.getD l · d) ↔ x ∈ Set.range (List.getD l · d) := by
  conv =>
    congr
    · simp [-Set.range_list_getD, -exists_getD_eq]
    · simp [-Set.mem_range, -exists_getD_eq]
  fail_if_success simpa [-exists_getD_eq]
  simp

/-- Without `exists_getI_eq`, `Set.range_list_getI` and `Set.mem_range`
create a simp confluence issue. -/
example [Inhabited α] (l : List α) (x : α) :
    x ∈ Set.range (List.getI l) ↔ x ∈ Set.range (List.getI l) := by
  conv =>
    congr
    · simp [-Set.range_list_getI, -exists_getI_eq]
    · simp [-Set.mem_range, -exists_getI_eq]
  fail_if_success simpa [-exists_getI_eq]
  simp

/-- Without `exists_nthLe_eq`, `Set.range_list_nthLe` and `Set.mem_range`
create a simp confluence issue. -/
example (l : List α) (x : α) :
    x ∈ (Set.range fun k : Fin l.length ↦ List.nthLe l ↑k k.prop) ↔ x ∈ (Set.range fun (k : Fin l.length) ↦ List.nthLe l ↑k k.prop) := by
  conv =>
    congr
    · simp [-Set.range_list_nthLe, -exists_nthLe_eq]
    · simp [-Set.mem_range, -exists_nthLe_eq]
  fail_if_success simpa [-exists_nthLe_eq]
  simp

end List

/-- Without `Set.exists_mem_coe_eq`, `Set.range_inclusion` and `Set.mem_range`
create a simp confluence issue. -/
example {s : Set α} {t : Set α} (h : s ⊆ t) (x : t) :
    x ∈ Set.range (Set.inclusion h) ↔ x ∈ Set.range (Set.inclusion h) := by
  conv =>
    congr
    · simp [-Set.range_inclusion, -Set.exists_mem_coe_eq]
    · simp [-Set.mem_range, -Set.exists_mem_coe_eq]
  fail_if_success simpa [-Set.exists_mem_coe_eq]
  simp
