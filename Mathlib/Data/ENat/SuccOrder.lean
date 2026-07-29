
instance : SuccAddOrder ℕ∞ where
  succ_eq_add_one x := by cases x <;> simp


@[simp] theorem succ_natCast (n : ℕ) : SuccOrder.succ (n : ℕ∞) = (n + 1 : ℕ) := WithTop.succ_coe

@[deprecated (since := "2026-07-17")] alias succ_coe := succ_natCast


@[simp] theorem succ_top : SuccOrder.succ (⊤ : ℕ∞) = ⊤ := rfl
