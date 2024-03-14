import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped Real NNReal SchwartzSpace BigOperators  -- TODO: Check

section Basic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace Function

theorem HasTemperateGrowth.differentiable {g : E → F} (hg : g.HasTemperateGrowth) :
    Differentiable ℝ g :=
  hg.1.differentiable le_top

/-- A constant function is a trivial example of `HasTemperateGrowth`. -/
theorem hasTemperateGrowth_const (c : F) : HasTemperateGrowth fun _ : E ↦ c := by
  refine ⟨contDiff_const, ?_⟩
  intro n
  refine ⟨0, ‖c‖, ?_⟩
  cases n <;> simp [iteratedFDeriv_const_of_ne]

end Function

/-- Any Schwartz function `HasTemperateGrowth`. -/
theorem SchwartzMap.hasTemperateGrowth (f : 𝓢(E, F)) : Function.HasTemperateGrowth ⇑f := by
  refine ⟨f.smooth', ?_⟩
  intro n
  rcases f.decay' 0 n with ⟨C, hC⟩
  exact ⟨0, C, by simpa using hC⟩

end Basic


section Monotone

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem Function.HasTemperateGrowth.monotone_bound_nnreal {f : E → ℝ} :
    Monotone (fun a : ℕ × NNReal ↦ ∀ x, f x ≤ a.2 * (1 + ‖x‖) ^ a.1)
  | ⟨k, C⟩, ⟨k', C'⟩, hab, h, x => by
    rw [Prod.mk_le_mk] at hab
    refine le_trans (h x) ?_
    refine mul_le_mul hab.2 ?_ ?_ C'.prop
    · simp [pow_le_pow_right, hab.1]
    · simp [pow_nonneg, add_nonneg]

theorem Function.HasTemperateGrowth.monotone_bound_sup {f : E → ℝ} :
    Monotone (fun a : ℕ × ℝ ↦ ∀ x, f x ≤ (0 ⊔ a.2) * (1 + ‖x‖) ^ a.1)
  | ⟨k, C⟩, ⟨k', C'⟩, hab, h, x => by
    rw [Prod.mk_le_mk] at hab
    refine le_trans (h x) ?_
    refine mul_le_mul ?_ ?_ ?_ le_sup_left
    · cases le_or_lt 0 C with
      | inl hC => simp [hC, hab.2]
      | inr hC => simp [hC.le]
    · simp [pow_le_pow_right, hab.1]
    · simp [pow_nonneg, add_nonneg]

theorem Function.HasTemperateGrowth.monotoneOn_bound {f : E → ℝ} :
    MonotoneOn (fun a : ℕ × ℝ ↦ ∀ x, f x ≤ a.2 * (1 + ‖x‖) ^ a.1) {a | 0 ≤ a.2}
  | ⟨k, C⟩, hC, ⟨k', C'⟩, hC', hab, h, x => by
    rw [Set.mem_setOf_eq] at hC hC'
    rw [Prod.mk_le_mk] at hab
    refine le_trans (h x) (mul_le_mul hab.2 ?_ ?_ hC')
    · simp [pow_le_pow_right, hab.1]
    · simp [pow_nonneg, add_nonneg]


section Exists

variable {ι α : Type*} [SemilatticeSup α] {s : Finset ι} {p : ι → α → Prop}

-- TODO: Move inside `exists_forall_finset_of_orderBot`?
/--
Helper for `Monotone.exists_forall_finset_of_orderBot`.
Assumes `OrderBot α` for `Finset.sup`, `Finset.le_sup`.
-/
theorem Monotone.exists_forall_fintype_of_orderBot [Fintype ι] [OrderBot α]
    (hp : ∀ i, Monotone (p i ·)) (h : ∀ i, ∃ x, p i x) :
    ∃ x, ∀ i, p i x :=
  ⟨(Finset.univ (α := ι)).sup (fun i ↦ (h i).choose),
    fun i ↦ hp i (Finset.le_sup (Finset.mem_univ i)) (h i).choose_spec⟩

theorem Monotone.exists_forall_finset_of_orderBot [OrderBot α] (hp : ∀ i ∈ s, Monotone (p i ·))
    (h : ∀ i ∈ s, ∃ x, p i x) :
    ∃ x, ∀ i ∈ s, p i x := by
  simpa using exists_forall_fintype_of_orderBot (ι := s) (hp _ ·.prop) (h _ ·.prop)

/--
Helper for `Monotone.exists_forall_finset_of_nonempty`.
Assumes `Nonempty ι` rather than `OrderBot α`.
-/
theorem Monotone.exists_forall_fintype_of_nonempty [Fintype ι] [Nonempty ι]
    (hp : ∀ i, Monotone (p i ·)) (h : ∀ i, ∃ x, p i x) :
    ∃ x, ∀ i, p i x :=
  ⟨Finset.univ.sup' Finset.univ_nonempty (fun i ↦ (h i).choose),
    fun i ↦ hp i (Finset.le_sup' _ (Finset.mem_univ i)) (h i).choose_spec⟩

/--
Assumes `Finset.Nonempty s` rather than `OrderBot α`.
-/
theorem Monotone.exists_forall_finset_of_nonempty (hs : s.Nonempty) (hp : ∀ i ∈ s, Monotone (p i ·))
    (h : ∀ i ∈ s, ∃ x, p i x) :
    ∃ x, ∀ i ∈ s, p i x := by
  have _ : Nonempty s := hs.coe_sort  -- Is this idiomatic?
  simpa using exists_forall_fintype_of_nonempty (ι := s) (hp _ ·.prop) (h _ ·.prop)

section MonotoneOn

variable {t : Set α} (ht : SupClosed t)

-- -- Tried using `Set.monotoneOn_iff_monotone` to prove `MonotoneOn` from `Monotone`,
-- -- but encountered mismatch between:
-- -- `@LE.le { x // x ∈ t } Preorder.toLE a b`
-- -- `@LE.le { x // x ∈ t } Subtype.le a b`
-- theorem MonotoneOn.exists_forall_finset_of_nonempty (hs : s.Nonempty)
--     (ht : SupClosed t) (hp : ∀ i ∈ s, MonotoneOn (p i ·) t) (h : ∀ i ∈ s, ∃ x ∈ t, p i x) :
--     ∃ x ∈ t, ∀ i ∈ s, p i x := by
--   have inst : SemilatticeSup t := Subtype.semilatticeSup fun _ _ ha hb ↦ ht ha hb
--   suffices ∃ x : t, ∀ i ∈ s, p i x by simpa only [Subtype.exists, exists_prop]
--   replace h : ∀ i ∈ s, ∃ x : t, p i x := by simpa only [Subtype.exists, exists_prop]
--   refine Monotone.exists_forall_finset_of_nonempty hs ?_ h
--   intro i hi a b hab ha
--   refine hp i hi a.prop b.prop ?_ ha
--   rw [Subtype.coe_le_coe]
--   -- exact hab
--   sorry

/--
Helper for `MonotoneOn.exists_forall_finset_of_nonempty`.
Assumes `Nonempty ι` rather than `OrderBot α`.
-/
theorem MonotoneOn.exists_forall_fintype_of_nonempty [Fintype ι] [Nonempty ι]
    (hp : ∀ i, MonotoneOn (p i ·) t) (h : ∀ i, ∃ x ∈ t, p i x) :
    ∃ x ∈ t, ∀ i, p i x := by
  have h_mem := SupClosed.finsetSup'_mem ht Finset.univ_nonempty fun i _ ↦ (h i).choose_spec.1
  have h_le (i) := Finset.le_sup' (fun i ↦ (h i).choose) (Finset.mem_univ i)
  exact ⟨_, h_mem, fun i ↦ hp i (h i).choose_spec.1 h_mem (h_le i) (h i).choose_spec.2⟩

-- TODO: Can this be implemented using `Set.monotoneOn_iff_monotone` instead?
theorem MonotoneOn.exists_forall_finset_of_nonempty (hs : s.Nonempty)
    (hp : ∀ i ∈ s, MonotoneOn (p i ·) t) (h : ∀ i ∈ s, ∃ x ∈ t, p i x) :
    ∃ x ∈ t, ∀ i ∈ s, p i x := by
  have _ : Nonempty s := hs.coe_sort  -- Is this idiomatic?
  simpa using exists_forall_fintype_of_nonempty (ι := s) ht (hp _ ·.prop) (h _ ·.prop)

-- TODO: Maybe overkill to define this?
/-- Uses `Set.Nonempty t` instead of `Finset.Nonempty s` to ensure existence of `x ∈ t`. -/
theorem MonotoneOn.exists_forall_finset_of_nonempty' (ht_ne : t.Nonempty)
    (hp : ∀ i ∈ s, MonotoneOn (p i ·) t) (h : ∀ i ∈ s, ∃ x ∈ t, p i x) :
    ∃ x ∈ t, ∀ i ∈ s, p i x :=
  s.eq_empty_or_nonempty.elim (fun hs ↦ by simpa [hs]) (exists_forall_finset_of_nonempty ht · hp h)

/--
Helper for `Monotone.exists_forall_finset_of_orderBot`.
Requires `OrderBot α` for `Finset.sup`, `Finset.le_sup`.
-/
theorem MonotoneOn.exists_forall_fintype_of_orderBot [Fintype ι] [OrderBot α] (ht_bot : ⊥ ∈ t)
    (hp : ∀ i, MonotoneOn (p i ·) t) (h : ∀ i, ∃ x ∈ t, p i x) :
    ∃ x ∈ t, ∀ i, p i x := by
  have h_mem := Finset.univ.sup_mem t ht_bot (fun a ha b hb ↦ ht ha hb) _
    fun i _ ↦ (h i).choose_spec.1
  have h_le (i) := Finset.le_sup (f := fun i ↦ (h i).choose) (Finset.mem_univ i)
  exact ⟨_, h_mem, fun i ↦ hp i (h i).choose_spec.1 h_mem (h_le i) (h i).choose_spec.2⟩

theorem MonotoneOn.exists_forall_finset_of_orderBot [OrderBot α] (ht_bot : ⊥ ∈ t)
    (hp : ∀ i ∈ s, MonotoneOn (p i ·) t) (h : ∀ i ∈ s, ∃ x ∈ t, p i x) :
    ∃ x ∈ t, ∀ i ∈ s, p i x := by
  simpa using exists_forall_fintype_of_orderBot (ι := s) ht ht_bot (hp _ ·.prop) (h _ ·.prop)

end MonotoneOn

end Exists

end Monotone


namespace Function

variable {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

theorem HasTemperateGrowth.bound_forall_of_forall_bound {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    (h : ∀ i ∈ s, ∃ (k : ℕ) (C : ℝ), ∀ x, f i x ≤ C * (1 + ‖x‖) ^ k) :
    ∃ k C, 0 ≤ C ∧ ∀ i ∈ s, ∀ x, f i x ≤ C * (1 + ‖x‖) ^ k := by
  -- Switch to `C : ℝ≥0` to have `OrderBot`.
  suffices ∃ a : ℕ × ℝ≥0, ∀ i ∈ s, ∀ x, f i x ≤ ↑a.2 * (1 + ‖x‖) ^ a.1 by
    simpa [Prod.exists, NNReal.exists]
  -- replace h : ∀ i ∈ s, ∃ a : ℕ × ℝ≥0, ∀ x, f i x ≤ ↑a.2 * (1 + ‖x‖) ^ a.1 := fun i hi ↦ by
  --   rcases h i hi with ⟨k, C, h⟩
  --   use ⟨k, C.toNNReal⟩
  --   intro x
  --   exact le_trans (h x) <| mul_le_mul_of_nonneg_right (le_max_left C 0) (by simp [add_nonneg])
  refine Monotone.exists_forall_finset_of_orderBot
    (fun _ _ ↦ Function.HasTemperateGrowth.monotone_bound_nnreal) ?_
  intro i hi
  rcases h i hi with ⟨k, C, h⟩
  use ⟨k, C.toNNReal⟩
  intro x
  exact le_trans (h x) <| mul_le_mul_of_nonneg_right (le_max_left C 0) (by simp [add_nonneg])

/-- Gives a polynomial bound on the norm of all derivatives up to `n`. -/
theorem HasTemperateGrowth.bound_forall_norm_iteratedDeriv (s : Finset ℕ) {f : E → F}
    (hf : f.HasTemperateGrowth) :
    ∃ k C, 0 ≤ C ∧ ∀ i ∈ s, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C * (1 + ‖x‖) ^ k :=
  bound_forall_of_forall_bound s (fun i _ ↦ hf.2 i)

/-- The Fréchet derivative `HasTemperateGrowth`. -/
theorem HasTemperateGrowth.fderiv {f : E → F} (hf : f.HasTemperateGrowth) :
    HasTemperateGrowth (fun x ↦ _root_.fderiv ℝ f x) :=
  ⟨hf.1.fderiv_right le_top, fun n ↦ by simpa [norm_iteratedFDeriv_fderiv] using hf.2 (n + 1)⟩

section Compose

/-- The composition of two `HasTemperateGrowth` functions is a `HasTemperateGrowth` function. -/
theorem HasTemperateGrowth.comp {g : F → G} (hg : g.HasTemperateGrowth) {f : E → F}
    (hf : f.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ g (f x) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro n
  -- Obtain `k, C` for derivatives `i ≤ n` of `g` and `f`.
  rcases hg.bound_forall_norm_iteratedDeriv (Finset.Iic n) with ⟨kg, Cg, ⟨hCg_nn, hCg⟩⟩
  rcases hf.bound_forall_norm_iteratedDeriv (Finset.Iic n) with ⟨kf, Cf, ⟨_, hCf⟩⟩
  simp only [Finset.mem_Iic, zero_le, true_and, and_imp] at hCg hCf
  have hCf₀ (x) : ‖f x‖ ≤ Cf * (1 + ‖x‖) ^ kf := by simpa using hCf 0 n.zero_le x
  -- Need to show `‖iteratedFDeriv ℝ n (fun x ↦ g (f x)) x‖ ≤ C * (1 + ‖x‖) ^ k` for some `k, C`.
  -- Using `norm_iteratedFDeriv_comp_le` with
  -- `hC : ∀ i ≤ n, ‖iteratedFDeriv 𝕜 i g (f x)‖ ≤ C`
  -- `hD : ∀ (i : ℕ), 1 ≤ i → i ≤ n → ‖iteratedFDeriv 𝕜 i f x‖ ≤ D ^ i`
  -- (where `C` and `D` can depend on `x`) gives
  -- `‖iteratedFDeriv 𝕜 n (g ∘ f) x‖ ≤ n.factorial * C * D ^ n`.
  -- For `D`, we can set `D = max 1 Cf * (1 + ‖x‖) ^ kf` to ensure `1 ≤ D`,
  -- and then we have `‖iteratedFDeriv 𝕜 i f x‖ ≤ D ≤ D ^ i`.
  -- For `C`, need to obtain upper bound of the form `C * (1 + ‖x‖) ^ k` from
  -- `‖iteratedFDeriv 𝕜 i g (f x)‖ ≤ Cg * (1 + ‖f x‖) ^ kg` given `‖f x‖ ≤ Cf * (1 + ‖x‖) ^ kf`.
  -- One way to obtain this is to note `1, ‖f x‖ ≤ max 1 Cf * (1 + ‖x‖) ^ kf`,
  -- giving `1 + ‖f x‖ ≤ (2 * max 1 Cf) * (1 + ‖x‖) ^ kf` and therefore
  -- `‖iteratedFDeriv ℝ i g (f x)‖ ≤ (Cg * (2 * max 1 Cf) ^ kg) * (1 + ‖x‖) ^ (kf * kg)`.
  -- Combining these gives us the upper bound
  -- `(n.factorial * Cg * 2 ^ kg * max 1 Cf ^ (kg + n)) * (1 + ‖x‖) ^ (kf * (kg + n))`.
  have hD (x) : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i f x‖ ≤ (max 1 Cf * (1 + ‖x‖) ^ kf) ^ i := fun i hi hin ↦ by
    refine le_trans (hCf i hin x) ?_
    refine le_trans (mul_le_mul_of_nonneg_right (le_max_right 1 Cf) (by simp [add_nonneg])) ?_
    refine le_self_pow ?_ (Nat.one_le_iff_ne_zero.mp hi)
    simp [one_le_mul_of_one_le_of_one_le, one_le_pow_of_one_le]
  have hgf (x) : 1 + ‖f x‖ ≤ 2 * max 1 Cf * (1 + ‖x‖) ^ kf
  . rw [mul_assoc, two_mul]
    refine add_le_add ?_ ?_
    . simp [one_le_mul_of_one_le_of_one_le, one_le_pow_of_one_le]
    . exact le_trans (hCf₀ x) <| mul_le_mul_of_nonneg_right (by simp) (by simp [add_nonneg])
  have hC (x) : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g (f x)‖ ≤
      Cg * (2 * max 1 Cf * (1 + ‖x‖) ^ kf) ^ kg := fun i hi ↦ by
    refine le_trans (hCg i hi (f x)) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCg_nn
    exact pow_le_pow_left (by simp [add_nonneg]) (hgf x) kg
  exact ⟨kf * (kg + n), n.factorial * Cg * 2 ^ kg * max 1 Cf ^ (kg + n), fun x ↦
    le_of_le_of_eq (norm_iteratedFDeriv_comp_le hg.1 hf.1 le_top x (hC x) (hD x)) (by ring)⟩

end Compose


section ParametricLinear

-- TODO: Generalize to `f : D → E →L[𝕜] F`?
/-- Application of a parametric `ContinuousLinearMap` is a `HasTemperateGrowth` function. -/
theorem HasTemperateGrowth.clm_apply {f : D → E →L[ℝ] F} (hf : f.HasTemperateGrowth) {g : D → E}
    (hg : g.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ (f x) (g x) := by
  refine ⟨hf.1.clm_apply hg.1, ?_⟩
  intro n
  rcases hg.bound_forall_norm_iteratedDeriv (Finset.Iic n) with ⟨kg, Cg, ⟨_, hCg⟩⟩
  rcases hf.bound_forall_norm_iteratedDeriv (Finset.Iic n) with ⟨kf, Cf, ⟨hCf_nn, hCf⟩⟩
  simp only [Finset.mem_Iic] at hCg hCf
  -- From `norm_iteratedFDeriv_clm_apply`, have upper bound
  -- `∑ i in Finset.Iic n, n.choose i * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖`.
  -- For any `i, j`, `‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ j g x‖` is bounded above by
  -- constant function `(Cg * Cf) * (1 + ‖x‖) ^ (kg + kf)`.
  -- Also have `∑ i in Finset.range n.succ, n.choose i ≤ 2 ^ n`.
  have (x) : ‖iteratedFDeriv ℝ n (fun y ↦ (f y) (g y)) x‖ ≤
      2 ^ n * (Cf * (1 + ‖x‖) ^ kf) * (Cg * (1 + ‖x‖) ^ kg) := by
    refine le_trans (norm_iteratedFDeriv_clm_apply hf.1 hg.1 x le_top) ?_
    norm_cast
    simp only [← Nat.sum_range_choose, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro i hi
    simp only [mul_assoc (Nat.choose _ _ : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    simp only [Finset.mem_range, Nat.lt_succ] at hi
    exact mul_le_mul (hCf i hi x) (hCg _ (n.sub_le i) x) (norm_nonneg _)
      (mul_nonneg hCf_nn (by simp [add_nonneg]))
  exact ⟨kf + kg, 2 ^ n * Cf * Cg, fun x ↦ le_of_le_of_eq (this x) (by ring)⟩

end ParametricLinear


section Linear

theorem HasTemperateGrowth.clm (g : F →L[ℝ] G) {f : E → F} (hf : f.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ g (f x) :=
  clm_apply (hasTemperateGrowth_const g) hf

theorem hasTemperateGrowth_id : HasTemperateGrowth (id : E → E) := by
  refine ⟨contDiff_id, ?_⟩
  intro n
  cases n with
  | zero => exact ⟨1, 1, by simp⟩
  | succ n =>
    simp only [iteratedFDeriv_succ_eq_comp_right]
    cases n with
    | zero => exact ⟨0, 1, by simp [ContinuousLinearMap.norm_id_le]⟩
    | succ n => exact ⟨0, 0, by simp [iteratedFDeriv_const_of_ne]⟩

theorem hasTemperateGrowth_id' : HasTemperateGrowth fun x : E ↦ x := hasTemperateGrowth_id

/-- Any `ContinuousLinearMap` is a `HasTemperateGrowth` function. -/
theorem hasTemperateGrowth_clm (a : E →L[ℝ] F) : HasTemperateGrowth fun x ↦ a x :=
  hasTemperateGrowth_id.clm a

theorem hasTemperateGrowth_neg : HasTemperateGrowth fun x : E ↦ (-x) :=
  hasTemperateGrowth_clm (-ContinuousLinearMap.id ℝ E)

theorem hasTemperateGrowth_re : HasTemperateGrowth fun x : ℂ ↦ x.re :=
  hasTemperateGrowth_clm Complex.reCLM

theorem hasTemperateGrowth_im : HasTemperateGrowth fun x : ℂ ↦ x.im :=
  hasTemperateGrowth_clm Complex.imCLM

theorem HasTemperateGrowth.neg {f : E → F} (hf : f.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ (-f x) :=
  comp hasTemperateGrowth_neg hf

theorem HasTemperateGrowth.re {f : E → ℂ} (hf : f.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ (f x).re :=
  comp hasTemperateGrowth_re hf

theorem HasTemperateGrowth.im {f : E → ℂ} (hf : f.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ (f x).im :=
  comp hasTemperateGrowth_im hf

section Mul

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

theorem hasTemperateGrowth_const_mul (a : 𝔸) : HasTemperateGrowth fun x : 𝔸 ↦ a * x :=
  hasTemperateGrowth_clm <| .mul ℝ 𝔸 a

theorem hasTemperateGrowth_mul_const (a : 𝔸) : HasTemperateGrowth fun x : 𝔸 ↦ x * a :=
  hasTemperateGrowth_clm <| .flip (.mul ℝ 𝔸) a

theorem HasTemperateGrowth.const_mul (a : 𝔸) {f : E → 𝔸} (hf : f.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ a * f x :=
  comp (hasTemperateGrowth_const_mul a) hf

theorem HasTemperateGrowth.mul_const {f : E → 𝔸} (hf : f.HasTemperateGrowth) (a : 𝔸) :
    HasTemperateGrowth fun x ↦ f x * a :=
  comp (hasTemperateGrowth_mul_const a) hf

end Mul

section Div

variable {𝔸 : Type*} [NormedDivisionRing 𝔸] [NormedAlgebra ℝ 𝔸]

theorem hasTemperateGrowth_div_const (a : 𝔸) : HasTemperateGrowth fun x : 𝔸 ↦ x / a := by
  simpa [div_eq_mul_inv] using hasTemperateGrowth_mul_const a⁻¹

theorem HasTemperateGrowth.div_const {f : E → 𝔸} (hf : f.HasTemperateGrowth) (a : 𝔸) :
    HasTemperateGrowth fun x ↦ f x / a :=
  comp (hasTemperateGrowth_div_const a) hf

end Div

end Linear


section Add

/-- The addition of two `HasTemperateGrowth` functions is a `HasTemperateGrowth` function. -/
theorem HasTemperateGrowth.add {f : E → F} (hf : f.HasTemperateGrowth) {g : E → F}
    (hg : g.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ f x + g x := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro n
  rcases hf.2 n with ⟨kf, Cf, hCf⟩
  rcases hg.2 n with ⟨kg, Cg, hCg⟩
  have hCf_nn : 0 ≤ Cf := by simpa using le_trans (norm_nonneg _) (hCf 0)
  have hCg_nn : 0 ≤ Cg := by simpa using le_trans (norm_nonneg _) (hCg 0)
  use max kf kg, Cf + Cg
  intro x
  rw [← Pi.add_def f g, iteratedFDeriv_add_apply (hf.1.of_le le_top) (hg.1.of_le le_top)]
  refine le_trans (norm_add_le _ _) ?_
  rw [add_mul]
  refine add_le_add ?_ ?_
  . refine le_trans (hCf x) (mul_le_mul_of_nonneg_left ?_ hCf_nn)
    simp [pow_le_pow_right]
  . refine le_trans (hCg x) (mul_le_mul_of_nonneg_left ?_ hCg_nn)
    simp [pow_le_pow_right]

theorem HasTemperateGrowth.sub {f : E → F} (hf : f.HasTemperateGrowth) {g : E → F}
    (hg : g.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ f x - g x := by
  simpa [sub_eq_add_neg] using add hf hg.neg

theorem HasTemperateGrowth.add_const {f : E → F} (hf : f.HasTemperateGrowth) (c : F) :
    HasTemperateGrowth fun x ↦ f x + c :=
  add hf (hasTemperateGrowth_const c)

theorem HasTemperateGrowth.const_add (c : F) {f : E → F} (hf : f.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ c + f x :=
  add (hasTemperateGrowth_const c) hf

end Add


section ConstSMul

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

theorem HasTemperateGrowth.const_smul (c : 𝕜) {f : E → F} (hf : f.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ c • f x :=
  comp (hasTemperateGrowth_clm (c • ContinuousLinearMap.id ℝ F)) hf

end ConstSMul

section SMulConst

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [Module 𝕜 F] [IsScalarTower ℝ 𝕜 F]
  [ContinuousSMul 𝕜 F]

theorem HasTemperateGrowth.smul_const {f : E → 𝕜} (hf : f.HasTemperateGrowth) (c : F) :
    HasTemperateGrowth fun x ↦ f x • c :=
  comp (hasTemperateGrowth_clm (.smulRight (.id ℝ 𝕜) c)) hf

end SMulConst


section Bilinear

theorem HasTemperateGrowth.bilin (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} (hf : f.HasTemperateGrowth)
    {g : D → F} (hg : g.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ B (f x) (g x) :=
  clm_apply (clm B hf) hg

end Bilinear

section Mul

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A]

theorem HasTemperateGrowth.mul {f : E → A} (hf : f.HasTemperateGrowth) {g : E → A}
    (hg : g.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ f x * g x :=
  bilin (.mul ℝ A) hf hg

end Mul

section SMul

-- TODO: Generalize to `f : E → 𝕜`?
theorem HasTemperateGrowth.smul {f : E → ℝ} (hf : f.HasTemperateGrowth) {g : E → F}
    (hg : g.HasTemperateGrowth) :
    HasTemperateGrowth fun x ↦ f x • g x :=
  bilin (ContinuousLinearMap.smulRightL ℝ ℝ F (ContinuousLinearMap.id ℝ ℝ)) hg hf

end SMul

section Prod

-- TODO: Does this work even though `HasTemperateGrowth.add` is not defined with `to_additive`?
@[to_additive]
theorem HasTemperateGrowth.prod {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, HasTemperateGrowth (f i)) :
    HasTemperateGrowth (fun x ↦ ∏ i in s, f i x) := by
  induction s using Finset.cons_induction with
  | empty => simp [hasTemperateGrowth_const]
  | @cons i s hi IH =>
    simp only [Finset.mem_cons, forall_eq_or_imp] at hf
    simpa using .mul hf.1 (IH hf.2)

end Prod

end Function


namespace SchwartzMap

variable {𝕜 E F : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

-- TODO: Generalize to `𝕜`?
/-- Pointwise multiplication by a scalar-valued `HasTemperateGrowth` function as a CLM. -/
noncomputable def hasTemperateGrowth_smul {g : E → 𝕜} (hg : g.HasTemperateGrowth) :
    𝓢(E, F) →L[ℝ] 𝓢(E, F) :=
  bilinLeftCLM isBoundedBilinearMap_smul.toContinuousLinearMap.flip hg

theorem hasTemperateGrowth_smul_apply {g : E → 𝕜} (hg : g.HasTemperateGrowth)
    {φ : 𝓢(E, F)} {x : E} :
    hasTemperateGrowth_smul hg φ x = g x • φ x :=
  rfl

end SchwartzMap
