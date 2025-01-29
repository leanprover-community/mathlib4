/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Multilinear.Defs

/-!
# Basic results about multilinear maps
-/

open Fin Function Finset Set

universe uR uS uι v v' v₁ v₂ v₃

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

namespace MultilinearMap

section Semiring

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)

initialize_simps_projections MultilinearMap (toFun → apply)

section

variable {M₁' : ι → Type*} [∀ i, AddCommMonoid (M₁' i)] [∀ i, Module R (M₁' i)]
variable {M₁'' : ι → Type*} [∀ i, AddCommMonoid (M₁'' i)] [∀ i, Module R (M₁'' i)]

@[simp]
theorem compLinearMap_apply (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i →ₗ[R] M₁' i)
    (m : ∀ i, M₁ i) : g.compLinearMap f m = g fun i => f i (m i) :=
  rfl

/-- Composing a multilinear map twice with a linear map in each argument is
the same as composing with their composition. -/
theorem compLinearMap_assoc (g : MultilinearMap R M₁'' M₂) (f₁ : ∀ i, M₁' i →ₗ[R] M₁'' i)
    (f₂ : ∀ i, M₁ i →ₗ[R] M₁' i) :
    (g.compLinearMap f₁).compLinearMap f₂ = g.compLinearMap fun i => f₁ i ∘ₗ f₂ i :=
  rfl

/-- Composing the zero multilinear map with a linear map in each argument. -/
@[simp]
theorem zero_compLinearMap (f : ∀ i, M₁ i →ₗ[R] M₁' i) :
    (0 : MultilinearMap R M₁' M₂).compLinearMap f = 0 :=
  ext fun _ => rfl

/-- Composing a multilinear map with the identity linear map in each argument. -/
@[simp]
theorem compLinearMap_id (g : MultilinearMap R M₁' M₂) :
    (g.compLinearMap fun _ => LinearMap.id) = g :=
  ext fun _ => rfl

/-- Composing with a family of surjective linear maps is injective. -/
theorem compLinearMap_injective (f : ∀ i, M₁ i →ₗ[R] M₁' i) (hf : ∀ i, Surjective (f i)) :
    Injective fun g : MultilinearMap R M₁' M₂ => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by
    simpa [fun i => surjInv_eq (hf i)]
      using MultilinearMap.ext_iff.mp h fun i => surjInv (hf i) (x i)

theorem compLinearMap_inj (f : ∀ i, M₁ i →ₗ[R] M₁' i) (hf : ∀ i, Surjective (f i))
    (g₁ g₂ : MultilinearMap R M₁' M₂) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff

/-- Composing a multilinear map with a linear equiv on each argument gives the zero map
if and only if the multilinear map is the zero map. -/
@[simp]
theorem comp_linearEquiv_eq_zero_iff (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i ≃ₗ[R] M₁' i) :
    (g.compLinearMap fun i => (f i : M₁ i →ₗ[R] M₁' i)) = 0 ↔ g = 0 := by
  set f' := fun i => (f i : M₁ i →ₗ[R] M₁' i)
  rw [← zero_compLinearMap f', compLinearMap_inj f' fun i => (f i).surjective]

end

/-- If one adds to a vector `m'` another vector `m`, but only for coordinates in a finset `t`, then
the image under a multilinear map `f` is the sum of `f (s.piecewise m m')` along all subsets `s` of
`t`. This is mainly an auxiliary statement to prove the result when `t = univ`, given in
`map_add_univ`, although it can be useful in its own right as it does not require the index set `ι`
to be finite. -/
theorem map_piecewise_add [DecidableEq ι] (m m' : ∀ i, M₁ i) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s ∈ t.powerset, f (s.piecewise m m') := by
  revert m'
  refine Finset.induction_on t (by simp) ?_
  intro i t hit Hrec m'
  have A : (insert i t).piecewise (m + m') m' = update (t.piecewise (m + m') m') i (m i + m' i) :=
    t.piecewise_insert _ _ _
  have B : update (t.piecewise (m + m') m') i (m' i) = t.piecewise (m + m') m' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [hit]
    · simp [h]
  let m'' := update m' i (m i)
  have C : update (t.piecewise (m + m') m') i (m i) = t.piecewise (m + m'') m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', hit]
    · by_cases h' : j ∈ t <;> simp [m'', h, hit, h']
  rw [A, f.map_update_add, B, C, Finset.sum_powerset_insert hit, Hrec, Hrec, add_comm (_ : M₂)]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  have : (insert i s).piecewise m m' = s.piecewise m m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', Finset.not_mem_of_mem_powerset_of_not_mem hs hit]
    · by_cases h' : j ∈ s <;> simp [m'', h, h']
  rw [this]

/-- Additivity of a multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum of `f (s.piecewise m m')` over all sets `s`. -/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ∀ i, M₁ i) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') := by
  simpa using f.map_piecewise_add m m' Finset.univ

section ApplySum

variable {α : ι → Type*} (g : ∀ i, α i → M₁ i) (A : ∀ i, Finset (α i))

open Fintype Finset

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. Here, we give an auxiliary statement tailored for an inductive proof. Use instead
`map_sum_finset`. -/
theorem map_sum_finset_aux [DecidableEq ι] [Fintype ι] {n : ℕ} (h : (∑ i, #(A i)) = n) :
    (f fun i => ∑ j ∈ A i, g i j) = ∑ r ∈ piFinset A, f fun i => g i (r i) := by
  letI := fun i => Classical.decEq (α i)
  induction' n using Nat.strong_induction_on with n IH generalizing A
  -- If one of the sets is empty, then all the sums are zero
  by_cases Ai_empty : ∃ i, A i = ∅
  · obtain ⟨i, hi⟩ : ∃ i, ∑ j ∈ A i, g i j = 0 := Ai_empty.imp fun i hi ↦ by simp [hi]
    have hpi : piFinset A = ∅ := by simpa
    rw [f.map_coord_zero i hi, hpi, Finset.sum_empty]
  push_neg at Ai_empty
  -- Otherwise, if all sets are at most singletons, then they are exactly singletons and the result
  -- is again straightforward
  by_cases Ai_singleton : ∀ i, #(A i) ≤ 1
  · have Ai_card : ∀ i, #(A i) = 1 := by
      intro i
      have pos : #(A i) ≠ 0 := by simp [Finset.card_eq_zero, Ai_empty i]
      have : #(A i) ≤ 1 := Ai_singleton i
      exact le_antisymm this (Nat.succ_le_of_lt (_root_.pos_iff_ne_zero.mpr pos))
    have :
      ∀ r : ∀ i, α i, r ∈ piFinset A → (f fun i => g i (r i)) = f fun i => ∑ j ∈ A i, g i j := by
      intro r hr
      congr with i
      have : ∀ j ∈ A i, g i j = g i (r i) := by
        intro j hj
        congr
        apply Finset.card_le_one_iff.1 (Ai_singleton i) hj
        exact mem_piFinset.mp hr i
      simp only [Finset.sum_congr rfl this, Finset.mem_univ, Finset.sum_const, Ai_card i, one_nsmul]
    simp only [Finset.sum_congr rfl this, Ai_card, card_piFinset, prod_const_one, one_nsmul,
      Finset.sum_const]
  -- Remains the interesting case where one of the `A i`, say `A i₀`, has cardinality at least 2.
  -- We will split into two parts `B i₀` and `C i₀` of smaller cardinality, let `B i = C i = A i`
  -- for `i ≠ i₀`, apply the inductive assumption to `B` and `C`, and add up the corresponding
  -- parts to get the sum for `A`.
  push_neg at Ai_singleton
  obtain ⟨i₀, hi₀⟩ : ∃ i, 1 < #(A i) := Ai_singleton
  obtain ⟨j₁, j₂, _, hj₂, _⟩ : ∃ j₁ j₂, j₁ ∈ A i₀ ∧ j₂ ∈ A i₀ ∧ j₁ ≠ j₂ :=
    Finset.one_lt_card_iff.1 hi₀
  let B := Function.update A i₀ (A i₀ \ {j₂})
  let C := Function.update A i₀ {j₂}
  have B_subset_A : ∀ i, B i ⊆ A i := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [B, sdiff_subset, update_self]
    · simp only [B, hi, update_of_ne, Ne, not_false_iff, Finset.Subset.refl]
  have C_subset_A : ∀ i, C i ⊆ A i := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [C, hj₂, Finset.singleton_subset_iff, update_self]
    · simp only [C, hi, update_of_ne, Ne, not_false_iff, Finset.Subset.refl]
  -- split the sum at `i₀` as the sum over `B i₀` plus the sum over `C i₀`, to use additivity.
  have A_eq_BC :
    (fun i => ∑ j ∈ A i, g i j) =
      Function.update (fun i => ∑ j ∈ A i, g i j) i₀
        ((∑ j ∈ B i₀, g i₀ j) + ∑ j ∈ C i₀, g i₀ j) := by
    ext i
    by_cases hi : i = i₀
    · rw [hi, update_self]
      have : A i₀ = B i₀ ∪ C i₀ := by
        simp only [B, C, Function.update_self, Finset.sdiff_union_self_eq_union]
        symm
        simp only [hj₂, Finset.singleton_subset_iff, Finset.union_eq_left]
      rw [this]
      refine Finset.sum_union <| Finset.disjoint_right.2 fun j hj => ?_
      have : j = j₂ := by
        simpa [C] using hj
      rw [this]
      simp only [B, mem_sdiff, eq_self_iff_true, not_true, not_false_iff, Finset.mem_singleton,
        update_self, and_false]
    · simp [hi]
  have Beq :
    Function.update (fun i => ∑ j ∈ A i, g i j) i₀ (∑ j ∈ B i₀, g i₀ j) = fun i =>
      ∑ j ∈ B i, g i j := by
    ext i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [update_self]
    · simp only [B, hi, update_of_ne, Ne, not_false_iff]
  have Ceq :
    Function.update (fun i => ∑ j ∈ A i, g i j) i₀ (∑ j ∈ C i₀, g i₀ j) = fun i =>
      ∑ j ∈ C i, g i j := by
    ext i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [update_self]
    · simp only [C, hi, update_of_ne, Ne, not_false_iff]
  -- Express the inductive assumption for `B`
  have Brec : (f fun i => ∑ j ∈ B i, g i j) = ∑ r ∈ piFinset B, f fun i => g i (r i) := by
    have : ∑ i, #(B i) < ∑ i, #(A i) := by
      refine sum_lt_sum (fun i _ => card_le_card (B_subset_A i)) ⟨i₀, mem_univ _, ?_⟩
      have : {j₂} ⊆ A i₀ := by simp [hj₂]
      simp only [B, Finset.card_sdiff this, Function.update_self, Finset.card_singleton]
      exact Nat.pred_lt (ne_of_gt (lt_trans Nat.zero_lt_one hi₀))
    rw [h] at this
    exact IH _ this B rfl
  -- Express the inductive assumption for `C`
  have Crec : (f fun i => ∑ j ∈ C i, g i j) = ∑ r ∈ piFinset C, f fun i => g i (r i) := by
    have : (∑ i, #(C i)) < ∑ i, #(A i) :=
      Finset.sum_lt_sum (fun i _ => Finset.card_le_card (C_subset_A i))
        ⟨i₀, Finset.mem_univ _, by simp [C, hi₀]⟩
    rw [h] at this
    exact IH _ this C rfl
  have D : Disjoint (piFinset B) (piFinset C) :=
    haveI : Disjoint (B i₀) (C i₀) := by simp [B, C]
    piFinset_disjoint_of_disjoint B C this
  have pi_BC : piFinset A = piFinset B ∪ piFinset C := by
    apply Finset.Subset.antisymm
    · intro r hr
      by_cases hri₀ : r i₀ = j₂
      · apply Finset.mem_union_right
        refine mem_piFinset.2 fun i => ?_
        by_cases hi : i = i₀
        · have : r i₀ ∈ C i₀ := by simp [C, hri₀]
          rwa [hi]
        · simp [C, hi, mem_piFinset.1 hr i]
      · apply Finset.mem_union_left
        refine mem_piFinset.2 fun i => ?_
        by_cases hi : i = i₀
        · have : r i₀ ∈ B i₀ := by simp [B, hri₀, mem_piFinset.1 hr i₀]
          rwa [hi]
        · simp [B, hi, mem_piFinset.1 hr i]
    · exact
        Finset.union_subset (piFinset_subset _ _ fun i => B_subset_A i)
          (piFinset_subset _ _ fun i => C_subset_A i)
  rw [A_eq_BC]
  simp only [MultilinearMap.map_update_add, Beq, Ceq, Brec, Crec, pi_BC]
  rw [← Finset.sum_union D]

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
theorem map_sum_finset [DecidableEq ι] [Fintype ι] :
    (f fun i => ∑ j ∈ A i, g i j) = ∑ r ∈ piFinset A, f fun i => g i (r i) :=
  f.map_sum_finset_aux _ _ rfl

/-- If `f` is multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
theorem map_sum [DecidableEq ι] [Fintype ι] [∀ i, Fintype (α i)] :
    (f fun i => ∑ j, g i j) = ∑ r : ∀ i, α i, f fun i => g i (r i) :=
  f.map_sum_finset g fun _ => Finset.univ

theorem map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α → M₁ i)
    (m : ∀ i, M₁ i) : f (update m i (∑ a ∈ t, g a)) = ∑ a ∈ t, f (update m i (g a)) := by
  classical
    induction' t using Finset.induction with a t has ih h
    · simp
    · simp [Finset.sum_insert has, ih]

end ApplySum

@[simp]
lemma linearDeriv_apply [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x y : (i : ι) → M₁ i) :
    f.linearDeriv x y = ∑ i, f (update x i (y i)) := by
  unfold linearDeriv
  simp only [LinearMap.coeFn_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, toLinearMap_apply]

end Semiring

end MultilinearMap

namespace LinearMap

variable [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [AddCommMonoid M'] [∀ i, Module R (M₁ i)] [Module R M₂] [Module R M₃] [Module R M']

/-- The multilinear version of `LinearMap.subtype_comp_codRestrict` -/
@[simp]
theorem subtype_compMultilinearMap_codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂)
    (h) : p.subtype.compMultilinearMap (f.codRestrict p h) = f :=
  rfl

/-- The multilinear version of `LinearMap.comp_codRestrict` -/
@[simp]
theorem compMultilinearMap_codRestrict (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂)
    (p : Submodule R M₃) (h) :
    (g.codRestrict p h).compMultilinearMap f =
      (g.compMultilinearMap f).codRestrict p fun v => h (f v) :=
  rfl

variable {ι₁ ι₂ : Type*}

@[simp]
theorem compMultilinearMap_domDomCongr (σ : ι₁ ≃ ι₂) (g : M₂ →ₗ[R] M₃)
    (f : MultilinearMap R (fun _ : ι₁ => M') M₂) :
    (g.compMultilinearMap f).domDomCongr σ = g.compMultilinearMap (f.domDomCongr σ) := by
  ext
  simp [MultilinearMap.domDomCongr]

end LinearMap

namespace MultilinearMap

section CommSemiring

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂] (f f' : MultilinearMap R M₁ M₂)

@[simp]
theorem map_update_smul_left [DecidableEq ι] [Fintype ι]
    (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update (c • m) i x) = c ^ (Fintype.card ι - 1) • f (update m i x) := by
  have :
    f ((Finset.univ.erase i).piecewise (c • update m i x) (update m i x)) =
      (∏ _i ∈ Finset.univ.erase i, c) • f (update m i x) :=
    map_piecewise_smul f _ _ _
  simpa [← Function.update_smul c m] using this

section

variable (R ι)
variable (A : Type*) [CommSemiring A] [Algebra R A] [Fintype ι]

variable {R A ι}

@[simp]
theorem mkPiAlgebra_apply (m : ι → A) : MultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i :=
  rfl

end

section

variable (R n)
variable (A : Type*) [Semiring A] [Algebra R A]

variable {R A n}

@[simp]
theorem mkPiAlgebraFin_apply (m : Fin n → A) :
    MultilinearMap.mkPiAlgebraFin R n A m = (List.ofFn m).prod :=
  rfl

theorem mkPiAlgebraFin_apply_const (a : A) :
    (MultilinearMap.mkPiAlgebraFin R n A fun _ => a) = a ^ n := by simp

end

@[simp]
theorem smulRight_apply (f : MultilinearMap R M₁ R) (z : M₂) (m : ∀ i, M₁ i) :
    f.smulRight z m = f m • z :=
  rfl

theorem mkPiRing_eq_iff [Fintype ι] {z₁ z₂ : M₂} :
    MultilinearMap.mkPiRing R ι z₁ = MultilinearMap.mkPiRing R ι z₂ ↔ z₁ = z₂ := by
  simp_rw [MultilinearMap.ext_iff, mkPiRing_apply]
  constructor <;> intro h
  · simpa using h fun _ => 1
  · intro x
    simp [h]

theorem mkPiRing_zero [Fintype ι] : MultilinearMap.mkPiRing R ι (0 : M₂) = 0 := by
  ext; rw [mkPiRing_apply, smul_zero, MultilinearMap.zero_apply]

theorem mkPiRing_eq_zero_iff [Fintype ι] (z : M₂) : MultilinearMap.mkPiRing R ι z = 0 ↔ z = 0 := by
  rw [← mkPiRing_zero, mkPiRing_eq_iff]

end CommSemiring

section RangeAddCommGroup

variable [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f g : MultilinearMap R M₁ M₂)

@[simp]
theorem neg_apply (m : ∀ i, M₁ i) : (-f) m = -f m :=
  rfl

@[simp]
theorem sub_apply (m : ∀ i, M₁ i) : (f - g) m = f m - g m :=
  rfl

end RangeAddCommGroup

section AddCommGroup

variable [Semiring R] [∀ i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f : MultilinearMap R M₁ M₂)

@[simp]
theorem map_update_neg [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x : M₁ i) :
    f (update m i (-x)) = -f (update m i x) :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← MultilinearMap.map_update_add, neg_add_cancel, f.map_coord_zero i (update_self i 0 m)]


@[deprecated (since := "2024-11-03")] protected alias map_neg := MultilinearMap.map_update_neg

@[simp]
theorem map_update_sub [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, MultilinearMap.map_update_add, map_update_neg]

@[deprecated (since := "2024-11-03")] protected alias map_sub := MultilinearMap.map_update_sub

lemma map_update [DecidableEq ι] (x : (i : ι) → M₁ i) (i : ι) (v : M₁ i)  :
    f (update x i v) = f x - f (update x i (x i - v)) := by
  rw [map_update_sub, update_eq_self, sub_sub_cancel]

open Finset in
lemma map_sub_map_piecewise [LinearOrder ι] (a b : (i : ι) → M₁ i) (s : Finset ι) :
    f a - f (s.piecewise b a) =
    ∑ i ∈ s, f (fun j ↦ if j ∈ s → j < i then a j else if i = j then a j - b j else b j) := by
  refine s.induction_on_min ?_ fun k s hk ih ↦ ?_
  · rw [Finset.piecewise_empty, sum_empty, sub_self]
  rw [Finset.piecewise_insert, map_update, ← sub_add, ih,
      add_comm, sum_insert (lt_irrefl _ <| hk k ·)]
  simp_rw [s.mem_insert]
  congr 1
  · congr; ext i; split_ifs with h₁ h₂
    · rw [update_of_ne, Finset.piecewise_eq_of_not_mem]
      · exact fun h ↦ (hk i h).not_lt (h₁ <| .inr h)
      · exact fun h ↦ (h₁ <| .inl h).ne h
    · cases h₂
      rw [update_self, s.piecewise_eq_of_not_mem _ _ (lt_irrefl _ <| hk k ·)]
    · push_neg at h₁
      rw [update_of_ne (Ne.symm h₂), s.piecewise_eq_of_mem _ _ (h₁.1.resolve_left <| Ne.symm h₂)]
  · apply sum_congr rfl; intro i hi; congr; ext j; congr 1; apply propext
    simp_rw [imp_iff_not_or, not_or]; apply or_congr_left'
    intro h; rw [and_iff_right]; rintro rfl; exact h (hk i hi)

/-- This calculates the differences between the values of a multilinear map at
two arguments that differ on a finset `s` of `ι`. It requires a
linear order on `ι` in order to express the result. -/
lemma map_piecewise_sub_map_piecewise [LinearOrder ι] (a b v : (i : ι) → M₁ i) (s : Finset ι) :
    f (s.piecewise a v) - f (s.piecewise b v) = ∑ i ∈ s, f
      fun j ↦ if j ∈ s then if j < i then a j else if j = i then a j - b j else b j else v j := by
  rw [← s.piecewise_idem_right b a, map_sub_map_piecewise]
  refine Finset.sum_congr rfl fun i hi ↦ congr_arg f <| funext fun j ↦ ?_
  by_cases hjs : j ∈ s
  · rw [if_pos hjs]; by_cases hji : j < i
    · rw [if_pos fun _ ↦ hji, if_pos hji, s.piecewise_eq_of_mem _ _ hjs]
    rw [if_neg (Classical.not_imp.mpr ⟨hjs, hji⟩), if_neg hji]
    obtain rfl | hij := eq_or_ne i j
    · rw [if_pos rfl, if_pos rfl, s.piecewise_eq_of_mem _ _ hi]
    · rw [if_neg hij, if_neg hij.symm]
  · rw [if_neg hjs, if_pos fun h ↦ (hjs h).elim, s.piecewise_eq_of_not_mem _ _ hjs]

open Finset in
lemma map_add_eq_map_add_linearDeriv_add [DecidableEq ι] [Fintype ι] (x h : (i : ι) → M₁ i) :
    f (x + h) = f x + f.linearDeriv x h + ∑ s with 2 ≤ #s, f (s.piecewise h x) := by
  rw [add_comm, map_add_univ, ← Finset.powerset_univ,
      ← sum_filter_add_sum_filter_not _ (2 ≤ #·)]
  simp_rw [not_le, Nat.lt_succ, le_iff_lt_or_eq (b := 1), Nat.lt_one_iff, filter_or,
    ← powersetCard_eq_filter, sum_union (univ.pairwise_disjoint_powersetCard zero_ne_one),
    powersetCard_zero, powersetCard_one, sum_singleton, Finset.piecewise_empty, sum_map,
    Function.Embedding.coeFn_mk, Finset.piecewise_singleton, linearDeriv_apply, add_comm]

open Finset in
/-- This expresses the difference between the values of a multilinear map
at two points "close to `x`" in terms of the "derivative" of the multilinear map at `x`
and of "second-order" terms. -/
lemma map_add_sub_map_add_sub_linearDeriv [DecidableEq ι] [Fintype ι] (x h h' : (i : ι) → M₁ i) :
    f (x + h) - f (x + h') - f.linearDeriv x (h - h') =
    ∑ s with 2 ≤ #s, (f (s.piecewise h x) - f (s.piecewise h' x)) := by
  simp_rw [map_add_eq_map_add_linearDeriv_add, add_assoc, add_sub_add_comm, sub_self, zero_add,
    ← LinearMap.map_sub, add_sub_cancel_left, sum_sub_distrib]

end AddCommGroup

end MultilinearMap

section Currying

/-!
### Currying

We associate to a multilinear map in `n+1` variables (i.e., based on `Fin n.succ`) two
curried functions, named `f.curryLeft` (which is a linear map on `E 0` taking values
in multilinear maps in `n` variables) and `f.curryRight` (which is a multilinear map in `n`
variables taking values in linear maps on `E 0`). In both constructions, the variable that is
singled out is `0`, to take advantage of the operations `cons` and `tail` on `Fin n`.
The inverse operations are called `uncurryLeft` and `uncurryRight`.

We also register linear equiv versions of these correspondences, in
`multilinearCurryLeftEquiv` and `multilinearCurryRightEquiv`.
-/


open MultilinearMap

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

variable (R M M₂)

namespace MultilinearMap

variable {ι' : Type*} {R M₂}

variable (ι ι' R M₂ M')

variable {ι ι' R M₂ M'}

@[simp]
theorem coe_currySumEquiv : ⇑(currySumEquiv R ι M₂ M' ι') = currySum :=
  rfl

-- Porting note: fixed missing letter `y` in name
@[simp]
theorem coe_currySumEquiv_symm : ⇑(currySumEquiv R ι M₂ M' ι').symm = uncurrySum :=
  rfl

variable (R M₂ M')

variable {R M₂ M'}

@[simp]
theorem curryFinFinset_apply {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin n => M') M₂) (mk : Fin k → M') (ml : Fin l → M') :
    curryFinFinset R M₂ M' hk hl f mk ml =
      f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl

@[simp]
theorem curryFinFinset_symm_apply {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (m : Fin n → M') :
    (curryFinFinset R M₂ M' hk hl).symm f m =
      f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i =>
        m <| finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl

theorem curryFinFinset_symm_apply_piecewise_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x y : M') :
    (curryFinFinset R M₂ M' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) =
      f (fun _ => x) fun _ => y := by
  rw [curryFinFinset_symm_apply]; congr
  · ext
    rw [finSumEquivOfFinset_inl, Finset.piecewise_eq_of_mem]
    apply Finset.orderEmbOfFin_mem
  · ext
    rw [finSumEquivOfFinset_inr, Finset.piecewise_eq_of_not_mem]
    exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ _)

@[simp]
theorem curryFinFinset_symm_apply_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x : M') : ((curryFinFinset R M₂ M' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl

theorem curryFinFinset_apply_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin n => M') M₂) (x y : M') :
    (curryFinFinset R M₂ M' hk hl f (fun _ => x) fun _ => y) =
      f (s.piecewise (fun _ => x) fun _ => y) := by
  -- Porting note: `rw` fails
  refine (curryFinFinset_symm_apply_piecewise_const hk hl _ _ _).symm.trans ?_
  rw [LinearEquiv.symm_apply_apply]

end MultilinearMap

end Currying

namespace MultilinearMap

section Submodule

variable [Ring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M₁ i)] [Module R M'] [Module R M₂]

/-- The map is always nonempty. This lemma is needed to apply `SubMulAction.zero_mem`. -/
theorem map_nonempty [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : ∀ i, Submodule R (M₁ i)) :
    (map f p : Set M₂).Nonempty :=
  ⟨f 0, 0, fun i => (p i).zero_mem, rfl⟩

end Submodule

end MultilinearMap
