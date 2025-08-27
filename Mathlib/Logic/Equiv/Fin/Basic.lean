/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Embedding.Set
import Mathlib.Logic.Equiv.Option
import Mathlib.Data.Int.Init

/-!
# Equivalences for `Fin n`
-/

assert_not_exists MonoidWithZero

universe u

variable {m n : ℕ}

/-!
### Miscellaneous

This is currently not very sorted. PRs welcome!
-/

theorem Fin.preimage_apply_01_prod {α : Fin 2 → Type u} (s : Set (α 0)) (t : Set (α 1)) :
    (fun f : ∀ i, α i => (f 0, f 1)) ⁻¹' s ×ˢ t =
      Set.pi Set.univ (Fin.cons s <| Fin.cons t finZeroElim) := by
  ext f
  simp [Fin.forall_fin_two]

theorem Fin.preimage_apply_01_prod' {α : Type u} (s t : Set α) :
    (fun f : Fin 2 → α => (f 0, f 1)) ⁻¹' s ×ˢ t = Set.pi Set.univ ![s, t] :=
  @Fin.preimage_apply_01_prod (fun _ => α) s t

/-- A product space `α × β` is equivalent to the space `Π i : Fin 2, γ i`, where
`γ = Fin.cons α (Fin.cons β finZeroElim)`. See also `piFinTwoEquiv` and
`finTwoArrowEquiv`. -/
@[simps! -fullyApplied]
def prodEquivPiFinTwo (α β : Type u) : α × β ≃ ∀ i : Fin 2, ![α, β] i :=
  (piFinTwoEquiv (Fin.cons α (Fin.cons β finZeroElim))).symm

/-- The space of functions `Fin 2 → α` is equivalent to `α × α`. See also `piFinTwoEquiv` and
`prodEquivPiFinTwo`. -/
@[simps -fullyApplied]
def finTwoArrowEquiv (α : Type*) : (Fin 2 → α) ≃ α × α :=
  { piFinTwoEquiv fun _ => α with invFun := fun x => ![x.1, x.2] }

/-- An equivalence that removes `i` and maps it to `none`.
This is a version of `Fin.predAbove` that produces `Option (Fin n)` instead of
mapping both `i.castSucc` and `i.succ` to `i`. -/
def finSuccEquiv' (i : Fin (n + 1)) : Fin (n + 1) ≃ Option (Fin n) where
  toFun := i.insertNth none some
  invFun x := x.casesOn' i (Fin.succAbove i)
  left_inv x := Fin.succAboveCases i (by simp) (fun j => by simp) x
  right_inv x := by cases x <;> simp

@[simp]
theorem finSuccEquiv'_at (i : Fin (n + 1)) : (finSuccEquiv' i) i = none := by
  simp [finSuccEquiv']

@[simp]
theorem finSuccEquiv'_succAbove (i : Fin (n + 1)) (j : Fin n) :
    finSuccEquiv' i (i.succAbove j) = some j :=
  @Fin.insertNth_apply_succAbove n (fun _ => Option (Fin n)) i _ _ _

theorem finSuccEquiv'_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i) (Fin.castSucc m) = m := by
  rw [← Fin.succAbove_of_castSucc_lt _ _ h, finSuccEquiv'_succAbove]

theorem finSuccEquiv'_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i) m.succ = some m := by
  rw [← Fin.succAbove_of_le_castSucc _ _ h, finSuccEquiv'_succAbove]

@[simp]
theorem finSuccEquiv'_symm_none (i : Fin (n + 1)) : (finSuccEquiv' i).symm none = i :=
  rfl

@[simp]
theorem finSuccEquiv'_symm_some (i : Fin (n + 1)) (j : Fin n) :
    (finSuccEquiv' i).symm (some j) = i.succAbove j :=
  rfl

@[simp]
theorem finSuccEquiv'_eq_some {i j : Fin (n + 1)} {k : Fin n} :
    finSuccEquiv' i j = k ↔ j = i.succAbove k :=
  (finSuccEquiv' i).apply_eq_iff_eq_symm_apply

@[simp]
theorem finSuccEquiv'_eq_none {i j : Fin (n + 1)} : finSuccEquiv' i j = none ↔ i = j :=
  (finSuccEquiv' i).apply_eq_iff_eq_symm_apply.trans eq_comm

theorem finSuccEquiv'_symm_some_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i).symm (some m) = Fin.castSucc m :=
  Fin.succAbove_of_castSucc_lt i m h

theorem finSuccEquiv'_symm_some_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i).symm (some m) = m.succ :=
  Fin.succAbove_of_le_castSucc i m h

theorem finSuccEquiv'_symm_coe_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i).symm m = Fin.castSucc m :=
  finSuccEquiv'_symm_some_below h

theorem finSuccEquiv'_symm_coe_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i).symm m = m.succ :=
  finSuccEquiv'_symm_some_above h

/-- Equivalence between `Fin (n + 1)` and `Option (Fin n)`.
This is a version of `Fin.pred` that produces `Option (Fin n)` instead of
requiring a proof that the input is not `0`. -/
def finSuccEquiv (n : ℕ) : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' 0

@[simp]
theorem finSuccEquiv_zero : (finSuccEquiv n) 0 = none :=
  rfl

@[simp]
theorem finSuccEquiv_succ (m : Fin n) : (finSuccEquiv n) m.succ = some m :=
  finSuccEquiv'_above (Fin.zero_le _)

@[simp]
theorem finSuccEquiv_symm_none : (finSuccEquiv n).symm none = 0 :=
  finSuccEquiv'_symm_none _

@[simp]
theorem finSuccEquiv_symm_some (m : Fin n) : (finSuccEquiv n).symm (some m) = m.succ :=
  congr_fun Fin.succAbove_zero m

@[simp]
theorem finSuccEquiv_eq_some {i : Fin (n + 1)} {j : Fin n} :
    finSuccEquiv n i = j ↔ i = j.succ :=
  (finSuccEquiv n).apply_eq_iff_eq_symm_apply

@[simp]
theorem finSuccEquiv_eq_none {i : Fin (n + 1)} : finSuccEquiv n i = none ↔ i = 0 :=
  (finSuccEquiv n).apply_eq_iff_eq_symm_apply

/-- The equiv version of `Fin.predAbove_zero`. -/
theorem finSuccEquiv'_zero : finSuccEquiv' (0 : Fin (n + 1)) = finSuccEquiv n :=
  rfl

theorem finSuccEquiv'_last_apply_castSucc (i : Fin n) :
    finSuccEquiv' (Fin.last n) (Fin.castSucc i) = i := by
  rw [← Fin.succAbove_last, finSuccEquiv'_succAbove]

theorem finSuccEquiv'_last_apply {i : Fin (n + 1)} (h : i ≠ Fin.last n) :
    finSuccEquiv' (Fin.last n) i = Fin.castLT i (Fin.val_lt_last h) := by
  simp

theorem finSuccEquiv'_ne_last_apply {i j : Fin (n + 1)} (hi : i ≠ Fin.last n) (hj : j ≠ i) :
    finSuccEquiv' i j = (i.castLT (Fin.val_lt_last hi)).predAbove j := by
  rcases Fin.exists_succAbove_eq hj with ⟨j, rfl⟩
  rcases Fin.exists_castSucc_eq.2 hi with ⟨i, rfl⟩
  simp

/-- `Fin.succAbove` as an order isomorphism between `Fin n` and `{x : Fin (n + 1) // x ≠ p}`. -/
def finSuccAboveEquiv (p : Fin (n + 1)) : Fin n ≃ { x : Fin (n + 1) // x ≠ p } :=
  .optionSubtype p ⟨(finSuccEquiv' p).symm, rfl⟩

theorem finSuccAboveEquiv_apply (p : Fin (n + 1)) (i : Fin n) :
    finSuccAboveEquiv p i = ⟨p.succAbove i, p.succAbove_ne i⟩ :=
  rfl

theorem finSuccAboveEquiv_symm_apply_last (x : { x : Fin (n + 1) // x ≠ Fin.last n }) :
    (finSuccAboveEquiv (Fin.last n)).symm x = Fin.castLT x.1 (Fin.val_lt_last x.2) := by
  rw [← Option.some_inj]
  simp [finSuccAboveEquiv]

theorem finSuccAboveEquiv_symm_apply_ne_last {p : Fin (n + 1)} (h : p ≠ Fin.last n)
    (x : { x : Fin (n + 1) // x ≠ p }) :
    (finSuccAboveEquiv p).symm x = (p.castLT (Fin.val_lt_last h)).predAbove x := by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv] using finSuccEquiv'_ne_last_apply h x.property

/-- `Equiv` between `Fin (n + 1)` and `Option (Fin n)` sending `Fin.last n` to `none` -/
def finSuccEquivLast : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' (Fin.last n)

@[simp]
theorem finSuccEquivLast_castSucc (i : Fin n) : finSuccEquivLast (Fin.castSucc i) = some i :=
  finSuccEquiv'_below i.2

@[simp]
theorem finSuccEquivLast_last : finSuccEquivLast (Fin.last n) = none := by
  simp [finSuccEquivLast]

@[simp]
theorem finSuccEquivLast_symm_some (i : Fin n) :
    finSuccEquivLast.symm (some i) = Fin.castSucc i :=
  finSuccEquiv'_symm_some_below i.2

@[simp] theorem finSuccEquivLast_symm_none : finSuccEquivLast.symm none = Fin.last n :=
  finSuccEquiv'_symm_none _

/-- An embedding `e : Fin (n+1) ↪ ι` corresponds to an embedding `f : Fin n ↪ ι` (corresponding
the last `n` coordinates of `e`) together with a value not taken by `f` (corresponding to `e 0`). -/
def Equiv.embeddingFinSucc (n : ℕ) (ι : Type*) :
    (Fin (n + 1) ↪ ι) ≃ (Σ (e : Fin n ↪ ι), {i // i ∉ Set.range e}) :=
  ((finSuccEquiv n).embeddingCongr (Equiv.refl ι)).trans
    (Function.Embedding.optionEmbeddingEquiv (Fin n) ι)

@[simp] lemma Equiv.embeddingFinSucc_fst {n : ℕ} {ι : Type*} (e : Fin (n + 1) ↪ ι) :
    ((Equiv.embeddingFinSucc n ι e).1 : Fin n → ι) = e ∘ Fin.succ := rfl

@[simp] lemma Equiv.embeddingFinSucc_snd {n : ℕ} {ι : Type*} (e : Fin (n + 1) ↪ ι) :
    ((Equiv.embeddingFinSucc n ι e).2 : ι) = e 0 := rfl

@[simp] lemma Equiv.coe_embeddingFinSucc_symm {n : ℕ} {ι : Type*}
    (f : Σ (e : Fin n ↪ ι), {i // i ∉ Set.range e}) :
    ((Equiv.embeddingFinSucc n ι).symm f : Fin (n + 1) → ι) = Fin.cons f.2.1 f.1 := by
  ext i
  exact Fin.cases rfl (fun j ↦ rfl) i

/-- Equivalence between `Fin m ⊕ Fin n` and `Fin (m + n)` -/
def finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n) where
  toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := @Fin.addCases m n (fun _ => Fin m ⊕ Fin n) Sum.inl Sum.inr i
  left_inv x := by rcases x with y | y <;> simp
  right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp

@[simp]
theorem finSumFinEquiv_apply_left (i : Fin m) :
    (finSumFinEquiv (Sum.inl i) : Fin (m + n)) = Fin.castAdd n i :=
  rfl

@[simp]
theorem finSumFinEquiv_apply_right (i : Fin n) :
    (finSumFinEquiv (Sum.inr i) : Fin (m + n)) = Fin.natAdd m i :=
  rfl

@[simp]
theorem finSumFinEquiv_symm_apply_castAdd (x : Fin m) :
    finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x :=
  finSumFinEquiv.symm_apply_apply (Sum.inl x)

@[simp]
theorem finSumFinEquiv_symm_apply_castSucc (x : Fin m) :
    finSumFinEquiv.symm (Fin.castSucc x) = Sum.inl x :=
  finSumFinEquiv_symm_apply_castAdd x

@[simp]
theorem finSumFinEquiv_symm_apply_natAdd (x : Fin n) :
    finSumFinEquiv.symm (Fin.natAdd m x) = Sum.inr x :=
  finSumFinEquiv.symm_apply_apply (Sum.inr x)

@[simp]
theorem finSumFinEquiv_symm_last : finSumFinEquiv.symm (Fin.last n) = Sum.inr 0 :=
  finSumFinEquiv_symm_apply_natAdd 0

/-- Equivalence between `Fin n ⊕ ℕ` and `ℕ` that sends `inl (a : Fin n)` to
`(a : ℕ)` and `inr a` to `n + a`. -/
def finSumNatEquiv (n : ℕ) : Fin n ⊕ ℕ ≃ ℕ where
  toFun := Sum.elim Fin.val (n + ·)
  invFun i := if hi : i < n then .inl ⟨i, hi⟩ else .inr (i - n)
  left_inv i := (i.casesOn
    (fun _ => dif_pos (Fin.is_lt _))
    (fun _ => (dif_neg (Nat.le_add_right _ _).not_gt).trans <|
      congrArg _ (Nat.add_sub_cancel_left _ _)))
  right_inv i := (apply_dite _ _ _ _).trans <| (i.lt_or_ge n).by_cases
    (fun hi => dif_pos hi)
    (fun hi => (dif_neg hi.not_gt).trans <| Nat.add_sub_cancel' hi)

@[simp] theorem finSumNatEquiv_apply_left (i : Fin n) :
    finSumNatEquiv n (.inl i) = i := rfl

@[simp] theorem finSumNatEquiv_apply_right (i : ℕ) :
    finSumNatEquiv n (.inr i) = n + i := rfl

@[simp] theorem finSumNatEquiv_symm_apply_of_lt {i : ℕ} (hi : i < n) :
    (finSumNatEquiv n).symm i = .inl ⟨i, hi⟩ := dif_pos hi

@[simp] theorem finSumNatEquiv_symm_apply_of_ge {i : ℕ} (hi : n ≤ i) :
    (finSumNatEquiv n).symm i = .inr (i - n) := dif_neg (Nat.not_lt_of_ge hi)

theorem finSumNatEquiv_symm_apply_fin (i : Fin n) :
    (finSumNatEquiv n).symm i = .inl i := by simp

theorem finSumNatEquiv_symm_apply_add_left (i : ℕ) :
    (finSumNatEquiv n).symm (i + n) = .inr i := by simp

theorem finSumNatEquiv_symm_apply_add_right (i : ℕ) :
    (finSumNatEquiv n).symm (n + i) = .inr i := by simp

@[simp] theorem isLeft_finSumNatEquiv_symm_apply (i : ℕ) :
    ((finSumNatEquiv n).symm i).isLeft = decide (i < n) := by
  rcases i.lt_or_ge n with hi | hi
  · simp_rw [finSumNatEquiv_symm_apply_of_lt hi, hi, Sum.isLeft_inl, decide_true]
  · simp_rw [finSumNatEquiv_symm_apply_of_ge hi, hi.not_gt, Sum.isLeft_inr, decide_false]

@[simp] theorem isRight_finSumNatEquiv_symm_apply (i : ℕ) :
    ((finSumNatEquiv n).symm i).isRight = decide (n ≤ i) := by
  simp_rw [← not_lt, decide_not, ← isLeft_finSumNatEquiv_symm_apply]
  cases (finSumNatEquiv n).symm i <;> rfl

/-- The equivalence between `Fin (m + n)` and `Fin (n + m)` which rotates by `n`. -/
def finAddFlip : Fin (m + n) ≃ Fin (n + m) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv

@[simp]
theorem finAddFlip_apply_castAdd (k : Fin m) (n : ℕ) :
    finAddFlip (Fin.castAdd n k) = Fin.natAdd n k := by simp [finAddFlip]

@[simp]
theorem finAddFlip_apply_natAdd (k : Fin n) (m : ℕ) :
    finAddFlip (Fin.natAdd m k) = Fin.castAdd m k := by simp [finAddFlip]

@[simp]
theorem finAddFlip_apply_mk_left {k : ℕ} (h : k < m) (hk : k < m + n := Nat.lt_add_right n h)
    (hnk : n + k < n + m := Nat.add_lt_add_left h n) :
    finAddFlip (⟨k, hk⟩ : Fin (m + n)) = ⟨n + k, hnk⟩ := by
  convert finAddFlip_apply_castAdd ⟨k, h⟩ n

@[simp]
theorem finAddFlip_apply_mk_right {k : ℕ} (h₁ : m ≤ k) (h₂ : k < m + n) :
    finAddFlip (⟨k, h₂⟩ : Fin (m + n)) = ⟨k - m, by omega⟩ := by
  convert @finAddFlip_apply_natAdd n ⟨k - m, by omega⟩ m
  simp [Nat.add_sub_cancel' h₁]

/-- Equivalence between `Fin m × Fin n` and `Fin (m * n)` -/
@[simps]
def finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n) where
  toFun x :=
    ⟨x.2 + n * x.1,
      calc
        x.2.1 + n * x.1.1 + 1 = x.1.1 * n + x.2.1 + 1 := by ac_rfl
        _ ≤ x.1.1 * n + n := Nat.add_le_add_left x.2.2 _
        _ = (x.1.1 + 1) * n := Eq.symm <| Nat.succ_mul _ _
        _ ≤ m * n := Nat.mul_le_mul_right _ x.1.2
        ⟩
  invFun x := (x.divNat, x.modNat)
  left_inv := fun ⟨x, y⟩ =>
    have H : 0 < n := Nat.pos_of_ne_zero fun H => Nat.not_lt_zero y.1 <| H ▸ y.2
    Prod.ext
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) / n = y.1 / n + x.1 := Nat.add_mul_div_left _ _ H
          _ = 0 + x.1 := by rw [Nat.div_eq_of_lt y.2]
          _ = x.1 := Nat.zero_add x.1
          )
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) % n = y.1 % n := Nat.add_mul_mod_self_left _ _ _
          _ = y.1 := Nat.mod_eq_of_lt y.2
          )
  right_inv _ := Fin.eq_of_val_eq <| Nat.mod_add_div _ _

/-- The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
This is like `finProdFinEquiv.symm` but with `m` infinite.
See `Nat.div_mod_unique` for a similar propositional statement. -/
@[simps]
def Nat.divModEquiv (n : ℕ) [NeZero n] : ℕ ≃ ℕ × Fin n where
  toFun a := (a / n, Fin.ofNat n a)
  invFun p := p.1 * n + ↑p.2
  -- TODO: is there a canonical order of `*` and `+` here?
  left_inv _ := Nat.div_add_mod' _ _
  right_inv p := by
    refine Prod.ext ?_ (Fin.ext <| Nat.mul_add_mod_of_lt p.2.is_lt)
    dsimp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ n.pos_of_neZero, Nat.div_eq_of_lt p.2.is_lt,
      Nat.zero_add]

/-- The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
See `Int.ediv_emod_unique` for a similar propositional statement. -/
@[simps]
def Int.divModEquiv (n : ℕ) [NeZero n] : ℤ ≃ ℤ × Fin n where
  -- TODO: could cast from int directly if we import `Data.ZMod.Defs`, though there are few lemmas
  -- about that coercion.
  toFun a := (a / n, Fin.ofNat n (a.natMod n))
  invFun p := p.1 * n + ↑p.2
  left_inv a := by
    simp_rw [Fin.val_ofNat, natCast_mod, natMod,
      toNat_of_nonneg (emod_nonneg _ <| natCast_eq_zero.not.2 (NeZero.ne n)), emod_emod,
      ediv_add_emod']
  right_inv := fun ⟨q, r, hrn⟩ => by
    simp only [Prod.mk_inj, Fin.ext_iff]
    obtain ⟨h1, h2⟩ := Int.natCast_nonneg r, Int.ofNat_lt.2 hrn
    rw [Int.add_comm, add_mul_ediv_right _ _ (natCast_eq_zero.not.2 (NeZero.ne n)),
      ediv_eq_zero_of_lt h1 h2, natMod, add_mul_emod_self_right, emod_eq_of_lt h1 h2, toNat_natCast]
    exact ⟨q.zero_add, Fin.val_cast_of_lt hrn⟩

/-- Promote a `Fin n` into a larger `Fin m`, as a subtype where the underlying
values are retained.

This is the `Equiv` version of `Fin.castLE`. -/
@[simps apply symm_apply]
def Fin.castLEquiv {n m : ℕ} (h : n ≤ m) : Fin n ≃ { i : Fin m // (i : ℕ) < n } where
  toFun i := ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp

@[deprecated Fin.subsingleton_zero (since := "2025-06-03")]
theorem subsingleton_fin_zero : Subsingleton (Fin 0) :=
  Fin.subsingleton_zero

@[deprecated Fin.subsingleton_one (since := "2025-06-03")]
theorem subsingleton_fin_one : Subsingleton (Fin 1) :=
  Fin.subsingleton_one

/-- The natural `Equiv` between `(Fin m → α) × (Fin n → α)` and `Fin (m + n) → α` -/
@[simps]
def Fin.appendEquiv {α : Type*} (m n : ℕ) :
    (Fin m → α) × (Fin n → α) ≃ (Fin (m + n) → α) where
  toFun fg := Fin.append fg.1 fg.2
  invFun f := ⟨fun i ↦ f (Fin.castAdd n i), fun i ↦ f (Fin.natAdd m i)⟩
  left_inv fg := by simp
  right_inv f := by simp [Fin.append_castAdd_natAdd]

/-- `Fin (n + 1) → α` and `(Fin n → α) × α` are equivalent. -/
@[simps!]
def Fin.succFunEquiv (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ (Fin n → α) × α :=
  (appendEquiv n 1).symm.trans (Equiv.prodCongrRight fun _ ↦ Equiv.funUnique (Fin 1) α)
