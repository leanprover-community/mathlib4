import Mathlib.Combinatorics.Enumerative.Fin.OrderedPartition.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
### Extending and shrinking ordered finpartitions

We show how an ordered finpartition can be extended to the left, either by adding a new atomic
part (in `extendLeft`) or adding the new element to an existing part (in `extendMiddle`).
Conversely, one can shrink a finpartition by deleting the element to the left, with a different
behavior if it was an atomic part (in `eraseLeft`, in which case the number of parts decreases by
one) or if it belonged to a non-atomic part (in `eraseMiddle`, in which case the number of parts
stays the same).

These operations are inverse to each other, giving rise to an equivalence between
`((c : OrderedPartition n) × Option (Fin c.length))` and `OrderedPartition (n + 1)`
called `OrderedFinPartition.extendEquiv`.
-/

open Set Function

namespace Fin

namespace OrderedPartition

variable {n : ℕ}

namespace Part

/-- Map all elements of a part to `Fin (n + 1)` using `Fin.succ`,
then prepend zero. -/
@[simps size]
def extendZero (p : Part n) : Part (n + 1) where
  size := p.size + 1
  size_ne_zero := Nat.succ_ne_zero _
  toFun := Fin.cons 0 (.succ ∘ p)
  strictMono := by
    intro i j hlt
    rcases Fin.exists_succ_eq.mpr hlt.ne_bot with ⟨j, rfl⟩
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa using hlt

@[simp]
theorem extendZero_apply_zero (p : Part n) : p.extendZero 0 = 0 := rfl

@[simp]
theorem extendZero_apply_succ (p : Part n) (i : Fin p.size) : p.extendZero i.succ = (p i).succ := by
  simp [extendZero]

@[simp]
theorem extendZero_last (p : Part n) : p.extendZero.last = p.last.succ := by
  rw [last, last, ← extendZero_apply_succ, Fin.succ_top]

theorem range_extendZero_eq_cons (p : Part n) :
    p.extendZero.range = .cons 0 (p.range.map (Fin.succEmb n)) (by simp [Fin.succ_ne_zero]) := by
  ext
  simp [extendZero, Fin.exists_fin_succ, eq_comm (a := (0 : Fin _)), mem_range]

@[simp]
theorem extendZero_ne_atom (p : Part n) (i : Fin (n + 1)) : p.extendZero ≠ atom i :=
  ne_of_apply_ne size <| by simp

@[simps size, simps (config := .lemmasOnly) apply]
def mapPred (p : Part (n + 1)) (h : p 0 ≠ 0) : Part n where
  size := p.size
  size_ne_zero := p.size_ne_zero
  toFun i := (p i).pred <| apply_ne_zero.2 h i
  strictMono := Fin.strictMono_pred_comp _ p.strictMono

@[simp]
lemma mapPred_inj {p₁ p₂ : Part (n + 1)} {h₁ h₂} :
    p₁.mapPred h₁ = p₂.mapPred h₂ ↔ p₁ = p₂ := by
  simp +contextual [Part.ext_iff, Fin.heq_fun_iff, mapPred_apply]

@[simp]
theorem mapPred_last (p : Part (n + 1)) (h : p 0 ≠ 0) :
    (p.mapPred h).last = p.last.pred (apply_ne_zero.2 h ⊤) :=
  rfl

theorem mapPred_range_eq_preimage (p : Part (n + 1)) (h : p 0 ≠ 0) :
    (p.mapPred h).range = p.range.preimage Fin.succ (succ_injective _).injOn := by
  ext
  simp [Part.mem_range, pred_eq_iff_eq_succ, mapPred_apply]

@[simp]
theorem mapPred_map_succ (p : Part n) :
    (p.map (succOrderEmb n)).mapPred (Fin.succ_ne_zero _) = p := by
  cases p
  simp [map, mapPred]

@[simp]
theorem map_succ_mapPred (p : Part (n + 1)) (h : p 0 ≠ 0) :
    (p.mapPred h).map (succOrderEmb n) = p := by
  rw [← mapPred_inj, mapPred_map_succ]

@[simps size, simps (config := .lemmasOnly) apply]
def eraseZero [NeZero n] (p : Part n) (h₁ : p 0 = 0) (h₂ : p ≠ atom 0) : Part n where
  size := p.size - 1
  size_ne_zero := (Nat.sub_pos_of_lt <| one_lt_size_of_eq_of_ne_atom h₁ h₂).ne'
  toFun i := p <| i.succ.cast <| Nat.sub_add_cancel p.one_le_size
  strictMono i j hlt := by simpa [Fin.cast_lt_cast]

@[simp]
lemma eraseZero_last [NeZero n] (p : Part n) (h₁ : p 0 = 0) (h₂ : p ≠ atom 0) :
    (p.eraseZero h₁ h₂).last = p.last := by
  rw [Part.last, eraseZero_apply]
  simp

lemma eraseZero_ne_zero [NeZero n] (p : Part n) (h₁ : p 0 = 0) (h₂ : p ≠ atom 0)
    (i : Fin (p.size - 1)) : p.eraseZero h₁ h₂ i ≠ 0 :=
  h₁ ▸ (p.strictMono <| Nat.succ_pos i).ne'

@[simp]
lemma eraseZero_range [NeZero n] (p : Part n) (h₁ : p 0 = 0) (h₂ : p ≠ atom 0) :
    (p.eraseZero h₁ h₂).range = p.range.erase 0 := by
  ext i
  by_cases hi : i = 0 <;> simp [Part.mem_range, eraseZero_apply, hi, p.injective.eq_iff' h₁,
    (finCongr <| Nat.sub_add_cancel p.one_le_size).surjective.exists, exists_fin_succ, h₁, Ne.symm]

def preimageSucc (p : Part (n + 1)) (h : p ≠ atom 0) : Part n :=
  if h₀ : p 0 = 0 then (p.eraseZero h₀ h).mapPred (p.eraseZero_ne_zero _ _ _) else p.mapPred h₀

@[simp]
theorem preimageSucc_last (p : Part (n + 1)) (h : p ≠ atom 0) :
    (p.preimageSucc h).last = p.last.pred (by simpa) := by
  unfold preimageSucc
  split_ifs <;> simp

@[simp]
theorem preimageSucc_range (p : Part (n + 1)) (h : p ≠ atom 0) :
    (p.preimageSucc h).range = p.range.preimage succ (succ_injective _).injOn := by
  simp [← Finset.coe_inj, preimageSucc, apply_dite Part.range, mapPred_range_eq_preimage,
    Set.disjoint_left, succ_ne_zero]

@[simp]
lemma preimageSucc_extendZero (p : Part n) :
    p.extendZero.preimageSucc (extendZero_ne_atom _ _) = p := by
  simp [Part.ext_iff, extendZero, preimageSucc, mapPred, eraseZero]

@[simp]
lemma preimageSucc_map_succ (p : Part n) :
    (p.map (succOrderEmb n)).preimageSucc (by simp [succ_ne_zero]) = p := by
  simp [Part.ext_iff, preimageSucc, succ_ne_zero]

lemma extendZero_preimageSucc (p : Part (n + 1)) (h₁ : p ≠ atom 0) (h₂ : p 0 = 0) :
    (p.preimageSucc h₁).extendZero = p := by
  simp [preimageSucc, h₂, Part.ext_iff, Fin.heq_fun_iff, forall_fin_succ, mapPred_apply,
    eraseZero_apply, Fin.cast]

lemma map_succ_preimageSucc (p : Part (n + 1)) (h : p 0 ≠ 0) :
    (p.preimageSucc <| ne_of_apply_ne (toFun · 0) h).map (succOrderEmb n) = p := by
  simp [Part.ext_iff, preimageSucc, h]

end Part

variable (c : OrderedPartition n)

/-- Extend an ordered partition of `n` entries, by adding a new singleton part to the left. -/
@[simps length]
def zeroCons (c : OrderedPartition n) : OrderedPartition (n + 1) where
  length := c.length + 1
  part := Fin.cons (.atom 0) fun i ↦ (c.part i).map (Fin.succOrderEmb n)
  part_last_strictMono i j hij := by
    rcases Fin.eq_succ_of_ne_zero hij.ne_bot with ⟨j, rfl⟩
    cases i using Fin.cases with
    | zero => simp
    | succ => simpa using c.part_last_strictMono (Fin.succ_lt_succ_iff.mp hij)
  disjoint := by
    rw [pairwise_disjoint_on]
    intro i j hij
    rcases Fin.eq_succ_of_ne_zero hij.ne_bot with ⟨j, rfl⟩
    cases i using Fin.cases with
    | zero => simp [Fin.succ_ne_zero]
    | succ => simpa using c.disjoint (Fin.succ_lt_succ_iff.mp hij).ne
  cover i := by
    cases i using Fin.cases with
    | zero =>
      use 0
      simp
    | succ i =>
      use (c.index i).succ
      simp

@[simp]
theorem zeroCons_part_zero (c : OrderedPartition n) : c.zeroCons.part 0 = .atom 0 := rfl

@[simp]
theorem zeroCons_part_succ (c : OrderedPartition n) (i : Fin c.length) :
    c.zeroCons.part i.succ = (c.part i).map (Fin.succOrderEmb n) :=
  rfl

@[simp]
theorem zeroCons_atomic : (atomic n).zeroCons = atomic (n + 1) := by simp [← length_eq_iff]

/-- Extend an ordered partition of `n` entries, by adding to the `i`-th part a new point to the
left. -/
@[simps length, simps (config := .lemmasOnly) part]
def extendPart (c : OrderedPartition n) (k : Fin c.length) : OrderedPartition (n + 1) where
  length := c.length
  part := update (fun i ↦ (c.part i).map (Fin.succOrderEmb n)) k (c.part k).extendZero
  part_last_strictMono := by
    simpa [apply_update fun _ ↦ Part.last] using Fin.strictMono_succ.comp c.part_last_strictMono
  disjoint i j hne := by
    wlog hik : i ≠ k generalizing i j
    · obtain rfl : i = k := by push_neg at hik; exact hik
      exact this j i hne.symm hne.symm |>.symm
    rcases eq_or_ne j k with rfl | hjk <;>
      simpa [onFun, *, Part.range_extendZero_eq_cons, Fin.succ_ne_zero] using c.disjoint hne
  cover i := by
    cases i using Fin.cases with
    | zero =>
      use k
      simp
    | succ i =>
      use c.index i
      rcases eq_or_ne (c.index i) k with rfl | hne <;> simp [*, Part.range_extendZero_eq_cons]

@[simp]
theorem extendPart_part_self (c : OrderedPartition n) (k : Fin c.length) :
    (c.extendPart k).part k = (c.part k).extendZero := by
  simp [extendPart_part]

@[simp]
theorem extendPart_part_of_ne (c : OrderedPartition n) {i j : Fin c.length} (h : j ≠ i) :
    (c.extendPart i).part j = (c.part j).map (Fin.succOrderEmb n) := by
  simp [extendPart_part, h]

@[simp]
theorem extendPart_indiscrete (h : n ≠ 0) (k) :
    (indiscrete n h).extendPart k = indiscrete (n + 1) n.succ_ne_zero := by
  simp [← length_eq_one_iff]

/-- If the first part of a partition is not `Part.atom 0`,
then none of the the parts is `Part.atom 0`. -/
theorem part_ne_atom_zero [NeZero n] (h : c.part 0 ≠ .atom 0) (i) : c.part i ≠ .atom 0 := by
  contrapose! h
  rw [← Part.last_eq_zero, ← (Fin.zero_le' _).le_iff_eq] at h ⊢
  exact (c.part_last_strictMono.monotone (Fin.zero_le' _)).trans h

@[simp]
theorem extendPart_part_ne_atom_zero (k : Fin c.length) :
    ∀ i, (c.extendPart k).part i ≠ .atom 0 := by
  intro i
  rcases eq_or_ne k i with rfl | hne <;>
    simp [extendPart_part, *, Ne.symm, succ_ne_zero]

/-- Extend an ordered partition of `n` entries, by adding singleton to the left
or appending it to one of the existing part. -/
def extend (c : OrderedPartition n) : Fin (c.length + 1) → OrderedPartition (n + 1) :=
  Fin.cons c.zeroCons c.extendPart

@[simp]
lemma extend_zero (c : OrderedPartition n) : c.extend 0 = c.zeroCons := rfl

@[simp]
lemma extend_succ (c : OrderedPartition n) (i : Fin c.length) :
    c.extend i.succ = c.extendPart i :=
  rfl

/-- Given an ordered finpartition of `n + 1`, with a leftmost part equal to `Part.atom 0`,
remove this atom to form an ordered finpartition of `n`. -/
@[simps length, simps (config := .lemmasOnly) part]
def eraseLeft (c : OrderedPartition (n + 1)) (hc : c.part 0 = .atom 0) :
    OrderedPartition n :=
  have eq : c.length - 1 + 1 = c.length := Nat.sub_add_cancel <| by simp
  { length := c.length - 1
    part i := (c.part <| i.succ.cast eq).mapPred <| by
      rw [ne_eq, ← Part.zero_mem_range]
      exact Finset.disjoint_left.mp (c.disjoint (i := 0) (by simp [Fin.ext_iff])) (by simp [hc])
    part_last_strictMono i j hlt := by simpa
    disjoint i j hne := by
      simp_rw [onFun, Part.mapPred_range_eq_preimage]
      simpa [← Finset.disjoint_coe] using (c.disjoint_setRange (by simpa)).preimage Fin.succ
    cover i := by
      simpa [Part.mapPred_range_eq_preimage, (finCongr eq).surjective.exists, exists_fin_succ, hc,
        succ_ne_zero] using c.cover i.succ }

@[simp]
theorem eraseLeft_zeroCons : c.zeroCons.eraseLeft rfl = c := by
  simp [eraseLeft, zeroCons, funext_iff]

theorem zeroCons_injective : Injective (@zeroCons n) := by
  intro c₁ c₂ h
  rw [← c₁.eraseLeft_zeroCons, ← c₂.eraseLeft_zeroCons]
  simp only [h]

@[simp]
lemma zeroCons_inj {c₁ c₂ : OrderedPartition n} :
    c₁.zeroCons = c₂.zeroCons ↔ c₁ = c₂ :=
  zeroCons_injective.eq_iff

@[simp]
theorem zeroCons_eraseLeft (c : OrderedPartition (n + 1)) (hc : c.part 0 = .atom 0) :
    (c.eraseLeft hc).zeroCons = c := by
  simp [OrderedPartition.ext_iff, eraseLeft, zeroCons, Fin.heq_fun_iff, forall_fin_succ, hc,
    ← Fin.val_inj]

/-- Given an ordered finpartition of `n+1`, with a leftmost atom different from `{0}`, remove `{0}`
from the atom that contains it, to form an ordered finpartition of `n`. -/
@[simps]
def eraseZeroPart (c : OrderedPartition (n + 1)) (hc : c.part 0 ≠ .atom 0) :
    OrderedPartition n where
  length := c.length
  part i := (c.part i).preimageSucc (c.part_ne_atom_zero hc i)
  part_last_strictMono i j hlt := by simpa
  disjoint i j hne := by
    simpa [onFun, ← Finset.disjoint_coe] using (c.disjoint_setRange hne).preimage succ
  cover i := by simpa using c.cover i.succ

@[simp]
theorem eraseZeroPart_extendPart (i : Fin c.length) :
    (c.extendPart i).eraseZeroPart (extendPart_part_ne_atom_zero c i 0) = c := by
  suffices ∀ j, ((c.extendPart i).part j).preimageSucc _ = c.part j by
    simpa [OrderedPartition.ext_iff, funext_iff]
  intro j
  rcases eq_or_ne i j with rfl | hne <;> simp [*, Ne.symm]

@[simp]
theorem extendPart_eraseZeroPart (c : OrderedPartition (n + 1)) (hc : c.part 0 ≠ .atom 0) :
    (c.eraseZeroPart hc).extendPart (c.index 0) = c := by
  suffices ∀ j, ((c.eraseZeroPart hc).extendPart (c.index 0)).part j = c.part j by
    simpa [OrderedPartition.ext_iff, funext_iff]
  intro j
  rcases eq_or_ne j (c.index 0) with rfl | hne
  · simp [Part.extendZero_preimageSucc]
  · have : c.part j 0 ≠ 0 := by
      simpa [index_eq_iff_mem_range] using hne.symm
    simp [*, Part.map_succ_preimageSucc]

/-- Extending the ordered partitions of `Fin n` bijects with the ordered partitions
of `Fin (n+1)`. -/
def extendEquiv (n : ℕ) :
    ((c : OrderedPartition n) × Fin (c.length + 1)) ≃ OrderedPartition (n + 1) where
  toFun c := c.1.extend c.2
  invFun c := if h : c.part 0 = .atom 0 then ⟨c.eraseLeft h, 0⟩ else
    ⟨c.eraseZeroPart h, .succ (c.index 0)⟩
  left_inv := by
    rintro ⟨c, o⟩
    cases o using Fin.cases with
    | zero =>
      simp
    | succ o =>
      simp [index_eq_iff_mem_range]
  right_inv c := by
    simp only
    rw [apply_dite (fun c : (c : OrderedPartition n) × Fin (c.length + 1) ↦ c.1.extend c.2)]
    split_ifs with h
    · simp
    · simp

instance instFintype : ∀ n, Fintype (OrderedPartition n)
  | 0 => Unique.fintype
  | n + 1 => letI := instFintype n; .ofEquiv _ (extendEquiv n)

variable {M : Type*} [CommMonoid M]

theorem card_succ :
    Fintype.card (OrderedPartition (n + 1)) = ∑ c : OrderedPartition n, (c.length + 1) := by
  simp [← Fintype.card_congr (extendEquiv n)]

theorem univ_two_eq : Finset.univ = {atomic 2, indiscrete 2 two_ne_zero} := by
  rw [eq_comm, ← Finset.card_eq_iff_eq_univ, card_succ]
  simp

@[to_additive]
theorem prod_univ_two (f : OrderedPartition 2 → M) :
    ∏ c, f c = f (atomic 2) * f (indiscrete 2 two_ne_zero) := by
  simp [univ_two_eq]

@[to_additive]
theorem prod_univ_three (f : OrderedPartition 3 → M) :
    ∏ c, f c = f (atomic 3) * f ((atomic 2).extendPart 0) * f ((atomic 2).extendPart 1) *
      f (indiscrete 2 two_ne_zero).zeroCons * f (indiscrete 3 (by decide)) := by
  simp only [← (extendEquiv 2).prod_comp, Fintype.prod_sigma, prod_univ_two, Fin.prod_univ_succ]
  simp [extendEquiv, mul_assoc]

end OrderedPartition

end Fin
