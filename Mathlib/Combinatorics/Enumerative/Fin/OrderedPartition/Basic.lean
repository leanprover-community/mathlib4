import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.ApplyFun

open Set Function List

namespace List

variable {α β : Type*}

theorem perm_map_iff {f : α → β} (hf : f.Injective) {l₁ l₂ : List α} :
    l₁.map f ~ l₂.map f ↔ l₁ ~ l₂ := by
  refine ⟨fun hl ↦ ?_, .map f⟩
  induction l₁ generalizing l₂ with
  | nil => simp_all
  | cons a l₁ ihl₁ =>
    obtain ⟨i, hi, rfl⟩ : ∃ (i : ℕ) (hi : i < l₂.length), l₂[i] = a := by
      rw [← mem_iff_getElem, ← mem_map_of_injective hf, ← hl.mem_iff]
      simp
    refine .trans (.cons _ <| ihl₁ ?_) (getElem_cons_eraseIdx_perm hi)
    rw [← perm_cons, ← map_cons f l₂[i] (l₂.eraseIdx i)]
    exact hl.trans <| .map _ <| (getElem_cons_eraseIdx_perm hi).symm

@[simp] -- TODO: generalize to `finSuccEquiv'`
theorem filterMap_finSuccEquiv_finRange (n : ℕ) :
    (finRange (n + 1)).filterMap (finSuccEquiv n) = finRange n := by
  simp [finRange_succ, comp_def]

theorem flatMap_filterMap_right (f : α → Option β) (l : List (List α)) :
    l.flatMap (·.filterMap f) = l.flatten.filterMap f := by
  induction l <;> simp [*]

theorem pmap_congr_prop {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) (f : ∀ a, P a → β) (l : List α)
    (hl : ∀ a ∈ l, P a) :
    l.pmap f hl = l.pmap (fun a ha ↦ f a ((h a).mpr ha)) (fun a ha ↦ (h a).mp (hl a ha)) := by
  obtain rfl : P = Q := by ext; simp [h]
  rfl

theorem pmap_cons' {P : α → Prop} (f : ∀ a, P a → β) (a : α) (l : List α)
    (ha : P a) (hl : ∀ x ∈ l, P x) :
    (a :: l).pmap f (by simpa [ha]) = f a ha :: l.pmap f hl :=
  pmap_cons ..

theorem modify_eq_set_getElem {l : List α} {n : ℕ} (h : n < l.length) (f : α → α) :
    l.modify f n = l.set n (f l[n]) :=
  modify_eq_set_get _ _

theorem modify_eq_insertIdx_eraseIdx {l : List α} {n : ℕ} (h : n < l.length) (f : α → α) :
    l.modify f n = insertIdx n (f l[n]) (l.eraseIdx n) := by
  rw [insertIdx_eraseIdx h.ne, modify_eq_set_getElem h]

theorem modify_perm_cons_eraseIdx {l : List α} {n : ℕ} (h : n < l.length) (f : α → α) :
    l.modify f n ~ f l[n] :: l.eraseIdx n := by
  rw [modify_eq_set_getElem h]
  exact set_perm_cons_eraseIdx h _

theorem Pairwise.rel_head_tail {l : List α} {R : α → α → Prop} (h₁ : l.Pairwise R) {a : α}
    (ha : a ∈ l.tail) : R (l.head fun hl ↦ by simp [hl] at ha) a := by
  generalize_proofs hl
  rw [← head_cons_tail l hl, pairwise_cons] at h₁
  exact h₁.1 a ha

theorem Pairwise.rel_head {R : α → α → Prop} [IsRefl α R] {l : List α} (h₁ : l.Pairwise R)
    {a : α} (ha : a ∈ l) : R (l.head <| ne_nil_of_mem ha) a := by
  rw [← head_cons_tail l (ne_nil_of_mem ha), mem_cons] at ha
  exact ha.elim (fun h ↦ h ▸ refl_of ..) h₁.rel_head_tail

end List

namespace Fin

@[ext]
structure OrderedPartition (n : ℕ) where
  parts : List (List (Fin n))
  sorted_le_of_mem_parts ⦃l⦄ : l ∈ parts → l.Sorted (· ≤ ·)
  not_nil_mem_parts : [] ∉ parts
  sorted_getLast_le :
    (parts.pmap getLast fun _l hl ↦ ne_of_mem_of_not_mem hl not_nil_mem_parts).Sorted (· ≤ ·)
  perm_finRange : parts.flatten.Perm (.finRange n)
  deriving DecidableEq, Repr

variable {n : ℕ}

namespace OrderedPartition

attribute [simp] not_nil_mem_parts

theorem ne_nil_of_mem_parts (c : OrderedPartition n) {l : List (Fin n)} (hl : l ∈ c.parts) :
    l ≠ [] :=
  ne_of_mem_of_not_mem hl c.not_nil_mem_parts

@[simp]
theorem parts_getElem_ne_nil (c : OrderedPartition n) (i : ℕ) (hi : i < c.parts.length) :
    c.parts[i] ≠ [] :=
  c.ne_nil_of_mem_parts (getElem_mem ..)

theorem pairwise_disjoint_parts (c : OrderedPartition n) : c.parts.Pairwise List.Disjoint := by
  have := c.perm_finRange.symm.nodup (nodup_finRange n)
  rw [nodup_flatten] at this
  exact this.2

@[simp]
theorem disjoint_getElem_parts (c : OrderedPartition n) {i j : ℕ} {hi : i < c.parts.length}
    {hj : j < c.parts.length} : c.parts[i].Disjoint c.parts[j] ↔ i ≠ j := by
  constructor
  · rintro h rfl
    simp [List.Disjoint, ← eq_nil_iff_forall_not_mem] at h
  · intro hne
    have := pairwise_iff_getElem.mp c.pairwise_disjoint_parts
    exact hne.lt_or_lt.elim (this _ _ _ _) (.symm ∘ this _ _ _ _)

theorem nodup_of_mem_parts (c : OrderedPartition n) {l : List (Fin n)} (hl : l ∈ c.parts) :
    l.Nodup :=
  (nodup_flatten.mp (c.perm_finRange.symm.nodup (nodup_finRange n))).1 l hl

@[simp]
theorem nodup_getElem_parts (c : OrderedPartition n) {i : ℕ} (hi : i < c.parts.length) :
    c.parts[i].Nodup :=
  c.nodup_of_mem_parts <| getElem_mem ..

theorem sorted_lt_of_mem_parts (c : OrderedPartition n) {l : List (Fin n)} (hl : l ∈ c.parts) :
    l.Sorted (· < ·) :=
  (c.sorted_le_of_mem_parts hl).lt_of_le (c.nodup_of_mem_parts hl)

theorem sorted_getLast_lt (c : OrderedPartition n) :
    (c.parts.pmap getLast fun _ ↦ c.ne_nil_of_mem_parts).Sorted (· < ·) := by
  apply c.sorted_getLast_le.lt_of_le
  refine c.pairwise_disjoint_parts.pmap _ fun l _ l' _ hd ↦ ?_
  exact disjoint_iff_ne.mp hd _ (getLast_mem _) _ (getLast_mem _)

@[simp]
theorem getElem_mem_getElem_iff (c : OrderedPartition n) {i j k : ℕ} {hi : i < c.parts.length}
    {hj : j < c.parts.length} {hk : k < c.parts[i].length} :
    c.parts[i][k] ∈ c.parts[j] ↔ i = j :=
  ⟨not_imp_not.mp fun h ↦ c.disjoint_getElem_parts.mpr h (getElem_mem ..), by rintro rfl; simp⟩

theorem getElem_bijective₂ (c : OrderedPartition n) :
    Bijective fun x : (i : Fin c.parts.length) × Fin c.parts[i.1].length ↦ c.parts[x.1][x.2] := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    obtain rfl : i = j := by
      dsimp at h
      simpa [← h, Fin.val_inj] using getElem_mem y.2
    simpa [Fin.val_inj, (c.nodup_getElem_parts i.2).getElem_inj_iff] using h
  · intro i
    simpa [← mem_iff_getElem, Fin.exists_iff, exists_mem_iff_getElem] using c.perm_finRange.mem_iff

@[simps symm_apply]
def equivSigma (c : OrderedPartition n) :
    Fin n ≃ (i : Fin c.parts.length) × Fin c.parts[i.1].length where
  toFun := Fintype.bijInv c.getElem_bijective₂
  invFun x := c.parts[x.1][x.2]
  left_inv := Fintype.rightInverse_bijInv _
  right_inv := Fintype.leftInverse_bijInv _

/-- Given `j : Fin n`, the index of the part to which it belongs. -/
def index (c : OrderedPartition n) (j : Fin n) : Fin c.parts.length :=
  (c.equivSigma j).1

@[simp]
theorem equivSigma_getElem (c : OrderedPartition n) (i : ℕ) (hi : i < c.parts.length)
    (j : ℕ) (hj : j < c.parts[i].length) : c.equivSigma c.parts[i][j] = ⟨⟨i, hi⟩, j, hj⟩ :=
  c.equivSigma.apply_symm_apply ⟨⟨i, hi⟩, ⟨j, hj⟩⟩

@[simp]
theorem index_getElem (c : OrderedPartition n) (i : ℕ) (hi : i < c.parts.length)
    (j : ℕ) (hj : j < c.parts[i].length) : c.index c.parts[i][j] = ⟨i, hi⟩ :=
  congrArg Sigma.fst (c.equivSigma_getElem ..)

lemma index_eq_iff_mem_getElem (c : OrderedPartition n) {i j} :
    c.index i = j ↔ i ∈ c.parts[j] := by
  rcases c.equivSigma.symm.surjective i with ⟨⟨k, l⟩, rfl⟩
  simp [Fin.val_inj]

@[simp]
lemma mem_getElem_index (c : OrderedPartition n) (i : Fin n) : i ∈ c.parts[(c.index i).1] :=
  c.index_eq_iff_mem_getElem.mp rfl

@[simp]
lemma head_getElem_index_zero [NeZero n] (c : OrderedPartition n) :
    c.parts[(c.index 0).1].head (by simp) = 0 := by
  refine le_antisymm ?_ (Fin.zero_le' _)
  exact (c.sorted_le_of_mem_parts <| getElem_mem _).rel_head (c.mem_getElem_index 0)

@[simp]
lemma zero_cons_tail_getElem_index_zero [NeZero n] (c : OrderedPartition n) :
    0 :: c.parts[(c.index 0).1].tail = c.parts[c.index 0] := by
  simpa only [c.head_getElem_index_zero] using head_cons_tail c.parts[(c.index 0).1] (by simp)

@[simp]
theorem sum_length_parts (c : OrderedPartition n) : (c.parts.map length).sum = n := by
  rw [← length_flatten, c.perm_finRange.length_eq, length_finRange]

@[simp]
theorem parts_eq_nil (c : OrderedPartition n) : c.parts = [] ↔ n = 0 := by
  refine ⟨fun h ↦ by simpa [h] using c.sum_length_parts.symm, ?_⟩
  rintro rfl
  rw [eq_nil_iff_forall_not_mem, Unique.forall_iff]
  exact c.not_nil_mem_parts

theorem length_parts_neZero [NeZero n] (c : OrderedPartition n) : NeZero c.parts.length :=
  ⟨(length_eq_zero.trans c.parts_eq_nil).not.mpr (NeZero.ne n)⟩

attribute [scoped instance] length_parts_neZero

def zeroCons (c : OrderedPartition n) : OrderedPartition (n + 1) where
  parts := [0] :: c.parts.map (·.map Fin.succ)
  sorted_le_of_mem_parts := by simpa [List.Sorted, List.pairwise_map] using c.sorted_le_of_mem_parts
  not_nil_mem_parts := by simp
  sorted_getLast_le := by
    simpa [Sorted, pmap_map, pairwise_pmap] using c.sorted_getLast_le
  perm_finRange := by
    rw [List.flatten_cons, List.singleton_append, finRange_succ, ← List.map_flatten]
    exact .cons _ <| .map _ c.perm_finRange

@[simp]
theorem index_zero_zeroCons (c : OrderedPartition n) : c.zeroCons.index 0 = 0 := by
  rw [index_eq_iff_mem_getElem]
  apply mem_singleton_self

@[simp]
theorem length_parts_zeroCons (c : OrderedPartition n) :
    c.zeroCons.parts.length = c.parts.length + 1 := by
  simp [zeroCons]

def atomic (n : ℕ) : OrderedPartition n where
  parts := (finRange n).map ([·])
  sorted_le_of_mem_parts := by simp
  not_nil_mem_parts := by simp
  sorted_getLast_le := by simpa [Sorted, pmap_map, pairwise_pmap] using pairwise_le_finRange n
  perm_finRange := by simp [← flatMap_def]

@[simp]
theorem zeroCons_atomic (n : ℕ) : (atomic n).zeroCons = atomic (n + 1) := by
  ext1
  simp [atomic, zeroCons, finRange_succ]

theorem singleton_zero_mem_parts [NeZero n] (c : OrderedPartition n) :
    [0] ∈ c.parts ↔ c.parts.head (by simp [NeZero.ne]) = [0] := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ head_mem _⟩
  rcases mem_iff_getElem.mp h with ⟨i, hi, hci⟩
  rcases i.eq_zero_or_pos with rfl | hi₀
  · rw [head_eq_getElem, ← hci]
  · have := pairwise_iff_getElem.mp c.sorted_getLast_lt 0 i (by simp [length_pos, NeZero.ne])
      (by simpa) hi₀
    simp [hci, (Fin.zero_le' _).not_lt] at this

/-- An ordered partition is `zeroCons c` for some `c` iff `[0]` is one of the parts. -/
theorem range_zeroCons : Set.range (@zeroCons n) = {c | [0] ∈ c.parts} := by
  refine (range_subset_iff.mpr fun c ↦ mem_cons_self _ _).antisymm fun c hc ↦ ?_
  obtain ⟨L, hL⟩ : ∃ L : List (List (Fin n)), c.parts = [0] :: L.map (·.map Fin.succ) := by
    rw [mem_setOf_eq, singleton_zero_mem_parts] at hc
    have : ∀ l ∈ c.parts.tail, ∀ x ∈ l, x ≠ 0 := by
      rintro l hl _ hl₀ rfl
      refine c.pairwise_disjoint_parts.rel_head_tail hl ?_ hl₀
      simp [hc]
    use c.parts.tail.pmap (fun l hl ↦ l.pmap Fin.pred hl) this
    simp [map_pmap, ← hc]
  use! L
  · simpa [hL, Sorted, pairwise_map] using c.sorted_le_of_mem_parts
  · simpa [hL] using c.not_nil_mem_parts
  · simpa [hL, Sorted, pmap_map, pairwise_pmap] using c.sorted_getLast_le
  · rw [← perm_map_iff (succ_injective _), ← perm_cons, ← finRange_succ,
      map_flatten, ← singleton_append, ← flatten_cons, ← hL]
    exact c.perm_finRange
  · ext1
    exact hL.symm

/-- Auxiliary definition for `extendPart`. We move it to a separate definition
so that we can prove some `Iff` lemmas about it before we give the definition. -/
def extendPart.parts (L : List (List (Fin n))) (i : Fin L.length) : List (List (Fin (n + 1))) :=
  (L.map (·.map Fin.succ)).modify (List.cons 0) i

theorem extendPart.parts_sorted_le_iff {L : List (List (Fin n))} {i : Fin L.length} :
    (∀ l ∈ parts L i, l.Sorted (· ≤ ·)) ↔ ∀ l ∈ L, l.Sorted (· ≤ ·) := by
  simp [parts, mem_iff_getElem, @forall_swap (List _), getElem_modify, Sorted,
    apply_ite (Pairwise _), pairwise_map]

theorem extendPart.parts_sorted_getLast_le_iff {L : List (List (Fin n))} {i : Fin L.length}
    (h₁ : ∀ l ∈ parts L i, l ≠ []) (h₂ : ∀ l ∈ L, l ≠ []) :
    ((parts L i).pmap getLast h₁).Sorted (· ≤ ·) ↔ (L.pmap getLast h₂).Sorted (· ≤ ·) := by
  simp? [Sorted, parts, ← pmap_cons' getLast, pmap_map, modify_eq_take_cons_drop, ← map_take, ←
      map_drop, pmap_congr_prop fun _ ↦ map_eq_nil_iff.not, h₂] says
    simp only [Sorted, ne_eq, parts, length_map, is_lt, modify_eq_take_cons_drop, ← map_take,
      getElem_map, ← map_drop, pmap_append, pmap_map, getLast_map,
      pmap_congr_prop fun _ ↦ map_eq_nil_iff.not, pmap_cons, map_eq_nil_iff, getElem_mem, h₂,
      not_false_eq_true, getLast_cons]
  simp only [← map_pmap succ, ← map_cons succ, ← map_append, pairwise_map, succ_le_succ_iff,
    ← pmap_cons' getLast, ← pmap_append']
  simp

def extendPart (c : OrderedPartition n) (i : Fin c.parts.length) : OrderedPartition (n + 1) where
  parts := (c.parts.map (·.map Fin.succ)).modify (List.cons 0) i
  sorted_le_of_mem_parts := by
    suffices List.Sorted (· ≤ ·) c.parts[i] ∧ ∀ l ∈ c.parts.eraseIdx i, List.Sorted (· ≤ ·) l by
      intro l hl
      rw [(modify_perm_cons_eraseIdx (by simp) _).mem_iff] at hl
      revert l
      simpa [Sorted, pairwise_map, eraseIdx_map]
    exact ⟨c.sorted_le_of_mem_parts (getElem_mem ..), fun l hl ↦ c.sorted_le_of_mem_parts <|
      eraseIdx_subset _ _ hl⟩
  not_nil_mem_parts := by simp [mem_iff_getElem, getElem_modify, ite_eq_iff]
  sorted_getLast_le := by
    simp? [Sorted, ← pmap_cons' getLast, pmap_map, modify_eq_take_cons_drop, ← map_take, ← map_drop,
        pmap_congr_prop fun _ ↦ map_eq_nil_iff.not] says
      simp only [Sorted, ne_eq, length_map, is_lt, modify_eq_take_cons_drop, ← map_take,
        getElem_map, ← map_drop, pmap_append, pmap_map, getLast_map,
        pmap_congr_prop fun _ ↦ map_eq_nil_iff.not, pmap_cons, map_eq_nil_iff, parts_getElem_ne_nil,
        not_false_eq_true, getLast_cons]
    simp only [← map_pmap succ, ← map_cons succ, ← map_append, pairwise_map, succ_le_succ_iff,
      ← pmap_cons' getLast, ← pmap_append']
    convert c.sorted_getLast_le
    rw [← set_eq_take_cons_drop _ i.2, set_getElem_self]
  perm_finRange := calc
    ((c.parts.map (·.map Fin.succ)).modify (List.cons 0) i).flatten
      ~ ((0 :: (map (map succ) c.parts)[i]) :: (map (map succ) c.parts).eraseIdx i).flatten :=
      (modify_perm_cons_eraseIdx (by simp) _).flatten
    _ = 0 :: map succ (c.parts[i] :: c.parts.eraseIdx i).flatten := by simp [eraseIdx_map]
    _ ~ 0 :: map succ (finRange n) :=
      .cons _ <| .map _ <| (getElem_cons_eraseIdx_perm i.2).flatten.trans c.perm_finRange
    _ = finRange (n + 1) := .symm <| finRange_succ n

@[simp]
theorem length_parts_extendPart (c : OrderedPartition n) (i : Fin c.parts.length) :
    (c.extendPart i).parts.length = c.parts.length := by
  simp [extendPart]

@[simp]
theorem getElem_extendPart_same (c : OrderedPartition n) (i : Fin c.parts.length) :
    (c.extendPart i).parts[i.1] = 0 :: c.parts[i].map succ := by
  simp [extendPart]

@[simp]
theorem getElem_extendPart_of_ne (c : OrderedPartition n) (i : Fin c.parts.length) {j : ℕ}
    (hne : i.1 ≠ j) (hj : j < (c.extendPart i).parts.length) :
    (c.extendPart i).parts[j] = (c.parts[j]'(by simpa using hj)).map succ := by
  simp [extendPart, hne]

@[simp]
theorem index_zero_extendPart (c : OrderedPartition n) (i : Fin c.parts.length) :
    (c.extendPart i).index 0 = i.cast (c.length_parts_extendPart i).symm := by
  simp [index_eq_iff_mem_getElem]

theorem val_index_zero_extendPart (c : OrderedPartition n) (i : Fin c.parts.length) :
    ((c.extendPart i).index 0 : ℕ) = i := by
  simp

theorem extendPart_injective (c : OrderedPartition n) : c.extendPart.Injective := by
  intro i j h
  ext
  rw [← c.val_index_zero_extendPart, ← c.val_index_zero_extendPart, h]

def extend (c : OrderedPartition n) : Fin (c.parts.length + 1) → OrderedPartition (n + 1) :=
  Matrix.vecCons c.zeroCons c.extendPart

@[simp]
lemma extend_zero (c : OrderedPartition n) : c.extend 0 = c.zeroCons := rfl

@[simp]
lemma extend_succ (c : OrderedPartition n) (i : Fin c.parts.length) :
    c.extend i.succ = (c.extendPart i) :=
  rfl

theorem parts_eq_of_extend (c : OrderedPartition n) (i : Fin (c.parts.length + 1)) :
    c.parts = ((c.extend i).parts.map (·.filterMap (finSuccEquiv n))).filter (!·.isEmpty) := by
  symm
  cases i using Fin.cases <;>
    simp +contextual [zeroCons, extendPart, modify_eq_set_get, comp_def, c.ne_nil_of_mem_parts]

theorem extend_injective (c : OrderedPartition n) : c.extend.Injective := by
  intro i j h
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ _ => exact absurd congr($h |>.parts.length) (by simp)
  | succ =>
    cases j using Fin.cases with
    | zero => exact absurd congr($h |>.parts.length) (by simp)
    | succ _ => simpa [Fin.val_inj] using congr($h |>.index 0 |>.val)

theorem extend_injective₂ :
    Injective fun ci : (c : OrderedPartition n) × Fin (c.parts.length + 1) ↦ ci.1.extend ci.2 := by
  rintro ⟨c₁, i₁⟩ ⟨c₂, i₂⟩ h
  dsimp only at h
  obtain rfl : c₁ = c₂ := by
    ext1
    rw [parts_eq_of_extend c₁ i₁, parts_eq_of_extend c₂ i₂, h]
  simp [c₁.extend_injective h]

theorem extend_surjective : 
    Surjective fun ci : (c : OrderedPartition n) × Fin (c.parts.length + 1) ↦ ci.1.extend ci.2 := by
  intro c
  have : CanLift (Fin (n + 1)) (Fin n) Fin.succ (· ≠ 0) := ⟨fun _ ↦ exists_succ_eq_of_ne_zero⟩
  by_cases hc : [0] ∈ c.parts
  · obtain ⟨L, hL⟩ : ∃ L : List (List (Fin (n + 1))), c.parts = [0] :: L := by
      rw [← head_cons_tail c.parts, c.singleton_zero_mem_parts.mp hc]
      use c.parts.tail
    have hLf : L.flatten ~ (finRange n).map succ := by
      rw [← perm_cons, ← finRange_succ, ← rel_congr_right c.perm_finRange]
      simp [hL]
    lift L to List (List (Fin n)) using by
      suffices 0 ∉ L.flatten by simpa [@imp_not_comm _ (_ = _)] using this
      rw [hLf.mem_iff]
      simp
    rw [← map_flatten, perm_map_iff (succ_injective _)] at hLf
    use! L
    · intro l hl
      
      
    

/-
  obtain ⟨L, i, hi, hcL⟩ :
      ∃ L : List (List (Fin (n + 1))), ∃ i < L.length, c.parts = L.modify (0 :: ·) i :=
    ⟨c.parts.modify .tail (c.index 0), c.index 0, by simp, by simp [modify_eq_set_getElem]⟩
  have hLf : L.flatten ~ (finRange n).map succ := by
    rw [← perm_cons, ← finRange_succ, ← rel_congr_right c.perm_finRange, hcL,
      modify_eq_set_getElem hi, rel_congr_right (set_perm_cons_eraseIdx hi _).flatten,
      flatten_cons, cons_append, ← flatten_cons]
    exact .cons _ (getElem_cons_eraseIdx_perm ..).flatten.symm
  lift L to List (List (Fin n)) using by
    suffices 0 ∉ L.flatten by simpa [@imp_not_comm _ (_ = _)] using this
    rw [hLf.mem_iff]
    simp
  rw [← map_flatten, perm_map_iff (succ_injective _)] at hLf
-/

theorem eq_concat_succ_of_ne_zero (c : OrderedPartition (n + 1)) {l : List (Fin (n + 1))}
    (h₁ : l ∈ c.parts) (h₂ : l ≠ [0]) : ∃ l' a, l = l' ++ [succ a] := by
  rcases l.eq_nil_or_concat'.resolve_left (c.ne_nil_of_mem_parts h₁) with ⟨l', b, rfl⟩
  cases b using Fin.cases with
  | zero =>
    have := c.sorted_lt_of_mem_parts h₁
    simp_all [Sorted, pairwise_append, ← eq_nil_iff_forall_not_mem]
  | succ a => exact ⟨_, _, rfl⟩

def mapPred (c : OrderedPartition (n + 1)) : OrderedPartition n where
  parts := (c.parts.map (·.filterMap (finSuccEquiv n))).filter (!·.isEmpty)
  sorted_le_of_mem_parts := by
    suffices ∀ l ∈ c.parts, Sorted (· ≤ ·) (filterMap (finSuccEquiv n) l) by
      simp_all [Fin.forall_fin_succ, @forall_swap (List _), succ_ne_zero]
    refine fun l hl ↦ (c.sorted_le_of_mem_parts hl).filterMap _ ?_
    simp +contextual [@forall_swap (_ ≤ _)]
  not_nil_mem_parts := by simp
  sorted_getLast_le := by
    simp only [filter_map, comp_def, pmap_map, Sorted, pairwise_pmap]
    refine (((pairwise_pmap _).mp c.sorted_getLast_le).filter _).imp_of_mem ?_
    simp +contextual only [mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, isEmpty_eq_false,
      ne_eq, filterMap_eq_nil_iff, finSuccEquiv_eq_none, not_forall, Classical.not_imp, exists_prop,
      Unique.forall_iff]
    rintro l₁ l₂ ⟨hl₁, hl₁'⟩ ⟨hl₂, hl₂'⟩ H
    rcases c.eq_concat_succ_of_ne_zero hl₁ (by rintro rfl; simp at hl₁') with ⟨l₁, a₁, rfl⟩
    rcases c.eq_concat_succ_of_ne_zero hl₂ (by rintro rfl; simp at hl₂') with ⟨l₂, a₂, rfl⟩
    simpa using H
  perm_finRange := by
    rw [flatten_filter_not_isEmpty, ← flatMap_def, flatMap_filterMap_right,
      ← filterMap_finSuccEquiv_finRange]
    exact .filterMap _ c.perm_finRange

theorem zero_nmem_of_mem_tail (c : OrderedPartition (n + 1)) (h : [0] ∈ c.parts) {l}
    (hl : l ∈ c.parts.tail) : 0 ∉ l :=
  c.pairwise_disjoint_parts.rel_head_tail hl <| by simp_all [singleton_zero_mem_parts]

theorem zeroCons_mapPred (c : OrderedPartition (n + 1)) (h : [0] ∈ c.parts) :
    c.mapPred.zeroCons = c := by
  ext1
  obtain ⟨L, hL⟩ : ∃ L, c.parts = [0]

theorem mapPred_parts_of_singleton_zero_mem (c : OrderedPartition (n + 1)) (h : [0] ∈ c.parts) :
    c.mapPred.parts =
      c.parts.tail.pmap
        (fun l (hl : 0 ∉ l) ↦ l.pmap pred fun a ha ↦ ne_of_mem_of_not_mem ha hl)
        (fun _ ↦ c.zero_nmem_of_mem_tail h) := by
  simp [mapPred]

@[simp]
lemma mapPred_zeroCons (c : OrderedPartition n) : c.zeroCons.mapPred = c := by
  ext1
  simp +contextual [zeroCons, mapPred, comp_def, c.ne_nil_of_mem_parts]

@[simp]
lemma mapPred_extendPart (c : OrderedPartition n) (i : Fin c.parts.length) :
    (c.extendPart i).mapPred = c := by
  ext1
  simp +contextual [extendPart, mapPred, modify_eq_set_get, comp_def, c.ne_nil_of_mem_parts]

@[simp]
lemma mapPred_extend (c : OrderedPartition n) (i : Fin (c.parts.length + 1)) :
    (c.extend i).mapPred = c := by
  cases i using Fin.cases <;> simp

def extendInv (c : OrderedPartition (n + 1)) :
    (c : OrderedPartition n) × Fin (c.parts.length + 1) := by
  refine ⟨c.mapPred, if h₀ : [0] ∈ c.parts.head? then 0 else .succ <| (c.index 0).cast ?_⟩
  

-- namespace OrderedPartition

-- /-- A part of an ordered finpartition. It is a nonempty finite set in `Fin n`,
-- but we use sorted tuples instead, so that we can get nice definitional equalities
-- for the size and the embedding.  -/
-- @[ext]
-- structure Part (n : ℕ) where
--   size : ℕ
--   size_ne_zero : size ≠ 0
--   toFun : Fin size → Fin n
--   strictMono : StrictMono toFun
--   deriving DecidableEq, Repr

-- namespace Part

-- variable {m n : ℕ}

-- initialize_simps_projections Part (toFun → apply)

-- instance size_neZero (p : Part n) : NeZero p.size := ⟨p.size_ne_zero⟩

-- attribute [simp] size_ne_zero

-- @[simp]
-- theorem size_pos (p : Part n) : 0 < p.size := Nat.pos_iff_ne_zero.mpr p.size_ne_zero

-- @[simp]
-- theorem one_le_size (p : Part n) : 1 ≤ p.size := p.size_pos

-- attribute [coe] toFun
-- instance : CoeFun (Part n) fun p ↦ Fin p.size → Fin n where coe := toFun

-- @[simp]
-- theorem lt_iff_lt (p : Part n) {i j : Fin p.size} : p i < p j ↔ i < j :=
--   p.strictMono.lt_iff_lt

-- @[simp]
-- theorem le_iff_le (p : Part n) {i j : Fin p.size} : p i ≤ p j ↔ i ≤ j :=
--   p.strictMono.le_iff_le

-- theorem injective (p : Part n) : Injective p := p.strictMono.injective

-- @[simp]
-- theorem apply_inj (p : Part n) {i j : Fin p.size} : p i = p j ↔ i = j :=
--   p.injective.eq_iff

-- /-- The last (and the greatest) element of a part.
-- We introduce a definition instead of using `p ⊤`
-- to avoid dependent types. -/
-- def last (p : Part n) : Fin n := p ⊤

-- @[simp] lemma apply_top (p : Part n) : p ⊤ = p.last := rfl

-- /-!
-- ### Equivalence to nonempty `Finset`s
-- -/

-- /-- Range of a `OrderedFinpartition.Part` as a `Finset`. -/
-- protected def range (p : Part n) : Finset (Fin n) :=
--   Finset.univ.map ⟨p, p.strictMono.injective⟩

-- @[simp]
-- theorem coe_range (p : Part n) : (p.range : Set (Fin n)) = Set.range p := by
--   simp [Part.range]

-- theorem mem_range (p : Part n) {i : Fin n} : i ∈ p.range ↔ ∃ j, p j = i := by
--   simp [Part.range]

-- @[simp]
-- theorem card_range (p : Part n) : p.range.card = p.size := by simp [Part.range]

-- theorem range_nonempty (p : Part n) : p.range.Nonempty := by simp [← Finset.card_pos]

-- theorem range_injective : Injective (@Part.range n) := by
--   intro p₁ p₂ h
--   have h₁ : p₁.size = p₂.size := by simpa using congr(Finset.card $h)
--   cases p₁; cases p₂
--   subst h₁
--   congr
--   rw [← StrictMono.range_inj ‹_› ‹_›]
--   simpa [Part.range, ← Finset.coe_inj] using h

-- @[simp]
-- lemma range_inj {p₁ p₂ : Part n} : p₁.range = p₂.range ↔ p₁ = p₂ := range_injective.eq_iff

-- /-- Define a `Part n` from a nonempty `Finset`. -/
-- @[simps]
-- def ofFinset (s : Finset (Fin n)) (hs : s.Nonempty) : Part n where
--   size := s.card
--   size_ne_zero := by simp [hs.ne_empty]
--   toFun := s.orderEmbOfFin rfl
--   strictMono := OrderEmbedding.strictMono _

-- @[simp]
-- theorem range_ofFinset (s : Finset (Fin n)) (hs : s.Nonempty) : (ofFinset s hs).range = s := by
--   simp [Part.range, ← Finset.coe_inj]

-- @[simp]
-- theorem ofFinset_range (p : Part n) : ofFinset p.range p.range_nonempty = p := by
--   simp [← range_inj]

-- /-- Equivalence between `Part n` and the set of nonempty finite sets in `Fin n`. -/
-- @[simps]
-- def equivFinset : Part n ≃ {s : Finset (Fin n) // s.Nonempty} where
--   toFun p := ⟨p.range, p.range_nonempty⟩
--   invFun s := ofFinset s.1 s.2
--   left_inv := ofFinset_range
--   right_inv _ := Subtype.eq <| range_ofFinset _ _

-- /-- Each `Fin n` has finitely many parts. -/
-- instance : Fintype (Part n) := .ofEquiv _ equivFinset.symm

-- @[simp]
-- theorem card_part : Fintype.card (Part n) = 2 ^ n - 1 := by
--   simp [Fintype.card_congr equivFinset, Finset.nonempty_iff_ne_empty]

-- @[simp]
-- theorem size_le (p : Part n) : p.size ≤ n := by simpa using p.range.card_le_univ

-- theorem pos (p : Part n) : 0 < n := p.size_pos.trans_le p.size_le

-- theorem neZero (p : Part n) : NeZero n := .of_pos p.pos

-- /-- There are nonempty parts of `Fin 0`. -/
-- instance instIsEmpty : IsEmpty (Part 0) where
--   false p := p.pos.ne rfl

-- @[simp]
-- theorem zero_mem_range (p : Part n) :
--     haveI := p.neZero; 0 ∈ p.range ↔ p 0 = 0 := by
--   haveI := p.neZero
--   rw [p.mem_range]
--   refine ⟨fun ⟨j, hj⟩ ↦ le_antisymm ?_ (Fin.zero_le' _), fun h ↦ ⟨0, h⟩⟩
--   exact hj ▸ p.strictMono.monotone (Fin.zero_le' _)

-- theorem apply_ne_zero {p : Part n} :
--     haveI := p.neZero; (∀ i, p i ≠ 0) ↔ p 0 ≠ 0 := by
--   simp only [ne_eq, ← not_exists, ← mem_range, zero_mem_range]

-- /-- A part that contains a single element. -/
-- @[simps]
-- def atom (i : Fin n) : Part n where
--   size := 1
--   size_ne_zero := one_ne_zero
--   toFun _ := i
--   strictMono := Subsingleton.strictMono _

-- @[simp]
-- lemma atom_last (i : Fin n) : (atom i).last = i := rfl

-- @[simp]
-- theorem atom_range (i : Fin n) : (atom i).range = {i} := by simp [Part.range]

-- theorem atom_injective : (@atom n).Injective := LeftInverse.injective atom_last

-- @[simp]
-- lemma atom_inj {i j : Fin n} : atom i = atom j ↔ i = j := atom_injective.eq_iff

-- @[simp]
-- theorem range_eq_singleton {p : Part n} {i : Fin n} : p.range = {i} ↔ p = atom i :=
--   range_injective.eq_iff' <| atom_range i

-- theorem size_eq_one {p : Part n} : p.size = 1 ↔ ∃ i, atom i = p := by
--   rw [← card_range, Finset.card_eq_one]
--   simp_rw [range_eq_singleton, eq_comm]

-- theorem one_lt_size_of_eq_of_ne_atom {p : Part n} {i j} (h₁ : p i = j) (h₂ : p ≠ atom j) :
--     1 < p.size := by
--   rw [p.one_le_size.gt_iff_ne, ne_eq, size_eq_one]
--   rintro ⟨k, rfl⟩
--   simp_all

-- @[simp]
-- lemma last_eq_zero {p : Part n} : haveI := p.neZero; p.last = 0 ↔ p = atom 0 := by
--   refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
--   suffices ∀ i, p i = p.last by
--     rw [← range_eq_singleton, ← p.range_nonempty.subset_singleton_iff]
--     simpa [Finset.subset_iff, Part.mem_range, h] using this
--   exact fun i ↦ le_antisymm (p.strictMono.monotone le_top) <| h.symm ▸ Nat.zero_le _

-- @[simp]
-- lemma last_pos {p : Part n} : haveI := p.neZero; 0 < p.last ↔ p ≠ atom 0 := by
--   haveI := p.neZero
--   simp [pos_iff_ne_zero']

-- /-- If `n ≠ 0`, then `atom 0` is the default `Part n`. -/
-- instance instInhabited [NeZero n] : Inhabited (Part n) := ⟨atom 0⟩

-- @[simp]
-- theorem default_eq_atom [NeZero n] : (default : Part n) = atom 0 := rfl

-- /-- There is a unique part in `Fin 1`. -/
-- instance instUnique : Unique (Part 1) where
--   uniq p := range_injective <| by simp only [(range_nonempty _).eq_univ]

-- /-- The part that contains the whole type. -/
-- @[simps]
-- def univ (n : ℕ) (h : n ≠ 0) : Part n where
--   size := n
--   size_ne_zero := h
--   toFun := id
--   strictMono := strictMono_id

-- @[simp]
-- theorem range_univ (n : ℕ) (h : n ≠ 0) : (univ n h).range = .univ := by
--   simp [Part.range]

-- @[simp]
-- theorem last_univ (n : ℕ) [NeZero n] : (univ n (NeZero.ne _)).last = ⊤ := rfl

-- theorem size_eq_iff (h : n ≠ 0) {p : Part n} : p.size = n ↔ p = univ n h := by
--   simp [← range_inj, ← Finset.card_eq_iff_eq_univ]

-- @[simp]
-- theorem atom_eq_univ_iff (h : n ≠ 0) (i : Fin n) : atom i = univ n h ↔ n = 1 := by
--   simpa [← size_eq_iff h] using eq_comm

-- @[simp]
-- theorem univ_eq_atom_iff (h : n ≠ 0) (i : Fin n) : univ n h = atom i ↔ n = 1 :=
--   eq_comm.trans <| atom_eq_univ_iff h i

-- @[simp]
-- theorem univ_one : univ 1 one_ne_zero = atom 0 := by simp

-- /-- The embedding as a bundled `OrderEmbedding`. -/
-- @[simps! (config := .asFn)]
-- def emb (p : Part n) : Fin p.size ↪o Fin n :=
--   .ofStrictMono p p.strictMono

-- /-- Map a `Part m` along an order embedding from `Fin m` to `Fin n`.

-- The two intended applications are:
-- - `f = Fin.succOrderEmb`;
-- - `f = q.emb` for `q : Part n` and `p : Part q.size`. -/
-- @[simps (config := .asFn)]
-- def map (f : Fin m ↪o Fin n) (p : Part m) : Part n where
--   __ := p
--   toFun := f ∘ p
--   strictMono := f.strictMono.comp p.strictMono

-- @[simp]
-- theorem range_map (p : Part m) (f : Fin m ↪o Fin n) :
--     (p.map f).range = p.range.map f.toEmbedding := by
--   ext; simp [Part.mem_range]

-- @[simp]
-- theorem map_inj {p₁ p₂ : Part m} {f : Fin m ↪o Fin n} : p₁.map f = p₂.map f ↔ p₁ = p₂ := by
--   simp [← range_inj]

-- @[simps (config := .asFn)]
-- def mapEmb (f : Fin m ↪o Fin n) : Part m ↪ Part n :=
--   ⟨map f, fun _ _ ↦ map_inj.mp⟩

-- @[simp]
-- theorem last_map (p : Part m) (f : Fin m ↪o Fin n) : (p.map f).last = f p.last :=
--   rfl

-- @[simp]
-- theorem map_atom (f : Fin m ↪o Fin n) (i : Fin m) : (atom i).map f = atom (f i) := rfl

-- @[simp]
-- theorem map_eq_atom {p : Part m} {f : Fin m ↪o Fin n} {i : Fin n} :
--     p.map f = atom i ↔ ∃ j, f j = i ∧ p = atom j := by
--   refine ⟨fun h ↦ ?_, fun ⟨j, hji, hpj⟩ ↦ by simp [*]⟩
--   obtain ⟨j, rfl⟩ : ∃ j, atom j = p := by
--     rw [← size_eq_one, ← map_size, h, atom_size]
--   use j, by simpa using h

-- end Part

-- end OrderedPartition

-- /-- A partition of `Fin n` into finitely many nonempty subsets, given by the increasing
-- parameterization of these subsets. We order the subsets by increasing greatest element.
-- This definition is tailored-made for the Faa di Bruno formula, and probably not useful elsewhere,
-- because of the specific parameterization by `Fin n` and the peculiar ordering. -/
-- @[ext]
-- structure OrderedPartition (n : ℕ) where
--   /-- The number of parts in the partition -/
--   length : ℕ
--   /-- The size of each part -/
--   part : Fin length → OrderedPartition.Part n
--   /-- The parts are ordered by increasing greatest element. -/
--   part_last_strictMono : StrictMono fun m ↦ (part m).last
--   /-- The parts are disjoint -/
--   disjoint : Pairwise (Disjoint on fun m ↦ (part m).range)
--   /-- The parts cover everything -/
--   cover x : ∃ m, x ∈ (part m).range
--   deriving DecidableEq

-- namespace OrderedPartition

-- /-! ### Basic API for ordered finpartitions -/

-- /-- The ordered finpartition of `Fin n` into singletons. -/
-- @[simps] def atomic (n : ℕ) : OrderedPartition n where
--   length := n
--   part i :=  .atom i
--   part_last_strictMono := strictMono_id
--   disjoint _ _ h := by simp [h.symm]
--   cover m := by simp

-- variable {n : ℕ} (c : OrderedPartition n)

-- instance : Inhabited (OrderedPartition n) := ⟨atomic n⟩

-- @[simp]
-- theorem default_eq_atomic : default = atomic n := rfl

-- @[simp]
-- lemma part_last_inj {i j : Fin c.length} : (c.part i).last = (c.part j).last ↔ i = j :=
--   c.part_last_strictMono.injective.eq_iff

-- @[simp]
-- lemma part_last_lt_part_last {i j : Fin c.length} : (c.part i).last < (c.part j).last ↔ i < j :=
--   c.part_last_strictMono.lt_iff_lt

-- @[simp]
-- lemma part_last_le_part_last {i j : Fin c.length} : (c.part i).last ≤ (c.part j).last ↔ i ≤ j :=
--   c.part_last_strictMono.le_iff_le

-- lemma length_le : c.length ≤ n := by
--   simpa only [Fintype.card_fin]
--     using Fintype.card_le_of_injective _ c.part_last_strictMono.injective

-- lemma part_injective : Injective c.part :=
--   c.part_last_strictMono.injective.of_comp (f := Part.last)

-- @[simp]
-- lemma part_inj {i j} : c.part i = c.part j ↔ i = j := c.part_injective.eq_iff

-- lemma part_injective₂ :
--     Injective fun x : (i : Fin c.length) × Fin (c.part i).size ↦ c.part x.1 x.2 := by
--   rintro ⟨i, x⟩ ⟨j, y⟩ h
--   obtain rfl : i = j := by
--     apply c.disjoint.eq
--     have h : ∃ x y, c.part j y = c.part i x := ⟨x, y, h.symm⟩
--     simpa [onFun, Finset.disjoint_left, Part.mem_range] using h
--   simpa using (c.part i).injective h

-- theorem part_bijective₂ :
--     Bijective fun x : (i : Fin c.length) × Fin (c.part i).size ↦ c.part x.1 x.2 :=
--   ⟨c.part_injective₂, fun i ↦ by simpa [Part.mem_range] using c.cover i⟩

-- @[simp]
-- lemma part_inj₂ {i j i' j'} : c.part i j = c.part i' j' ↔ i = i' ∧ (j : ℕ) = j' := by
--   simpa +contextual only [Sigma.mk.inj_iff, ← exists_prop, Fin.heq_ext_iff]
--     using c.part_injective₂.eq_iff (a := ⟨i, j⟩) (b := ⟨i', j'⟩)

-- @[simp]
-- lemma part_mem_range {i j k} : c.part i j ∈ (c.part k).range ↔ i = k := by
--   suffices i = k → ∃ (x : Fin (c.part k).size), (j : ℕ) = x by
--     simpa [Part.mem_range, eq_comm] using this
--   rintro rfl
--   use j

-- /-- The finite set of all parts of an ordered finpartition. -/
-- def parts : Finset (Part n) :=
--   Finset.univ.map ⟨c.part, c.part_injective⟩

-- @[simp]
-- lemma card_parts : c.parts.card = c.length := by simp [parts]

-- @[simp]
-- lemma coe_parts : c.parts.toSet = Set.range c.part := by simp [parts]

-- @[simp]
-- lemma mem_parts {p} : p ∈ c.parts ↔ ∃ i, c.part i = p := by simp [parts]

-- /-- An ordered finpartition is completely determined by the finite set of its parts. -/
-- theorem parts_injective : Injective (@parts n) := by
--   intro c₁ c₂ h
--   have h₁ : c₁.length = c₂.length := by simpa using congr($h |>.card)
--   replace h : Set.range c₁.part = Set.range c₂.part := by
--     simp only [← coe_parts, h]
--   cases' c₁ with length₁ part₁ mono₁ disj₁ _
--   cases' c₂ with length₂ part₂ mono₂ disj₂ _
--   subst h₁
--   suffices part₁ = part₂ by congr
--   have h₂ : (part₁ · |>.last) = (part₂ · |>.last) := by
--     rw [← mono₁.range_inj mono₂]
--     simpa only [← Set.range_comp] using congr((fun p ↦ p ⊤) '' $h)
--   ext1 i
--   obtain ⟨j, hj⟩ : part₂ i ∈ Set.range part₁ := by simp [h]
--   have h₃ : part₁ i ⊤ = part₁ j ⊤ := .trans congr($h₂ i) <| .symm congr($hj ⊤)
--   rw [← hj, mono₁.injective h₃]

-- theorem disjoint_setRange {i j} (h : i ≠ j) : Disjoint (range (c.part i)) (range (c.part j)) := by
--   simpa only [← Part.coe_range, Finset.disjoint_coe] using c.disjoint h

-- instance instUniqueZero : Unique (OrderedPartition 0) where
--   uniq _ := parts_injective <| Subsingleton.elim _ _

-- /-- An ordered finpartition gives an equivalence between `Fin n`
-- and the disjoint union of the parts, each of them parameterized by `Fin (c.part i).size`. -/
-- @[simps symm_apply]
-- def equivSigma : Fin n ≃ ((i : Fin c.length) × Fin (c.part i).size) where
--   toFun := Fintype.bijInv c.part_bijective₂
--   invFun x := c.part x.1 x.2
--   left_inv := Fintype.rightInverse_bijInv _
--   right_inv := Fintype.leftInverse_bijInv _

-- /-- Given `j : Fin n`, the index of the part to which it belongs. -/
-- def index (j : Fin n) : Fin c.length :=
--   (c.equivSigma j).1

-- /-- The inverse of `c.emb` for `c : OrderedPartition`. It maps `j : Fin n` to the point in
-- `Fin (c.partSize (c.index j))` which is mapped back to `j` by `c.emb (c.index j)`. -/
-- def invEmbedding (j : Fin n) : Fin (c.part (c.index j)).size :=
--   (c.equivSigma j).2

-- @[simp] lemma part_invEmbedding (j : Fin n) :
--     c.part (c.index j) (c.invEmbedding j) = j :=
--   c.equivSigma.symm_apply_apply j

-- @[simp]
-- lemma equivSigma_part (i j) : c.equivSigma (c.part i j) = ⟨i, j⟩ :=
--   c.equivSigma.apply_symm_apply ⟨i, j⟩

-- @[simp]
-- lemma index_part (i j) : c.index (c.part i j) = i := by simp [index]

-- lemma index_eq_iff_mem_range {i j} : c.index i = j ↔ i ∈ (c.part j).range := by
--   rcases c.equivSigma.symm.surjective i with ⟨⟨k, l⟩, rfl⟩
--   simp

-- @[simp]
-- lemma mem_part_index_range (j : Fin n) : j ∈ (c.part (c.index j)).range :=
--   (Part.mem_range _).mpr ⟨_, c.part_invEmbedding j⟩

-- @[to_additive] lemma prod_sigma_eq_prod {M : Type*} [CommMonoid M] (v : Fin n → M) :
--     ∏ (m : Fin c.length), ∏ (r : Fin (c.part m).size), v (c.part m r) = ∏ i, v i := by
--   rw [Finset.prod_sigma', Finset.univ_sigma_univ, ← c.equivSigma.symm.prod_comp]
--   simp only [equivSigma_symm_apply]

-- @[simp]
-- theorem sum_part_size : ∑ i, (c.part i).size = n := by
--   simpa using c.sum_sigma_eq_sum (1 : Fin n → ℕ)

-- @[simp]
-- lemma length_eq_zero : c.length = 0 ↔ n = 0 where
--   mp h := by
--     have : IsEmpty (Fin c.length) := by rw [h]; infer_instance
--     rw [← c.sum_part_size, Finset.sum_of_isEmpty]
--   mpr := by
--     rintro rfl
--     rw [Unique.eq_default c]
--     rfl

-- @[simp]
-- lemma length_pos : 0 < c.length ↔ 0 < n := by
--   simp only [Nat.pos_iff_ne_zero, ne_eq, length_eq_zero]

-- @[simp]
-- lemma one_le_length : 1 ≤ c.length ↔ 1 ≤ n := c.length_pos

-- instance neZero_length [NeZero n] (c : OrderedPartition n) : NeZero c.length :=
--   .of_pos <| c.length_pos.2 pos'

-- @[simp]
-- lemma part_index_zero_zero [NeZero n] : c.part (c.index 0) 0 = 0 :=
--   (Part.zero_mem_range _).mp <| c.mem_part_index_range 0

-- instance instUniqueOne : Unique (OrderedPartition 1) where
--   uniq c := by
--     simp [OrderedPartition.ext_iff, (c.one_le_length.2 le_rfl).antisymm c.length_le,
--       Fin.heq_fun_iff, eq_iff_true_of_subsingleton]

-- theorem size_add_length_le (i) : (c.part i).size + c.length ≤ n + 1 := calc
--   (c.part i).size + c.length = (c.part i).size + ∑ j ∈ {i}ᶜ, 1 + 1 := by
--     have : 1 ≤ n := i.pos.trans_le c.length_le
--     simp [Finset.card_compl, add_assoc, this]
--   _ ≤ (c.part i).size + ∑ j ∈ {i}ᶜ, (c.part j).size + 1 := by gcongr; apply Part.one_le_size
--   _ = n + 1 := by
--     rw [← Fintype.sum_eq_add_sum_compl i fun j ↦ (c.part j).size, sum_part_size]

-- theorem size_le_sub (i) : (c.part i).size ≤ n + 1 - c.length :=
--   Nat.le_sub_of_add_le <| c.size_add_length_le i

-- theorem length_eq_iff : c.length = n ↔ c = atomic n := by
--   refine ⟨fun h ↦ parts_injective ?_, fun h ↦ h ▸ rfl⟩
--   apply Finset.eq_of_subset_of_card_le
--   · suffices ∀ i, (c.part i).size = 1 by simpa [Finset.subset_iff, ← Part.size_eq_one]
--     refine fun i ↦ le_antisymm ?_ (c.part i).one_le_size
--     simpa [h] using c.size_le_sub i
--   · simp [h]

-- theorem length_lt_iff : c.length < n ↔ c ≠ atomic n := by
--   rw [c.length_le.lt_iff_ne]
--   exact c.length_eq_iff.not

-- /-- The indiscrete partition. -/
-- @[simps]
-- def indiscrete (n : ℕ) (hn : n ≠ 0) : OrderedPartition n where
--   length := 1
--   part _ := .univ n hn
--   part_last_strictMono := Subsingleton.strictMono _
--   disjoint := Subsingleton.pairwise
--   cover _ := by simp

-- @[simp]
-- theorem indiscrete_eq_atomic_iff (h : n ≠ 0) : indiscrete n h = atomic n ↔ n = 1 := by
--   rw [← length_eq_iff, eq_comm, indiscrete_length]

-- @[simp]
-- theorem atomic_eq_indiscrete_iff (h : n ≠ 0) : atomic n = indiscrete n h ↔ n = 1 :=
--   eq_comm.trans <| indiscrete_eq_atomic_iff h

-- @[simp]
-- theorem indiscrete_one : indiscrete 1 one_ne_zero = atomic 1 := by
--   simp

-- theorem length_eq_one_iff (h : n ≠ 0) : c.length = 1 ↔ c = indiscrete n h := by
--   refine ⟨fun h₁ ↦ ?_, fun h₁ ↦ h₁ ▸ rfl⟩
--   suffices ∀ i, c.part i = .univ n h by simp [OrderedPartition.ext_iff, h₁, Fin.heq_fun_iff, this]
--   have : Subsingleton (Fin c.length) := by rw [h₁]; infer_instance
--   intro i
--   simpa only [Fintype.sum_subsingleton _ i, ← Part.size_eq_iff] using c.sum_part_size

-- theorem length_eq_one_iff_exists : c.length = 1 ↔ ∃ h, c = indiscrete n h := by
--   rcases eq_or_ne n 0 with rfl | h
--   · simp [Unique.uniq _ c]
--   · simp [length_eq_one_iff, h]

-- end OrderedPartition

end Fin
