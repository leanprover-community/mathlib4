import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Inv
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.Indexes
import Mathlib.Combinatorics.Enumerative.Composition

open Set Function List
open scoped Finset

namespace StrictMono

variable {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β} {l : List α}

@[simp]
theorem sorted_le_listMap (hf : StrictMono f) :
    (l.map f).Sorted (· ≤ ·) ↔ l.Sorted (· ≤ ·) := by
  simp only [Sorted, pairwise_map, hf.le_iff_le]

@[simp]
theorem sorted_lt_listMap (hf : StrictMono f) :
    (l.map f).Sorted (· < ·) ↔ l.Sorted (· < ·) := by
  simp only [Sorted, pairwise_map, hf.lt_iff_lt]

end StrictMono

namespace OrderEmbedding

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
theorem sorted_le_listMap (e : α ↪o β) {l : List α} :
    (l.map e).Sorted (· ≤ ·) ↔ l.Sorted (· ≤ ·) := by
  simp only [Sorted, pairwise_map, e.le_iff_le]

@[simp]
theorem sorted_lt_listMap (e : α ↪o β) {l : List α} :
    (l.map e).Sorted (· < ·) ↔ l.Sorted (· < ·) := by
  simp [Sorted, pairwise_map]

end OrderEmbedding

namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
theorem sorted_le_listMap (e : α ≃o β) {l : List α} :
    (l.map e).Sorted (· ≤ ·) ↔ l.Sorted (· ≤ ·) :=
  e.toOrderEmbedding.sorted_le_listMap

@[simp]
theorem sorted_lt_listMap (e : α ≃o β) {l : List α} :
    (l.map e).Sorted (· < ·) ↔ l.Sorted (· < ·) :=
  e.toOrderEmbedding.sorted_lt_listMap

end OrderIso

namespace List

variable {α β γ : Type*}

theorem Pairwise.rel_dropLast_getLast {R : α → α → Prop} {l : List α} {a : α} (h : l.Pairwise R)
    (ha : a ∈ l.dropLast) : R a (l.getLast <| ne_nil_of_mem <| dropLast_subset _ ha) := by
  rw [← List.pairwise_reverse] at h
  rw [getLast_eq_head_reverse]
  exact h.rel_head_tail (by rwa [tail_reverse, mem_reverse])

theorem Pairwise.rel_getLast_of_rel_getLast_getLast {R : α → α → Prop} {l : List α} {a : α}
    (h₁ : l.Pairwise R) (ha : a ∈ l)
    (hlast : R (l.getLast <| ne_nil_of_mem ha) (l.getLast <| ne_nil_of_mem ha)) :
    R a (l.getLast <| ne_nil_of_mem ha) := by
  rw [← dropLast_concat_getLast (ne_nil_of_mem ha), mem_append, List.mem_singleton] at ha
  exact ha.elim h₁.rel_dropLast_getLast (· ▸ hlast)

theorem Pairwise.rel_getLast {R : α → α → Prop} {l : List α} {a : α}
    [IsRefl α R] (h₁ : l.Pairwise R) (ha : a ∈ l) :
    R a (l.getLast <| ne_nil_of_mem ha) :=
  h₁.rel_getLast_of_rel_getLast_getLast ha (refl_of ..)

theorem mem_unattach {p : α → Prop} {l : List (Subtype p)} {x : α} :
    x ∈ l.unattach ↔ ∃ y ∈ l, y.1 = x :=
  mem_map

/-- A version of `modify_id` that uses `fun x => x` instead of `id`. -/
@[simp]
theorem modify_id' (n : ℕ) (l : List α) : modify (·) n l = l := modify_id ..

theorem subset_flatMap_of_mem {l : List α} {a : α} (ha : a ∈ l) (f : α → List β) :
    f a ⊆ l.flatMap f := fun _b hb ↦ mem_flatMap_of_mem ha hb

theorem subset_flatten_of_mem {L : List (List α)} {l : List α} (h : l ∈ L) : l ⊆ L.flatten :=
  fun _b hb ↦ mem_flatten_of_mem h hb

@[simp] -- TODO: generalize to `finSuccEquiv'`
theorem filterMap_finSuccEquiv_finRange (n : ℕ) :
    (finRange (n + 1)).filterMap (finSuccEquiv n) = finRange n := by
  simp [finRange_succ, comp_def]

theorem flatMap_filterMap_right (f : α → Option β) (l : List (List α)) :
    l.flatMap (·.filterMap f) = l.flatten.filterMap f := by
  induction l <;> simp [*]

-- TODO: can we allow `q` to depend on `(a : α) (ha : p a)`?
-- What happens to `g` in the RHS then?
theorem flatten_pmap_pmap {p : α → Prop} {q : β → Prop} {l : List α} {f : (a : α) → p a → List β}
    (hp : ∀ a ∈ l, p a) (hq : ∀ a (ha : p a), ∀ b ∈ f a ha, q b)
    (g : (b : β) → q b → γ) :
    (l.pmap (fun a ha ↦ (f a ha).pmap g (hq a ha)) hp).flatten =
      (l.pmap f hp).flatten.pmap g fun b hb ↦ by
        simp only [mem_flatten, mem_pmap] at hb
        rcases hb with ⟨_, ⟨a, ha, rfl⟩, hab⟩
        exact hq a (hp a ha) b hab := by
  induction l <;> simp [*]

theorem pmap_flatten {L : List (List α)} {p : α → Prop} (h : ∀ a ∈ L.flatten, p a)
    (f : ∀ a, p a → β) :
    L.flatten.pmap f h =
      (L.pmap (fun l hl ↦ l.pmap f fun a ha ↦ h a (hl ha))
        fun _ ↦ subset_flatten_of_mem).flatten := by
  rw [flatten_pmap_pmap]
  simp

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

end List

namespace Fin

variable {n m : ℕ}

/-- If `i ≤ Fin.castSucc j`, then `Fin.castPred i _ ≤ j`.
This is one implication of `Fin.castPred_le_iff`,
with the assumption `i ≠ Fin.last _` deduced from `i ≤ Fin.castSucc j`. -/
lemma castPred_le_of_le_castSucc {j : Fin n} {i : Fin (n + 1)} (h : i ≤ castSucc j) :
    i.castPred (fun h' ↦ h.not_lt <| h' ▸ j.castSucc_lt_last) ≤ j :=
  h

lemma castLT_le_of_le_castLE {j : Fin m} {i : Fin n} (h₁ : m ≤ n) (h₂ : i ≤ castLE h₁ j) :
    i.castLT ((le_def.mp h₂).trans_lt j.is_lt) ≤ j :=
  h₂

@[simp]
lemma image_castLE_setIic (i : Fin n) (h : n ≤ m) :
    castLE h '' Set.Iic i = Set.Iic (i.castLE h) := by
  aesop (add unsafe castLT_le_of_le_castLE)

@[simp]
lemma image_castAdd_setIic (m) (i : Fin n) :
    castAdd m '' Set.Iic i = Set.Iic (i.castAdd m) :=
  image_castLE_setIic i _
  
@[simp]
lemma image_castSucc_setIic (i : Fin n) : castSucc '' Set.Iic i = Set.Iic i.castSucc :=
  image_castAdd_setIic _ _

@[simp]
lemma image_cast_setIic (i : Fin n) (h : n = m) : Fin.cast h '' Set.Iic i = Set.Iic (i.cast h) :=
  image_castLE_setIic i h.le

@[simp]
lemma image_castLE_finsetIic (i : Fin n) (h : n ≤ m) :
    (Finset.Iic i).image (castLE h) = Finset.Iic (i.castLE h) := by
  simp [← Finset.coe_inj]

@[simp]
lemma image_castAdd_finsetIic (m) (i : Fin n) :
    (Finset.Iic i).image (castAdd m) = Finset.Iic (i.castAdd m) :=
  image_castLE_finsetIic _ _

@[simp]
lemma image_castSucc_finsetIic (i : Fin n) :
    (Finset.Iic i).image castSucc = Finset.Iic i.castSucc :=
  image_castAdd_finsetIic _ _

@[simp]
lemma image_cast_finsetIic (i : Fin n) (h : n = m) :
    (Finset.Iic i).image (Fin.cast h) = Finset.Iic (i.cast h) :=
  image_castLE_finsetIic _ h.le

@[simp]
lemma map_castLEEmb_finsetIic (i : Fin n) (h : n ≤ m) :
    (Finset.Iic i).map (Fin.castLEEmb h) = .Iic (i.castLE h) := by
  simp [Finset.map_eq_image]

@[simp]
lemma map_castAddEmb_finsetIic (m) (i : Fin n) :
    (Finset.Iic i).map (Fin.castAddEmb m) = .Iic (i.castAdd m) :=
  map_castLEEmb_finsetIic _ _

@[simp]
lemma map_castSuccEmb_finsetIic (i : Fin n) :
    (Finset.Iic i).map castSuccEmb = Finset.Iic i.castSucc :=
  map_castAddEmb_finsetIic _ _

variable {M : Type*} [CommMonoid M]

@[to_additive]
lemma prod_Iic_castLE (f : Fin m → M) (i : Fin n) (h : n ≤ m) :
    ∏ j ∈ .Iic (i.castLE h), f j = ∏ j ∈ .Iic i, f (j.castLE h) := by
  rw [← map_castLEEmb_finsetIic, Finset.prod_map, coe_castLEEmb]

@[to_additive]
lemma prod_Iic_castAdd (f : Fin (n + m) → M) (i : Fin n) :
    ∏ j ∈ .Iic (i.castAdd m), f j = ∏ j ∈ .Iic i, f (j.castAdd m) :=
  prod_Iic_castLE ..

@[to_additive]
lemma prod_Iic_castSucc (f : Fin (n + 1) → M) (i : Fin n) :
    ∏ j ∈ .Iic i.castSucc, f j = ∏ j ∈ .Iic i, f j.castSucc :=
  prod_Iic_castAdd ..

@[to_additive]
lemma prod_Iic_cast (f : Fin m → M) (i : Fin n) (h : n = m) :
    ∏ j ∈ .Iic (i.cast h), f j = ∏ j ∈ .Iic i, f (j.cast h) :=
  prod_Iic_castLE _ _ h.le

end Fin

attribute [simp] List.prod_reverse List.sum_reverse

namespace Composition

attribute [simp] blocks_sum

variable {m n : ℕ}

@[simps]
def cast (c : Composition m) (hmn : m = n) : Composition n where
  __ := c
  blocks_sum := c.blocks_sum.trans hmn

@[simp]
theorem cast_rfl (c : Composition n) : c.cast rfl = c := rfl

theorem cast_heq (c : Composition m) (hmn : m = n) : HEq (c.cast hmn) c := by subst m; rfl

@[simps]
def append (c₁ : Composition m) (c₂ : Composition n) : Composition (m + n) where
  blocks := c₁.blocks ++ c₂.blocks
  blocks_pos := by
    intro i hi
    rw [mem_append] at hi
    exact hi.elim c₁.blocks_pos c₂.blocks_pos
  blocks_sum := by simp

@[simps]
def reverse (c : Composition n) : Composition n where
  blocks := c.blocks.reverse
  blocks_pos hi := c.blocks_pos (mem_reverse.mp hi)
  blocks_sum := by simp

@[simp]
lemma reverse_reverse (c : Composition n) : c.reverse.reverse = c :=
  Composition.ext <| List.reverse_reverse _

lemma reverse_involutive : Function.Involutive (@reverse n) := reverse_reverse
lemma reverse_bijective : Function.Bijective (@reverse n) := reverse_involutive.bijective
lemma reverse_injective : Function.Injective (@reverse n) := reverse_involutive.injective
lemma reverse_surjective : Function.Surjective (@reverse n) := reverse_involutive.surjective

@[simp]
lemma reverse_inj {c₁ c₂ : Composition n} : c₁.reverse = c₂.reverse ↔ c₁ = c₂ :=
  reverse_injective.eq_iff

@[simp]
lemma reverse_ones : (ones n).reverse = ones n := by ext1; simp

@[simp]
lemma reverse_single (hn : 0 < n) : (single n hn).reverse = single n hn := by ext1; simp

@[simp]
lemma reverse_eq_ones {c : Composition n} : c.reverse = ones n ↔ c = ones n :=
  reverse_injective.eq_iff' reverse_ones

@[simp]
lemma reverse_eq_single {hn : 0 < n} {c : Composition n} :
    c.reverse = single n hn ↔ c = single n hn :=
  reverse_injective.eq_iff' <| reverse_single _

lemma reverse_append (c₁ : Composition m) (c₂ : Composition n) :
    reverse (append c₁ c₂) = (append c₂.reverse c₁.reverse).cast (add_comm _ _) :=
  Composition.ext <| by simp

@[elab_as_elim]
def recOnSingleAppend {motive : ∀ n, Composition n → Sort*} {n : ℕ} (c : Composition n)
    (zero : motive 0 (ones 0))
    (single_append : ∀ k n c, motive n c →
      motive (k + 1 + n) (append (single (k + 1) k.succ_pos) c)) :
    motive n c :=
  match n, c with
  | _, ⟨[], _, rfl⟩ => zero
  | _, ⟨0 :: _, h, rfl⟩ => by simp at h
  | _, ⟨(k + 1) :: l, h, rfl⟩ =>
    single_append k l.sum ⟨l, fun hi ↦ h <| mem_cons_of_mem _ hi, rfl⟩ <|
      recOnSingleAppend _ zero single_append

@[elab_as_elim]
def recOnAppendSingle {motive : ∀ n, Composition n → Sort*} {n : ℕ} (c : Composition n)
    (zero : motive 0 (ones 0))
    (append_single : ∀ k n c, motive n c →
      motive (n + (k + 1)) (append c (single (k + 1) k.succ_pos))) :
    motive n c :=
  reverse_reverse c ▸ c.reverse.recOnSingleAppend zero fun k n c ih ↦ by
    convert append_single k n c.reverse ih using 1
    · apply add_comm
    · rw [reverse_append, reverse_single]
      apply cast_heq

end Composition

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

def mkDec (L : List (List (Fin n)))
    (chain₁ : ∀ l ∈ L, l.Chain' (· ≤ ·) := by decide)
    (not_nil : [] ∉ L := by decide)
    (chain₂ : (L.pmap getLast fun _l hl ↦
      ne_of_mem_of_not_mem hl not_nil).Chain' (· ≤ ·) := by decide)
    (sort : L.flatten.mergeSort = finRange n) :
    OrderedPartition n where
  parts := L
  sorted_le_of_mem_parts l hl := chain'_iff_pairwise.mp (chain₁ l hl)
  not_nil_mem_parts := not_nil
  sorted_getLast_le := chain'_iff_pairwise.mp chain₂
  perm_finRange := sort ▸ (mergeSort_perm _ _).symm

attribute [simp] not_nil_mem_parts

theorem ne_nil_of_mem_parts (c : OrderedPartition n) {l : List (Fin n)} (hl : l ∈ c.parts) :
    l ≠ [] :=
  ne_of_mem_of_not_mem hl c.not_nil_mem_parts

@[simp]
theorem parts_getElem_ne_nil (c : OrderedPartition n) (i : ℕ) (hi : i < c.parts.length) :
    c.parts[i] ≠ [] :=
  c.ne_nil_of_mem_parts (getElem_mem ..)

theorem nodup_flatten_parts (c : OrderedPartition n) : c.parts.flatten.Nodup :=
  c.perm_finRange.symm.nodup (nodup_finRange n)

theorem pairwise_disjoint_parts (c : OrderedPartition n) : c.parts.Pairwise List.Disjoint :=
  (nodup_flatten.mp c.nodup_flatten_parts).2

-- TODO: this is true for any list of pairwise disjoint nonempty lists.
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
  (nodup_flatten.mp c.nodup_flatten_parts).1 l hl

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
  invFun x := c.parts[x.1.1][x.2.1]
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
    0 :: c.parts[(c.index 0).1].tail = c.parts[(c.index 0).1] := by
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

theorem parts_ne_nil [NeZero n] (c : OrderedPartition n) : c.parts ≠ [] :=
  c.parts_eq_nil.not.mpr (NeZero.ne n)

theorem length_parts_neZero [NeZero n] (c : OrderedPartition n) : NeZero c.parts.length :=
  ⟨(length_eq_zero.trans c.parts_eq_nil).not.mpr (NeZero.ne n)⟩

attribute [scoped instance] length_parts_neZero

@[simp]
theorem getLast_getLast_parts (c : OrderedPartition (n + 1)) :
    (c.parts.getLast c.parts_ne_nil).getLast (c.ne_nil_of_mem_parts <| getLast_mem _) = .last n :=
  top_unique <| calc
    ⊤ ≤ c.parts[c.index ⊤].getLast (by simp) :=
      (c.sorted_le_of_mem_parts <| getElem_mem _).rel_getLast <| c.mem_getElem_index ⊤
    _ ≤ _ := by simpa using c.sorted_getLast_le.rel_getLast (by aesop)

@[irreducible]
def extendLeft (c : OrderedPartition n) : OrderedPartition (n + 1) where
  parts := [0] :: c.parts.map (·.map Fin.succ)
  sorted_le_of_mem_parts := by simpa [List.Sorted, List.pairwise_map] using c.sorted_le_of_mem_parts
  not_nil_mem_parts := by simp
  sorted_getLast_le := by
    simpa [Sorted, pmap_map, pairwise_pmap] using c.sorted_getLast_le
  perm_finRange := by
    rw [List.flatten_cons, List.singleton_append, finRange_succ, ← List.map_flatten]
    exact .cons _ <| .map _ c.perm_finRange

@[simp]
theorem index_zero_extendLeft (c : OrderedPartition n) : c.extendLeft.index 0 = 0 := by
  rw [index_eq_iff_mem_getElem, extendLeft]
  apply mem_singleton_self

@[simp]
theorem length_parts_extendLeft (c : OrderedPartition n) :
    c.extendLeft.parts.length = c.parts.length + 1 := by
  simp [extendLeft]

@[irreducible]
def atomic (n : ℕ) : OrderedPartition n where
  parts := (finRange n).map ([·])
  sorted_le_of_mem_parts := by simp
  not_nil_mem_parts := by simp
  sorted_getLast_le := by simpa [Sorted, pmap_map, pairwise_pmap] using pairwise_le_finRange n
  perm_finRange := by simp [← flatMap_def]

@[simp]
theorem extendLeft_atomic (n : ℕ) : (atomic n).extendLeft = atomic (n + 1) := by
  ext1
  simp [atomic, extendLeft, finRange_succ]

instance : Inhabited (OrderedPartition n) := ⟨atomic n⟩

@[simp] theorem default_eq_atomic : default = atomic n := rfl

instance instUniqueZero : Unique (OrderedPartition 0) where
  uniq c := by ext1; simp [atomic]

protected abbrev head [NeZero n] (c : OrderedPartition n) : List (Fin n) :=
  c.parts.head (by simp [NeZero.ne])

theorem getElem_index_zero_eq_zero [NeZero n] (c : OrderedPartition n) :
    c.parts[(c.index 0).1] = [0] ↔ c.head = [0] := by
  rw [OrderedPartition.head, head_eq_getElem]
  constructor <;> intro h <;> convert h
  · refine (Nat.zero_le _).eq_or_lt.resolve_right fun hpos ↦ ?_
    simpa [h, (Fin.zero_le' _).not_lt]
      using pairwise_iff_getElem.mp c.sorted_getLast_lt _ _ (by simp [NeZero.pos]) (by simp) hpos
  · simp [index_eq_iff_mem_getElem, h]

@[irreducible]
def eraseLeft.partsAux (c : OrderedPartition (n + 1)) (hc : c.head = [0]) :
    List (List (Fin n)) :=
  c.parts.tail.pmap (fun l hl ↦ l.pmap Fin.pred hl) <| by
    rintro l hl _ hl₀ rfl
    refine c.pairwise_disjoint_parts.rel_head_tail hl ?_ hl₀
    simp [hc]

theorem eraseLeft.zero_cons_map_partsAux (c : OrderedPartition (n + 1)) (hc : c.head = [0]) :
    [0] :: map (map succ) (eraseLeft.partsAux c hc) = c.parts := by
  simp [eraseLeft.partsAux, map_pmap, ← hc]

def eraseLeft (c : OrderedPartition (n + 1)) (hc : c.head = [0]) : OrderedPartition n where
  parts := eraseLeft.partsAux c hc
  sorted_le_of_mem_parts := by
    simpa [← eraseLeft.zero_cons_map_partsAux c hc, Sorted, pairwise_map]
      using c.sorted_le_of_mem_parts
  not_nil_mem_parts := by simpa [← eraseLeft.zero_cons_map_partsAux c hc] using c.not_nil_mem_parts
  sorted_getLast_le := by
    simpa [← eraseLeft.zero_cons_map_partsAux c hc, Sorted, pairwise_pmap, pmap_map]
      using c.sorted_getLast_le
  perm_finRange := by
    rw [← map_perm_map_iff (succ_injective _), ← perm_cons, ← finRange_succ,
      map_flatten, ← singleton_append, ← flatten_cons, eraseLeft.zero_cons_map_partsAux]
    exact c.perm_finRange

@[simp]
lemma head_extendLeft (c : OrderedPartition n) : c.extendLeft.head = [0] := by
  simp [extendLeft, OrderedPartition.head]

@[simp]
lemma eraseLeft_extendLeft (c : OrderedPartition n) :
    c.extendLeft.eraseLeft c.head_extendLeft = c := by
  ext1
  simp [eraseLeft, eraseLeft.partsAux, extendLeft, pmap_map]

@[simp]
lemma extendLeft_eraseLeft (c : OrderedPartition (n + 1)) (hc : c.head = [0]) :
    (c.eraseLeft hc).extendLeft = c := by
  ext1
  simpa only [extendLeft] using eraseLeft.zero_cons_map_partsAux _ hc

/-- Auxiliary definition for `extendPart`. We move it to a separate definition
so that we can prove some `Iff` lemmas about it before we give the definition. -/
@[irreducible]
def extendPart.partsAux (L : List (List (Fin n))) (i : ℕ) : List (List (Fin (n + 1))) :=
  (L.map (·.map Fin.succ)).modify (List.cons 0) i

theorem extendPart.partsAux_sorted_le_iff {L : List (List (Fin n))} {i : ℕ} :
    (∀ l ∈ partsAux L i, l.Sorted (· ≤ ·)) ↔ ∀ l ∈ L, l.Sorted (· ≤ ·) := by
  simp [partsAux, mem_iff_getElem, @forall_swap (List _), getElem_modify, Sorted,
    apply_ite (Pairwise _), pairwise_map]

theorem extendPart.partsAux_sorted_getLast_le_iff {L : List (List (Fin n))} {i : ℕ}
    (hi : i < L.length) (h₁ : ∀ l ∈ partsAux L i, l ≠ []) (h₂ : ∀ l ∈ L, l ≠ []) :
    ((partsAux L i).pmap getLast h₁).Sorted (· ≤ ·) ↔ (L.pmap getLast h₂).Sorted (· ≤ ·) := by
  simp? [Sorted, partsAux, pmap_map, modify_eq_take_cons_drop, ← map_take, ← map_drop, h₂, hi,
      pmap_congr_prop fun _ ↦ map_eq_nil_iff.not] says
    simp only [Sorted, ne_eq, partsAux, length_map, hi, modify_eq_take_cons_drop, ← map_take,
      getElem_map, ← map_drop, pmap_append, pmap_map, getLast_map,
      pmap_congr_prop fun _ ↦ map_eq_nil_iff.not, pmap_cons, map_eq_nil_iff, getElem_mem, h₂,
      not_false_eq_true, getLast_cons]
  simp only [← map_pmap succ, ← map_cons succ, ← map_append, pairwise_map, succ_le_succ_iff,
    ← pmap_cons' getLast, ← pmap_append']
  simp

theorem extendPart.perm_partsAux_iff {L : List (List (Fin n))} {i : ℕ} (hi : i < L.length) :
    (partsAux L i).flatten ~ finRange (n + 1) ↔ L.flatten ~ finRange n := by
  rw [← rel_congr_left (getElem_cons_eraseIdx_perm hi).flatten]
  simp [partsAux, rel_congr_left (modify_perm_cons_eraseIdx _ _).flatten, finRange_succ,
    ← map_perm_map_iff (succ_injective n), eraseIdx_map, hi]

def extendPart (c : OrderedPartition n) (i : Fin c.parts.length) : OrderedPartition (n + 1) where
  parts := extendPart.partsAux c.parts i
  sorted_le_of_mem_parts := extendPart.partsAux_sorted_le_iff.mpr c.sorted_le_of_mem_parts
  not_nil_mem_parts := by simp [extendPart.partsAux, mem_iff_getElem, getElem_modify, ite_eq_iff]
  sorted_getLast_le := (extendPart.partsAux_sorted_getLast_le_iff i.2 _ _).mpr c.sorted_getLast_le
  perm_finRange := (extendPart.perm_partsAux_iff i.is_lt).mpr c.perm_finRange

@[simp]
theorem length_parts_extendPart (c : OrderedPartition n) (i : Fin c.parts.length) :
    (c.extendPart i).parts.length = c.parts.length := by
  simp [extendPart, extendPart.partsAux]

@[simp]
theorem getElem_extendPart_same (c : OrderedPartition n) (i : Fin c.parts.length) :
    (c.extendPart i).parts[i.1] = 0 :: c.parts[i].map succ := by
  simp [extendPart, extendPart.partsAux]

@[simp]
theorem getElem_extendPart_of_ne (c : OrderedPartition n) (i : Fin c.parts.length) {j : ℕ}
    (hne : i.1 ≠ j) (hj : j < (c.extendPart i).parts.length) :
    (c.extendPart i).parts[j] = (c.parts[j]'(by simpa using hj)).map succ := by
  simp [extendPart, extendPart.partsAux, hne]

@[simp]
theorem index_zero_extendPart (c : OrderedPartition n) (i : Fin c.parts.length) :
    (c.extendPart i).index 0 = i.cast (c.length_parts_extendPart i).symm := by
  simp [index_eq_iff_mem_getElem]

theorem val_index_zero_extendPart (c : OrderedPartition n) (i : Fin c.parts.length) :
    ((c.extendPart i).index 0 : ℕ) = i := by
  simp

@[simp]
theorem head_extendPart_ne_singleton_zero (c : OrderedPartition n) (i : Fin c.parts.length) :
    (c.extendPart i).head ≠ [0] := by
  simp [ne_eq, ← getElem_index_zero_eq_zero]

@[irreducible]
def eraseMiddle.partsAux (c : OrderedPartition (n + 1)) : List (List (Fin n)) :=
  (c.parts.modify List.tail (c.index 0)).pmap (fun l hl ↦ l.pmap Fin.pred hl) <| by
    rintro l hl _ hl₀ rfl
    rw [(modify_perm_cons_eraseIdx (Fin.is_lt _) _).mem_iff, mem_cons,
      mem_eraseIdx_iff_getElem] at hl
    rcases hl with rfl | ⟨i, hi_lt, hi_ne, rfl⟩
    · simpa using (c.nodup_getElem_parts (c.index 0).is_lt).rel_head_tail hl₀
    · exact c.disjoint_getElem_parts.mpr hi_ne hl₀ (c.mem_getElem_index _)

theorem eraseMiddle.length_partsAux (c : OrderedPartition (n + 1)) :
    (partsAux c).length = c.parts.length := by
  simp [partsAux]

theorem eraseMiddle.extendPartPartsAux_partsAux (c : OrderedPartition (n + 1)) :
    extendPart.partsAux (partsAux c) (c.index 0) = c.parts := by
  simp [extendPart.partsAux, modify_eq_set_getElem, map_pmap, partsAux]

def eraseMiddle (c : OrderedPartition (n + 1)) (hc : c.head ≠ [0]) : OrderedPartition n where
  parts := eraseMiddle.partsAux c
  sorted_le_of_mem_parts := by
    rw [← extendPart.partsAux_sorted_le_iff, eraseMiddle.extendPartPartsAux_partsAux c]
    exact c.sorted_le_of_mem_parts
  not_nil_mem_parts := by
    suffices c.parts[(c.index 0).1].tail ≠ [] by
      simpa [eraseMiddle.partsAux, (modify_perm_cons_eraseIdx _ _).mem_iff, mt mem_of_mem_eraseIdx]
    rwa [ne_eq, ← List.cons_inj_right, zero_cons_tail_getElem_index_zero,
      getElem_index_zero_eq_zero]
  sorted_getLast_le := by
    rw [← extendPart.partsAux_sorted_getLast_le_iff (i := c.index 0)
      (by simp [eraseMiddle.length_partsAux])]
    simpa only [← eraseMiddle.extendPartPartsAux_partsAux c] using c.sorted_getLast_le
  perm_finRange := by
    rw [← extendPart.perm_partsAux_iff, eraseMiddle.extendPartPartsAux_partsAux]
    · exact c.perm_finRange
    · simp [eraseMiddle.length_partsAux]

@[simp]
lemma length_parts_eraseMiddle (c : OrderedPartition (n + 1)) (hc : c.head ≠ [0]) :
    (c.eraseMiddle hc).parts.length = c.parts.length :=
  eraseMiddle.length_partsAux c

@[simp]
lemma extendPart_eraseMiddle (c : OrderedPartition (n + 1)) (hc : c.head ≠ [0]) :
    (c.eraseMiddle hc).extendPart ((c.index 0).cast (c.length_parts_eraseMiddle hc).symm) = c :=
  OrderedPartition.ext <| eraseMiddle.extendPartPartsAux_partsAux c

@[simp]
lemma eraseMiddle_extendPart (c : OrderedPartition n) (i : Fin c.parts.length) :
    (c.extendPart i).eraseMiddle (head_extendPart_ne_singleton_zero c i) = c := by
  ext1
  simp only [eraseMiddle, eraseMiddle.partsAux, index_zero_extendPart, coe_cast]
  simp [extendPart, extendPart.partsAux, modify_modify_eq, comp_def, pmap_map]

def extendEquiv :
    (OrderedPartition n ⊕ (c : OrderedPartition n) × Fin c.parts.length) ≃
      OrderedPartition (n + 1) where
  toFun c := c.elim extendLeft fun c ↦ c.1.extendPart c.2
  invFun c :=
    if h : c.head = [0] then .inl (c.eraseLeft h)
    else .inr ⟨c.eraseMiddle h, (c.index 0).cast (c.length_parts_eraseMiddle _).symm⟩
  left_inv := by rintro (c | ⟨c, i⟩) <;> simp [Fin.heq_ext_iff]
  right_inv c := by by_cases h : c.head = [0] <;> simp [h]

instance instFintype : ∀ n, Fintype (OrderedPartition n)
  | 0 => Unique.fintype
  | n + 1 => letI := instFintype n; .ofEquiv _ extendEquiv

theorem _root_.Fintype.card_finOrderedPartition_succ_eq_sum_length (n : ℕ) :
    Fintype.card (OrderedPartition (n + 1)) = ∑ c : OrderedPartition n, (c.parts.length + 1) := by
  rw [← Fintype.card_congr OrderedPartition.extendEquiv]
  simp [Finset.sum_add_distrib, add_comm]

instance instUniqueOne : Unique (OrderedPartition 1) :=
  haveI : Subsingleton (OrderedPartition 1) := by
    rw [← Fintype.card_le_one_iff_subsingleton,
      Fintype.card_finOrderedPartition_succ_eq_sum_length]
    simp
  Unique.mk' _

@[simp]
theorem coe_flatten_parts (c : OrderedPartition n) :
    (c.parts.flatten : Multiset (Fin n)) = finRange n :=
  Multiset.coe_eq_coe.mpr c.perm_finRange

@[simp]
theorem multisetBind_parts (c : OrderedPartition n) :
    (c.parts : Multiset (List (Fin n))).bind (↑) = (finRange n : Multiset (Fin n)) := by
  rw [Multiset.coe_bind, flatMap_id', coe_flatten_parts]

def ofUnsortedGetLast (L : List (List (Fin n))) (sorted : ∀ l ∈ L, l.Sorted (· ≤ ·))
    (not_nil : [] ∉ L) (perm : L.flatten ~ finRange n) : OrderedPartition n where
  parts := L.pmap Subtype.mk (fun _ h ↦ ne_of_mem_of_not_mem h not_nil)
    |>.mergeSort (fun l₁ l₂ ↦ ((fun l : {l // l ≠ []} ↦ l.1.getLast l.2)  ⁻¹'o (· ≤ ·)) l₁ l₂)
    |>.unattach
  sorted_le_of_mem_parts := by simp +contextual [mem_unattach, sorted]
  not_nil_mem_parts := by simp [mem_unattach]
  sorted_getLast_le := by
    simp only [unattach, pmap_map, Sorted, pairwise_pmap]
    exact (sorted_mergeSort' _ _).imp fun h _ _ ↦ h
  perm_finRange := by
    refine ((mergeSort_perm _ _).map _).flatten.trans ?_
    simpa [map_pmap]

def bindRight (c : OrderedPartition n)
    (cs : ∀ i : Fin c.parts.length, OrderedPartition c.parts[i.1].length) :
    OrderedPartition n := by
  apply ofUnsortedGetLast
    ((finRange c.parts.length).flatMap fun i ↦ (cs i).parts.map <| map (c.parts[i.1][·]))
  · simp only [mem_flatMap, mem_map]
    rintro _ ⟨i, -, l, hl, rfl⟩
    simp only [Sorted, pairwise_map]
    exact ((cs i).sorted_le_of_mem_parts hl).imp fun h ↦
      (c.sorted_le_of_mem_parts (getElem_mem ..)).get_mono h
  · simp
  · simp only [← Multiset.coe_eq_coe, ← Multiset.coe_join, ← Multiset.map_coe, ← Multiset.coe_bind]
    rw [← Multiset.bind, Multiset.bind_assoc]
    simp only [Multiset.bind_map, ← Multiset.map_coe, ← Multiset.map_bind, multisetBind_parts]
    simp only [Multiset.map_coe, map_getElem_finRange]
    conv_rhs => rw [← c.multisetBind_parts, ← map_getElem_finRange c.parts, ← Multiset.map_coe,
      Multiset.bind_map]
    rfl

def ofNodup.orderIso {m : ℕ} (L : List (List (Fin n))) (nodup : L.flatten.Nodup)
    (hm : L.flatten.length = m) : Fin m ≃o {x // x ∈ L.flatten} :=
  Finset.orderIsoOfFin ⟨(L.flatten : Multiset (Fin n)), nodup⟩ hm

open ofNodup in
def ofNodup {m : ℕ} (L : List (List (Fin n))) (sorted₁ : ∀ l ∈ L, l.Sorted (· ≤ ·))
    (not_nil : [] ∉ L)
    (sorted₂ : (L.pmap getLast fun _l hl ↦ ne_of_mem_of_not_mem hl not_nil).Sorted (· ≤ ·))
    (nodup : L.flatten.Nodup) (hm : L.flatten.length = m) : OrderedPartition m where
  parts :=
    L.pmap (fun l hl ↦ l.pmap (fun x hx ↦ (orderIso L nodup hm).symm ⟨x, hx⟩) fun x hx ↦ hl hx)
      fun _ ↦ subset_flatten_of_mem
  sorted_le_of_mem_parts := by
    simp only [mem_pmap, Sorted, forall_exists_index, @forall_swap (List (Fin m)),
      forall_apply_eq_imp_iff, pairwise_pmap, OrderIso.le_iff_le, Subtype.mk_le_mk]
    exact fun l hl ↦ (sorted₁ l hl).imp fun hle _ _ ↦ hle
  not_nil_mem_parts := by simp [not_nil]
  sorted_getLast_le := by
    simp only [Sorted, ne_eq, pairwise_pmap, pmap_eq_nil_iff, getLast_pmap, OrderIso.le_iff_le,
      Subtype.mk_le_mk]
    exact ((pairwise_pmap _).1 sorted₂).imp fun H₁ _ _ H₂ H₃ ↦ H₁ H₂ H₃
  perm_finRange := by
    set s : Finset (Fin n) := ⟨⟦L.flatten⟧, nodup⟩
    set e : Fin m ≃o s := Finset.orderIsoOfFin s hm
    simp only [flatten_pmap_pmap, pmap_eq_map, map_id']
    simp only [pmap_eq_map_attach, Subtype.coe_eta, ← Multiset.coe_eq_coe]
    exact congrArg Finset.val (Finset.map_univ_equiv e.symm.toEquiv)

def dropLast {m : ℕ} (c : OrderedPartition n) (hm : c.parts.dropLast.flatten.length = m) :
    OrderedPartition m :=
  ofNodup c.parts.dropLast
    (fun _l hl ↦ c.sorted_le_of_mem_parts (dropLast_subset _ hl))
    (fun h ↦ c.not_nil_mem_parts <| dropLast_subset _ h)
    ((pairwise_pmap _).mpr <| ((pairwise_pmap _).mp c.sorted_getLast_le).sublist <|
      dropLast_sublist _)
    (c.nodup_flatten_parts.sublist <| .flatten (dropLast_sublist _))
    hm

def appendLast.lastPart (l : List (Fin n)) : List (Fin (n + 1)) := l.map castSucc ++ [.last _]

@[simp]
theorem appendLast.lastPart_inj {l₁ l₂ : List (Fin n)} : lastPart l₁ = lastPart l₂ ↔ l₁ = l₂ := by
  simp [lastPart, map_inj_right (Fin.castSucc_injective _)]

@[simp]
theorem appendLast.length_lastPart (l : List (Fin n)) : (lastPart l).length = l.length + 1 := by
  simp [lastPart]

@[simp]
theorem appendLast.sorted_lastPart {l : List (Fin n)} :
    (lastPart l).Sorted (· < ·) ↔ l.Sorted (· < ·) := by
  simp [lastPart, Sorted, pairwise_append, pairwise_map, castSucc_lt_last]

@[simp]
theorem appendLast.getLast_lastPart (l : List (Fin n)) :
    (lastPart l).getLast (by simp [lastPart]) = .last n := by
  simp [lastPart]

def appendLast.lastPartFinset (l : List (Fin n)) (hl : l.Sorted (· < ·)) : Finset (Fin (n + 1)) :=
  .mk (lastPart l) (sorted_lastPart.mpr hl).nodup

@[simp]
theorem appendLast.mem_lastPartFinset {l : List (Fin n)} {hl : l.Sorted (· < ·)} {a : Fin (n + 1)} :
    a ∈ lastPartFinset l hl ↔ a ∈ lastPart l :=
  .rfl

@[simp]
theorem appendLast.val_lastPartFinset (l : List (Fin n)) (hl : l.Sorted (· < ·)) :
    (lastPartFinset l hl).val = lastPart l := rfl

@[simp]
theorem appendLast.card_lastPartFinset (l : List (Fin n)) (hl : l.Sorted (· < ·)) :
    (lastPartFinset l hl).card = l.length + 1 := by
  simp [lastPartFinset]

def appendLast.emb (l : List (Fin n)) (hl : l.Sorted (· < ·)) {m : ℕ} (hm : m = n - l.length) :
    Fin m ↪o Fin (n + 1) :=
  (lastPartFinset l hl)ᶜ.orderEmbOfFin <| by simp [Finset.card_compl, hm]

@[simp]
theorem appendLast.range_emb  (l : List (Fin n)) (hl : l.Sorted (· < ·)) {m : ℕ}
    (hm : m = n - l.length) : Set.range (emb l hl hm) = {x | x ∉ lastPart l} := by
  ext
  simp [emb, lastPartFinset]

open appendLast in
def appendLast {m : ℕ} (c : OrderedPartition m) (l : List (Fin n)) (hl : l.Sorted (· < ·))
    (hm : m = n - l.length) : OrderedPartition (n + 1) where
  parts := c.parts.map (map (emb l hl hm)) ++ [lastPart l]
  sorted_le_of_mem_parts := by
    simpa [or_imp, forall_and, (sorted_lastPart.mpr hl).le_of_lt] using c.sorted_le_of_mem_parts
  not_nil_mem_parts := by simp [lastPart]
  sorted_getLast_le := by
    simpa [Sorted, pairwise_append, le_last, pairwise_pmap, pmap_map]
      using (pairwise_pmap _).1 c.sorted_getLast_le
  perm_finRange := calc
    (map (map (emb l hl hm)) c.parts ++ [lastPart l]).flatten
      = map (emb l hl hm) c.parts.flatten ++ lastPart l := by
      rw [flatten_append, map_flatten, flatten_singleton]
    _ ~ map (emb l hl hm) (finRange m) ++ lastPart l := by rel [c.perm_finRange]
    _ ~ (finRange (n + 1)).diff (lastPart l) ++ lastPart l := by
      gcongr
      rw [emb, Finset.listMap_orderEmbOfFin_finRange, ← Multiset.coe_eq_coe,
        ← Multiset.coe_sub, ← Finset.val_univ_fin, ← val_lastPartFinset l hl,
        ← Finset.sdiff_val, ← Finset.compl_eq_univ_sdiff, Finset.sort_eq]
    _ ~ finRange (n + 1) := by
      rw [← Multiset.coe_eq_coe]
      exact tsub_add_cancel_of_le (Finset.val_le_iff.mpr (le_top : lastPartFinset l hl ≤ ⊤))

@[simp]
theorem getLast_parts_appendLast {m : ℕ} (c : OrderedPartition m) {l : List (Fin n)}
    (hl : l.Sorted (· < ·)) (hm : m = n - l.length) :
    (c.appendLast l hl hm).parts.getLast (by simp) = appendLast.lastPart l :=
  getLast_concat ..

@[simp]
theorem dropLast_parts_appendLast {m : ℕ} (c : OrderedPartition m) {l : List (Fin n)}
    (hl : l.Sorted (· < ·)) (hm : m = n - l.length) :
    (c.appendLast l hl hm).parts.dropLast = c.parts.map (map (appendLast.emb l hl hm)) := by
  simp [appendLast]

@[simp]
theorem dropLast_appendLast {m : ℕ} (c : OrderedPartition m) (l : List (Fin n))
    (hl : l.Sorted (· < ·)) (hm : m = n - l.length) :
    (c.appendLast l hl hm).dropLast (by simp [Function.comp_def]) = c := by
  ext1
  simp only [dropLast, ofNodup, Multiset.quot_mk_to_coe, dropLast_parts_appendLast, pmap_map,
    pmap_eq_self, OrderIso.symm_apply_eq, Subtype.ext_iff]
  rintro - _ i _
  erw [Finset.coe_orderIsoOfFin_apply ⟨_, _⟩ _ i] -- TODO: fix
  simp only [appendLast.emb]
  congr with x
  simp [← map_flatten, ← Multiset.map_coe, ← Set.mem_range]

theorem dropLast_appendLast_heq {m m' : ℕ} (c : OrderedPartition m) (l : List (Fin n))
    (hl : l.Sorted (· < ·)) (hm : m = n - l.length)
    (hm' : (c.appendLast l hl hm).parts.dropLast.flatten.length = m') :
    HEq ((c.appendLast l hl hm).dropLast hm') c := by
  obtain rfl : m = m' := by simp [← hm', Function.comp_def]
  rw [dropLast_appendLast]

def appendLastDropLastList (c : OrderedPartition (n + 1)) : List (Fin n) :=
  (c.parts.getLast c.parts_ne_nil).dropLast.pmap Fin.castPred fun _a ha ↦ ne_of_lt <|
    ((c.sorted_lt_of_mem_parts (getLast_mem _)).rel_dropLast_getLast ha).lt_top

@[simp]
theorem appendLastDropLastList_appendLast {m : ℕ} (c : OrderedPartition m) (l : List (Fin n))
    (hl : l.Sorted (· < ·)) (hm : m = n - l.length) :
    (c.appendLast l hl hm).appendLastDropLastList = l := by
  simp [appendLast, appendLastDropLastList, appendLast.lastPart, pmap_map]

theorem sorted_lt_appendLastDropLastList (c : OrderedPartition (n + 1)) :
    c.appendLastDropLastList.Sorted (· < ·) := by
  have := c.sorted_lt_of_mem_parts (getLast_mem (by simp))
  unfold appendLastDropLastList
  aesop (add simp [Sorted, pairwise_iff_getElem, Fin.castPred_lt_castPred_iff, ])

@[simp]
theorem mergeSort_appendLastDropLastList (c : OrderedPartition (n + 1)) :
    c.appendLastDropLastList.mergeSort (· ≤ ·) = c.appendLastDropLastList :=
  mergeSort_eq_self _ c.sorted_lt_appendLastDropLastList.le_of_lt

theorem nodup_appendLastDropLastList (c : OrderedPartition (n + 1)) :
    c.appendLastDropLastList.Nodup :=
  c.sorted_lt_appendLastDropLastList.nodup

theorem length_appendLastDropLastList (c : OrderedPartition (n + 1)) :
    c.appendLastDropLastList.length = (c.parts.getLast c.parts_ne_nil).length - 1 := by
  simp [appendLastDropLastList]

theorem length_flatten_dropLast_add_length_appendLastDropLastList (c : OrderedPartition (n + 1)) :
    c.parts.dropLast.flatten.length + c.appendLastDropLastList.length = n := by
  rw [length_appendLastDropLastList, ← Nat.add_sub_assoc]
  · apply tsub_eq_of_eq_add
    simpa using congrArg (length ∘ flatten) (dropLast_concat_getLast c.parts_ne_nil)
  · exact length_pos.2 <| c.ne_nil_of_mem_parts <| getLast_mem _

theorem length_flatten_dropLast_eq_sub (c : OrderedPartition (n + 1)) :
    c.parts.dropLast.flatten.length = n - c.appendLastDropLastList.length :=
  eq_tsub_of_add_eq c.length_flatten_dropLast_add_length_appendLastDropLastList

theorem sub_length_flatten_dropLast_eq (c : OrderedPartition (n + 1)) :
    n - c.parts.dropLast.flatten.length = c.appendLastDropLastList.length :=
  tsub_eq_of_eq_add <| .symm <| (add_comm _ _).trans <|
    c.length_flatten_dropLast_add_length_appendLastDropLastList

@[simp]
theorem appendLast.lastPart_appendLastDropLastList (c : OrderedPartition (n + 1)) :
    appendLast.lastPart c.appendLastDropLastList = c.parts.getLast c.parts_ne_nil := by
  simpa [lastPart, appendLastDropLastList, map_pmap]
    using dropLast_concat_getLast <| c.ne_nil_of_mem_parts <| getLast_mem _

theorem appendLast_dropLast {m} (c : OrderedPartition (n + 1)) (hm : _ = m) :
    (c.dropLast hm).appendLast c.appendLastDropLastList c.sorted_lt_appendLastDropLastList
      (by rw [← hm, c.length_flatten_dropLast_eq_sub]) = c := by
  ext1
  simp only [appendLast, dropLast, ofNodup, map_pmap, appendLast.lastPart_appendLastDropLastList]
  conv_rhs => rw [← dropLast_concat_getLast c.parts_ne_nil]
  congr 1
  simp only [pmap_eq_self]
  intro l hl i hi
  generalize_proofs H₁ H₂ H₃ H₄
  lift i to {i // i ∈ c.parts.dropLast.flatten} using id H₄
  simp only [Subtype.coe_eta]
  clear hi H₄
  revert i
  rw [← funext_iff, ← StrictMono.range_inj (by intro _ _ _; simpa) (Subtype.strictMono_coe _),
    Set.range_comp', (EquivLike.surjective _).range_eq, image_univ, appendLast.range_emb,
    Subtype.range_coe_subtype, appendLast.lastPart_appendLastDropLastList]
  ext x
  simp only [mem_setOf_eq, ← count_pos_iff]
  have : count x c.parts.dropLast.flatten + count x (c.parts.getLast c.parts_ne_nil) = 1 := by
    conv_rhs =>
      rw [← count_finRange x, ← c.perm_finRange.count_eq, ← dropLast_concat_getLast c.parts_ne_nil]
    simp
  omega

def appendLastEquiv :
    ((s : Finset (Fin n)) × OrderedPartition (n - s.card)) ≃ OrderedPartition (n + 1) where
  toFun c := c.2.appendLast (c.1.sort (· ≤ ·)) (Finset.sort_sorted_lt _) <| by simp
  invFun c := .mk ⟨c.appendLastDropLastList, c.nodup_appendLastDropLastList⟩ <|
    c.dropLast <| by simp [← length_flatten_dropLast_eq_sub]
  left_inv := by
    rintro ⟨s, c⟩
    simp [dropLast_appendLast_heq]
  right_inv c := by
    convert c.appendLast_dropLast _
    simp [Finset.sort]

@[simps]
def toComposition (c : OrderedPartition n) : Composition n where
  blocks := c.parts.map length
  blocks_pos := by
    rw [List.forall_mem_map]
    exact fun l hl ↦ length_pos.mpr <| c.ne_nil_of_mem_parts hl
  blocks_sum := c.sum_length_parts

@[simp]
lemma toComposition_atomic : (atomic n).toComposition = .ones n := by
  ext1
  simp [atomic, Function.comp_def]

def fiberToCompositionConcatEquiv {m} (c : Composition m) (k : ℕ) :
    {c' : OrderedPartition (m + k + 1) //
      c'.toComposition = c.append (.single (k + 1) k.succ_pos)} ≃
      ({c' : OrderedPartition m // c'.toComposition = c} ×
        {s : Finset (Fin (m + k)) // s.card = k}) where
  toFun c' := by
    have : c'.1.parts.map length = c.blocks ++ [k + 1] :=
        congrArg Composition.blocks c'.2
    refine ⟨⟨c'.1.dropLast ?_, ?_⟩, ⟨⟨c'.1.appendLastDropLastList,
      c'.1.nodup_appendLastDropLastList⟩, ?_⟩⟩
    · simp [this, c.blocks_sum]
    · ext1
      simp [this, dropLast, ofNodup, map_pmap]
    · calc
        _ = (c'.1.parts.map length).getLast (by simp) - 1 := by
          simp [length_appendLastDropLastList]
        _ = _ := by simp [this]
  invFun c' := by
    refine ⟨c'.1.1.appendLast (c'.2.1.sort (· ≤ ·)) (Finset.sort_sorted_lt _) ?_, ?_⟩
    · simp [c'.2.2]
    · simpa [Composition.ext_iff, appendLast, Function.comp_def, c'.2.2] using c'.1.2
  left_inv := by
    rintro ⟨c', hc'⟩
    ext1
    convert appendLast_dropLast _ _
    simp [Finset.sort]
  right_inv := by
    rintro ⟨⟨c', hc'⟩, s, hs⟩
    simp

/-- The number of ordered partitions that map to a given composition `c`
is given by the formula TODO LaTeX version. -/
theorem card_fiber_toComposition (c : Composition n) :
    #{c' : OrderedPartition n | c'.toComposition = c} =
      ∏ i : Fin c.length, Nat.choose (∑ j ∈ .Iic i, c.blocks[j] - 1) (c.blocks[i] - 1) := by
  have step : ∀ m k, ∀ c : Composition m,
      #{c' : OrderedPartition (m + (k + 1)) |
        c'.toComposition = c.append (.single (k + 1) k.succ_pos)} =
        #{c' : OrderedPartition m | c'.toComposition = c} * (m + k).choose k := by
    intro m k c
    simpa [Fintype.card_subtype]
      using Fintype.card_congr (fiberToCompositionConcatEquiv c k)
  induction c using Composition.recOnAppendSingle with
  | zero => simp [Composition.length, Finset.filter_singleton]
  | append_single k n c ih =>
    rw [step, ih]
    clear step ih
    set s := Composition.single (k + 1) k.succ_pos
    have hlen : c.length + 1 = (c.append s).length := by
      simp [s, Composition.length]
    simp only [← (finCongr hlen).prod_comp, Fin.prod_univ_castSucc, finCongr_apply]
    simp [Fin.sum_Iic_cast, Fin.sum_Iic_castSucc, ← Fin.top_eq_last, getElem_append_left,
      Fin.sum_univ_castSucc, s]

end OrderedPartition

end Fin
