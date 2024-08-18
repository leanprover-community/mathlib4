import Mathlib.Order.SuccPred.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.WellFoundedSet
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Atoms
import Mathlib.Data.Finite.Card

structure RootedTree where
  α : Type*
  [order : SemilatticeInf α]
  [bot : OrderBot α]
  [pred : PredOrder α]
  [pred_archimedean : IsPredArchimedean α]

attribute [coe] RootedTree.α

instance coeSort : CoeSort RootedTree (Type*) := ⟨RootedTree.α⟩

variable (t : RootedTree) (r : t)

def SubRootedTree : Type* := t

def SubRootedTree.root {t} (v : SubRootedTree t) : t := v

def RootedTree.subtree : SubRootedTree t := r

@[simp]
lemma RootedTree.root_subtree : (t.subtree r).root = r := rfl

@[simp]
lemma RootedTree.subtree_root (v : SubRootedTree t) : t.subtree v.root = v := rfl

@[ext]
lemma SubRootedTree.ext {t} (v₁ v₂ : SubRootedTree t) (h : v₁.root = v₂.root) : v₁ = v₂ := h

instance [Finite t] : Finite (SubRootedTree t) := inferInstanceAs (Finite t)

instance : SemilatticeInf t := t.order
instance : PredOrder t := t.pred
instance : OrderBot t := t.bot
instance : IsPredArchimedean t := t.pred_archimedean

instance Set.Ici.predOrder {α : Type*} [DecidableEq α] [PartialOrder α] [PredOrder α] {a : α} :
  PredOrder (Set.Ici a) where
  pred := fun x ↦ if ha : x.1 = a then ⟨a, by simp⟩ else
    ⟨Order.pred x.1, Order.le_pred_of_lt <| lt_of_le_of_ne (by simpa using x.2) <| Ne.symm ha⟩
  pred_le := fun ⟨x, hx⟩ ↦ by dsimp; split <;> simp_all [Order.pred_le]
  min_of_le_pred := @fun ⟨x, hx⟩ h ↦ by
    dsimp at h
    rw [isMin_iff_eq_bot]
    apply Subtype.val_injective
    simp only [coe_bot]
    split at h
    · assumption
    · simp only [Subtype.mk_le_mk] at h
      apply Order.min_of_le_pred at h
      exact (h.eq_of_le hx).symm
  -- le_of_pred_lt := @fun ⟨b, hb⟩ ⟨c, hc⟩ h ↦ by
  --   dsimp only at h
  --   rw [Subtype.mk_le_mk]
  --   split at h
  --   · simp_all [le_of_lt]
  --   · exact Order.le_of_pred_lt h
  le_pred_of_lt := @fun ⟨b, hb⟩ ⟨c, hc⟩ h ↦ by
    rw [Subtype.mk_lt_mk] at h
    dsimp only
    split
    · simp_all [le_of_lt]
    · exact Order.le_pred_of_lt h

instance Set.Ici.isPredArchimedean {α : Type*} [DecidableEq α] [PartialOrder α] [PredOrder α]
    [IsPredArchimedean α] {a : α} : IsPredArchimedean (Set.Ici a) where
  exists_pred_iterate_of_le := @fun ⟨b, hb⟩ ⟨c, hc⟩ hbc ↦ by
    rw [Subtype.mk_le_mk] at hbc
    obtain ⟨n, hn⟩ := IsPredArchimedean.exists_pred_iterate_of_le hbc
    use n
    clear hbc
    induction n generalizing b
    · simpa
    case succ n hn1 =>
      simp_all only [mem_Ici, Function.iterate_succ', Function.comp_apply]
      rw [mem_Ici] at hb hc
      rw [hn1 (Order.pred^[n] c)]
      · change dite .. = _
        apply Subtype.val_injective
        simp only [apply_dite Subtype.val, dite_eq_ite, ← hn, ite_eq_right_iff]
        intro h
        rw [h] at hn ⊢
        rw [← hn] at hb
        apply le_antisymm hb (Order.pred_le a)
      · apply le_trans _ (Order.pred_le ..)
        rwa [hn]
      · rfl

lemma IsPredArchimedean.le_total_of_le {α : Type*} [DecidableEq α] [PartialOrder α] [PredOrder α]
    [IsPredArchimedean α] (r v₁ v₂ : α) (h₁ : v₁ ≤ r) (h₂ : v₂ ≤ r) :
    v₁ ≤ v₂ ∨ v₂ ≤ v₁ := by
  obtain ⟨n, rfl⟩ := h₁.exists_pred_iterate
  obtain ⟨m, rfl⟩ := h₂.exists_pred_iterate
  clear h₁ h₂
  wlog h : n ≤ m
  · rw [Or.comm]
    apply this
    omega
  right
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, Function.iterate_add, Function.comp_apply]
  apply Order.pred_iterate_le

lemma IsPredArchimedean.lt_or_le_of_le {α : Type*} [DecidableEq α] [PartialOrder α] [PredOrder α]
    [IsPredArchimedean α] (r v₁ v₂ : α) (h₁ : v₁ ≤ r) (h₂ : v₂ ≤ r) :
    v₁ < v₂ ∨ v₂ ≤ v₁ := by
  rw [Classical.or_iff_not_imp_right]
  intro nh
  rcases le_total_of_le r v₁ v₂ h₁ h₂ with h | h
  · apply lt_of_le_of_ne h (ne_of_not_le nh).symm
  · contradiction

def IsPredArchimedean.find_atom {α : Type*} [DecidableEq α] [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] (r : α) : α :=
  Order.pred^[Nat.find (bot_le (a := r)).exists_pred_iterate - 1] r

lemma IsPredArchimedean.find_atom_le {α : Type*} [DecidableEq α] [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] (r : α) : IsPredArchimedean.find_atom r ≤ r :=
  Order.pred_iterate_le _ _

@[simp]
lemma IsPredArchimedean.pred_find_atom {α : Type*} [DecidableEq α] [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] (r : α) :
    Order.pred (IsPredArchimedean.find_atom r) = ⊥ := by
  unfold find_atom
  generalize h : Nat.find (bot_le (a := r)).exists_pred_iterate = n
  cases n
  · have : Order.pred^[0] r = ⊥ := by
      rw [← h]
      apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate
    simp only [Function.iterate_zero, id_eq] at this
    simp [this]
  · simp only [add_tsub_cancel_right, ← Function.iterate_succ_apply', Nat.succ_eq_add_one]
    rw [←h]
    apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate

lemma IsPredArchimedean.find_atom_ne_bot {α : Type*} [DecidableEq α] [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] (r : α) (hr : r ≠ ⊥) :
    IsPredArchimedean.find_atom r ≠ ⊥ := by
  unfold find_atom
  intro nh
  have := Nat.find_min' (bot_le (a := r)).exists_pred_iterate nh
  replace : Nat.find (bot_le (a := r)).exists_pred_iterate = 0 := by omega
  simp [this, hr] at nh

def IsPredArchimedean.find_atom_is_atom {α : Type*} [DecidableEq α] [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] (r : α) (hr : r ≠ ⊥) :
    IsAtom (IsPredArchimedean.find_atom r) := by
  constructor
  · apply find_atom_ne_bot r hr
  · intro b hb
    apply Order.le_pred_of_lt at hb
    simpa using hb


instance IsPredArchimedean.instIsAtomic {α : Type*} [DecidableEq α] [PartialOrder α] [OrderBot α]
    [PredOrder α] [IsPredArchimedean α] : IsAtomic α where
  eq_bot_or_exists_atom_le b := by
    rw [Classical.or_iff_not_imp_left]
    intro hb
    use find_atom b, find_atom_is_atom b hb, find_atom_le b

@[coe, reducible]
def coeTree {t : RootedTree} [DecidableEq t] (r : SubRootedTree t) : RootedTree :=
  {α := Set.Ici r.root}

instance [DecidableEq t] : CoeOut (SubRootedTree t) RootedTree := ⟨coeTree⟩

@[coe]
def coeSet {t} (r : SubRootedTree t) : Set t := Set.Ici r.root

instance : Coe (SubRootedTree t) (Set t) := ⟨coeSet⟩

instance [DecidableEq t] (r : SubRootedTree t) : CoeOut r t where
  coe := Subtype.val

lemma root_eq_bot_of_coe_eq_bot {t : RootedTree} [DecidableEq t] (r : SubRootedTree t) (v : ↑r)
    (hv : (v : t) = ⊥) : r.root = ⊥ := by
  simpa [hv] using v.2

def RootedTree.subtrees [DecidableEq t] : Set (SubRootedTree t) :=
  {x | IsAtom x.root}

lemma root_ne_bot {t : RootedTree} [DecidableEq t] (r : t.subtrees) : r.1.root ≠ ⊥ := by
  have := r.2
  simp only [RootedTree.subtrees, Set.mem_setOf_eq] at this
  exact this.1

lemma mem_subtree_ne_bot {t : RootedTree} [DecidableEq t] {r : t.subtrees}
    (v : ↑r) : (v : t) ≠ ⊥ := by
  intro nh
  have := v.2
  simp only [nh, Set.mem_Ici, le_bot_iff] at this
  apply root_ne_bot _ this

lemma subtrees_inf_eq_bot_iff {t : RootedTree} [DecidableEq t]
    {t₁ t₂ : t.subtrees} (v₁ v₂ : t) (h₁ : v₁ ∈ (t₁ : Set t)) (h₂ : v₂ ∈ (t₂ : Set t)) :
      v₁ ⊓ v₂ = ⊥ ↔ t₁ ≠ t₂ where
  mp h := by
    intro nh
    have : t₁.1.root ≤ (v₁ : t) ⊓ (v₂ : t) := by
      simp only [le_inf_iff]
      exact ⟨h₁, nh ▸ h₂⟩
    rw [h] at this
    simp only [le_bot_iff] at this
    exact root_ne_bot _ this
  mpr h := by
    obtain ⟨t₁, ht1 : IsAtom t₁.root⟩ := t₁
    obtain ⟨t₂, ht2 : IsAtom t₂.root⟩ := t₂
    simp only [Set.mem_Ici] at h₁ h₁ ⊢
    contrapose! h
    rw [← bot_lt_iff_ne_bot] at h
    rcases IsPredArchimedean.lt_or_le_of_le v₁ (v₁ ⊓ v₂) t₁.root (by simp) ‹_› with oh | oh
    · have : IsAtom t₁.root := ht1
      simp_all [this.lt_iff]
    rw [le_inf_iff] at oh
    have := IsPredArchimedean.le_total_of_le v₂ t₁.root t₂.root oh.2 ‹_›
    simp only [ht2.le_iff_eq ht1.1, ht1.le_iff_eq ht2.1, eq_comm, or_self] at this
    ext
    exact this

lemma subtrees_val_inj {t : RootedTree} [DecidableEq t]
    {t₁ t₂ : t.subtrees} {v₁ : ↑t₁} {v₂ : ↑t₂} (h : (v₁ : t) = (v₂ : t)) : t₁ = t₂ := by
  by_contra! nh
  rw [← subtrees_inf_eq_bot_iff v₁.1 v₂.1 v₁.2 v₂.2] at nh
  simp only [h, le_refl, inf_of_le_left, imp_false] at nh
  apply mem_subtree_ne_bot _ nh

def RootedTree.subtreeOf [DecidableEq t] (r : t) (hr : r ≠ ⊥) : t.subtrees :=
  ⟨t.subtree <| IsPredArchimedean.find_atom r, by
    simp only [subtrees, Set.mem_setOf_eq, root_subtree]
    exact IsPredArchimedean.find_atom_is_atom r hr⟩

lemma RootedTree.mem_subtreeOf [DecidableEq t] {r : t} (hr : r ≠ ⊥) :
  r ∈ (t.subtreeOf r hr : Set t) :=
  IsPredArchimedean.find_atom_le r

lemma subtreeOf_inf {t : RootedTree} [DecidableEq t]
    (v₁ v₂ : t) (h : v₁ ⊓ v₂ ≠ ⊥) :
    t.subtreeOf (v₁ ⊓ v₂) h = t.subtreeOf v₂ (fun nh ↦ by simp [nh] at h) := by
  by_contra! nh
  rw [← subtrees_inf_eq_bot_iff (v₁ ⊓ v₂) v₂] at nh
  simp [h] at nh
  apply RootedTree.mem_subtreeOf
  apply RootedTree.mem_subtreeOf

def RootedTree.homeomorphism (a b : RootedTree) : Prop := ∃ f : InfHom a b, Function.Injective f

instance : IsRefl RootedTree RootedTree.homeomorphism where
  refl a := ⟨InfHom.id a, fun ⦃_ _⦄ ↦ id⟩

instance : IsTrans RootedTree RootedTree.homeomorphism where
  trans _ _ _ := fun ⟨ab, hab⟩ ⟨bc, hbc⟩ ↦ ⟨bc.comp ab, hbc.comp hab⟩

def InfHom.subtype_val  {α : Type*} [SemilatticeInf α] {P : α → Prop}
    (Pinf : ∀ ⦃x y : α⦄, P x → P y → P (x ⊓ y)) :
    letI := Subtype.semilatticeInf Pinf
    InfHom {x : α // P x} α :=
  letI := Subtype.semilatticeInf Pinf
  InfHom.mk Subtype.val (by simp)

def InfHom.Ici_val  {α : Type*} [SemilatticeInf α] {r : α} :
    InfHom (Set.Ici r) α := InfHom.subtype_val (fun _ _ ↦ le_inf)

lemma RootedTree.homeomorphism_of_subtree {a b : RootedTree} [DecidableEq b.α] {x : b}
    (h : a.homeomorphism (b.subtree x)) : a.homeomorphism b := by
  obtain ⟨f, hf⟩ := h
  use InfHom.comp InfHom.Ici_val f
  rw [InfHom.coe_comp]
  apply Function.Injective.comp _ hf
  exact Subtype.val_injective

lemma RootedTree.subtree_card_lt {a : RootedTree} [Finite a] [DecidableEq a.α]
    {x : a} (hx : x ≠ ⊥) :
    Nat.card (a.subtree x) < Nat.card a := Finite.card_subtype_lt (x := ⊥) (by simpa)

def Set.embeddingRel {α β : Type*} (r : α → β → Prop) (a : Set α) (b : Set β) : Prop :=
  ∃ f : a ↪ b, ∀ x : a, r x (f x)

theorem RootedTree.homeomorphism_of_subtrees_embeddingRel (t₁ t₂ : RootedTree)
    [DecidableEq t₁] [DecidableEq t₂]
    (h : Set.embeddingRel
      (fun (x : SubRootedTree t₁) (y : SubRootedTree t₂) ↦ RootedTree.homeomorphism x y)
      t₁.subtrees t₂.subtrees) :
    t₁.homeomorphism t₂ := by classical
  obtain ⟨g, hg⟩ := h
  choose g' hg' using hg
  let g'' (t : t₁.subtrees) (b : t₁) : t₂ := if h : b ∈ ↑t.1 then g' t ⟨b, h⟩ else ⊥
  have hg''1 (t : t₁.subtrees) : Set.MapsTo (g'' t) t (g t) := fun x hx ↦ by
    simp only [hx, ↓reduceDIte, g'']
    apply Subtype.coe_prop
  have hg''2 (t : t₁.subtrees) : Set.InjOn (g'' t) t := fun x hx y hy hxy ↦ by
    simp only [hx, ↓reduceDIte, hy, g'', Subtype.val_inj] at hxy
    apply hg' at hxy
    simpa using hxy
  clear hg'
  let ans (b : t₁) : t₂ := if h : b = ⊥ then ⊥ else g'' (t₁.subtreeOf b h) b
  use InfHom.mk ans ?minf
  case minf =>
    intro a b
    by_cases ha : a = ⊥
    · simp [ha, ans]
    by_cases hb : b = ⊥
    · simp [hb, ans]
    by_cases hab : t₁.subtreeOf a ha = t₁.subtreeOf b hb
    · simp only [ha, ↓reduceDIte, hab, hb, ans]
      have : a ⊓ b ≠ ⊥ := by
        simp [subtrees_inf_eq_bot_iff a b (RootedTree.mem_subtreeOf _ ha)
          (RootedTree.mem_subtreeOf _ hb), hab]
      simp only [this, ↓reduceDIte]
      rw [subtreeOf_inf]
      simp only [ne_eq, eq_mp_eq_cast, g'']
      rw [dite_cond_eq_true, dite_cond_eq_true, dite_cond_eq_true]
      · rw [← Subtype.coe_inf ?pinf]
        congr 1
        rw [← InfHomClass.map_inf]
        congr
        · intros
          simp_all
      · simp [RootedTree.mem_subtreeOf _ hb]
      · simp [← hab, RootedTree.mem_subtreeOf _ ha]
      · simp [← subtreeOf_inf (h := this), RootedTree.mem_subtreeOf _ this]
    · trans ⊥
      · simp [ans, subtrees_inf_eq_bot_iff a b (RootedTree.mem_subtreeOf _ ha)
          (RootedTree.mem_subtreeOf _ hb), hab]
      · rw [eq_comm, subtrees_inf_eq_bot_iff
          (t₁ := g <| t₁.subtreeOf a ha) (t₂ := g <| t₁.subtreeOf b hb)]
        · simp [hab]
        · simp [ans, ha]
          apply hg''1
          apply RootedTree.mem_subtreeOf _ ha
        · simp [ans, hb]
          apply hg''1
          apply RootedTree.mem_subtreeOf _ hb
  · dsimp only [InfHom.coe_mk]
    intro x y hxy
    simp only [ans] at hxy
    split_ifs at hxy with hx hy hy
    · cc
    · have := RootedTree.mem_subtreeOf _ hy
      simp only [this, ↓reduceDIte, g''] at hxy
      exact (mem_subtree_ne_bot _ hxy.symm).elim
    · have := RootedTree.mem_subtreeOf _ hx
      simp only [this, ↓reduceDIte, g''] at hxy
      exact (mem_subtree_ne_bot _ hxy).elim
    · have m1 := RootedTree.mem_subtreeOf _ hx
      have m2 := RootedTree.mem_subtreeOf _ hy
      have : t₁.subtreeOf x hx = t₁.subtreeOf y hy := by
        simp only [m1, ↓reduceDIte, m2, g''] at hxy
        apply subtrees_val_inj at hxy
        exact g.injective hxy
      rw [this] at m1 hxy
      apply hg''2 _ m1 m2 hxy


def Finset.embeddingRel {α β : Type*} (r : α → β → Prop) (a : Finset α) (b : Finset β) : Prop :=
  ∃ f : a ↪ b, ∀ x : a, r x (f x)

lemma Finset.embeddingRel_of_toList_sublistForall₂ {α β : Type*} (r : α → β → Prop)
    (a : Finset α) (b : Finset β) (h : List.SublistForall₂ r a.toList b.toList) :
    Finset.embeddingRel r a b := by classical
  rw [List.sublistForall₂_iff] at h
  obtain ⟨l, hl, hl3⟩ := h
  apply List.sublist_eq_map_getElem at hl3
  obtain ⟨is, rfl, hl3⟩ := hl3
  rw [List.forall₂_iff_get] at hl
  obtain ⟨hl1, hl2⟩ := hl
  simp only [List.length_map, Fin.getElem_fin, List.getElem_map] at hl1
  use ⟨fun x ↦ ⟨b.toList[is[a.toList.indexOf x.1]'(by
    simp only [← hl1, List.indexOf_lt_length, Finset.mem_toList, Finset.coe_mem]
    )], by
      rw [← Finset.mem_toList]
      apply List.getElem_mem
    ⟩, by
    intro x y hxy
    have n1 := Finset.nodup_toList b
    simp only [Fin.getElem_fin, Subtype.mk.injEq, n1.getElem_inj_iff, Fin.val_inj] at hxy
    rw [hl3.nodup.getElem_inj_iff] at hxy
    apply_fun a.toList.get? at hxy
    simp only [List.get?_eq_getElem?, Finset.mem_toList, Finset.coe_mem, List.getElem?_indexOf,
      Option.some.injEq] at hxy
    ext
    exact hxy⟩
  intro
  dsimp only [Function.Embedding.coeFn_mk]
  simp only [List.length_map, Fin.getElem_fin, List.getElem_map,
    List.get_eq_getElem] at hl2
  conv =>
    enter [1]
    tactic =>
      apply (a.toList.getElem_indexOf _).symm
      simp only [List.indexOf_lt_length, Finset.mem_toList, Finset.coe_mem]
  apply hl2
  all_goals simp only [← hl1, List.indexOf_lt_length, Finset.mem_toList, Finset.coe_mem]

theorem Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_finsetEmbedding {α : Type*}
    {β : ℕ → Type*} (dβ : {n : ℕ} → β n → α)
    (r : α → α → Prop) [IsRefl α r] [IsTrans α r] {s : Set α}
    (h : s.PartiallyWellOrderedOn r) :
    ∀ f : (n : ℕ) → Finset (β n), (∀ n, dβ '' (f n).toSet ⊆ s) →
      ∃ m n : ℕ, m < n ∧ Finset.embeddingRel (fun a b ↦ r (dβ a) (dβ b))
      (f m) (f n) := by classical
  intro f hf
  have := partiallyWellOrderedOn_sublistForall₂ r h
  specialize this (fun n ↦ (f n).toList.map dβ) _
  · intro n x
    simp only [List.mem_map, Finset.mem_toList, forall_exists_index, and_imp]
    intro x hx _
    apply hf
    simp only [mem_image, Finset.mem_coe]
    use x, hx
  obtain ⟨n, m, hnm, h⟩ := this
  use n, m, hnm
  simp only [List.sublistForall₂_map_right_iff, List.sublistForall₂_map_left_iff] at h
  apply Finset.embeddingRel_of_toList_sublistForall₂ _ _ _ h

theorem Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_finiteSetEmbedding {α : Type*}
    {β : ℕ → Type*} (dβ : {n : ℕ} → β n → α)
    (r : α → α → Prop) [IsRefl α r] [IsTrans α r] {s : Set α}
    (h : s.PartiallyWellOrderedOn r) :
    ∀ f : (n : ℕ) → Set (β n), (∀ n, (f n).Finite ∧ dβ '' (f n) ⊆ s) →
      ∃ m n : ℕ, m < n ∧ Set.embeddingRel (fun a b ↦ r (dβ a) (dβ b))
      (f m) (f n) := by
  intro f hf
  obtain ⟨n, m, hnm, ⟨g, hg⟩⟩ :=
    Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_finsetEmbedding dβ r h
    (fun n ↦ (hf n).1.toFinset) (by simp [hf])
  use n, m, hnm, (hf n).1.subtypeEquivToFinset.toEmbedding.trans
    <| g.trans (hf m).1.subtypeEquivToFinset.symm.toEmbedding
  intro x
  exact hg <| (hf n).1.subtypeEquivToFinset x

-- This is Kruskal's tree theorem.
-- Following the proof in "On well-quasi-ordering finite trees, C. ST. J. A. NASH-WILLIAMS"
lemma Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_trees :
    {f : RootedTree | Finite f}.PartiallyWellOrderedOn RootedTree.homeomorphism := by classical
  rw [Set.PartiallyWellOrderedOn.iff_not_exists_isMinBadSeq (Nat.card ∘ RootedTree.α)]
  rintro ⟨f, ⟨hf1, hf2⟩, hf3⟩
  haveI : ∀ i, Finite (f i).α := hf1
  clear hf1
  let 𝔹 : Set RootedTree := ⋃ i, (↑) '' (f i).subtrees
  have : 𝔹.PartiallyWellOrderedOn RootedTree.homeomorphism := by
    rw [Set.PartiallyWellOrderedOn.iff_forall_not_isBadSeq]
    rintro g ⟨hg', hg⟩
    simp only [mem_iUnion, 𝔹] at hg'
    choose gi hgi using hg'
    have : (Set.univ : Set ℕ).IsPWO := Set.IsWF.isPWO wellFounded_lt
    obtain ⟨g', hg'⟩ := this.exists_monotone_subseq gi (by simp)
    let f' (i : ℕ) : RootedTree := if i < gi (g' 0) then f i else g (g' (i - gi (g' 0)))
    have : IsBadSeq RootedTree.homeomorphism {f | Finite f.α} f' := by
      constructor
      · intro n
        simp only [mem_setOf_eq, f']
        split
        · infer_instance
        · have := hgi (g' (n - gi (g' 0)))
          simp only [mem_range, RootedTree.subtrees, RootedTree.subtree] at this
          obtain ⟨x, -, hx⟩ := this
          rw [← hx]
          infer_instance
      · intro n m hnm
        unfold_let f'
        dsimp only
        by_cases hm : m < gi (g' 0)
        · have := hnm.trans hm
          simp_all
        · simp only [hm, ↓reduceIte]
          by_cases hn : n < gi (g' 0)
          · simp only [hn, ↓reduceIte]
            have := hgi (g' (m - gi (g' 0)))
            simp only [mem_range, RootedTree.subtrees, RootedTree.subtree] at this
            obtain ⟨x, -, hx⟩ := this
            rw [← hx]
            apply mt RootedTree.homeomorphism_of_subtree
            apply hf2
            apply hn.trans_le
            apply hg'
            simp
          · simp only [hn, ↓reduceIte]
            apply hg
            simp only [OrderEmbedding.lt_iff_lt]
            omega
    apply hf3 (gi (g' 0)) f' (by intros; simp_all [f']) _ this
    simp only [lt_self_iff_false, ↓reduceIte, le_refl, tsub_eq_zero_of_le, Function.comp_apply, f']
    have := hgi (g' 0)
    simp only [mem_range, RootedTree.subtrees, RootedTree.subtree, Subtype.exists] at this
    obtain ⟨x, hx1, hx2⟩ := this
    rw [← hx2]
    apply RootedTree.subtree_card_lt
    exact hx1.1
  replace this := Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_finiteSetEmbedding
    (β := fun n ↦ SubRootedTree (f n)) (↑) RootedTree.homeomorphism this
  specialize this (fun i ↦ (f i).subtrees) _
  · intro n
    constructor
    · apply Set.toFinite
    · simp only [image_subset_iff]
      intro x hx
      simp only [preimage_iUnion, mem_iUnion, mem_preimage, mem_image, RootedTree.mk.injEq, 𝔹]
      use n, x, hx
  obtain ⟨n, m, hnm, g⟩ := this
  apply hf2 n m hnm
  apply RootedTree.homeomorphism_of_subtrees_embeddingRel
  exact g

#print axioms Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_trees
