import Mathlib.Combinatorics.ToMathlib
import Mathlib.Order.SuccPred.Basic
import Mathlib.Data.Fintype.Basic
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

def LabeledTree (α : Type*) := (s : RootedTree) × (s → α)

@[coe, reducible]
def LabeledTree.coeLTree {α : Type*} (t : LabeledTree α) := t.1

instance coeLTree {α : Type*} : CoeOut (LabeledTree α) RootedTree := ⟨LabeledTree.coeLTree⟩

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

def LabeledTree.homeomorphism {α β : Type*} (r : α → β → Prop) (a : LabeledTree α)
    (b : LabeledTree β) : Prop :=
  ∃ f : InfHom a b, Function.Injective f ∧ ∀ x, r (a.2 x) (b.2 (f x))

def LabeledTree.subtrees {α : Type*} (t : LabeledTree α) [DecidableEq t] :=
  t.1.subtrees

@[coe, reducible]
def coeTreeL {α : Type*} {t : LabeledTree α} [DecidableEq t] (r : SubRootedTree t) :
    LabeledTree α :=
  ⟨r, fun x ↦ t.2 x⟩

instance {α : Type*} {t : LabeledTree α} [DecidableEq t] :
  CoeOut (SubRootedTree t) (LabeledTree α) := ⟨coeTreeL⟩

instance {α : Type*} (r : α → α → Prop) [IsRefl α r] :
    IsRefl (LabeledTree α) (LabeledTree.homeomorphism r) where
  refl a := ⟨InfHom.id a, fun ⦃_ _⦄ ↦ id, fun _ ↦ IsRefl.refl _⟩

instance {α : Type*} (r : α → α → Prop) [IsTrans α r] :
    IsTrans (LabeledTree α) (LabeledTree.homeomorphism r) where
  trans _ _ _ := fun ⟨ab, ⟨hab, hab2⟩⟩ ⟨bc, ⟨hbc, hbc2⟩⟩ ↦
    ⟨bc.comp ab, hbc.comp hab, fun _ ↦ Trans.trans (hab2 _) (hbc2 _)⟩

lemma RootedTree.homeomorphism_of_subtree {a b : RootedTree} [DecidableEq b.α] {x : b}
    (h : a.homeomorphism (b.subtree x)) : a.homeomorphism b := by
  obtain ⟨f, hf⟩ := h
  use InfHom.comp InfHom.Ici_val f
  rw [InfHom.coe_comp]
  apply Function.Injective.comp _ hf
  exact Subtype.val_injective

lemma LabeledTree.homeomorphism_of_subtree {α β : Type*} (r : α → β → Prop) {a : LabeledTree α}
    {b : LabeledTree β} [DecidableEq b] {x : b.1}
    (h : a.homeomorphism r (b.1.subtree x)) : a.homeomorphism r b := by
  obtain ⟨f, hf⟩ := h
  use InfHom.comp InfHom.Ici_val f
  rw [InfHom.coe_comp]
  constructor
  · apply Function.Injective.comp _ hf.1
    exact Subtype.val_injective
  · intro x
    apply hf.2

lemma RootedTree.subtree_card_lt {a : RootedTree} [Finite a] [DecidableEq a.α]
    {x : a} (hx : x ≠ ⊥) :
    Nat.card (a.subtree x) < Nat.card a := Finite.card_subtype_lt (x := ⊥) (by simpa)

def Set.embeddingRel {α β : Type*} (r : α → β → Prop) (a : Set α) (b : Set β) : Prop :=
  ∃ f : a ↪ b, ∀ x : a, r x (f x)

theorem LabeledTree.homeomorphism_of_subtrees_embeddingRel {α : Type*} (r : α → α → Prop)
    (t₁ t₂ : LabeledTree α) (hr : r (t₁.2 ⊥) (t₂.2 ⊥)) [DecidableEq t₁] [DecidableEq t₂]
    (h : Set.embeddingRel
      (fun (x : SubRootedTree t₁) (y : SubRootedTree t₂) ↦ LabeledTree.homeomorphism r x y)
      t₁.subtrees t₂.subtrees) :
    t₁.homeomorphism r t₂ := by classical
  obtain ⟨g, hg⟩ := h
  choose g' hg' using hg
  let g'' (t : t₁.subtrees) (b : t₁.1) : t₂.1 := if h : b ∈ ↑t.1 then g' t ⟨b, h⟩ else ⊥
  have hg''1 (t : t₁.subtrees) : Set.MapsTo (g'' t) t (g t) := fun x hx ↦ by
    simp only [hx, ↓reduceDIte, g'']
    apply Subtype.coe_prop
  have hg''2 (t : t₁.subtrees) : Set.InjOn (g'' t) t := fun x hx y hy hxy ↦ by
    simp only [hx, ↓reduceDIte, hy, g'', Subtype.val_inj] at hxy
    apply (hg' _).1 at hxy
    simpa using hxy
  have hg''3 (t : t₁.subtrees) :
      ∀ x ∈ (t : Set t₁), r (t₁.2 x) (t₂.2 (g'' t x)) := fun x hx ↦ by
    simp only [hx, ↓reduceDIte, g'', Subtype.val_inj]
    change r ((t : LabeledTree α).2 ⟨x, hx⟩) _
    apply (hg' t).2
  clear hg'
  let ans (b : t₁.1) : t₂.1 := if h : b = ⊥ then ⊥ else g'' (t₁.1.subtreeOf b h) b
  use InfHom.mk ans ?minf, ?_, ?_
  case minf =>
    intro a b
    by_cases ha : a = ⊥
    · simp [ha, ans]
    by_cases hb : b = ⊥
    · simp [hb, ans]
    by_cases hab : t₁.1.subtreeOf a ha = t₁.1.subtreeOf b hb
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
          (t₁ := g <| t₁.1.subtreeOf a ha) (t₂ := g <| t₁.1.subtreeOf b hb)]
        · simpa [g.apply_eq_iff_eq]
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
      have : t₁.1.subtreeOf x hx = t₁.1.subtreeOf y hy := by
        simp only [m1, ↓reduceDIte, m2, g''] at hxy
        apply subtrees_val_inj at hxy
        exact g.injective hxy
      rw [this] at m1 hxy
      apply hg''2 _ m1 m2 hxy
  · intro x
    dsimp only [InfHom.coe_mk, ans]
    split_ifs with h
    · simpa [h]
    · apply hg''3
      apply RootedTree.mem_subtreeOf


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
      ∃ g : ℕ ↪o ℕ, ∀ n m, n ≤ m → Finset.embeddingRel (fun a b ↦ r (dβ a) (dβ b))
      (f (g n)) (f (g m)) := by classical
  intro f hf
  have := partiallyWellOrderedOn_sublistForall₂ r h |>.exists_monotone_subseq
  specialize this (fun n ↦ (f n).toList.map dβ) _
  · intro n x
    simp only [List.mem_map, Finset.mem_toList, forall_exists_index, and_imp]
    intro x hx _
    apply hf
    simp only [mem_image, Finset.mem_coe]
    use x, hx
  obtain ⟨g, hg⟩ := this
  use g
  intro n m hnm
  specialize hg n m hnm
  simp only [List.sublistForall₂_map_right_iff, List.sublistForall₂_map_left_iff] at hg
  apply Finset.embeddingRel_of_toList_sublistForall₂ _ _ _ hg

theorem Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_finiteSetEmbedding {α : Type*}
    {β : ℕ → Type*} (dβ : {n : ℕ} → β n → α)
    (r : α → α → Prop) [IsRefl α r] [IsTrans α r] {s : Set α}
    (h : s.PartiallyWellOrderedOn r) :
    ∀ f : (n : ℕ) → Set (β n), (∀ n, (f n).Finite ∧ dβ '' (f n) ⊆ s) →
      ∃ g : ℕ ↪o ℕ, ∀ n m, n ≤ m → Set.embeddingRel (fun a b ↦ r (dβ a) (dβ b))
      (f (g n)) (f (g m)) := fun f hf ↦
  have ⟨g, hg⟩ :=
    Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_finsetEmbedding dβ r h
    (fun n ↦ (hf n).1.toFinset) (by simp [hf])
  ⟨g, fun n m hnm ↦
    have ⟨g', hg'⟩ := hg n m hnm
    ⟨(hf _).1.subtypeEquivToFinset.toEmbedding.trans <|
      g'.trans (hf _).1.subtypeEquivToFinset.symm.toEmbedding,
        fun x ↦ hg' <| (hf _).1.subtypeEquivToFinset x⟩⟩

-- This is Kruskal's tree theorem.
-- Following the proof in "On well-quasi-ordering finite trees, C. ST. J. A. NASH-WILLIAMS"
lemma Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_trees {α : Type*}
    (r : α → α → Prop) [IsRefl α r] [IsTrans α r] (s : Set α) (hs : s.PartiallyWellOrderedOn r) :
    {f : LabeledTree α | Finite f ∧ Set.range f.2 ⊆ s}.PartiallyWellOrderedOn
      (LabeledTree.homeomorphism r) := by classical
  rw [Set.PartiallyWellOrderedOn.iff_not_exists_isMinBadSeq (Nat.card ·.1)]
  rintro ⟨f, ⟨hf1, hf2⟩, hf3⟩
  simp only [mem_setOf_eq, forall_and] at hf1
  obtain ⟨hf11, hf12⟩ := hf1
  haveI : ∀ i, Finite (f i).1 := hf11
  clear hf11
  let 𝔹 : Set (LabeledTree α) := ⋃ i, (↑) '' (f i).subtrees
  have : 𝔹.PartiallyWellOrderedOn (LabeledTree.homeomorphism r) := by
    rw [Set.PartiallyWellOrderedOn.iff_forall_not_isBadSeq]
    rintro g ⟨hg', hg⟩
    simp only [mem_iUnion, 𝔹] at hg'
    choose gi hgi using hg'
    have : (Set.univ : Set ℕ).IsPWO := Set.IsWF.isPWO wellFounded_lt
    obtain ⟨g', hg'⟩ := this.exists_monotone_subseq gi (by simp)
    let f' (i : ℕ) : LabeledTree α := if i < gi (g' 0) then f i else g (g' (i - gi (g' 0)))
    have : IsBadSeq (LabeledTree.homeomorphism r) {f | Finite f ∧ Set.range f.2 ⊆ s} f' := by
      constructor
      · intro n
        constructor
        · simp only [f']
          split
          · infer_instance
          · have := hgi (g' (n - gi (g' 0)))
            simp only [mem_range, RootedTree.subtrees, RootedTree.subtree] at this
            obtain ⟨x, -, hx⟩ := this
            rw [← hx]
            infer_instance
        · unfold_let f'
          dsimp
          split_ifs with h
          · have : (if n < gi (g' 0) then f n else g (g' (n - gi (g' 0)))) =
                f n := by
              simp [h]
            rw [this]
            apply hf12
          · have : (if n < gi (g' 0) then f n else g (g' (n - gi (g' 0)))) =
                g (g' (n - gi (g' 0))) := by
              simp [h]
            rw [this]
            have := hgi (g' (n - gi (g' 0)))
            simp only [LabeledTree.subtrees, RootedTree.subtrees, mem_image] at this
            obtain ⟨x, -, hx⟩ := this
            rw [← hx]
            trans Set.range (f (gi (g' (n - gi (g' 0))))).snd
            · rw [Set.range_subset_range_iff_exists_comp]
              use (↑)
              rfl
            · apply hf12
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
            apply mt (LabeledTree.homeomorphism_of_subtree r)
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
    (β := fun n ↦ SubRootedTree (f n)) (↑) (LabeledTree.homeomorphism r) this
  specialize this (fun i ↦ (f i).subtrees) _
  · intro n
    constructor
    · apply Set.toFinite
    · simp only [image_subset_iff]
      intro x hx
      simp only [preimage_iUnion, mem_iUnion, mem_preimage, mem_image, RootedTree.mk.injEq, 𝔹]
      use n, x, hx
  obtain ⟨g, hg⟩ := this
  specialize hs (fun n ↦ (f (g n)).2 ⊥) (fun n ↦ hf12 (g n) (by simp))
  obtain ⟨n, m, hnm, hr⟩ := hs
  apply hf2 (g n) (g m) (g.strictMono hnm)
  apply LabeledTree.homeomorphism_of_subtrees_embeddingRel
  exact hr
  apply hg _ _ hnm.le
