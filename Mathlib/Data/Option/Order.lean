import Mathlib.Order.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Logic.Equiv.Basic
/-! TODO TBD -/

namespace Option

/-- TODO TBD Delete once std4 patch merges -/
inductive StrictRel {α : Type*} {β : Type*} (r : α → β → Prop) : Option α → Option β → Prop
  /-- If `a ~ b`, then `some a ~ some b` -/
  | some {a b} : r a b → StrictRel r (some a) (some b)

section LT

/-- TODO rename once core removes existing instance -/
instance instLTOption' {α : Type*} [LT α] : LT (Option (α)) := ⟨StrictRel (· < ·)⟩

variable {α : Type*} [LT α]

@[simp]
lemma not_none_lt_none : ¬ (none : Option α) < none := fun ha => by cases ha
@[simp]
lemma not_none_lt_some {a : α} :
    ¬ (none : Option α) < some a := fun ha => by cases ha
@[simp]
lemma not_some_lt_none {a : α} :
    ¬ some a < (none : Option α) := fun ha => by cases ha
lemma some_lt_some_of_lt {a b : α} (hab : a < b) :
    some a < some b := StrictRel.some hab
lemma lt_of_some_lt_some {a b : α} (hab : some a < some b) :
    a < b := by cases hab; assumption
@[simp]
lemma some_lt_some_iff {a b : α} : some a < some b ↔ a < b :=
  ⟨lt_of_some_lt_some, some_lt_some_of_lt⟩

lemma isSome_of_lt {oa ob : Option α} (hab : oa < ob) : oa.isSome := by cases hab; rfl
lemma isSome_of_gt {oa ob : Option α} (hab : oa < ob) : ob.isSome := by cases hab; rfl

lemma lt_of_mem_lt_mem {oa ob : Option α} {a b : α} (ha : a ∈ oa) (hb : b ∈ ob)
    (hab : a < b) : oa < ob := by
  cases oa
  · cases ha
  · cases ob
    · cases hb
    · rw [ha, hb]
      exact some_lt_some_of_lt hab

lemma mem_lt_mem_of_lt {oa ob : Option α} {a b : α} (ha : a ∈ oa) (hb : b ∈ ob)
  (hab : oa < ob ) : a < b := by
  refine lt_of_some_lt_some ?_
  rw [← ha, ← hb]
  exact hab

lemma mem_lt_mem_iff_lt {oa ob : Option α} {a b : α} (ha : a ∈ oa) (hb : b ∈ ob) :
    oa < ob ↔ a < b := ⟨mem_lt_mem_of_lt ha hb, lt_of_mem_lt_mem ha hb⟩

lemma lt_of_get_lt_get {oa ob : Option α} (ha : oa.isSome) (hb : ob.isSome)
    (hab : get oa ha < get ob hb) : oa < ob :=
  lt_of_mem_lt_mem (get_mem _) (get_mem _) hab

lemma get_lt_get_of_lt {oa ob : Option α} (hab : oa < ob) (ha := isSome_of_lt hab)
    (hb := isSome_of_gt hab) : get oa ha < get ob hb := by
  cases' hab with _ _ hab
  exact hab

lemma get_lt_get_iff_lt {oa ob : Option α} (ha : oa.isSome) (hb : ob.isSome) :
    get oa ha < get ob hb ↔ oa < ob := ⟨lt_of_get_lt_get ha hb, get_lt_get_of_lt⟩

lemma getD_let_getD_of_lt {oa ob : Option α} (hab : oa < ob) (c d : α) :
    getD oa c < getD ob d := by
  cases' hab with _ _ hab
  exact hab

end LT

section LE

instance instLEOption {α : Type*} [LE α] : LE (Option (α)) := ⟨Rel (· ≤ ·)⟩

variable {α β : Type*} [LE α] [LE β]

@[simp]
lemma none_le_none : (none : Option α) ≤ none := Rel.none
@[simp]
lemma not_none_le_some {a : α} : ¬ none ≤ some a := fun ha => by cases ha
@[simp]
lemma not_some_le_none {a : α} : ¬ some a ≤ none := fun ha => by cases ha

lemma some_le_some_of_le {a b : α} (hab : a ≤ b) :
    some a ≤ some b := Rel.some hab
lemma le_of_some_le_some {a b : α} (hab : some a ≤ some b) :
    a ≤ b := by cases hab; assumption
@[simp]
lemma some_le_some_iff {a b : α} : some a ≤ some b ↔ a ≤ b :=
  ⟨le_of_some_le_some, some_le_some_of_le⟩

lemma isSome_of_le_some {oa : Option α} {b : α} (hab : oa ≤ some b) :
    oa.isSome := by cases hab; rfl
lemma isSome_of_le_mem {oa ob : Option α} (hab : oa ≤ ob) {b : α} (hb : b ∈ ob) :
    oa.isSome := isSome_of_le_some (hb ▸ hab)
lemma isSome_of_le_isSome {oa ob : Option α} (hab : oa ≤ ob) (hb : isSome ob) :
    oa.isSome := isSome_of_le_mem hab (get_mem hb)

lemma isSome_of_ge_some {ob : Option α} {a : α} (hab : some a ≤ ob) :
    ob.isSome := by cases hab; rfl
lemma isSome_of_ge_mem {oa ob : Option α} (hab : oa ≤ ob) {a : α} (hb : a ∈ oa) :
    ob.isSome := isSome_of_ge_some (hb ▸ hab)
lemma isSome_of_ge_isSome {oa ob : Option α} (hab : oa ≤ ob) (ha : isSome oa) :
    ob.isSome := isSome_of_ge_mem hab (get_mem ha)

lemma isSome_and_isSome_of_le_or_ge_isSome {oa ob : Option α} (hab₁ : oa ≤ ob)
    (hab₂ : oa.isSome ∨ ob.isSome) : oa.isSome ∧ ob.isSome :=
  hab₂.by_cases (fun ha => ⟨ha, isSome_of_ge_isSome hab₁ ha⟩)
  fun hb => ⟨isSome_of_le_isSome hab₁ hb, hb⟩

lemma get_le_get_of_le {oa : Option α} (ha : oa.isSome) {ob : Option α}
    (hb : ob.isSome) (hab : oa ≤ ob) : get oa ha ≤ get ob hb := by
  cases' hab with _ _ hab
  · exact hab
  · exact Bool.noConfusion ha

lemma le_of_mem_le_mem {oa ob : Option α} {a b : α} (ha : a ∈ oa) (hb : b ∈ ob)
(hab : a ≤ b) : oa ≤ ob := by
  cases oa
  · cases ha
  · cases ob
    · cases hb
    · rw [ha, hb]
      exact some_le_some_of_le hab

lemma mem_le_mem_of_le {oa ob : Option α} {a b : α} (ha : a ∈ oa) (hb : b ∈ ob)
(hab : oa ≤ ob) : a ≤ b := by
  refine le_of_some_le_some ?_
  rw [← ha, ← hb]
  exact hab

lemma mem_le_mem_iff_lt {oa ob : Option α} {a b : α} (ha : a ∈ oa) (hb : b ∈ ob) :
    oa ≤ ob ↔ a ≤ b := ⟨mem_le_mem_of_le ha hb, le_of_mem_le_mem ha hb⟩

lemma le_of_get_le_get {oa ob : Option α} (ha : oa.isSome) (hb : ob.isSome)
    (hab : get oa ha ≤ get ob hb) : oa ≤ ob :=
  le_of_mem_le_mem (get_mem _) (get_mem _) hab

lemma get_le_get_iff_le {oa : Option α} (ha : oa.isSome) {ob : Option α} (hb : ob.isSome) :
    get oa ha ≤ get ob hb ↔ oa ≤ ob :=
  ⟨le_of_get_le_get ha hb,  get_le_get_of_le ha hb⟩

lemma getD_le_getD_of_le {oa ob : Option α} (hab : oa ≤ ob) {c d : α} (hcd : c ≤ d):
    getD oa c ≤ getD ob d := by
  cases' hab with _ _ hab
  · exact hab
  · exact hcd

/-- The set of `x : Option α` such that `isSome x` is order-equivalent to `α`. -/
@[simps]
def optionIsSomeOrderIso (α : Type*) [LE α] : { x : Option α // x.isSome } ≃o α where
  toFun o := Option.get _ o.2
  invFun x := ⟨some x, rfl⟩
  left_inv _ := Subtype.eq <| Option.some_get _
  right_inv _ := Option.get_some _ _
  map_rel_iff' := get_le_get_iff_le _ _

lemma map_le_map_of_le {f : α → β} (hf : ∀ {a b}, a ≤ b → f a ≤ f b) {oa ob : Option α}
    (hab : oa ≤ ob) : Option.map f oa ≤ Option.map f ob := by
  cases' hab with _ _ hab
  · exact some_le_some_of_le (hf hab)
  · exact none_le_none

lemma le_of_map_le_map {f : α → β} (hf : ∀ {a b}, f a ≤ f b → a ≤ b) {oa ob : Option α}
    (hab : Option.map f oa ≤ Option.map f ob) : oa ≤ ob := by
  cases' oa with a
  · cases ob
    · exact none_le_none
    · cases hab
  · cases ob
    · cases hab
    · exact (some_le_some_of_le (hf (le_of_some_le_some hab)))

lemma map_le_map_iff_le {f : α → β} (hf : ∀ {a b}, f a ≤ f b ↔ a ≤ b) {oa ob : Option α} :
    Option.map f oa ≤ Option.map f ob ↔ oa ≤ ob :=
  ⟨le_of_map_le_map hf.mp, map_le_map_of_le hf.mpr⟩

/-- TODO -/
def _root_.OrderEmbedding.optionCongr (f : α ↪o β) : Option α ↪o Option β where
  toFun := Option.map f
  inj' := map_injective f.injective
  map_rel_iff' := map_le_map_iff_le f.map_rel_iff

/-- TODO -/
def _root_.OrderIso.optionCongr (e : α ≃o β) : Option α ≃o Option β where
  toEquiv := e.toEquiv.optionCongr
  map_rel_iff' := map_le_map_iff_le e.map_rel_iff

end LE

section Preorder

instance {α : Type*} [Preorder α] : Preorder (Option α) where
  le_refl a := a.casesOn Rel.none (fun _ => Rel.some (le_refl _))
  le_trans a b c hab hbc := by
    cases' hab with _ _ hab
    · cases' hbc with _ _ hbc
      exact Rel.some (hab.trans hbc)
    · cases hbc
      exact Rel.none
  lt_iff_le_not_le a b := Iff.intro (fun hab => by
    cases' hab with _ _ hab
    simp_rw [some_le_some_iff]
    exact le_not_le_of_lt hab)
    (fun ⟨hab, hba⟩ => by
      cases' hab with _ _ hab
      · simp_rw [some_le_some_iff] at hba
        exact some_lt_some_of_lt (lt_iff_le_not_le.mpr ⟨hab, hba⟩)
      · exact (hba none_le_none).elim)

variable {α β : Type*} [Preorder α] [Preorder β]

theorem monotone_iff {f : Option α → β} :
    Monotone f ↔ Monotone (fun a => f a : α → β) :=
  ⟨fun h => fun a b hab => h (some_le_some_of_le hab),
  fun h a b hab => by cases' hab with _ _ hab; exacts [h hab, le_refl _]⟩

lemma monotone_map_iff {f : α → β} : Monotone (Option.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp_rw [Monotone, map_some', some_le_some_iff]

theorem antitone_iff {f : Option α → β} :
    Antitone f ↔ Antitone (fun a => f a : α → β) :=
  ⟨fun h => fun a b hab => h (some_le_some_of_le hab),
  fun h a b hab => by cases' hab with _ _ hab; exacts [h hab, le_refl _]⟩

lemma antitone_map_iff {f : α → β} : Antitone (Option.map f) ↔ Antitone f :=
  antitone_iff.trans <| by simp_rw [Antitone, map_some', some_le_some_iff]

theorem strictMono_iff {f : Option α → β} :
    StrictMono f ↔ StrictMono (fun a => f a : α → β) :=
  ⟨fun h => fun a b hab => h (some_lt_some_of_lt hab),
  fun h a b hab => by cases' hab with _ _ hab; exact h hab⟩

lemma strictMono_map_iff {f : α → β} : StrictMono (Option.map f) ↔ StrictMono f :=
  strictMono_iff.trans <| by simp_rw [StrictMono, map_some', some_lt_some_iff]

theorem strictAnti_iff {f : Option α → β} :
    StrictAnti f ↔ StrictAnti (fun a => f a : α → β) :=
  ⟨fun h => fun a b hab => h (some_lt_some_of_lt hab),
  fun h a b hab => by cases' hab with _ _ hab; exact h hab⟩

lemma strictAnti_map_iff {f : α → β} : StrictAnti (Option.map f) ↔ StrictAnti f :=
  strictAnti_iff.trans <| by simp_rw [StrictAnti, map_some', some_lt_some_iff]

/-- TODO -/
def mapOrderHom (f : α →o β) : Option α →o Option β where
  toFun := Option.map f
  monotone' := monotone_map_iff.mpr (f.monotone)

/-- TODO -/
def someOrderEmbedding (α : Type*) [Preorder α] : OrderEmbedding α (Option α) :=
RelEmbedding.trans (optionIsSomeOrderIso α).symm.toOrderEmbedding (OrderEmbedding.subtype _)

lemma someOrderEmbedding_apply  (a : α) : (someOrderEmbedding α) a = some a := rfl

lemma monotone_some : Monotone (some : α → (Option α)) :=
  (someOrderEmbedding α).monotone

lemma strictMono_some : StrictMono (some : α → (Option α)) :=
  (someOrderEmbedding α).strictMono

end Preorder

section PartialOrder

instance {α : Type*} [PartialOrder α] : PartialOrder (Option α) where
  le_antisymm a b hab hba := by
    cases' hab with _ _ hab
    · exact (some.injEq _ _).symm ▸ (le_antisymm hab (le_of_some_le_some hba))
    · exact rfl

end PartialOrder

end Option
