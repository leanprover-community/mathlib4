import Mathlib.Order.Basic
import Mathlib.Order.Hom.Basic
/-! TODO TBD -/

variable {α : Type*}

namespace Option

/-- TODO TBD Delete once std4 patch merges -/
inductive StrictRel {α : Type*} {β : Type*} (r : α → β → Prop) : Option α → Option β → Prop
  /-- If `a ~ b`, then `some a ~ some b` -/
  | some {a b} : r a b → StrictRel r (some a) (some b)

instance instLTOption' [LT α] : LT (Option (α)) := ⟨StrictRel (· < ·)⟩
instance instLEOption [LE α] : LE (Option (α)) := ⟨Rel (· ≤ ·)⟩

@[simp]
lemma none_le_none {α : Type*} [LE α] : (none : Option α) ≤ none := Rel.none
@[simp]
lemma not_none_le_some {α : Type*} [LE α] {a : α} : ¬ none ≤ some a := fun ha => by cases ha
@[simp]
lemma not_some_le_none {α : Type*} [LE α] {a : α} : ¬ some a ≤ none := fun ha => by cases ha

lemma some_le_some_of_le {α : Type*} [LE α] {a b : α} (hab : a ≤ b) :
    some a ≤ some b := Rel.some hab
lemma le_of_some_le_some {α : Type*} [LE α] {a b : α} (hab : some a ≤ some b) :
    a ≤ b := by cases hab; assumption
@[simp]
lemma some_le_some_iff {α : Type*} [LE α] {a b : α} : some a ≤ some b ↔ a ≤ b :=
  ⟨le_of_some_le_some, some_le_some_of_le⟩

@[simp]
lemma not_none_lt_none {α : Type*} [LT α] : ¬ (none : Option α) < none := fun ha => by cases ha
@[simp]
lemma not_none_lt_some {α : Type*} [LT α] {a : α} :
    ¬ (none : Option α) < some a := fun ha => by cases ha
@[simp]
lemma not_some_lt_none {α : Type*} [LT α] {a : α} :
    ¬ some a < (none : Option α) := fun ha => by cases ha
lemma some_lt_some_of_lt {α : Type*} [LT α] {a b : α} (hab : a < b) :
    some a < some b := StrictRel.some hab
lemma lt_of_some_lt_some {α : Type*} [LT α] {a b : α} (hab : some a < some b) :
    a < b := by cases hab; assumption
@[simp]
lemma some_lt_some_iff {α : Type*} [LT α] {a b : α} : some a < some b ↔ a < b :=
  ⟨lt_of_some_lt_some, some_lt_some_of_lt⟩

lemma lt_of_eq_some_lt_eq_some [LT α] {oa ob : Option α} {a b : α} (ha : oa = some a)
    (hb : ob = some b) (hab : a < b) : oa < ob := by
  rw [ha, hb]
  exact some_lt_some_of_lt hab

lemma lt_of_mem_lt_mem [LT α] {oa ob : Option α} {a b : α} (ha : a ∈ oa) (hb : b ∈ ob)
  (hab : a < b) : oa < ob := lt_of_eq_some_lt_eq_some ha hb hab

lemma lt_of_get_lt_get [LT α] {oa ob : Option α} (ha : oa.isSome) (hb : ob.isSome)
    (hab : get oa ha < get ob hb) : oa < ob := lt_of_mem_lt_mem (get_mem _) (get_mem _) hab

lemma isSome_of_lt [LT α] {oa ob : Option α} (hab : oa < ob) : oa.isSome := by cases hab; rfl
lemma isSome_of_gt [LT α] {oa ob : Option α} (hab : oa < ob) : ob.isSome := by cases hab; rfl

lemma get_lt_get_of_lt [LT α] {oa ob : Option α} (hab : oa < ob) (ha := isSome_of_lt hab)
    (hb := isSome_of_gt hab) : get oa ha < get ob hb := by
  rcases isSome_iff_exists.mp ha with ⟨a, rfl⟩
  rcases isSome_iff_exists.mp hb with ⟨b, rfl⟩
  exact lt_of_some_lt_some hab

lemma getD_let_getD_of_lt [LT α] {oa ob : Option α} (hab : oa < ob) (c d : α) :
    getD oa c < getD ob d := by
  rcases isSome_iff_exists.mp (isSome_of_lt hab) with ⟨a, rfl⟩
  rcases isSome_iff_exists.mp (isSome_of_gt hab) with ⟨b, rfl⟩
  exact lt_of_some_lt_some hab


lemma le_of_mem_le_mem [LE α] {oa ob : Option α} {a b : α} (ha : a ∈ oa) (hb : b ∈ ob)
(hab : a ≤ b) : oa ≤ ob := by
  rw [mem_iff] at ha hb
  rw [ha, hb]
  exact some_le_some_of_le hab

lemma le_of_get_le_get [LE α] {oa ob : Option α} (ha : oa.isSome) (hb : ob.isSome)
    (hab : get oa ha ≤ get ob hb) : oa ≤ ob :=
  le_of_mem_le_mem (get_mem _) (get_mem _) hab

lemma isSome_of_le_some [LE α] {oa : Option α} {b : α} (hab : oa ≤ some b) :
  oa.isSome := by cases hab; rfl
lemma isSome_of_le_eq_some [LE α] {oa ob : Option α} (hab : oa ≤ ob) {b : α} (hb : ob = some b) :
    oa.isSome := by
  rw [hb] at hab
  cases hab
  rfl
lemma isSome_of_le_isSome [LE α] {oa ob : Option α} (hab : oa ≤ ob) (hb : isSome ob) :
    oa.isSome := by
  rcases isSome_iff_exists.mp hb with ⟨b, rfl⟩
  exact isSome_of_le_some hab
lemma isSome_of_le_mem [LE α] {oa ob : Option α} (hab : oa ≤ ob) {b : α} (hb : b ∈ ob) :
    oa.isSome := isSome_of_le_eq_some hab hb

lemma isSome_of_ge_some [LE α] {ob : Option α} {a : α} (hab : some a ≤ ob) :
    ob.isSome := by cases hab; rfl
lemma isSome_of_ge_eq_some [LE α] {oa ob : Option α} (hab : oa ≤ ob) {a : α} (ha : oa = some a) :
    ob.isSome := by
  rw [ha] at hab
  cases hab
  rfl
lemma isSome_of_ge_isSome [LE α] {oa ob : Option α} (hab : oa ≤ ob) (ha : isSome oa) :
    ob.isSome := by
  rcases isSome_iff_exists.mp ha with ⟨a, rfl⟩
  exact isSome_of_ge_some hab
lemma isSome_of_ge_mem [LE α] {oa ob : Option α} (hab : oa ≤ ob) {a : α} (ha : a ∈ oa) :
    ob.isSome := isSome_of_ge_eq_some hab ha

lemma isSome_and_isSome_of_le_or_ge_isSome [LE α] {oa ob : Option α} (hab₁ : oa ≤ ob)
    (hab₂ : oa.isSome ∨ ob.isSome) : oa.isSome ∧ ob.isSome :=
  hab₂.by_cases (fun ha => ⟨ha, isSome_of_ge_isSome hab₁ ha⟩)
  fun hb => ⟨isSome_of_le_isSome hab₁ hb, hb⟩

lemma get_le_get_of_le_isSome [LE α] {oa ob : Option α} (hab : oa ≤ ob)
  (ha : oa.isSome) (hb := isSome_of_ge_isSome hab ha) : get oa ha ≤ get ob hb := by
  rcases isSome_iff_exists.mp ha with ⟨a, rfl⟩
  rcases isSome_iff_exists.mp hb with ⟨b, rfl⟩
  exact le_of_some_le_some hab

lemma get_le_get_of_ge_isSome [LE α] {oa ob : Option α} (hab : oa ≤ ob)
  (hb : ob.isSome) (ha := isSome_of_le_isSome hab hb) : get oa ha ≤ get ob hb := by
  rcases isSome_iff_exists.mp ha with ⟨a, rfl⟩
  rcases isSome_iff_exists.mp hb with ⟨b, rfl⟩
  exact le_of_some_le_some hab

lemma get_le_get_of_le_or_ge_isSome [LE α] {oa ob : Option α} (hab₁ : oa ≤ ob)
    (hab₂ : oa.isSome ∨ ob.isSome) (ha := (isSome_and_isSome_of_le_or_ge_isSome hab₁ hab₂).1)
    (hb := (isSome_and_isSome_of_le_or_ge_isSome hab₁ hab₂).2) : get oa ha ≤ get ob hb := by
  rcases isSome_iff_exists.mp ha with ⟨a, rfl⟩
  rcases isSome_iff_exists.mp hb with ⟨b, rfl⟩
  exact le_of_some_le_some hab₁

lemma getD_le_getD_of_le [LE α] {oa ob : Option α} (hab : oa ≤ ob) {c d : α} (hcd : c ≤ d):
    getD oa c ≤ getD ob d := by
  cases' hab with _ _ hab
  · exact hab
  · exact hcd

def someOrderEmbedding (α : Type*) [LE α] : OrderEmbedding α (Option α) where
  toFun := some
  inj' := some_injective _
  map_rel_iff' := some_le_some_iff

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

lemma monotone_some (α : Type*) [Preorder α] : Monotone (some : α → (Option α)) :=
  (someOrderEmbedding α).monotone

lemma strictMono_some (α : Type*) [Preorder α] : StrictMono (some : α → (Option α)) :=
  (someOrderEmbedding α).strictMono



instance {α : Type*} [PartialOrder α] : PartialOrder (Option α) where
  le_antisymm a b hab hba := by
    cases' hab with _ _ hab
    · exact (some.injEq _ _).symm ▸ (le_antisymm hab (le_of_some_le_some hba))
    · exact rfl

end Option
