/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Multiset.Pi
import Mathlib.Logic.Function.DependsOn

/-!
# The Cartesian product of finsets

## Main definitions

* `Finset.pi`: Cartesian product of finsets indexed by a finset.
-/

open Function

namespace Finset

open Multiset

/-! ### pi -/


section Pi

variable {α : Type*}

/-- The empty dependent product function, defined on the empty set. The assumption `a ∈ ∅` is never
satisfied. -/
def Pi.empty (β : α → Sort*) (a : α) (h : a ∈ (∅ : Finset α)) : β a :=
  Multiset.Pi.empty β a h

universe u v
variable {β : α → Type u} {δ : α → Sort v} {s : Finset α} {t : ∀ a, Finset (β a)}

section
variable [DecidableEq α]

/-- Given a finset `s` of `α` and for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `s.pi t` of all functions defined on elements of `s` taking values in `t a` for `a ∈ s`.
Note that the elements of `s.pi t` are only partially defined, on `s`. -/
def pi (s : Finset α) (t : ∀ a, Finset (β a)) : Finset (∀ a ∈ s, β a) :=
  ⟨s.1.pi fun a => (t a).1, s.nodup.pi fun a _ => (t a).nodup⟩

@[simp]
theorem pi_val (s : Finset α) (t : ∀ a, Finset (β a)) : (s.pi t).1 = s.1.pi fun a => (t a).1 :=
  rfl

@[simp]
theorem mem_pi {s : Finset α} {t : ∀ a, Finset (β a)} {f : ∀ a ∈ s, β a} :
    f ∈ s.pi t ↔ ∀ (a) (h : a ∈ s), f a h ∈ t a :=
  Multiset.mem_pi _ _ _

/-- Given a function `f` defined on a finset `s`, define a new function on the finset `s ∪ {a}`,
equal to `f` on `s` and sending `a` to a given value `b`. This function is denoted
`s.Pi.cons a b f`. If `a` already belongs to `s`, the new function takes the value `b` at `a`
anyway. -/
def Pi.cons (s : Finset α) (a : α) (b : δ a) (f : ∀ a, a ∈ s → δ a) (a' : α) (h : a' ∈ insert a s) :
    δ a' :=
  Multiset.Pi.cons s.1 a b f _ (Multiset.mem_cons.2 <| mem_insert.symm.2 h)

@[simp]
theorem Pi.cons_same (s : Finset α) (a : α) (b : δ a) (f : ∀ a, a ∈ s → δ a) (h : a ∈ insert a s) :
    Pi.cons s a b f a h = b :=
  Multiset.Pi.cons_same _

theorem Pi.cons_ne {s : Finset α} {a a' : α} {b : δ a} {f : ∀ a, a ∈ s → δ a} {h : a' ∈ insert a s}
    (ha : a ≠ a') : Pi.cons s a b f a' h = f a' ((mem_insert.1 h).resolve_left ha.symm) :=
  Multiset.Pi.cons_ne _ (Ne.symm ha)

theorem Pi.cons_injective {a : α} {b : δ a} {s : Finset α} (hs : a ∉ s) :
    Function.Injective (Pi.cons s a b) := fun e₁ e₂ eq =>
  @Multiset.Pi.cons_injective α _ δ a b s.1 hs _ _ <|
    funext fun e =>
      funext fun h =>
        have :
          Pi.cons s a b e₁ e (by simpa only [Multiset.mem_cons, mem_insert] using h) =
            Pi.cons s a b e₂ e (by simpa only [Multiset.mem_cons, mem_insert] using h) := by
          rw [eq]
        this

@[simp]
theorem pi_empty {t : ∀ a : α, Finset (β a)} : pi (∅ : Finset α) t = singleton (Pi.empty β) :=
  rfl

@[simp]
lemma pi_nonempty : (s.pi t).Nonempty ↔ ∀ a ∈ s, (t a).Nonempty := by
  simp [Finset.Nonempty, Classical.skolem]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, pi_nonempty_of_forall_nonempty⟩ := pi_nonempty

@[simp]
lemma pi_eq_empty : s.pi t = ∅ ↔ ∃ a ∈ s, t a = ∅ := by
  simp [← not_nonempty_iff_eq_empty]

@[simp]
theorem pi_insert [∀ a, DecidableEq (β a)] {s : Finset α} {t : ∀ a : α, Finset (β a)} {a : α}
    (ha : a ∉ s) : pi (insert a s) t = (t a).biUnion fun b => (pi s t).image (Pi.cons s a b) := by
  apply eq_of_veq
  rw [← (pi (insert a s) t).2.dedup]
  refine
    (fun s' (h : s' = a ::ₘ s.1) =>
        (?_ :
          dedup (Multiset.pi s' fun a => (t a).1) =
            dedup
              ((t a).1.bind fun b =>
                dedup <|
                  (Multiset.pi s.1 fun a : α => (t a).val).map fun f a' h' =>
                    Multiset.Pi.cons s.1 a b f a' (h ▸ h'))))
      _ (insert_val_of_notMem ha)
  subst s'; rw [pi_cons]
  congr; funext b
  exact ((pi s t).nodup.map <| Multiset.Pi.cons_injective ha).dedup.symm

theorem pi_singletons {β : Type*} (s : Finset α) (f : α → β) :
    (s.pi fun a => ({f a} : Finset β)) = {fun a _ => f a} := by
  rw [eq_singleton_iff_unique_mem]
  constructor
  · simp
  intro a ha
  ext i hi
  rw [mem_pi] at ha
  simpa using ha i hi

theorem pi_const_singleton {β : Type*} (s : Finset α) (i : β) :
    (s.pi fun _ => ({i} : Finset β)) = {fun _ _ => i} :=
  pi_singletons s fun _ => i

theorem pi_subset {s : Finset α} (t₁ t₂ : ∀ a, Finset (β a)) (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) :
    s.pi t₁ ⊆ s.pi t₂ := fun _ hg => mem_pi.2 fun a ha => h a ha (mem_pi.mp hg a ha)

theorem pi_disjoint_of_disjoint {δ : α → Type*} {s : Finset α} (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
    (ha : a ∈ s) (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (s.pi t₁) (s.pi t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a ha) (mem_pi.mp hf₁ a ha) (f₂ a ha) (mem_pi.mp hf₂ a ha) <|
      congr_fun (congr_fun eq₁₂ a) ha

end

/-! ### Diagonal -/

variable {ι : Type*} [DecidableEq (ι → α)] {s : Finset α} {f : ι → α}

/-- The diagonal of a finset `s : Finset α` as a finset of functions `ι → α`, namely the set of
constant functions valued in `s`. -/
def piDiag (s : Finset α) (ι : Type*) [DecidableEq (ι → α)] : Finset (ι → α) := s.image (const ι)

@[simp] lemma mem_piDiag : f ∈ s.piDiag ι ↔ ∃ a ∈ s, const ι a = f := mem_image

@[simp] lemma card_piDiag (s : Finset α) (ι : Type*) [DecidableEq (ι → α)] [Nonempty ι] :
    (s.piDiag ι).card = s.card := by rw [piDiag, card_image_of_injective _ const_injective]

/-! ### Restriction -/

variable {π : ι → Type*}

/-- Restrict domain of a function `f` to a finite set `s`. -/
@[simp]
def restrict (s : Finset ι) (f : (i : ι) → π i) : (i : s) → π i := fun x ↦ f x

theorem restrict_def (s : Finset ι) : s.restrict (π := π) = fun f x ↦ f x := rfl

variable {s t u : Finset ι}

theorem _root_.Set.piCongrLeft_comp_restrict :
    (s.equivToSet.symm.piCongrLeft (fun i : s.toSet ↦ π i)) ∘ s.toSet.restrict = s.restrict := rfl

theorem piCongrLeft_comp_restrict :
    (s.equivToSet.piCongrLeft (fun i : s ↦ π i)) ∘ s.restrict = s.toSet.restrict := rfl

/-- If a function `f` is restricted to a finite set `t`, and `s ⊆ t`,
this is the restriction to `s`. -/
@[simp]
def restrict₂ (hst : s ⊆ t) (f : (i : t) → π i) (i : s) : π i := f ⟨i.1, hst i.2⟩

theorem restrict₂_def (hst : s ⊆ t) : restrict₂ (π := π) hst = fun f x ↦ f ⟨x.1, hst x.2⟩ := rfl

theorem restrict₂_comp_restrict (hst : s ⊆ t) :
    (restrict₂ (π := π) hst) ∘ t.restrict = s.restrict := rfl

theorem restrict₂_comp_restrict₂ (hst : s ⊆ t) (htu : t ⊆ u) :
    (restrict₂ (π := π) hst) ∘ (restrict₂ htu) = restrict₂ (hst.trans htu) := rfl

lemma dependsOn_restrict (s : Finset ι) : DependsOn (s.restrict (π := π)) s :=
  (s : Set ι).dependsOn_restrict

lemma restrict_preimage [DecidablePred (· ∈ s)] (t : (i : s) → Set (π i)) :
    s.restrict ⁻¹' (Set.univ.pi t) =
      Set.pi s (fun i ↦ if h : i ∈ s then t ⟨i, h⟩ else Set.univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, restrict, forall_const, Subtype.forall,
    mem_coe]
  refine ⟨fun h i hi ↦ by simpa [hi] using h i hi, fun h i hi ↦ ?_⟩
  convert h i hi
  rw [dif_pos hi]

lemma restrict₂_preimage [DecidablePred (· ∈ s)] (hst : s ⊆ t) (u : (i : s) → Set (π i)) :
    (restrict₂ hst) ⁻¹' (Set.univ.pi u) =
      (@Set.univ t).pi (fun j ↦ if h : j.1 ∈ s then u ⟨j.1, h⟩ else Set.univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, restrict₂, forall_const, Subtype.forall]
  refine ⟨fun h i hi ↦ ?_, fun h i i_mem ↦ by simpa [i_mem] using h i (hst i_mem)⟩
  split_ifs with i_mem
  · exact h i i_mem
  · exact Set.mem_univ _

end Pi

end Finset
