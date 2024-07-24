/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Multiset.Bind

/-!
# The cartesian product of multisets
-/


namespace Multiset

section Pi

open Function

namespace Pi
variable {ι : Type*} [DecidableEq ι] {α : ι → Sort*}

/-- Given `α : ι → Type*`, `Pi.empty α` is the trivial dependent function out of the empty
multiset. -/
def empty {ι : Type*} (α : ι → Sort*) : ∀ a ∈ (0 : Multiset ι), α a :=
  nofun

variable (m : Multiset ι) (i : ι)

/-- Given `α : ι → Sort*`, a multiset `m` and a term `i`, as well as a term `a : α i` and a
function `f` such that `f j : α j` for all `j` in `m`, `Pi.cons a f` is a function `g` such
that `g k : α k` for all `k` in `i ::ₘ m`. -/
def cons (a : α i) (f : ∀ j ∈ m, α j) : ∀ j ∈ (i ::ₘ m), α j :=
  fun j hj ↦ if h : j = i then h.symm.ndrec a else f j <| (mem_cons.1 hj).resolve_left h

variable {m i}

lemma cons_same {a : α i} {f : ∀ j ∈ m, α j} (h : i ∈ i ::ₘ m) :
    Pi.cons m i a f i h = a :=
  dif_pos rfl

lemma cons_ne {a : α i} {f : ∀ j ∈ m, α j} {j : ι} (hj : j ∈ i ::ₘ m) (h : j ≠ i) :
    cons m i a f j hj = f j ((mem_cons.1 hj).resolve_left h) :=
  dif_neg h

lemma cons_swap {i i' : ι} {a : α i} {a' : α i'} {f : ∀ j ∈ m, α j} (h : i ≠ i') :
    HEq (cons _ _ a (cons _ _ a' f)) (cons _ _ a' (cons _ _ a f)) := by
  apply hfunext rfl
  simp only [heq_iff_eq]
  rintro j _ rfl
  refine' hfunext (by rw [Multiset.cons_swap]) fun ha₁ ha₂ _ ↦ ?_
  rcases ne_or_eq j i with h₁ | rfl
  on_goal 1 => rcases eq_or_ne a'' a' with (rfl | h₂)
  all_goals simp [*, Pi.cons_same, Pi.cons_ne]

@[simp, nolint simpNF] -- Porting note: false positive, this lemma can prove itself
lemma cons_eta (f : ∀ j ∈ i ::ₘ m, α j) :
    cons _ _ (f i (mem_cons_self _ _)) (fun j hj ↦ f j (mem_cons_of_mem hj)) = f := by
  ext j hj
  dsimp [cons]
  split_ifs with H
  · cases H
    rfl
  · rfl

lemma cons_map (a : α i) (f : ∀ j ∈ m, α j)
    {α' : ι → Sort*} (φ : ∀ ⦃j⦄, α j → α' j) :
    cons _ _ (φ a) (fun j hj ↦ φ (f j hj)) = (fun j hj ↦ φ ((cons _ _ a f) j hj)) := by
  ext j hj
  refine' (congrArg₂ _ _ rfl).trans (apply_dite (@φ _) (j = i) _ _).symm
  ext rfl
  rfl

lemma forall_rel_cons_ext {r : ∀ ⦃i⦄, α i → α i → Prop} {a₁ a₂ : α i} {f₁ f₂ : ∀ j ∈ m, α j}
    (ha : r a₁ a₂) (hf : ∀ (i : ι) (hi : i ∈ m), r (f₁ i hi) (f₂ i hi)) :
    ∀ j hj, r (cons _ _ a₁ f₁ j hj) (cons _ _ a₂ f₂ j hj) := by
  intros j hj
  dsimp [cons]
  split_ifs with H
  · cases H
    exact ha
  · exact hf _ _

lemma cons_injective {i : ι} {a : α i} {s : Multiset ι} (hs : i ∉ s) :
    Injective (@Pi.cons _ _ _ s _ a) := fun f₁ f₂ eq ↦
  funext fun j ↦
    funext fun h' ↦
      have ne : i ≠ j := fun h ↦ hs <| h.symm ▸ h'
      have : j ∈ i ::ₘ s := mem_cons_of_mem h'
      calc
        f₁ j h' = Pi.cons _ _ a f₁ j this := by rw [Pi.cons_ne this ne.symm]
              _ = Pi.cons _ _ a f₂ j this := by rw [eq]
              _ = f₂ j h' := by rw [Pi.cons_ne this ne.symm]

end Pi

section
variable {α : Type*} [DecidableEq α] {β : α → Type*}

/-- `pi m t` constructs the Cartesian product over `t` indexed by `m`. -/
def pi (m : Multiset α) (t : ∀ a, Multiset (β a)) : Multiset (∀ a ∈ m, β a) :=
  m.recOn {Pi.empty β}
    (fun a m (p : Multiset (∀ a ∈ m, β a)) => (t a).bind fun b => p.map <| Pi.cons _ _ b)
    (by
      intro a a' m n
      by_cases eq : a = a'
      · subst eq; rfl
      · simp only [map_bind, map_map, comp_apply, bind_bind (t a') (t a)]
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b _
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b' _
        apply map_hcongr
        · rw [cons_swap a a']
        intro f _
        exact Pi.cons_swap eq)

@[simp]
theorem pi_zero (t : ∀ a, Multiset (β a)) : pi 0 t = {Pi.empty β} :=
  rfl

@[simp]
theorem pi_cons (m : Multiset α) (t : ∀ a, Multiset (β a)) (a : α) :
    pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map <| Pi.cons _ _ b :=
  recOn_cons a m

theorem card_pi (m : Multiset α) (t : ∀ a, Multiset (β a)) :
    card (pi m t) = prod (m.map fun a => card (t a)) :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }) [mul_comm])

protected theorem Nodup.pi {s : Multiset α} {t : ∀ a, Multiset (β a)} :
    Nodup s → (∀ a ∈ s, Nodup (t a)) → Nodup (pi s t) :=
  Multiset.induction_on s (fun _ _ => nodup_singleton _)
    (by
      intro a s ih hs ht
      have has : a ∉ s := by simp only [nodup_cons] at hs; exact hs.1
      have hs : Nodup s := by simp only [nodup_cons] at hs; exact hs.2
      simp only [pi_cons, nodup_bind]
      refine
        ⟨fun b _ => ((ih hs) fun a' h' => ht a' <| mem_cons_of_mem h').map (Pi.cons_injective has),
          ?_⟩
      refine (ht a <| mem_cons_self _ _).pairwise ?_
      exact fun b₁ _ b₂ _ neb =>
        disjoint_map_map.2 fun f _ g _ eq =>
          have : Pi.cons _ _ b₁ f a (mem_cons_self _ _) = Pi.cons _ _ b₂ g a (mem_cons_self _ _) :=
            by rw [eq]
          neb <| show b₁ = b₂ by rwa [Pi.cons_same, Pi.cons_same] at this)

theorem mem_pi {m : Multiset α} {t : ∀ a, Multiset (β a)} {f : ∀ a ∈ m, β a} :
    f ∈ pi m t ↔ ∀ (a) (h : a ∈ m), f a h ∈ t a := by
  induction' m using Multiset.induction_on with a m ih
  · have : f = Pi.empty β := funext (fun _ => funext fun h => (not_mem_zero _ h).elim)
    simp only [this, pi_zero, mem_singleton, true_iff]
    intro _ h; exact (not_mem_zero _ h).elim
  simp_rw [pi_cons, mem_bind, mem_map, ih]
  constructor
  · rintro ⟨b, hb, f', hf', rfl⟩ a' ha'
    by_cases h : a' = a
    · subst h
      rwa [Pi.cons_same]
    · rw [Pi.cons_ne _ h]
      apply hf'
  · intro hf
    refine ⟨_, hf a (mem_cons_self _ _), _, fun a ha => hf a (mem_cons_of_mem ha), ?_⟩
    rw [Pi.cons_eta]

end

end Pi

end Multiset
