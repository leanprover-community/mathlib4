/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Multiset.Nodup

#align_import data.multiset.pi from "leanprover-community/mathlib"@"b2c89893177f66a48daf993b7ba5ef7cddeff8c9"

/-!
# The cartesian product of multisets
-/


namespace Multiset

section Pi

open Function

namespace Pi
variable {ι : Type _} [DecidableEq ι] {α : ι → Sort _}

/-- Given `β : α → Type _`, `Pi.empty β` is the trivial dependent function out of the empty
multiset. -/
def empty {ι : Type _} (α : ι → Sort _) : ∀ a ∈ (0 : Multiset ι), α a :=
  fun.
#align multiset.pi.empty Multiset.Pi.empty

variable {i : ι} {m : Multiset ι}

/-- Given `α : ι → Sort _`, a multiset `m` and a term `i`, as well as a term `a : α i` and a
function `f` such that `f j : α j` for all `j` in `m`, `Pi.cons a f` is a function `g` such
that `g k : α k` for all `k` in `i ::ₘ m`. -/
def cons (a : α i) (f : ∀ j ∈ m, α j) : ∀ j ∈ (i ::ₘ m), α j :=
  fun j hj ↦ if h : j = i then h.symm.rec a else f j <| (mem_cons.1 hj).resolve_left h
#align multiset.pi.cons Multiset.Pi.cons

lemma cons_same {a : α i} {f : ∀ j ∈ m, α j} (h : i ∈ i ::ₘ m) :
    Pi.cons a f i h = a :=
  dif_pos rfl
#align multiset.pi.cons_same Multiset.Pi.cons_same

lemma cons_ne {a : α i} {f : ∀ j ∈ m, α j} {j : ι} (hj : j ∈ i ::ₘ m) (h : j ≠ i) :
    cons a f j hj = f j ((mem_cons.1 hj).resolve_left h) :=
  dif_neg h
#align multiset.pi.cons_ne Multiset.Pi.cons_ne

lemma cons_swap {i i' : ι} {a : α i} {a' : α i'} {f : ∀ j ∈ m, α j} (h : i ≠ i') :
    HEq (cons a (cons a' f)) (cons a' (cons a f)) := by
  apply hfunext rfl
  simp only [heq_iff_eq]
  rintro j _ rfl
  refine' hfunext (by rw [Multiset.cons_swap]) (fun ha₁ ha₂ _ ↦ _)
  rcases ne_or_eq j i with h₁ | rfl
  rcases eq_or_ne j i' with rfl | h₂
  all_goals { simp [*, Pi.cons_same, Pi.cons_ne] }
#align multiset.pi.cons_swap Multiset.Pi.cons_swap

@[simp, nolint simpNF] --Porting note: false positive, this lemma can prove itself
lemma cons_eta (f : ∀ j ∈ (i ::ₘ m), α j) :
    cons (f i (mem_cons_self _ _)) (fun j hj ↦ f j (mem_cons_of_mem hj)) = f := by
  ext j hj
  dsimp [cons]
  split_ifs with H
  · cases H
    rfl
  · rfl
#align multiset.pi.cons_eta Multiset.Pi.cons_eta

lemma cons_map (a : α i) (f : ∀ j ∈ m, α j)
    {α' : ι → Sort _} (φ : ∀ ⦃j⦄, α j → α' j) :
    cons (φ a) (fun j hj ↦ φ (f j hj)) = (fun j hj ↦ φ ((cons a f) j hj)) := by
  ext j hj
  refine' (congrArg₂ _ _ rfl).trans (apply_dite (@φ _) (j = i) _ _).symm
  ext rfl
  rfl

lemma forall_rel_cons_ext {r : ∀ ⦃i⦄, α i → α i → Prop} {a₁ a₂ : α i} {f₁ f₂ : ∀ j ∈ m, α j}
    (ha : r a₁ a₂) (hf : ∀ (i : ι) (hi : i ∈ m), r (f₁ i hi) (f₂ i hi)) :
    ∀ j hj, r (cons a₁ f₁ j hj) (cons a₂ f₂ j hj) := by
  intros j hj
  dsimp [cons]
  split_ifs with H
  · cases H
    exact ha
  · exact hf _ _

lemma cons_injective {i : ι} {a : α i} {s : Multiset ι} (hs : i ∉ s) :
    Injective (@Pi.cons _ _ _ _ s a) := fun f₁ f₂ eq ↦
  funext fun j ↦
    funext fun h' ↦
      have ne : i ≠ j := fun h ↦ hs <| h.symm ▸ h'
      have : j ∈ i ::ₘ s := mem_cons_of_mem h'
      calc
        f₁ j h' = Pi.cons a f₁ j this := by rw [Pi.cons_ne this ne.symm]
              _ = Pi.cons a f₂ j this := by rw [eq]
              _ = f₂ j h' := by rw [Pi.cons_ne this ne.symm]
#align multiset.pi.cons_injective Multiset.Pi.cons_injective

end Pi

section
variable {α : Type _} [DecidableEq α] {β : α → Type _}

/-- `pi m t` constructs the Cartesian product over `t` indexed by `m`. -/
def pi (m : Multiset α) (t : ∀ a, Multiset (β a)) : Multiset (∀ a ∈ m, β a) :=
  m.recOn {Pi.empty β}
    (fun a m (p : Multiset (∀ a ∈ m, β a)) => (t a).bind fun b => p.map <| Pi.cons b)
    (by
      intro a a' m n
      by_cases eq : a = a'
      · subst eq; rfl
      · simp [map_bind, bind_bind (t a') (t a)]
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
#align multiset.pi Multiset.pi

@[simp]
theorem pi_zero (t : ∀ a, Multiset (β a)) : pi 0 t = {Pi.empty β} :=
  rfl
#align multiset.pi_zero Multiset.pi_zero

@[simp]
theorem pi_cons (m : Multiset α) (t : ∀ a, Multiset (β a)) (a : α) :
    pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map <| Pi.cons b :=
  recOn_cons a m
#align multiset.pi_cons Multiset.pi_cons

theorem card_pi (m : Multiset α) (t : ∀ a, Multiset (β a)) :
    card (pi m t) = prod (m.map fun a => card (t a)) :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }) [mul_comm])
#align multiset.card_pi Multiset.card_pi

protected theorem Nodup.pi {s : Multiset α} {t : ∀ a, Multiset (β a)} :
    Nodup s → (∀ a ∈ s, Nodup (t a)) → Nodup (pi s t) :=
  Multiset.induction_on s (fun _ _ => nodup_singleton _)
    (by
      intro a s ih hs ht
      have has : a ∉ s := by simp at hs; exact hs.1
      have hs : Nodup s := by simp at hs; exact hs.2
      simp
      refine'
        ⟨fun b _ => ((ih hs) fun a' h' => ht a' <| mem_cons_of_mem h').map (Pi.cons_injective has),
          _⟩
      refine' (ht a <| mem_cons_self _ _).pairwise _
      exact fun b₁ _ b₂ _ neb =>
        disjoint_map_map.2 fun f _ g _ eq =>
          have : Pi.cons b₁ f a (mem_cons_self _ _) = Pi.cons b₂ g a (mem_cons_self _ _) :=
            by rw [eq]
          neb <| show b₁ = b₂ by rwa [Pi.cons_same, Pi.cons_same] at this)
#align multiset.nodup.pi Multiset.Nodup.pi

theorem mem_pi {m : Multiset α} (t : ∀ a, Multiset (β a)) :
    ∀ f : ∀ a ∈ m, β a, f ∈ pi m t ↔ ∀ (a) (h : a ∈ m), f a h ∈ t a := by
  intro f
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
    refine' ⟨_, hf a (mem_cons_self _ _), _, fun a ha => hf a (mem_cons_of_mem ha), _⟩
    rw [Pi.cons_eta]
#align multiset.mem_pi Multiset.mem_pi

end

end Pi

end Multiset
