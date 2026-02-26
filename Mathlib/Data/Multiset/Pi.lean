/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Multiset.Bind

/-!
# The Cartesian product of multisets

## Main definitions

* `Multiset.pi`: Cartesian product of multisets indexed by a multiset.
-/

@[expose] public section


namespace Multiset

section Pi

open Function

namespace Pi
variable {α : Type*} [DecidableEq α] {δ : α → Sort*}

/-- Given `δ : α → Sort*`, `Pi.empty δ` is the trivial dependent function out of the empty
multiset. -/
def empty (δ : α → Sort*) : ∀ a ∈ (0 : Multiset α), δ a :=
  nofun

variable (m : Multiset α) (a : α)

/-- Given `δ : α → Sort*`, a multiset `m` and a term `a`, as well as a term `b : δ a` and a
function `f` such that `f a' : δ a'` for all `a'` in `m`, `Pi.cons m a b f` is a function `g` such
that `g a'' : δ a''` for all `a''` in `a ::ₘ m`. -/
def cons (b : δ a) (f : ∀ a ∈ m, δ a) : ∀ a' ∈ a ::ₘ m, δ a' :=
  fun a' ha' => if h : a' = a then Eq.ndrec b h.symm else f a' <| (mem_cons.1 ha').resolve_left h

variable {m a}

theorem cons_same {b : δ a} {f : ∀ a ∈ m, δ a} (h : a ∈ a ::ₘ m) :
    cons m a b f a h = b :=
  dif_pos rfl

theorem cons_ne {a a' : α} {b : δ a} {f : ∀ a ∈ m, δ a} (h' : a' ∈ a ::ₘ m)
    (h : a' ≠ a) : Pi.cons m a b f a' h' = f a' ((mem_cons.1 h').resolve_left h) :=
  dif_neg h

theorem cons_swap {a a' : α} {b : δ a} {b' : δ a'} {m : Multiset α} {f : ∀ a ∈ m, δ a}
    (h : a ≠ a') : Pi.cons (a' ::ₘ m) a b (Pi.cons m a' b' f) ≍
      Pi.cons (a ::ₘ m) a' b' (Pi.cons m a b f) := by
  apply hfunext rfl
  simp only [heq_iff_eq]
  rintro a'' _ rfl
  refine hfunext (by rw [Multiset.cons_swap]) fun ha₁ ha₂ _ => ?_
  rcases Decidable.ne_or_eq a'' a with (h₁ | rfl)
  on_goal 1 => rcases Decidable.eq_or_ne a'' a' with (rfl | h₂)
  all_goals simp [*, Pi.cons_same, Pi.cons_ne]

@[simp]
theorem cons_eta {m : Multiset α} {a : α} (f : ∀ a' ∈ a ::ₘ m, δ a') :
    (cons m a (f _ (mem_cons_self _ _)) fun a' ha' => f a' (mem_cons_of_mem ha')) = f := by
  ext a' h'
  by_cases h : a' = a
  · subst h
    rw [Pi.cons_same]
  · rw [Pi.cons_ne _ h]

theorem cons_map (b : δ a) (f : ∀ a' ∈ m, δ a')
    {δ' : α → Sort*} (φ : ∀ ⦃a'⦄, δ a' → δ' a') :
    Pi.cons _ _ (φ b) (fun a' ha' ↦ φ (f a' ha')) = (fun a' ha' ↦ φ ((cons _ _ b f) a' ha')) := by
  ext a' ha'
  refine (congrArg₂ _ ?_ rfl).trans (apply_dite (@φ _) (a' = a) _ _).symm
  ext rfl
  rfl

theorem forall_rel_cons_ext {r : ∀ ⦃a⦄, δ a → δ a → Prop} {b₁ b₂ : δ a} {f₁ f₂ : ∀ a' ∈ m, δ a'}
    (hb : r b₁ b₂) (hf : ∀ (a : α) (ha : a ∈ m), r (f₁ a ha) (f₂ a ha)) :
    ∀ a ha, r (cons _ _ b₁ f₁ a ha) (cons _ _ b₂ f₂ a ha) := by
  intro a ha
  dsimp [cons]
  split_ifs with H
  · cases H
    exact hb
  · exact hf _ _

theorem cons_injective {a : α} {b : δ a} {s : Multiset α} (hs : a ∉ s) :
    Function.Injective (Pi.cons s a b) := fun f₁ f₂ eq =>
  funext fun a' =>
    funext fun h' =>
      have ne : a ≠ a' := fun h => hs <| h.symm ▸ h'
      have : a' ∈ a ::ₘ s := mem_cons_of_mem h'
      calc
        f₁ a' h' = Pi.cons s a b f₁ a' this := by rw [Pi.cons_ne this ne.symm]
               _ = Pi.cons s a b f₂ a' this := by rw [eq]
               _ = f₂ a' h' := by rw [Pi.cons_ne this ne.symm]

end Pi

section
variable {α : Type*} [DecidableEq α] {β : α → Type*}

/-- `pi m t` constructs the Cartesian product over `t` indexed by `m`. -/
def pi (m : Multiset α) (t : ∀ a, Multiset (β a)) : Multiset (∀ a ∈ m, β a) :=
  m.recOn {Pi.empty β}
    (fun a m (p : Multiset (∀ a ∈ m, β a)) => (t a).bind fun b => p.map <| Pi.cons m a b)
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
    pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map <| Pi.cons m a b :=
  recOn_cons a m

theorem card_pi (m : Multiset α) (t : ∀ a, Multiset (β a)) :
    card (pi m t) = prod (m.map fun a => card (t a)) :=
  Multiset.induction_on m (by simp) (by simp +contextual)

protected theorem Nodup.pi {s : Multiset α} {t : ∀ a, Multiset (β a)} :
    Nodup s → (∀ a ∈ s, Nodup (t a)) → Nodup (pi s t) := by
  refine Multiset.induction_on s (fun _ _ ↦ nodup_singleton _) (fun a s ih hs ht ↦ ?_)
  simp only [pi_cons]
  specialize ih (nodup_cons.1 hs).2 (fun a' h' ↦ ht a' (mem_cons_of_mem h'))
  specialize ht a (mem_cons_self _ _)
  revert ih ht
  refine Quot.induction_on (t a) <| fun la ↦ Quot.induction_on (pi s t) (fun lp hlp hla ↦ ?_)
  simp only [quot_mk_to_coe', map_coe, coe_bind, coe_nodup, List.nodup_flatMap]
  refine ⟨fun b _ ↦ hlp.map (Pi.cons_injective (nodup_cons.1 hs).1), hla.imp
    (@fun b₁ b₂ hne x hx₁ hx₂ ↦ hne ?_)⟩
  obtain ⟨g₁, _, rfl⟩ := List.mem_map.1 hx₁
  obtain ⟨g₂, _, heq⟩ := List.mem_map.1 hx₂
  have h : Pi.cons s a b₁ g₁ a (mem_cons_self _ _) = Pi.cons s a b₂ g₂ a (mem_cons_self _ _) :=
    congr_fun (congr_fun heq a).symm (mem_cons_self _ _)
  rwa [Pi.cons_same (mem_cons_self a s), Pi.cons_same] at h

theorem mem_pi (m : Multiset α) (t : ∀ a, Multiset (β a)) (f : ∀ a ∈ m, β a) :
    f ∈ pi m t ↔ ∀ (a) (h : a ∈ m), f a h ∈ t a := by
  induction m using Multiset.induction_on with
  | empty =>
    have : f = Pi.empty β := funext (fun _ => funext fun h => (notMem_zero _ h).elim)
    simp only [this, pi_zero, mem_singleton, true_iff]
    intro _ h; exact (notMem_zero _ h).elim
  | cons a m ih => ?_
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
