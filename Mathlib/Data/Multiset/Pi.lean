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

variable {α : Type*}

open Function

/-- Given `δ : α → Type*`, `Pi.empty δ` is the trivial dependent function out of the empty
multiset. -/
def Pi.empty (δ : α → Sort*) : ∀ a ∈ (0 : Multiset α), δ a :=
  fun.
#align multiset.pi.empty Multiset.Pi.empty

universe u v
variable [DecidableEq α] {β : α → Type u} {δ : α → Sort v}

/-- Given `δ : α → Type*`, a multiset `m` and a term `a`, as well as a term `b : δ a` and a
function `f` such that `f a' : δ a'` for all `a'` in `m`, `Pi.cons m a b f` is a function `g` such
that `g a'' : δ a''` for all `a''` in `a ::ₘ m`. -/
def Pi.cons (m : Multiset α) (a : α) (b : δ a) (f : ∀ a ∈ m, δ a) : ∀ a' ∈ a ::ₘ m, δ a' :=
  fun a' ha' => if h : a' = a then Eq.ndrec b h.symm else f a' <| (mem_cons.1 ha').resolve_left h
#align multiset.pi.cons Multiset.Pi.cons

theorem Pi.cons_same {m : Multiset α} {a : α} {b : δ a} {f : ∀ a ∈ m, δ a} (h : a ∈ a ::ₘ m) :
    Pi.cons m a b f a h = b :=
  dif_pos rfl
#align multiset.pi.cons_same Multiset.Pi.cons_same

theorem Pi.cons_ne {m : Multiset α} {a a' : α} {b : δ a} {f : ∀ a ∈ m, δ a} (h' : a' ∈ a ::ₘ m)
    (h : a' ≠ a) : Pi.cons m a b f a' h' = f a' ((mem_cons.1 h').resolve_left h) :=
  dif_neg h
#align multiset.pi.cons_ne Multiset.Pi.cons_ne

theorem Pi.cons_swap {a a' : α} {b : δ a} {b' : δ a'} {m : Multiset α} {f : ∀ a ∈ m, δ a}
    (h : a ≠ a') : HEq (Pi.cons (a' ::ₘ m) a b (Pi.cons m a' b' f))
      (Pi.cons (a ::ₘ m) a' b' (Pi.cons m a b f)) := by
  apply hfunext rfl
  -- ⊢ ∀ (a_1 a'_1 : α), HEq a_1 a'_1 → HEq (cons (a' ::ₘ m) a b (cons m a' b' f) a …
  simp only [heq_iff_eq]
  -- ⊢ ∀ (a_1 a'_1 : α), a_1 = a'_1 → HEq (cons (a' ::ₘ m) a b (cons m a' b' f) a_1 …
  rintro a'' _ rfl
  -- ⊢ HEq (cons (a' ::ₘ m) a b (cons m a' b' f) a'') (cons (a ::ₘ m) a' b' (cons m …
  refine' hfunext (by rw [Multiset.cons_swap]) fun ha₁ ha₂ _ => _
  -- ⊢ HEq (cons (a' ::ₘ m) a b (cons m a' b' f) a'' ha₁) (cons (a ::ₘ m) a' b' (co …
  rcases ne_or_eq a'' a with (h₁ | rfl)
  -- ⊢ HEq (cons (a' ::ₘ m) a b (cons m a' b' f) a'' ha₁) (cons (a ::ₘ m) a' b' (co …
  rcases eq_or_ne a'' a' with (rfl | h₂)
  all_goals simp [*, Pi.cons_same, Pi.cons_ne]
  -- 🎉 no goals
#align multiset.pi.cons_swap Multiset.Pi.cons_swap

@[simp, nolint simpNF] --Porting note: false positive, this lemma can prove itself
theorem pi.cons_eta {m : Multiset α} {a : α} (f : ∀ a' ∈ a ::ₘ m, δ a') :
    (Pi.cons m a (f _ (mem_cons_self _ _)) fun a' ha' => f a' (mem_cons_of_mem ha')) = f := by
  ext a' h'
  -- ⊢ Pi.cons m a (f a (_ : a ∈ a ::ₘ m)) (fun a' ha' => f a' (_ : a' ∈ a ::ₘ m))  …
  by_cases h : a' = a
  -- ⊢ Pi.cons m a (f a (_ : a ∈ a ::ₘ m)) (fun a' ha' => f a' (_ : a' ∈ a ::ₘ m))  …
  · subst h
    -- ⊢ Pi.cons m a' (f a' (_ : a' ∈ a' ::ₘ m)) (fun a'_1 ha' => f a'_1 (_ : a'_1 ∈  …
    rw [Pi.cons_same]
    -- 🎉 no goals
  · rw [Pi.cons_ne _ h]
    -- 🎉 no goals
#align multiset.pi.cons_eta Multiset.pi.cons_eta

theorem Pi.cons_injective {a : α} {b : δ a} {s : Multiset α} (hs : a ∉ s) :
    Function.Injective (Pi.cons s a b) := fun f₁ f₂ eq =>
  funext fun a' =>
    funext fun h' =>
      have ne : a ≠ a' := fun h => hs <| h.symm ▸ h'
      have : a' ∈ a ::ₘ s := mem_cons_of_mem h'
      calc
        f₁ a' h' = Pi.cons s a b f₁ a' this := by rw [Pi.cons_ne this ne.symm]
                                                  -- 🎉 no goals
        _ = Pi.cons s a b f₂ a' this := by rw [eq]
                                           -- 🎉 no goals
        _ = f₂ a' h' := by rw [Pi.cons_ne this ne.symm]
                           -- 🎉 no goals
#align multiset.pi.cons_injective Multiset.Pi.cons_injective

/-- `pi m t` constructs the Cartesian product over `t` indexed by `m`. -/
def pi (m : Multiset α) (t : ∀ a, Multiset (β a)) : Multiset (∀ a ∈ m, β a) :=
  m.recOn {Pi.empty β}
    (fun a m (p : Multiset (∀ a ∈ m, β a)) => (t a).bind fun b => p.map <| Pi.cons m a b)
    (by
      intro a a' m n
      -- ⊢ HEq (bind (t a) fun b => map (Pi.cons (a' ::ₘ m) a b) (bind (t a') fun b =>  …
      by_cases eq : a = a'
      -- ⊢ HEq (bind (t a) fun b => map (Pi.cons (a' ::ₘ m) a b) (bind (t a') fun b =>  …
      · subst eq; rfl
        -- ⊢ HEq (bind (t a) fun b => map (Pi.cons (a ::ₘ m) a b) (bind (t a) fun b => ma …
                  -- 🎉 no goals
      · simp [map_bind, bind_bind (t a') (t a)]
        -- ⊢ HEq (bind (t a) fun b => bind (t a') fun a_1 => map (fun x => Pi.cons (a' :: …
        apply bind_hcongr
        -- ⊢ ((a_1 : α) → a_1 ∈ a ::ₘ a' ::ₘ m → β a_1) = ((a_1 : α) → a_1 ∈ a' ::ₘ a ::ₘ …
        · rw [cons_swap a a']
          -- 🎉 no goals
        intro b _
        -- ⊢ HEq (bind (t a') fun a_1 => map (fun x => Pi.cons (a' ::ₘ m) a b (Pi.cons m  …
        apply bind_hcongr
        -- ⊢ ((a_1 : α) → a_1 ∈ a ::ₘ a' ::ₘ m → β a_1) = ((a_1 : α) → a_1 ∈ a' ::ₘ a ::ₘ …
        · rw [cons_swap a a']
          -- 🎉 no goals
        intro b' _
        -- ⊢ HEq (map (fun x => Pi.cons (a' ::ₘ m) a b (Pi.cons m a' b' x)) n) (map (fun  …
        apply map_hcongr
        -- ⊢ ((a_1 : α) → a_1 ∈ a ::ₘ a' ::ₘ m → β a_1) = ((a_1 : α) → a_1 ∈ a' ::ₘ a ::ₘ …
        · rw [cons_swap a a']
          -- 🎉 no goals
        intro f _
        -- ⊢ HEq (Pi.cons (a' ::ₘ m) a b (Pi.cons m a' b' f)) (Pi.cons (a ::ₘ m) a' b' (P …
        exact Pi.cons_swap eq)
        -- 🎉 no goals
#align multiset.pi Multiset.pi

@[simp]
theorem pi_zero (t : ∀ a, Multiset (β a)) : pi 0 t = {Pi.empty β} :=
  rfl
#align multiset.pi_zero Multiset.pi_zero

@[simp]
theorem pi_cons (m : Multiset α) (t : ∀ a, Multiset (β a)) (a : α) :
    pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map <| Pi.cons m a b :=
  recOn_cons a m
#align multiset.pi_cons Multiset.pi_cons

theorem card_pi (m : Multiset α) (t : ∀ a, Multiset (β a)) :
    card (pi m t) = prod (m.map fun a => card (t a)) :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }) [mul_comm])
                              -- 🎉 no goals
                                        -- 🎉 no goals
#align multiset.card_pi Multiset.card_pi

protected theorem Nodup.pi {s : Multiset α} {t : ∀ a, Multiset (β a)} :
    Nodup s → (∀ a ∈ s, Nodup (t a)) → Nodup (pi s t) :=
  Multiset.induction_on s (fun _ _ => nodup_singleton _)
    (by
      intro a s ih hs ht
      -- ⊢ Nodup (pi (a ::ₘ s) t)
      have has : a ∉ s := by simp at hs; exact hs.1
      -- ⊢ Nodup (pi (a ::ₘ s) t)
      have hs : Nodup s := by simp at hs; exact hs.2
      -- ⊢ Nodup (pi (a ::ₘ s) t)
      simp
      -- ⊢ (∀ (a_1 : β a), a_1 ∈ t a → Nodup (Multiset.map (Pi.cons s a a_1) (pi s t))) …
      refine'
        ⟨fun b _ => ((ih hs) fun a' h' => ht a' <| mem_cons_of_mem h').map (Pi.cons_injective has),
          _⟩
      refine' (ht a <| mem_cons_self _ _).pairwise _
      -- ⊢ ∀ (a_1 : β a), a_1 ∈ t a → ∀ (b : β a), b ∈ t a → a_1 ≠ b → Disjoint (Multis …
      exact fun b₁ _ b₂ _ neb =>
        disjoint_map_map.2 fun f _ g _ eq =>
          have : Pi.cons s a b₁ f a (mem_cons_self _ _) = Pi.cons s a b₂ g a (mem_cons_self _ _) :=
            by rw [eq]
          neb <| show b₁ = b₂ by rwa [Pi.cons_same, Pi.cons_same] at this)
#align multiset.nodup.pi Multiset.Nodup.pi

theorem mem_pi (m : Multiset α) (t : ∀ a, Multiset (β a)) :
    ∀ f : ∀ a ∈ m, β a, f ∈ pi m t ↔ ∀ (a) (h : a ∈ m), f a h ∈ t a := by
  intro f
  -- ⊢ f ∈ pi m t ↔ ∀ (a : α) (h : a ∈ m), f a h ∈ t a
  induction' m using Multiset.induction_on with a m ih
  -- ⊢ f ∈ pi 0 t ↔ ∀ (a : α) (h : a ∈ 0), f a h ∈ t a
  · have : f = Pi.empty β := funext (fun _ => funext fun h => (not_mem_zero _ h).elim)
    -- ⊢ f ∈ pi 0 t ↔ ∀ (a : α) (h : a ∈ 0), f a h ∈ t a
    simp only [this, pi_zero, mem_singleton, true_iff]
    -- ⊢ ∀ (a : α) (h : a ∈ 0), Pi.empty β a h ∈ t a
    intro _ h; exact (not_mem_zero _ h).elim
    -- ⊢ Pi.empty β a✝ h ∈ t a✝
               -- 🎉 no goals
  simp_rw [pi_cons, mem_bind, mem_map, ih]
  -- ⊢ (∃ a_1, a_1 ∈ t a ∧ ∃ a_2, (∀ (a : α) (h : a ∈ m), a_2 a h ∈ t a) ∧ Pi.cons  …
  constructor
  -- ⊢ (∃ a_1, a_1 ∈ t a ∧ ∃ a_2, (∀ (a : α) (h : a ∈ m), a_2 a h ∈ t a) ∧ Pi.cons  …
  · rintro ⟨b, hb, f', hf', rfl⟩ a' ha'
    -- ⊢ Pi.cons m a b f' a' ha' ∈ t a'
    by_cases h : a' = a
    -- ⊢ Pi.cons m a b f' a' ha' ∈ t a'
    · subst h
      -- ⊢ Pi.cons m a' b f' a' ha' ∈ t a'
      rwa [Pi.cons_same]
      -- 🎉 no goals
    · rw [Pi.cons_ne _ h]
      -- ⊢ f' a' (_ : a' ∈ m) ∈ t a'
      apply hf'
      -- 🎉 no goals
  · intro hf
    -- ⊢ ∃ a_1, a_1 ∈ t a ∧ ∃ a_2, (∀ (a : α) (h : a ∈ m), a_2 a h ∈ t a) ∧ Pi.cons m …
    refine' ⟨_, hf a (mem_cons_self _ _), _, fun a ha => hf a (mem_cons_of_mem ha), _⟩
    -- ⊢ (Pi.cons m a (f a (_ : a ∈ a ::ₘ m)) fun a_1 ha => f a_1 (_ : a_1 ∈ a ::ₘ m) …
    rw [pi.cons_eta]
    -- 🎉 no goals
#align multiset.mem_pi Multiset.mem_pi

end Pi

end Multiset
