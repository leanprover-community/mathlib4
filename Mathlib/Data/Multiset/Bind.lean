/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Multiset.Basic

#align_import data.multiset.bind from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Bind operation for multisets

This file defines a few basic operations on `Multiset`, notably the monadic bind.

## Main declarations

* `Multiset.join`: The join, aka union or sum, of multisets.
* `Multiset.bind`: The bind of a multiset-indexed family of multisets.
* `Multiset.product`: Cartesian product of two multisets.
* `Multiset.sigma`: Disjoint sum of multisets in a sigma type.
-/


variable {α β γ δ : Type*}

namespace Multiset

/-! ### Join -/


/-- `join S`, where `S` is a multiset of multisets, is the lift of the list join
  operation, that is, the union of all the sets.
     join {{1, 2}, {1, 2}, {0, 1}} = {0, 1, 1, 1, 2, 2} -/
def join : Multiset (Multiset α) → Multiset α :=
  sum
#align multiset.join Multiset.join

theorem coe_join :
    ∀ L : List (List α), join (L.map ((↑) : List α → Multiset α) : Multiset (Multiset α)) = L.join
  | [] => rfl
  | l :: L => by
      -- Porting note: was `congr_arg (fun s : Multiset α => ↑l + s) (coe_join L)`
      simp only [join, List.map, coe_sum, List.sum_cons, List.join, ←coe_add, ←coe_join L]
      -- 🎉 no goals
#align multiset.coe_join Multiset.coe_join

@[simp]
theorem join_zero : @join α 0 = 0 :=
  rfl
#align multiset.join_zero Multiset.join_zero

@[simp]
theorem join_cons (s S) : @join α (s ::ₘ S) = s + join S :=
  sum_cons _ _
#align multiset.join_cons Multiset.join_cons

@[simp]
theorem join_add (S T) : @join α (S + T) = join S + join T :=
  sum_add _ _
#align multiset.join_add Multiset.join_add

@[simp]
theorem singleton_join (a) : join ({a} : Multiset (Multiset α)) = a :=
  sum_singleton _
#align multiset.singleton_join Multiset.singleton_join

@[simp]
theorem mem_join {a S} : a ∈ @join α S ↔ ∃ s ∈ S, a ∈ s :=
  Multiset.induction_on S (by simp) <| by
                              -- 🎉 no goals
    simp (config := { contextual := true }) [or_and_right, exists_or]
    -- 🎉 no goals
#align multiset.mem_join Multiset.mem_join

@[simp]
theorem card_join (S) : card (@join α S) = sum (map card S) :=
  Multiset.induction_on S (by simp) (by simp)
                              -- 🎉 no goals
                                        -- 🎉 no goals
#align multiset.card_join Multiset.card_join

theorem rel_join {r : α → β → Prop} {s t} (h : Rel (Rel r) s t) : Rel r s.join t.join := by
  induction h
  -- ⊢ Rel r (join 0) (join 0)
  case zero => simp
  -- ⊢ Rel r (join (a✝² ::ₘ as✝)) (join (b✝ ::ₘ bs✝))
  -- 🎉 no goals
  case cons a b s t hab hst ih => simpa using hab.add ih
  -- 🎉 no goals
  -- 🎉 no goals
#align multiset.rel_join Multiset.rel_join

/-! ### Bind -/


section Bind

variable (a : α) (s t : Multiset α) (f g : α → Multiset β)

/-- `s.bind f` is the monad bind operation, defined as `(s.map f).join`. It is the union of `f a` as
`a` ranges over `s`. -/
def bind (s : Multiset α) (f : α → Multiset β) : Multiset β :=
  (s.map f).join
#align multiset.bind Multiset.bind

@[simp]
theorem coe_bind (l : List α) (f : α → List β) : (@bind α β l fun a => f a) = l.bind f := by
  rw [List.bind, ← coe_join, List.map_map]
  -- ⊢ (bind ↑l fun a => ↑(f a)) = join ↑(List.map (ofList ∘ f) l)
  rfl
  -- 🎉 no goals
#align multiset.coe_bind Multiset.coe_bind

@[simp]
theorem zero_bind : bind 0 f = 0 :=
  rfl
#align multiset.zero_bind Multiset.zero_bind

@[simp]
theorem cons_bind : (a ::ₘ s).bind f = f a + s.bind f := by simp [bind]
                                                            -- 🎉 no goals
#align multiset.cons_bind Multiset.cons_bind

@[simp]
theorem singleton_bind : bind {a} f = f a := by simp [bind]
                                                -- 🎉 no goals
#align multiset.singleton_bind Multiset.singleton_bind

@[simp]
theorem add_bind : (s + t).bind f = s.bind f + t.bind f := by simp [bind]
                                                              -- 🎉 no goals
#align multiset.add_bind Multiset.add_bind

@[simp]
theorem bind_zero : s.bind (fun _ => 0 : α → Multiset β) = 0 := by simp [bind, join, nsmul_zero]
                                                                   -- 🎉 no goals
#align multiset.bind_zero Multiset.bind_zero

@[simp]
theorem bind_add : (s.bind fun a => f a + g a) = s.bind f + s.bind g := by simp [bind, join]
                                                                           -- 🎉 no goals
#align multiset.bind_add Multiset.bind_add

@[simp]
theorem bind_cons (f : α → β) (g : α → Multiset β) :
    (s.bind fun a => f a ::ₘ g a) = map f s + s.bind g :=
  Multiset.induction_on s (by simp)
                              -- 🎉 no goals
    (by simp (config := { contextual := true }) [add_comm, add_left_comm, add_assoc])
        -- 🎉 no goals
#align multiset.bind_cons Multiset.bind_cons

@[simp]
theorem bind_singleton (f : α → β) : (s.bind fun x => ({f x} : Multiset β)) = map f s :=
  Multiset.induction_on s (by rw [zero_bind, map_zero]) (by simp [singleton_add])
                              -- 🎉 no goals
                                                            -- 🎉 no goals
#align multiset.bind_singleton Multiset.bind_singleton

@[simp]
theorem mem_bind {b s} {f : α → Multiset β} : b ∈ bind s f ↔ ∃ a ∈ s, b ∈ f a := by
  simp [bind]
  -- 🎉 no goals
#align multiset.mem_bind Multiset.mem_bind

@[simp]
theorem card_bind : card (s.bind f) = (s.map (card ∘ f)).sum := by simp [bind]
                                                                   -- 🎉 no goals
#align multiset.card_bind Multiset.card_bind

theorem bind_congr {f g : α → Multiset β} {m : Multiset α} :
    (∀ a ∈ m, f a = g a) → bind m f = bind m g := by simp (config := { contextual := true }) [bind]
                                                     -- 🎉 no goals
#align multiset.bind_congr Multiset.bind_congr

theorem bind_hcongr {β' : Type _} {m : Multiset α} {f : α → Multiset β} {f' : α → Multiset β'}
    (h : β = β') (hf : ∀ a ∈ m, HEq (f a) (f' a)) : HEq (bind m f) (bind m f') := by
  subst h
  -- ⊢ HEq (bind m f) (bind m f')
  simp only [heq_eq_eq] at hf
  -- ⊢ HEq (bind m f) (bind m f')
  simp [bind_congr hf]
  -- 🎉 no goals
#align multiset.bind_hcongr Multiset.bind_hcongr

theorem map_bind (m : Multiset α) (n : α → Multiset β) (f : β → γ) :
    map f (bind m n) = bind m fun a => map f (n a) :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }))
                              -- 🎉 no goals
                                        -- 🎉 no goals
#align multiset.map_bind Multiset.map_bind

theorem bind_map (m : Multiset α) (n : β → Multiset γ) (f : α → β) :
    bind (map f m) n = bind m fun a => n (f a) :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }))
                              -- 🎉 no goals
                                        -- 🎉 no goals
#align multiset.bind_map Multiset.bind_map

theorem bind_assoc {s : Multiset α} {f : α → Multiset β} {g : β → Multiset γ} :
    (s.bind f).bind g = s.bind fun a => (f a).bind g :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }))
                              -- 🎉 no goals
                                        -- 🎉 no goals
#align multiset.bind_assoc Multiset.bind_assoc

theorem bind_bind (m : Multiset α) (n : Multiset β) {f : α → β → Multiset γ} :
    ((bind m) fun a => (bind n) fun b => f a b) = (bind n) fun b => (bind m) fun a => f a b :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }))
                              -- 🎉 no goals
                                        -- 🎉 no goals
#align multiset.bind_bind Multiset.bind_bind

theorem bind_map_comm (m : Multiset α) (n : Multiset β) {f : α → β → γ} :
    ((bind m) fun a => n.map fun b => f a b) = (bind n) fun b => m.map fun a => f a b :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }))
                              -- 🎉 no goals
                                        -- 🎉 no goals
#align multiset.bind_map_comm Multiset.bind_map_comm

@[to_additive (attr := simp)]
theorem prod_bind [CommMonoid β] (s : Multiset α) (t : α → Multiset β) :
    (s.bind t).prod = (s.map fun a => (t a).prod).prod :=
  Multiset.induction_on s (by simp) fun a s ih => by simp [ih, cons_bind]
                              -- 🎉 no goals
                                                     -- 🎉 no goals
#align multiset.prod_bind Multiset.prod_bind
#align multiset.sum_bind Multiset.sum_bind

theorem rel_bind {r : α → β → Prop} {p : γ → δ → Prop} {s t} {f : α → Multiset γ}
    {g : β → Multiset δ} (h : (r ⇒ Rel p) f g) (hst : Rel r s t) :
    Rel p (s.bind f) (t.bind g) := by
  apply rel_join
  -- ⊢ Rel (Rel p) (map f s) (map g t)
  rw [rel_map]
  -- ⊢ Rel (fun a b => Rel p (f a) (g b)) s t
  exact hst.mono fun a _ b _ hr => h hr
  -- 🎉 no goals
#align multiset.rel_bind Multiset.rel_bind

theorem count_sum [DecidableEq α] {m : Multiset β} {f : β → Multiset α} {a : α} :
    count a (map f m).sum = sum (m.map fun b => count a <| f b) :=
  Multiset.induction_on m (by simp) (by simp)
                              -- 🎉 no goals
                                        -- 🎉 no goals
#align multiset.count_sum Multiset.count_sum

theorem count_bind [DecidableEq α] {m : Multiset β} {f : β → Multiset α} {a : α} :
    count a (bind m f) = sum (m.map fun b => count a <| f b) :=
  count_sum
#align multiset.count_bind Multiset.count_bind

theorem le_bind {α β : Type*} {f : α → Multiset β} (S : Multiset α) {x : α} (hx : x ∈ S) :
    f x ≤ S.bind f := by
  classical
    rw [le_iff_count]
    intro a
    rw [count_bind]
    apply le_sum_of_mem
    rw [mem_map]
    exact ⟨x, hx, rfl⟩
#align multiset.le_bind Multiset.le_bind

-- Porting note: @[simp] removed because not in normal form
theorem attach_bind_coe (s : Multiset α) (f : α → Multiset β) :
    (s.attach.bind fun i => f i) = s.bind f :=
  congr_arg join <| attach_map_val' _ _
#align multiset.attach_bind_coe Multiset.attach_bind_coe

end Bind

/-! ### Product of two multisets -/


section Product

variable (a : α) (b : β) (s : Multiset α) (t : Multiset β)

/-- The multiplicity of `(a, b)` in `s ×ˢ t` is
  the product of the multiplicity of `a` in `s` and `b` in `t`. -/
def product (s : Multiset α) (t : Multiset β) : Multiset (α × β) :=
  s.bind fun a => t.map <| Prod.mk a
#align multiset.product Multiset.product

instance instSProd : SProd (Multiset α) (Multiset β) (Multiset (α × β)) where
  sprod := Multiset.product

@[simp]
theorem coe_product (l₁ : List α) (l₂ : List β) :
    (l₁ : Multiset α) ×ˢ (l₂ : Multiset β) = (l₁ ×ˢ l₂) := by
  dsimp only [SProd.sprod]
  -- ⊢ product ↑l₁ ↑l₂ = ↑(List.product l₁ l₂)
  rw [product, List.product, ← coe_bind]
  -- ⊢ (bind ↑l₁ fun a => map (Prod.mk a) ↑l₂) = bind ↑l₁ fun a => ↑(List.map (Prod …
  simp
  -- 🎉 no goals
#align multiset.coe_product Multiset.coe_product

@[simp]
theorem zero_product : (0 : Multiset α) ×ˢ t = 0 :=
  rfl
#align multiset.zero_product Multiset.zero_product

@[simp]
theorem cons_product : (a ::ₘ s) ×ˢ t = map (Prod.mk a) t + s ×ˢ t := by simp [SProd.sprod, product]
                                                                         -- 🎉 no goals
#align multiset.cons_product Multiset.cons_product

@[simp]
theorem product_zero : s ×ˢ (0 : Multiset β) = 0 := by simp [SProd.sprod, product]
                                                       -- 🎉 no goals
#align multiset.product_zero Multiset.product_zero

@[simp]
theorem product_cons : s ×ˢ (b ::ₘ t) = (s.map fun a => (a, b)) + s ×ˢ t := by
  simp [SProd.sprod, product]
  -- 🎉 no goals
#align multiset.product_cons Multiset.product_cons

@[simp]
theorem product_singleton : ({a} : Multiset α) ×ˢ ({b} : Multiset β) = {(a, b)} := by
  simp only [SProd.sprod, product, bind_singleton, map_singleton]
  -- 🎉 no goals
#align multiset.product_singleton Multiset.product_singleton

@[simp]
theorem add_product (s t : Multiset α) (u : Multiset β) : (s + t) ×ˢ u = s ×ˢ u + t ×ˢ u := by
  simp [SProd.sprod, product]
  -- 🎉 no goals
#align multiset.add_product Multiset.add_product

@[simp]
theorem product_add (s : Multiset α) : ∀ t u : Multiset β, s ×ˢ (t + u) = s ×ˢ t + s ×ˢ u :=
  Multiset.induction_on s (fun t u => rfl) fun a s IH t u => by
    rw [cons_product, IH]
    -- ⊢ map (Prod.mk a) (t + u) + (s ×ˢ t + s ×ˢ u) = (a ::ₘ s) ×ˢ t + (a ::ₘ s) ×ˢ u
    simp [add_comm, add_left_comm, add_assoc]
    -- 🎉 no goals
#align multiset.product_add Multiset.product_add

@[simp]
theorem mem_product {s t} : ∀ {p : α × β}, p ∈ @product α β s t ↔ p.1 ∈ s ∧ p.2 ∈ t
  | (a, b) => by simp [product, and_left_comm]
                 -- 🎉 no goals
#align multiset.mem_product Multiset.mem_product

@[simp]
theorem card_product : card (s ×ˢ t) = card s * card t := by simp [SProd.sprod, product]
                                                             -- 🎉 no goals
#align multiset.card_product Multiset.card_product

end Product

/-! ### Disjoint sum of multisets -/


section Sigma

variable {σ : α → Type*} (a : α) (s : Multiset α) (t : ∀ a, Multiset (σ a))

/-- `Multiset.sigma s t` is the dependent version of `Multiset.product`. It is the sum of
  `(a, b)` as `a` ranges over `s` and `b` ranges over `t a`. -/
protected def sigma (s : Multiset α) (t : ∀ a, Multiset (σ a)) : Multiset (Σa, σ a) :=
  s.bind fun a => (t a).map <| Sigma.mk a
#align multiset.sigma Multiset.sigma

@[simp]
theorem coe_sigma (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    (@Multiset.sigma α σ l₁ fun a => l₂ a) = l₁.sigma l₂ := by
  rw [Multiset.sigma, List.sigma, ← coe_bind]
  -- ⊢ (bind ↑l₁ fun a => map (Sigma.mk a) ↑(l₂ a)) = bind ↑l₁ fun a => ↑(List.map  …
  simp
  -- 🎉 no goals
#align multiset.coe_sigma Multiset.coe_sigma

@[simp]
theorem zero_sigma : @Multiset.sigma α σ 0 t = 0 :=
  rfl
#align multiset.zero_sigma Multiset.zero_sigma

@[simp]
theorem cons_sigma : (a ::ₘ s).sigma t = (t a).map (Sigma.mk a) + s.sigma t := by
  simp [Multiset.sigma]
  -- 🎉 no goals
#align multiset.cons_sigma Multiset.cons_sigma

@[simp]
theorem sigma_singleton (b : α → β) :
    (({a} : Multiset α).sigma fun a => ({b a} : Multiset β)) = {⟨a, b a⟩} :=
  rfl
#align multiset.sigma_singleton Multiset.sigma_singleton

@[simp]
theorem add_sigma (s t : Multiset α) (u : ∀ a, Multiset (σ a)) :
    (s + t).sigma u = s.sigma u + t.sigma u := by simp [Multiset.sigma]
                                                  -- 🎉 no goals
#align multiset.add_sigma Multiset.add_sigma

@[simp]
theorem sigma_add :
    ∀ t u : ∀ a, Multiset (σ a), (s.sigma fun a => t a + u a) = s.sigma t + s.sigma u :=
  Multiset.induction_on s (fun t u => rfl) fun a s IH t u => by
    rw [cons_sigma, IH]
    -- ⊢ map (Sigma.mk a) (t a + u a) + ((Multiset.sigma s fun a => t a) + Multiset.s …
    simp [add_comm, add_left_comm, add_assoc]
    -- 🎉 no goals
#align multiset.sigma_add Multiset.sigma_add

@[simp]
theorem mem_sigma {s t} : ∀ {p : Σa, σ a}, p ∈ @Multiset.sigma α σ s t ↔ p.1 ∈ s ∧ p.2 ∈ t p.1
  | ⟨a, b⟩ => by simp [Multiset.sigma, and_assoc, and_left_comm]
                 -- 🎉 no goals
#align multiset.mem_sigma Multiset.mem_sigma

@[simp]
theorem card_sigma : card (s.sigma t) = sum (map (fun a => card (t a)) s) := by
  simp [Multiset.sigma, (· ∘ ·)]
  -- 🎉 no goals
#align multiset.card_sigma Multiset.card_sigma

end Sigma

end Multiset
