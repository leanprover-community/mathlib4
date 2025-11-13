/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Bind operation for multisets

This file defines a few basic operations on `Multiset`, notably the monadic bind.

## Main declarations

* `Multiset.join`: The join, aka union or sum, of multisets.
* `Multiset.bind`: The bind of a multiset-indexed family of multisets.
* `Multiset.product`: Cartesian product of two multisets.
* `Multiset.sigma`: Disjoint sum of multisets in a sigma type.
-/

assert_not_exists MonoidWithZero MulAction

universe v

variable {α : Type*} {β : Type v} {γ δ : Type*}

namespace Multiset

/-! ### Join -/

/-- `join S`, where `S` is a multiset of multisets, is the lift of the list join
  operation, that is, the union of all the sets.
  For example, `join {{1, 2}, {1, 2}, {0, 1}} = {0, 1, 1, 1, 2, 2}`. -/
def join : Multiset (Multiset α) → Multiset α :=
  sum

theorem coe_join : ∀ L : List (List α), join (L.map ((↑) : List α → Multiset α) :
    Multiset (Multiset α)) = L.flatten
  | [] => rfl
  | l :: L => by
      exact congr_arg (fun s : Multiset α => ↑l + s) (coe_join L)

@[simp]
theorem join_zero : @join α 0 = 0 :=
  rfl

@[simp]
theorem join_cons (s S) : @join α (s ::ₘ S) = s + join S :=
  sum_cons _ _

@[simp]
theorem join_add (S T) : @join α (S + T) = join S + join T :=
  sum_add _ _

@[simp]
theorem singleton_join (a) : join ({a} : Multiset (Multiset α)) = a :=
  sum_singleton _

@[simp]
theorem mem_join {a S} : a ∈ @join α S ↔ ∃ s ∈ S, a ∈ s :=
  Multiset.induction_on S (by simp) <| by
    simp +contextual [or_and_right, exists_or]

@[simp]
theorem card_join (S) : card (@join α S) = sum (map card S) :=
  Multiset.induction_on S (by simp) (by simp)

@[simp]
theorem map_join (f : α → β) (S : Multiset (Multiset α)) :
    map f (join S) = join (map (map f) S) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

@[to_additive (attr := simp)]
theorem prod_join [CommMonoid α] {S : Multiset (Multiset α)} :
    prod (join S) = prod (map prod S) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

theorem rel_join {r : α → β → Prop} {s t} (h : Rel (Rel r) s t) : Rel r s.join t.join := by
  induction h with
  | zero => simp
  | cons hab hst ih => simpa using hab.add ih

/-! ### Bind -/


section Bind

variable (a : α) (s t : Multiset α) (f g : α → Multiset β)

/-- `s.bind f` is the monad bind operation, defined as `(s.map f).join`. It is the union of `f a` as
`a` ranges over `s`. -/
def bind (s : Multiset α) (f : α → Multiset β) : Multiset β :=
  (s.map f).join

@[simp]
theorem coe_bind (l : List α) (f : α → List β) : (@bind α β l fun a => f a) = l.flatMap f := by
  rw [List.flatMap, ← coe_join, List.map_map]
  rfl

@[simp]
theorem zero_bind : bind 0 f = 0 :=
  rfl

@[simp]
theorem cons_bind : (a ::ₘ s).bind f = f a + s.bind f := by simp [bind]

@[simp]
theorem singleton_bind : bind {a} f = f a := by simp [bind]

@[simp]
theorem add_bind : (s + t).bind f = s.bind f + t.bind f := by simp [bind]

@[simp]
theorem bind_zero : s.bind (fun _ => 0 : α → Multiset β) = 0 := by simp [bind, join, nsmul_zero]

@[simp]
theorem bind_add : (s.bind fun a => f a + g a) = s.bind f + s.bind g := by simp [bind, join]

@[simp]
theorem bind_cons (f : α → β) (g : α → Multiset β) :
    (s.bind fun a => f a ::ₘ g a) = map f s + s.bind g :=
  Multiset.induction_on s (by simp)
    (by simp +contextual [add_comm, add_left_comm, add_assoc])

@[simp]
theorem bind_singleton (f : α → β) : (s.bind fun x => ({f x} : Multiset β)) = map f s :=
  Multiset.induction_on s (by rw [zero_bind, map_zero]) (by simp [singleton_add])

@[simp]
theorem mem_bind {b s} {f : α → Multiset β} : b ∈ bind s f ↔ ∃ a ∈ s, b ∈ f a := by
  simp [bind]

@[simp]
theorem card_bind : card (s.bind f) = (s.map (card ∘ f)).sum := by simp [bind]

theorem bind_congr {f g : α → Multiset β} {m : Multiset α} :
    (∀ a ∈ m, f a = g a) → bind m f = bind m g := by simp +contextual [bind]

theorem bind_hcongr {β' : Type v} {m : Multiset α} {f : α → Multiset β} {f' : α → Multiset β'}
    (h : β = β') (hf : ∀ a ∈ m, f a ≍ f' a) : bind m f ≍ bind m f' := by
  subst h
  simp only [heq_eq_eq] at hf
  simp [bind_congr hf]

theorem map_bind (m : Multiset α) (n : α → Multiset β) (f : β → γ) :
    map f (bind m n) = bind m fun a => map f (n a) := by simp [bind]

theorem bind_map (m : Multiset α) (n : β → Multiset γ) (f : α → β) :
    bind (map f m) n = bind m fun a => n (f a) :=
  Multiset.induction_on m (by simp) (by simp +contextual)

theorem bind_assoc {s : Multiset α} {f : α → Multiset β} {g : β → Multiset γ} :
    (s.bind f).bind g = s.bind fun a => (f a).bind g :=
  Multiset.induction_on s (by simp) (by simp +contextual)

theorem bind_bind (m : Multiset α) (n : Multiset β) {f : α → β → Multiset γ} :
    ((bind m) fun a => (bind n) fun b => f a b) = (bind n) fun b => (bind m) fun a => f a b :=
  Multiset.induction_on m (by simp) (by simp +contextual)

theorem bind_map_comm (m : Multiset α) (n : Multiset β) {f : α → β → γ} :
    ((bind m) fun a => n.map fun b => f a b) = (bind n) fun b => m.map fun a => f a b :=
  Multiset.induction_on m (by simp) (by simp +contextual)

@[to_additive (attr := simp)]
theorem prod_bind [CommMonoid β] (s : Multiset α) (t : α → Multiset β) :
    (s.bind t).prod = (s.map fun a => (t a).prod).prod := by simp [bind]

open scoped Relator in
theorem rel_bind {r : α → β → Prop} {p : γ → δ → Prop} {s t} {f : α → Multiset γ}
    {g : β → Multiset δ} (h : (r ⇒ Rel p) f g) (hst : Rel r s t) :
    Rel p (s.bind f) (t.bind g) := by
  apply rel_join
  rw [rel_map]
  exact hst.mono fun a _ b _ hr => h hr

theorem count_sum [DecidableEq α] {m : Multiset β} {f : β → Multiset α} {a : α} :
    count a (map f m).sum = sum (m.map fun b => count a <| f b) :=
  Multiset.induction_on m (by simp) (by simp)

theorem count_bind [DecidableEq α] {m : Multiset β} {f : β → Multiset α} {a : α} :
    count a (bind m f) = sum (m.map fun b => count a <| f b) :=
  count_sum

theorem le_bind {α β : Type*} {f : α → Multiset β} (S : Multiset α) {x : α} (hx : x ∈ S) :
    f x ≤ S.bind f := by
  classical
  refine le_iff_count.2 fun a ↦ ?_
  obtain ⟨m', hm'⟩ := exists_cons_of_mem <| mem_map_of_mem (fun b ↦ count a (f b)) hx
  rw [count_bind, hm', sum_cons]
  exact Nat.le_add_right _ _

@[simp]
theorem attach_bind_coe (s : Multiset α) (f : α → Multiset β) :
    (s.attach.bind fun i => f i) = s.bind f :=
  congr_arg join <| attach_map_val' _ _

variable {f s t}

open scoped Function in -- required for scoped `on` notation
@[simp] lemma nodup_bind :
    Nodup (bind s f) ↔ (∀ a ∈ s, Nodup (f a)) ∧ s.Pairwise (Disjoint on f) := by
  have : ∀ a, ∃ l : List β, f a = l := fun a => Quot.induction_on (f a) fun l => ⟨l, rfl⟩
  choose f' h' using this
  have : f = fun a ↦ ofList (f' a) := funext h'
  have hd : Symmetric fun a b ↦ List.Disjoint (f' a) (f' b) := fun a b h ↦ h.symm
  exact Quot.induction_on s <| by
    unfold Function.onFun
    simp [this, List.nodup_flatMap, pairwise_coe_iff_pairwise hd]

@[simp]
lemma dedup_bind_dedup [DecidableEq α] [DecidableEq β] (s : Multiset α) (f : α → Multiset β) :
    (s.dedup.bind f).dedup = (s.bind f).dedup := by
  ext x
  -- Porting note: was `simp_rw [count_dedup, mem_bind, mem_dedup]`
  simp_rw [count_dedup]
  congr 1
  simp

variable (op : α → α → α) [hc : Std.Commutative op] [ha : Std.Associative op]

theorem fold_bind {ι : Type*} (s : Multiset ι) (t : ι → Multiset α) (b : ι → α) (b₀ : α) :
    (s.bind t).fold op ((s.map b).fold op b₀) =
    (s.map fun i => (t i).fold op (b i)).fold op b₀ := by
  induction s using Multiset.induction_on with
  | empty => rw [zero_bind, map_zero, map_zero, fold_zero]
  | cons a ha ih => rw [cons_bind, map_cons, map_cons, fold_cons_left, fold_cons_left, fold_add, ih]

end Bind

/-! ### Product of two multisets -/


section Product

variable (a : α) (b : β) (s : Multiset α) (t : Multiset β)

/-- The multiplicity of `(a, b)` in `s ×ˢ t` is
  the product of the multiplicity of `a` in `s` and `b` in `t`. -/
def product (s : Multiset α) (t : Multiset β) : Multiset (α × β) :=
  s.bind fun a => t.map <| Prod.mk a

instance instSProd : SProd (Multiset α) (Multiset β) (Multiset (α × β)) where
  sprod := Multiset.product

@[simp]
theorem coe_product (l₁ : List α) (l₂ : List β) :
    (l₁ : Multiset α) ×ˢ (l₂ : Multiset β) = (l₁ ×ˢ l₂) := by
  dsimp only [SProd.sprod]
  rw [product, List.product, ← coe_bind]
  simp

@[simp]
theorem zero_product : (0 : Multiset α) ×ˢ t = 0 :=
  rfl

@[simp]
theorem cons_product : (a ::ₘ s) ×ˢ t = map (Prod.mk a) t + s ×ˢ t := by simp [SProd.sprod, product]

@[simp]
theorem product_zero : s ×ˢ (0 : Multiset β) = 0 := by simp [SProd.sprod, product]

@[simp]
theorem product_cons : s ×ˢ (b ::ₘ t) = (s.map fun a => (a, b)) + s ×ˢ t := by
  simp [SProd.sprod, product]

@[simp]
theorem product_singleton : ({a} : Multiset α) ×ˢ ({b} : Multiset β) = {(a, b)} := by
  simp only [SProd.sprod, product, bind_singleton, map_singleton]

@[simp]
theorem add_product (s t : Multiset α) (u : Multiset β) : (s + t) ×ˢ u = s ×ˢ u + t ×ˢ u := by
  simp [SProd.sprod, product]

@[simp]
theorem product_add (s : Multiset α) : ∀ t u : Multiset β, s ×ˢ (t + u) = s ×ˢ t + s ×ˢ u :=
  Multiset.induction_on s (fun _ _ => rfl) fun a s IH t u => by
    rw [cons_product, IH]
    simp [add_left_comm, add_assoc]

@[simp]
theorem card_product : card (s ×ˢ t) = card s * card t := by simp [SProd.sprod, product]

variable {s t}

@[simp] lemma mem_product : ∀ {p : α × β}, p ∈ @product α β s t ↔ p.1 ∈ s ∧ p.2 ∈ t
  | (a, b) => by simp [product, and_left_comm]

protected theorem Nodup.product : Nodup s → Nodup t → Nodup (s ×ˢ t) :=
  Quotient.inductionOn₂ s t fun l₁ l₂ d₁ d₂ => by simp [List.Nodup.product d₁ d₂]

end Product

/-! ### Disjoint sum of multisets -/


section Sigma

variable {σ : α → Type*} (a : α) (s : Multiset α) (t : ∀ a, Multiset (σ a))

/-- `Multiset.sigma s t` is the dependent version of `Multiset.product`. It is the sum of
  `(a, b)` as `a` ranges over `s` and `b` ranges over `t a`. -/
protected def sigma (s : Multiset α) (t : ∀ a, Multiset (σ a)) : Multiset (Σ a, σ a) :=
  s.bind fun a => (t a).map <| Sigma.mk a

@[simp]
theorem coe_sigma (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    (@Multiset.sigma α σ l₁ fun a => l₂ a) = l₁.sigma l₂ := by
  rw [Multiset.sigma, List.sigma, ← coe_bind]
  simp

@[simp]
theorem zero_sigma : @Multiset.sigma α σ 0 t = 0 :=
  rfl

@[simp]
theorem cons_sigma : (a ::ₘ s).sigma t = (t a).map (Sigma.mk a) + s.sigma t := by
  simp [Multiset.sigma]

@[simp]
theorem sigma_singleton (b : α → β) :
    (({a} : Multiset α).sigma fun a => ({b a} : Multiset β)) = {⟨a, b a⟩} :=
  rfl

@[simp]
theorem add_sigma (s t : Multiset α) (u : ∀ a, Multiset (σ a)) :
    (s + t).sigma u = s.sigma u + t.sigma u := by simp [Multiset.sigma]

@[simp]
theorem sigma_add :
    ∀ t u : ∀ a, Multiset (σ a), (s.sigma fun a => t a + u a) = s.sigma t + s.sigma u :=
  Multiset.induction_on s (fun _ _ => rfl) fun a s IH t u => by
    rw [cons_sigma, IH]
    simp [add_comm, add_left_comm, add_assoc]

@[simp]
theorem card_sigma : card (s.sigma t) = sum (map (fun a => card (t a)) s) := by
  simp [Multiset.sigma, (· ∘ ·)]

variable {s t}

@[simp] lemma mem_sigma : ∀ {p : Σ a, σ a}, p ∈ @Multiset.sigma α σ s t ↔ p.1 ∈ s ∧ p.2 ∈ t p.1
  | ⟨a, b⟩ => by simp [Multiset.sigma, and_left_comm]

protected theorem Nodup.sigma {σ : α → Type*} {t : ∀ a, Multiset (σ a)} :
    Nodup s → (∀ a, Nodup (t a)) → Nodup (s.sigma t) :=
  Quot.induction_on s fun l₁ => by
    choose f hf using fun a => Quotient.exists_rep (t a)
    simpa [← funext hf] using List.Nodup.sigma

end Sigma

end Multiset
