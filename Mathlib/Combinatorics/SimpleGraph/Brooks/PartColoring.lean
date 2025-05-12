/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Coloring
/-!
Develop partial colorings of a `G : SimpleGraph α` using the`SimpleGraph.Coloring` API.

We want a partial `β`-coloring of `G` to be a map `C : α → β` that is valid on a given
subset of the vertices `s : Set α`. Where valid means `∀ a b ∈ s, G.Adj a b → C a ≠ C b`.

So given `G` and `s` we need a `SimpleGraph α` on which `SimpleGraph.Coloring`s look like this.

The obvious choice is `(G.induce s).spanningCoe` but an alternative choice is
`(⊤ : Subgraph G).induce s).spanningCoe`.

Propositionally these are the same thing but `(⊤ : Subgraph G).induce s).spanningCoe` is easier
to work with.

In particular if  `H := (⊤ : Subgraph G).induce s).spanningCoe` then
  `H.Adj a b` is `a ∈ s ∧ b ∈ s ∧ G.Adj a b`
while if `H := (G.induce s).spanningCoe` then `H.Adj a b` is
`(G.comap (Function.Embedding.subtype s)).map (Function.Embedding.subtype _).Adj a b`.
-/

namespace SimpleGraph

variable {α : Type*} (G : SimpleGraph α)

/--
A `PartColoring β s` of `G : SimpleGraph α` is an `β`-coloring of all vertices of `G` that is
a valid coloring on the set `s` -/
abbrev PartColoring (β : Type*) (s : Set α) := ((⊤ : Subgraph G).induce s).spanningCoe.Coloring β

/-- `G.PartColorable n s` iff the subgraph of `G` induced by `s` is `n` - colorable. -/
abbrev PartColorable (n : ℕ) (s : Set α) := Nonempty (G.PartColoring (Fin n) s)

variable {s t u : Set α} {β : Type*} {G}
/--
`C₂ : G.PartColoring β t` extends `C₁ : G.PartColoring β s` if `s ⊆ t` and `C₂` agrees with `C₁`
on `s`
-/
protected def PartColoring.Extends (C₂ : G.PartColoring β t) (C₁ : G.PartColoring β s) : Prop :=
  s ⊆ t ∧ ∀ ⦃v⦄, v ∈ s → C₂ v = C₁ v

namespace PartColoring

@[refl, simp]
lemma extends_refl {C₁ : G.PartColoring β s} : C₁.Extends C₁ := ⟨subset_refl _, fun _ _ ↦ rfl⟩

@[trans, simp]
lemma extends_trans {C₃ : G.PartColoring β u} {C₂ : G.PartColoring β t} {C₁ : G.PartColoring β s}
    (h1 : C₂.Extends C₁) (h2: C₃.Extends C₂) : C₃.Extends C₁ := by
  refine ⟨subset_trans h1.1 h2.1,?_⟩
  intro v hv
  rw [← h1.2 hv, h2.2 (h1.1 hv)]

/-- Construct a `G.PartColoring β t` from `C : G.PartColoring β s` and proof that `s = t` -/
@[simp]
def copy (C : G.PartColoring β s) (h : s = t) : G.PartColoring β t where
  toFun := C.toFun
  map_rel' := by
    subst h
    exact C.map_rel'

@[simp]
theorem copy_rfl  (C : G.PartColoring β s)  : C.copy rfl = C := rfl

@[simp]
theorem copy_copy {s t u} (C : G.PartColoring β s) (hs : s = t) (ht : t = u) :
    (C.copy hs).copy ht = C.copy (hs.trans ht) := by
  subst_vars
  rfl

@[simp]
lemma copy_def (C: G.PartColoring β s) (h : s = t) {v : α} :
  (C.copy h) v  = C v := rfl

@[simp]
lemma copy_extends {C₂ : G.PartColoring β t} {C₁ : G.PartColoring β s} (hc : C₂.Extends C₁)
  {h : t = u} : (C₂.copy h).Extends C₁ :=
    ⟨fun _ hx ↦ h ▸ hc.1 hx, fun _ hv ↦ by rw [copy_def]; exact hc.2 hv⟩

/-- A `G.PartColoring β Set.univ` is a `G.Coloring (Fin n)` -/
def toColoring (C : G.PartColoring β Set.univ) : G.Coloring β :=
    ⟨C, fun h ↦ C.valid (by simpa using h)⟩

end PartColoring

variable (G)

/-- We can color `{a}` with any color -/
def partColoringOfSingleton {β : Type*} (a : α) (c : β) : G.PartColoring β ({a} : Set α) where
  toFun := fun _ ↦ c
  map_rel':= by simp

@[simp]
lemma partColoringOfSingleton_def {β : Type*} {a v : α} {c : β} :
  G.partColoringOfSingleton a c v = c := rfl

/-- If `¬ G.Adj a b` then we can color `{a, b}` with any single color -/
def partColoringOfNotAdj {β : Type*} {a b : α} (h : ¬ G.Adj a b) (c : β) :
    G.PartColoring β ({a, b} : Set α) where
  toFun := fun _ ↦ c
  map_rel':= by
    intro x y hadj he
    cases hadj.1 <;> cases hadj.2.1 <;> subst_vars
    · exact G.loopless _ hadj.2.2
    · exact h hadj.2.2
    · exact h hadj.2.2.symm
    · exact G.loopless _ hadj.2.2

variable {G} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]

/--
We can combine colorings `C₁` of `s` and `C₂` of `t` if they are compatible i.e.
`∀ v w, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w` to get a coloring of `s ∪ t`.
This will extend `C₁` and, if `Disjoint s t`, it will also extend `C₂`.
-/
def PartColoring.union (C₁ : G.PartColoring β s) (C₂ : G.PartColoring β t)
    (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) : G.PartColoring β (s ∪ t) where
  toFun := fun v ↦ ite (v ∈ s) (C₁ v) (C₂ v)
  map_rel' := by
      simp only [Subgraph.spanningCoe_adj, Subgraph.induce_adj, Set.mem_union, Subgraph.top_adj,
        top_adj, ne_eq, and_imp]
      intro v w hv' hw' hadj hf
      by_cases hv : v ∈ s <;> by_cases hws : w ∈ s
      · rw [if_pos hv, if_pos hws] at hf
        exact C₁.valid (by simpa using ⟨hv, hws, hadj⟩) hf
      · by_cases hw : w ∈ t
        · rw [if_pos hv, if_neg hws] at hf
          exact h hv ⟨hw, hws⟩ hadj hf
        · exact hws <| Or.resolve_right hw' hw
      · rw [if_neg hv, if_pos hws] at hf
        exact h hws ⟨Or.resolve_left hv' hv, hv⟩ hadj.symm hf.symm
      · by_cases hw : w ∈ t
        · rw [if_neg hv, if_neg hws] at hf
          exact C₂.valid (by simpa using ⟨Or.resolve_left hv' hv, hw, hadj⟩) hf
        · exact hw <| Or.resolve_left hw' hws

@[simp]
lemma PartColoring.union_def {v : α} (C₁ : G.PartColoring β s) (C₂ : G.PartColoring β t)
    (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) :
  (C₁.union C₂ h) v = ite (v ∈ s) (C₁ v) (C₂ v) := rfl

@[simp]
lemma PartColoring.union_extends (C₁ : G.PartColoring β s) (C₂ : G.PartColoring β t)
    (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) : (C₁.union C₂ h).Extends C₁ :=
  ⟨Set.subset_union_left, fun _ hv ↦ by rw [union_def, if_pos hv]⟩

@[simp]
lemma PartColoring.union_extends_disjoint (hd : Disjoint s t) (C₁ : G.PartColoring β s)
    (C₂ : G.PartColoring β t) (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) :
    (C₁.union C₂ h).Extends C₂ :=
  ⟨Set.subset_union_right, fun _ hv ↦ by rw [union_def, if_neg (hd.not_mem_of_mem_right hv)]⟩


variable [DecidableEq α]

/-- The extension of a coloring of `s` to `insert a s` using a color `c` that is not used by `C` to
color a neighbor of `a` in `s` -/
protected def PartColoring.insert (a : α) {c : β} (C : G.PartColoring β s)
    (h : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C v ≠ c) : G.PartColoring β (insert a s) :=
  ((G.partColoringOfSingleton a c).union C (by
    simp only [Set.mem_singleton_iff, Set.mem_diff, and_imp]
    rintro _ _ rfl h' h1 had h2
    exact h h' had h2.symm)).copy (by simp [Set.union_comm])

variable {a v : α} {c : β}

@[simp]
lemma PartColoring.insert_def (C : G.PartColoring β s) (h : ∀ ⦃x⦄, x ∈ s → G.Adj a x → C x ≠ c) :
    (C.insert a h) v = ite (v = a) c (C v) := by
  rw [PartColoring.insert, copy_def, union_def]
  simp

@[simp]
lemma PartColoring.insert_extends {c : β} (C : G.PartColoring β s)
    (h : ∀ ⦃x⦄, x ∈ s → G.Adj a x → C x ≠ c) :
    (C.insert a h).Extends (G.partColoringOfSingleton a c) := copy_extends (union_extends ..)

@[simp]
lemma PartColoring.insert_extends_not_mem (C : G.PartColoring β s)
    (h : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C v ≠ c) (ha : a ∉ s) : (C.insert a h).Extends C :=
  copy_extends <| union_extends_disjoint (Set.disjoint_singleton_left.mpr ha) ..

end SimpleGraph
