/-
Copyright (c) 2026 Kyle Miller, Iván Renison, Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Peter Nelson, Iván Renison, Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Data.Multiset.Basic

/-!
# Walks

In a general graph structure, a *walk* is a finite sequence of adjacent vertices, and can be
thought of equally well as a sequence of directed edges.

**Warning:** graph theorists mean something different by "path" than do homotopy theorists.
A "walk" in graph theory is a "path" in homotopy theory.  Another warning: some graph theorists use
"path" and "simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `GraphLike.Walk` (with accompanying pattern definitions
  `GraphLike.Walk.nil'` and `GraphLike.Walk.cons'`)
* `GraphLike.Walk.Nil`: A predicate for the empty walk
* `GraphLike.Walk.length`: The length of a walk
* `GraphLike.Walk.support`: The list of vertices a walk visits in order
* `GraphLike.Walk.darts`: The list of darts a walk visits in order

## Tags
walks
-/

public section

namespace GraphLike

variable {α β Gr : Type*} {u v w : α} {G : Gr} {d : β}

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : α`, the type `Walk u v` consists
of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `GraphLike.Walk.support`.

See `GraphLike.Walk.nil'` and `GraphLike.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk (G : Gr) [GraphLike α β G] : α → α → Type (max u_1 u_2)
  | nil {u : α} : Walk G u u
  | cons {u v w : α} (s : step G u v) (p : Walk G v w) : Walk G u w

namespace Walk

section GraphLike

variable [GraphLike α β G] {p : Walk G u v}

/- Manual instances for `DecidableEq` because deriving gives an instance that requires
  `DecidableEq Gr` -/
@[reducible]
instance instDecidable [DecidableEq α] [DecidableEq β] {u v : α} (p q : Walk G u v) :
    Decidable (p = q) := by
  rcases p with (nil | @⟨u, v₁, w, d₁, p₁⟩) <;> rcases q with (nil | @⟨u, v₂, w, d₂, p₂⟩)
  · exact isTrue rfl
  · exact isFalse (by simp)
  · exact isFalse (by simp)
  · by_cases hv : v₁ = v₂
    · subst hv
      simp only [cons.injEq, heq_eq_eq, true_and]
      haveI := Walk.instDecidable p₁ p₂
      infer_instance
    · apply isFalse (by simp [hv])

instance instDecidableEq [DecidableEq α] [DecidableEq β] : DecidableEq (Walk G u v) :=
  Walk.instDecidable

attribute [refl] Walk.nil

@[simps]
instance instInhabited (G : Gr) [GraphLike α β G] (v : α) : Inhabited (Walk G v v) := ⟨Walk.nil⟩

/-- The one-edge walk associated to a single step, which is a dart from `u` to `v`. -/
@[expose, match_pattern, reducible]
def _root_.GraphLike.step.toWalk (s : step G u v) : Walk G u v :=
  Walk.cons s Walk.nil

/-- Pattern to get `Walk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (u : α) : Walk G u u := Walk.nil

/-- Pattern to get `Walk.cons` with the vertices as explicit arguments. -/
@[match_pattern]
abbrev cons' (u v w : α) (s : step G u v) (p : Walk G v w) : Walk G u w := Walk.cons s p

theorem exists_eq_cons_of_ne (hne : u ≠ v) :
    ∀ (p : Walk G u v), ∃ (w : α) (s : step G u w) (p' : Walk G w v), p = cons s p'
  | nil => (hne rfl).elim
  | cons s p' => ⟨_, s, p', rfl⟩

/-- The length of a walk is the number of edges/darts along it. -/
@[expose]
def length {u v : α} : Walk G u v → ℕ
  | nil => 0
  | cons _ q => q.length.succ

@[simp]
theorem length_nil : (nil : Walk G u u).length = 0 := rfl

@[simp]
theorem length_cons (s : step G u v) (p : Walk G v w) :
    (cons s p).length = p.length + 1 := rfl

theorem eq_of_length_eq_zero : ∀ {p : Walk G u v}, p.length = 0 → u = v
  | nil, _ => rfl

/-- If `u` and `v` connected by one-edge walk, then there exists a step between them. -/
def step_of_length_eq_one : ∀ {p : Walk G u v}, p.length = 1 → step G u v
  | cons s nil, _ => s

@[simp]
theorem exists_length_eq_zero_iff : (∃ p : Walk G u v, p.length = 0) ↔ u = v :=
  ⟨fun ⟨_, h⟩ ↦ (eq_of_length_eq_zero h), (· ▸ ⟨nil, rfl⟩)⟩

@[simp]
lemma exists_length_eq_one_iff : (∃ (p : Walk G u v), p.length = 1) ↔ Adj G u v := by
  rw [← exists_darts_iff_adj]
  refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun ⟨d, hd, hu, hv⟩ ↦ ⟨step.toWalk ⟨d, hd, hu, hv⟩, by simp⟩⟩
  induction p with
  | nil => simp at hp
  | cons d p' =>
    simp only [length_cons, Nat.add_eq_right] at hp
    obtain rfl := p'.eq_of_length_eq_zero hp
    obtain ⟨d, hd, hu, hv⟩ := d
    exact ⟨d, hd, hu, hv⟩

@[simp]
theorem length_eq_zero_iff {p : Walk G u u} : p.length = 0 ↔ p = nil := by cases p <;> simp

/-- The `support` of a walk is the list of vertices it visits in order. -/
@[expose]
def support {u v : α} : Walk G u v → List α
  | nil => [u]
  | cons _ p => u :: p.support

/-- The `darts` of a walk is the list of `dart`s it visits in order. -/
@[expose]
def darts {u v : α} : Walk G u v → List (darts G)
  | nil => []
  | cons s p => ⟨s.val, s.prop.1⟩ :: p.darts

@[simp]
theorem support_nil : (nil : Walk G u u).support = [u] := rfl

@[simp, grind =]
theorem support_cons (s : step G u v) (p : Walk G v w) :
    (cons s p).support = u :: p.support := rfl

@[simp]
theorem support_ne_nil (p : Walk G u v) : p.support ≠ [] := by cases p <;> simp

@[simp]
theorem head_support (p : Walk G u v) : p.support.head (by simp) = u := by cases p <;> simp

@[simp]
theorem getLast_support (p : Walk G u v) : p.support.getLast (by simp) = v := by
  induction p <;> simp [*]

theorem support_eq_cons (p : Walk G u v) : p.support = u :: p.support.tail := by
  cases p <;> simp

@[simp]
theorem start_mem_support (p : Walk G u v) : u ∈ p.support := by cases p <;> simp

@[simp]
theorem end_mem_support (p : Walk G u v) : v ∈ p.support := by induction p <;> simp [*]

@[simp]
theorem support_nonempty (p : Walk G u v) : { w | w ∈ p.support }.Nonempty :=
  ⟨u, by simp⟩

theorem mem_support_iff (p : Walk G u v) : w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail := by
  cases p <;> simp

theorem mem_support_nil_iff : u ∈ (nil : Walk G v v).support ↔ u = v := by simp

@[simp]
theorem end_mem_tail_support_of_ne (h : u ≠ v) (p : Walk G u v) : v ∈ p.support.tail := by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

theorem support_subset_support_cons (p : Walk G v w) (s : step G u v) :
    p.support ⊆ (p.cons s).support := by
  simp

theorem coe_support (p : Walk G u v) : (p.support : Multiset α) = {u} + p.support.tail := by
  cases p <;> rfl

theorem isChain_adj_cons_support {u v w : α} (s : step G u v) :
    ∀ (p : Walk G v w), List.IsChain (Adj G) (u :: p.support)
  | nil => .cons_cons s.adj (.singleton v)
  | cons h' p => .cons_cons s.adj (isChain_adj_cons_support h' p)

theorem isChain_adj_support : ∀ (p : Walk G u v), List.IsChain (Adj G) p.support
  | nil => .singleton _
  | cons h p => isChain_adj_cons_support h p

theorem isChain_dartAdj_cons_darts {d : GraphLike.darts G} (h : snd G d.val = v) (p : Walk G v w) :
    List.IsChain DartAdj (d :: p.darts) := by
  induction p generalizing d with
  | nil => exact .singleton _
  | cons h' p ih => exact .cons_cons (h.trans h'.fst.symm) (ih h'.snd)

theorem isChain_dartAdj_darts : ∀ (p : Walk G u v), List.IsChain DartAdj p.darts
  | nil => .nil
  | cons h p => isChain_dartAdj_cons_darts h.snd p

@[simp]
theorem darts_nil : (nil : Walk G u u).darts = [] := rfl

@[simp]
theorem darts_cons (s : step G u v) (p : Walk G v w) :
    (cons s p).darts = ⟨s.val, s.prop.1⟩ :: p.darts := rfl

theorem cons_map_snd_darts (p : Walk G u v) : (u :: p.darts.map (snd G ·.val)) = p.support := by
  induction p <;> simp [-List.map_subtype, *]

theorem map_snd_darts (p : Walk G u v) : p.darts.map (snd G ·.val) = p.support.tail := by
  simpa using congr_arg List.tail (cons_map_snd_darts p)

theorem map_fst_darts_append (p : Walk G u v) : p.darts.map (fst G ·.val) ++ [v] = p.support := by
  induction p <;> simp [-List.map_subtype, *]

theorem map_fst_darts (p : Walk G u v) : p.darts.map (fst G ·.val) = p.support.dropLast := by
  simpa! using congr_arg List.dropLast (map_fst_darts_append p)

@[simp, grind =]
theorem length_support (p : Walk G u v) : p.support.length = p.length + 1 := by
  induction p <;> simp [*]

@[simp, grind =]
theorem length_darts (p : Walk G u v) : p.darts.length = p.length := by
  induction p <;> simp [*]

@[simp]
theorem fst_darts_getElem {i : ℕ} (hi : i < p.darts.length) :
    fst G p.darts[i].val = p.support.dropLast[i]'(by grind) := by
  grind [map_fst_darts]

@[simp]
theorem snd_darts_getElem {i : ℕ} (hi : i < p.darts.length) :
    snd G p.darts[i].val = p.support.tail[i]'(by grind) := by
  grind [map_snd_darts]

@[simp]
lemma support_getElem_zero (p : Walk G u v) : p.support[0] = u := by cases p <;> simp

@[simp]
lemma support_getElem_length (p : Walk G u v) : p.support[p.length] = v := by
  induction p <;> simp_all

theorem dart_fst_mem_support_of_mem_darts {u v : α} :
    ∀ (p : Walk G u v) {d : GraphLike.darts G}, d ∈ p.darts → fst G d.val ∈ p.support
  | cons h p', d, hd => by
    simp only [support_cons, darts_cons, List.mem_cons] at hd ⊢
    rcases hd with rfl | hd
    · exact .inl h.fst
    · exact .inr (dart_fst_mem_support_of_mem_darts _ hd)

theorem darts_nodup_of_support_nodup (h : p.support.Nodup) : p.darts.Nodup := by
  induction p with
  | nil => simp
  | cons s p' ih =>
    simp only [darts_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨(h.1 <| s.fst ▸ dart_fst_mem_support_of_mem_darts p' ·), ih h.2⟩

theorem darts_injective {u v : α} : Function.Injective (Walk.darts : Walk G u v → _)
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _, h => by simp at h
  | .cons _ _, .nil, h => by simp at h
  | .cons' u v c s₁ w₁, .cons' _ v' _ s₂ w₂, h => by
    simp only [darts_cons, List.cons.injEq, Subtype.mk.injEq] at h
    obtain ⟨hs, h⟩ := h
    rw [cons.injEq]
    obtain rfl := step.right_eq_of_val_eq hs
    exact ⟨rfl, step.ext_HEq hs, heq_of_eq <| darts_injective h⟩

/-- Predicate for the empty walk.

Solves the dependent type problem where `p = Walk.nil` typechecks
only if `p` has defeq endpoints. -/
inductive Nil : {u v : α} → Walk G u v → Prop
  | nil {w : α} : Nil (nil : Walk G w w)

@[simp, grind .] lemma nil_nil : (nil : Walk G u u).Nil := Nil.nil

@[simp] lemma not_nil_cons {h : step G u v} {p : Walk G v w} : ¬ (cons h p).Nil := nofun

instance (p : Walk G v w) : Decidable p.Nil :=
  match p with
  | nil => isTrue .nil
  | cons _ _ => isFalse nofun

protected lemma Nil.eq : p.Nil → u = v | .nil => rfl

lemma not_nil_of_ne : u ≠ v → ¬ p.Nil := mt Nil.eq

lemma nil_iff_support_eq : p.Nil ↔ p.support = [v] := by
  cases p <;> simp

@[simp, grind =]
lemma darts_eq_nil : p.darts = [] ↔ p.Nil := by
  cases p <;> simp

lemma nil_iff_length_eq : p.Nil ↔ p.length = 0 := by
  cases p <;> simp

lemma not_nil_iff_lt_length : ¬ p.Nil ↔ 0 < p.length := by
  cases p <;> simp

lemma not_nil_iff : ¬ p.Nil ↔ ∃ (w : α) (h : step G u w) (q : Walk G w v), p = cons h q := by
  cases p <;> simp [*]

/-- A walk with its endpoints defeq is `Nil` if and only if it is equal to `nil`. -/
lemma nil_iff_eq_nil : ∀ {p : Walk G v v}, p.Nil ↔ p = nil
  | .nil | .cons _ _ => by simp

alias ⟨Nil.eq_nil, _⟩ := nil_iff_eq_nil

/-- The recursion principle for nonempty walks -/
@[elab_as_elim]
def notNilRec {motive : {u w : α} → (p : Walk G u w) → (h : ¬ p.Nil) → Sort*}
    (cons : {u v w : α} → (h : step G u v) → (q : Walk G v w) → motive (cons h q) not_nil_cons)
    (p : Walk G u w) : (hp : ¬ p.Nil) → motive p hp :=
  match p with
  | nil => fun hp => absurd .nil hp
  | .cons h q => fun _ => cons h q

@[simp]
lemma notNilRec_cons {motive : {u w : α} → (p : Walk G u w) → ¬ p.Nil → Sort*}
    (cons : {u v w : α} → (h : step G u v) → (q : Walk G v w) →
    motive (q.cons h) Walk.not_nil_cons) (h' : step G u v) (q' : Walk G v w) :
    @notNilRec _ _ _ _ _ _ _ _ cons _ _ = cons h' q' := by rfl

theorem end_mem_tail_support (h : ¬ p.Nil) : v ∈ p.support.tail :=
  p.notNilRec (by simp) h

/-- Given a set `S` and a walk `w` from `u` to `v` such that `u ∈ S` but `v ∉ S`,
there exists a step in the walk whose start is in `S` but whose end is not. -/
theorem exists_boundary_dart (p : Walk G u v) (S : Set α) (uS : u ∈ S) (vS : v ∉ S) :
    ∃ d : GraphLike.darts G, d ∈ p.darts ∧ fst G d.val ∈ S ∧ snd G d.val ∉ S := by
  induction p with
  | nil => cases vS uS
  | cons a p' ih =>
    rename_i x y z
    by_cases h : y ∈ S
    · obtain ⟨d, hd, hcd⟩ := ih h vS
      exact ⟨d, List.Mem.tail _ hd, hcd⟩
    · exact ⟨⟨a.val, a.prop.1⟩, List.Mem.head _, a.fst.symm ▸ uS, a.snd.symm ▸ h⟩

end GraphLike
end GraphLike.Walk
