/-
Copyright (c) 2026 Kyle Miller, Iván Renison, Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Peter Nelson, Iván Renison, Jun Kwon
-/
module

public import Mathlib.Combinatorics.HasDart.Basic
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

* `HasDart.Walk` (with accompanying pattern definitions
  `HasDart.Walk.nil'` and `HasDart.Walk.cons'`)
* `HasDart.Walk.Nil`: A predicate for the empty walk
* `HasDart.Walk.length`: The length of a walk
* `HasDart.Walk.support`: The list of vertices a walk visits in order
* `HasDart.Walk.prodDarts`: The list of `prodDart`s a walk visits in order

## Tags
walks
-/

@[expose] public section

namespace HasDart

universe u'' u'
variable {α Gr : Type*} {u v w : α} {G : Gr}

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : α`, the type `Walk u v` consists
of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `HasDart.Walk.support`.

See `HasDart.Walk.nil'` and `HasDart.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk {α : Type u'} {Gr : Type*} [HasDart.{u''} α Gr] (G : Gr) :
    α → α → Type (max u' u'')
  | nil {u : α} : Walk G u u
  | cons {u v w : α} (d : dart G u v) (p : Walk G v w) : Walk G u w

/- Manual instances for `DecidableEq` because deriving gives an instance that requires
  `DecidableEq Gr` -/
@[reducible]
instance Walk.instDecidable [DecidableEq α] [HasDart α Gr] [∀ u v, DecidableEq (dart G u v)]
    {u v : α} (p q : Walk G u v) : Decidable (p = q) := by
  rcases p with (nil | @⟨u, v₁, w, h₁, p₁⟩)
  <;> rcases q with (nil | @⟨u, v₂, w, h₂, p₂⟩)
  · exact isTrue rfl
  · exact isFalse (by simp)
  · exact isFalse (by simp)
  · by_cases hv : v₁ = v₂
    · subst hv
      simp only [cons.injEq, heq_eq_eq, true_and]
      haveI := Walk.instDecidable p₁ p₂
      infer_instance
    · apply isFalse (by simp [hv])

instance Walk.instDecidableEq [DecidableEq α] [HasDart α Gr] [∀ u v, DecidableEq (dart G u v)] :
    DecidableEq (Walk G u v) :=
  Walk.instDecidable

attribute [refl] Walk.nil

@[simps]
instance Walk.instInhabited [HasDart α Gr] (G : Gr) (v : α) : Inhabited (Walk G v v) := ⟨Walk.nil⟩

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
def dart.toWalk [HasDart α Gr] (h : dart G u v) : Walk G u v :=
  Walk.cons h Walk.nil

namespace Walk

section GeneralHasDart

variable [HasDart α Gr] {p : Walk G u v}

/-- Pattern to get `Walk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (u : α) : Walk G u u := Walk.nil

/-- Pattern to get `Walk.cons` with the vertices as explicit arguments. -/
@[match_pattern]
abbrev cons' (u v w : α) (h : dart G u v) (p : Walk G v w) : Walk G u w := Walk.cons h p

theorem exists_eq_cons_of_ne (hne : u ≠ v) :
    ∀ (p : Walk G u v), ∃ (w : α) (h : dart G u w) (p' : Walk G w v), p = cons h p'
  | nil => (hne rfl).elim
  | cons h p' => ⟨_, h, p', rfl⟩

/-- The length of a walk is the number of edges/prodDarts along it. -/
def length {u v : α} : Walk G u v → ℕ
  | nil => 0
  | cons _ q => q.length.succ

@[simp]
theorem length_nil : (nil : Walk G u u).length = 0 := rfl

@[simp]
theorem length_cons (h : dart G u v) (p : Walk G v w) :
    (cons h p).length = p.length + 1 := rfl

theorem eq_of_length_eq_zero : ∀ {p : Walk G u v}, p.length = 0 → u = v
  | nil, _ => rfl

/-- If `u` and `v` connected by one-edge walk, then there exists a dart between them. -/
def dart_of_length_eq_one : ∀ {p : Walk G u v}, p.length = 1 → dart G u v
  | cons h nil, _ => h

@[simp]
theorem exists_length_eq_zero_iff : (∃ p : Walk G u v, p.length = 0) ↔ u = v :=
  ⟨fun ⟨_, h⟩ ↦ (eq_of_length_eq_zero h), (· ▸ ⟨nil, rfl⟩)⟩

@[simp]
lemma exists_length_eq_one_iff : (∃ (p : Walk G u v), p.length = 1) ↔ Nonempty (dart G u v) := by
  refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun ⟨d⟩ ↦ ⟨d.toWalk, by simp⟩⟩
  induction p with
  | nil => simp at hp
  | cons d p' =>
    simp only [length_cons, Nat.add_eq_right] at hp
    exact ⟨(p'.eq_of_length_eq_zero hp) ▸ d⟩

@[simp]
theorem length_eq_zero_iff {p : Walk G u u} : p.length = 0 ↔ p = nil := by cases p <;> simp

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {u v : α} : Walk G u v → List α
  | nil => [u]
  | cons _ p => u :: p.support

/-- The `prodDarts` of a walk is the list of `prodDart` it visits in order. -/
def prodDarts {u v : α} : Walk G u v → List (prodDart G)
  | nil => []
  | cons h p => ⟨(u, _), h⟩ :: p.prodDarts

@[simp]
theorem support_nil : (nil : Walk G u u).support = [u] := rfl

@[simp, grind =]
theorem support_cons (h : dart G u v) (p : Walk G v w) :
    (cons h p).support = u :: p.support := rfl

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

theorem support_subset_support_cons (p : Walk G v w) (hadj : dart G u v) :
    p.support ⊆ (p.cons hadj).support := by
  simp

theorem coe_support (p : Walk G u v) : (p.support : Multiset α) = {u} + p.support.tail := by
  cases p <;> rfl

theorem isChain_adj_cons_support {u v w : α} (h : dart G u v) :
    ∀ (p : Walk G v w), List.IsChain (dart G) (u :: p.support)
  | nil => .cons_cons h (.singleton v)
  | cons h' p => .cons_cons h (isChain_adj_cons_support h' p)

theorem isChain_adj_support : ∀ (p : Walk G u v), List.IsChain (dart G) p.support
  | nil => .singleton _
  | cons h p => isChain_adj_cons_support h p

theorem isChain_dartAdj_cons_prodDarts {d : prodDart G} (h : d.snd = v) (p : Walk G v w) :
    List.IsChain (prodDartAdj G) (d :: p.prodDarts) := by
  induction p generalizing d with
  | nil => exact .singleton _
  | cons h' p ih => exact .cons_cons h (ih rfl)

theorem isChain_dartAdj_prodDarts : ∀ (p : Walk G u v), List.IsChain (prodDartAdj G) p.prodDarts
  | nil => .nil
  -- Porting note: needed to defer `rfl` to help elaboration
  | cons h p => isChain_dartAdj_cons_prodDarts (by rfl) p

@[simp]
theorem prodDarts_nil : (nil : Walk G u u).prodDarts = [] := rfl

@[simp]
theorem prodDarts_cons (h : dart G u v) (p : Walk G v w) :
    (cons h p).prodDarts = ⟨(u, v), h⟩ :: p.prodDarts := rfl

theorem cons_map_snd_prodDarts (p : Walk G u v) : (u :: p.prodDarts.map (·.snd)) = p.support := by
  induction p <;> simp [*]

theorem map_snd_prodDarts (p : Walk G u v) : p.prodDarts.map (·.snd) = p.support.tail := by
  simpa using congr_arg List.tail (cons_map_snd_prodDarts p)

theorem map_fst_prodDarts_append (p : Walk G u v) : p.prodDarts.map (·.fst) ++ [v] = p.support := by
  induction p <;> simp [*]

theorem map_fst_prodDarts (p : Walk G u v) : p.prodDarts.map (·.fst) = p.support.dropLast := by
  simpa! using congr_arg List.dropLast (map_fst_prodDarts_append p)

@[simp, grind =]
theorem length_support (p : Walk G u v) : p.support.length = p.length + 1 := by
  induction p <;> simp [*]

@[simp, grind =]
theorem length_prodDarts (p : Walk G u v) : p.prodDarts.length = p.length := by
  induction p <;> simp [*]

@[simp]
theorem fst_prodDarts_getElem {i : ℕ} (hi : i < p.prodDarts.length) :
    p.prodDarts[i].fst = p.support.dropLast[i]'(by grind) := by
  grind [map_fst_prodDarts]

@[simp]
theorem snd_prodDarts_getElem {i : ℕ} (hi : i < p.prodDarts.length) :
    p.prodDarts[i].snd = p.support.tail[i]'(by grind) := by
  grind [map_snd_prodDarts]

@[simp]
lemma support_getElem_zero (p : Walk G u v) : p.support[0] = u := by cases p <;> simp

@[simp]
lemma support_getElem_length (p : Walk G u v) : p.support[p.length] = v := by
  induction p <;> simp_all

theorem dart_fst_mem_support_of_mem_prodDarts {u v : α} :
    ∀ (p : Walk G u v) {d : prodDart G}, d ∈ p.prodDarts → d.fst ∈ p.support
  | cons h p', d, hd => by
    simp only [support_cons, prodDarts_cons, List.mem_cons] at hd ⊢
    rcases hd with rfl | hd
    · exact .inl rfl
    · exact .inr (dart_fst_mem_support_of_mem_prodDarts _ hd)

theorem prodDarts_nodup_of_support_nodup (h : p.support.Nodup) : p.prodDarts.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [prodDarts_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨(h.1 <| dart_fst_mem_support_of_mem_prodDarts p' ·), ih h.2⟩

theorem prodDarts_injective {u v : α} : Function.Injective (Walk.prodDarts : Walk G u v → _)
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _, h => by simp at h
  | .cons _ _, .nil, h => by simp at h
  | .cons' u v c h₁ w₁, .cons' _ v' _ h₂ w₂, h => by
    simp only [prodDarts_cons, List.cons.injEq, prodDart.mk.injEq, Prod.mk.injEq, true_and] at h
    obtain ⟨⟨rfl, hh⟩, h⟩ := h
    congr
    · simpa using hh
    · exact prodDarts_injective h

/-- Predicate for the empty walk.

Solves the dependent type problem where `p = Walk G.nil` typechecks
only if `p` has defeq endpoints. -/
inductive Nil : {u v : α} → Walk G u v → Prop
  | nil {w : α} : Nil (nil : Walk G w w)

@[simp, grind .] lemma nil_nil : (nil : Walk G u u).Nil := Nil.nil

@[simp] lemma not_nil_cons {h : dart G u v} {p : Walk G v w} : ¬ (cons h p).Nil := nofun

instance (p : Walk G v w) : Decidable p.Nil :=
  match p with
  | nil => isTrue .nil
  | cons _ _ => isFalse nofun

protected lemma Nil.eq : p.Nil → u = v | .nil => rfl

lemma not_nil_of_ne : u ≠ v → ¬ p.Nil := mt Nil.eq

lemma nil_iff_support_eq : p.Nil ↔ p.support = [v] := by
  cases p <;> simp

@[simp]
lemma prodDarts_eq_nil : p.prodDarts = [] ↔ p.Nil := by
  cases p <;> simp

lemma nil_iff_length_eq : p.Nil ↔ p.length = 0 := by
  cases p <;> simp

lemma not_nil_iff_lt_length : ¬ p.Nil ↔ 0 < p.length := by
  cases p <;> simp

lemma not_nil_iff : ¬ p.Nil ↔ ∃ (w : α) (h : dart G u w) (q : Walk G w v), p = cons h q := by
  cases p <;> simp [*]

/-- A walk with its endpoints defeq is `Nil` if and only if it is equal to `nil`. -/
lemma nil_iff_eq_nil : ∀ {p : Walk G v v}, p.Nil ↔ p = nil
  | .nil | .cons _ _ => by simp

alias ⟨Nil.eq_nil, _⟩ := nil_iff_eq_nil

/-- The recursion principle for nonempty walks -/
@[elab_as_elim]
def notNilRec {motive : {u w : α} → (p : Walk G u w) → (h : ¬ p.Nil) → Sort*}
    (cons : {u v w : α} → (h : dart G u v) → (q : Walk G v w) → motive (cons h q) not_nil_cons)
    (p : Walk G u w) : (hp : ¬ p.Nil) → motive p hp :=
  match p with
  | nil => fun hp => absurd .nil hp
  | .cons h q => fun _ => cons h q

@[simp]
lemma notNilRec_cons {motive : {u w : α} → (p : Walk G u w) → ¬ p.Nil → Sort*}
    (cons : {u v w : α} → (h : dart G u v) → (q : Walk G v w) →
    motive (q.cons h) Walk.not_nil_cons) (h' : dart G u v) (q' : Walk G v w) :
    @notNilRec _ _ _ _ _ _ _ cons _ _ = cons h' q' := by rfl

theorem end_mem_tail_support (h : ¬ p.Nil) : v ∈ p.support.tail :=
  p.notNilRec (by simp) h

/-- Given a set `S` and a walk `w` from `u` to `v` such that `u ∈ S` but `v ∉ S`,
there exists a dart in the walk whose start is in `S` but whose end is not. -/
theorem exists_boundary_dart (p : Walk G u v) (S : Set α) (uS : u ∈ S) (vS : v ∉ S) :
    ∃ d : (prodDart G), d ∈ p.prodDarts ∧ d.fst ∈ S ∧ d.snd ∉ S := by
  induction p with
  | nil => cases vS uS
  | cons a p' ih =>
    rename_i x y z
    by_cases h : y ∈ S
    · obtain ⟨d, hd, hcd⟩ := ih h vS
      exact ⟨d, List.Mem.tail _ hd, hcd⟩
    · exact ⟨⟨(x, y), a⟩, List.Mem.head _, uS, h⟩

end GeneralHasDart

section HasPDart

/-
### Prop-valued darts

Some graph-like structures have `Prop`-valued darts, such as `SimpleGraph` and `Digraph` and there
exists a generality for such structures, separate from the general graph-like structures with
`HasDart` typeclass.

This section assumes `HasDart.{0} α Gr` to proves lemmas for `Prop`-valued darts.
-/

variable [HasDart.{0} α Gr] {p : Walk G u v}

theorem mem_prodDarts_iff_infix_support {u' v'} (h : dart G u' v') :
    ⟨(u', v'), h⟩ ∈ p.prodDarts ↔ [u', v'] <:+: p.support := by
  refine .trans ⟨fun h ↦ ?_, fun ⟨i, hi, h⟩ ↦ ?_⟩ List.infix_iff_getElem?.symm
  · have ⟨i, hi, h⟩ := List.getElem_of_mem h
    exact ⟨i, by grind, fun j hj ↦ by grind [fst_prodDarts_getElem, snd_prodDarts_getElem]⟩
  · have := h 0
    have := h 1
    convert p.prodDarts.getElem_mem (n := i) (by grind)
      <;> grind [fst_prodDarts_getElem, snd_prodDarts_getElem]

theorem mem_prodDarts_iff_fst_snd_infix_support {d : prodDart G} :
    d ∈ p.prodDarts ↔ [d.fst, d.snd] <:+: p.support :=
  mem_prodDarts_iff_infix_support ..

end HasPDart

end HasDart.Walk
