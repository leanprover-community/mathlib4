/-
Copyright (c) 2021 David Wärn,. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Kim Morrison, Matteo Cipollina
-/
module

public import Mathlib.Combinatorics.Quiver.Prefunctor
public import Mathlib.Logic.Lemmas
public import Batteries.Data.List.Basic

/-!
# Paths in quivers

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Function

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace Quiver

/-- `Path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive Path {V : Type u} [Quiver.{v} V] (a : V) : V → Type max u v
  | nil : Path a a
  | cons : ∀ {b c : V}, Path a b → (b ⟶ c) → Path a c

-- See issue https://github.com/leanprover/lean4/issues/2049
compile_inductive% Path

/-- An arrow viewed as a path of length one. -/
def Hom.toPath {V} [Quiver V] {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e

namespace Path

variable {V : Type u} [Quiver V] {a b c d : V}

lemma nil_ne_cons (p : Path a b) (e : b ⟶ a) : Path.nil ≠ p.cons e :=
  fun h => by injection h

lemma cons_ne_nil (p : Path a b) (e : b ⟶ a) : p.cons e ≠ Path.nil :=
  fun h => by injection h

lemma obj_eq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : b = c := by injection h

lemma heq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : p ≍ p' := by injection h

lemma hom_heq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : e ≍ e' := by injection h

/-- The length of a path is the number of arrows it uses. -/
def length {a : V} : ∀ {b : V}, Path a b → ℕ
  | _, nil => 0
  | _, cons p _ => p.length + 1

instance {a : V} : Inhabited (Path a a) :=
  ⟨nil⟩

@[simp]
theorem length_nil {a : V} : (nil : Path a a).length = 0 :=
  rfl

@[simp]
theorem length_cons (a b c : V) (p : Path a b) (e : b ⟶ c) : (p.cons e).length = p.length + 1 :=
  rfl

theorem eq_of_length_zero (p : Path a b) (hzero : p.length = 0) : a = b := by
  cases p
  · rfl
  · cases Nat.succ_ne_zero _ hzero

theorem eq_nil_of_length_zero (p : Path a a) (hzero : p.length = 0) : p = nil := by
  cases p
  · rfl
  · simp at hzero

@[simp]
lemma length_toPath {a b : V} (e : a ⟶ b) : e.toPath.length = 1 := rfl

/-- Composition of paths. -/
def comp {a b : V} : ∀ {c}, Path a b → Path b c → Path a c
  | _, p, nil => p
  | _, p, cons q e => (p.comp q).cons e

@[simp]
theorem comp_cons {a b c d : V} (p : Path a b) (q : Path b c) (e : c ⟶ d) :
    p.comp (q.cons e) = (p.comp q).cons e :=
  rfl

@[simp]
theorem comp_nil {a b : V} (p : Path a b) : p.comp Path.nil = p :=
  rfl

@[simp]
theorem nil_comp {a : V} : ∀ {b} (p : Path a b), Path.nil.comp p = p
  | _, nil => rfl
  | _, cons p _ => by rw [comp_cons, nil_comp p]

@[simp]
theorem comp_assoc {a b c : V} :
    ∀ {d} (p : Path a b) (q : Path b c) (r : Path c d), (p.comp q).comp r = p.comp (q.comp r)
  | _, _, _, nil => rfl
  | _, p, q, cons r _ => by rw [comp_cons, comp_cons, comp_cons, comp_assoc p q r]

@[simp]
theorem length_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).length = p.length + q.length
  | _, nil => rfl
  | _, cons _ _ => congr_arg Nat.succ (length_comp _ _)

theorem comp_inj {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (hq : q₁.length = q₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  induction q₁ with
  | nil =>
    rcases q₂ with _ | ⟨q₂, f₂⟩
    · exact ⟨h, rfl⟩
    · cases hq
  | cons q₁ f₁ ih =>
    rcases q₂ with _ | ⟨q₂, f₂⟩
    · cases hq
    · simp only [comp_cons, cons.injEq] at h
      obtain rfl := h.1
      obtain ⟨rfl, rfl⟩ := ih (Nat.succ.inj hq) h.2.1.eq
      rw [h.2.2.eq]
      exact ⟨rfl, rfl⟩

theorem comp_inj' {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (h : p₁.length = p₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
  ⟨fun h_eq => (comp_inj <| Nat.add_left_cancel (n := p₂.length) <|
    by simpa [h] using congr_arg length h_eq).1 h_eq,
   by rintro ⟨rfl, rfl⟩; rfl⟩

theorem comp_injective_left (q : Path b c) : Injective fun p : Path a b => p.comp q :=
  fun _ _ h => ((comp_inj rfl).1 h).1

theorem comp_injective_right (p : Path a b) : Injective (p.comp : Path b c → Path a c) :=
  fun _ _ h => ((comp_inj' rfl).1 h).2

@[simp]
theorem comp_inj_left {p₁ p₂ : Path a b} {q : Path b c} : p₁.comp q = p₂.comp q ↔ p₁ = p₂ :=
  q.comp_injective_left.eq_iff

@[simp]
theorem comp_inj_right {p : Path a b} {q₁ q₂ : Path b c} : p.comp q₁ = p.comp q₂ ↔ q₁ = q₂ :=
  p.comp_injective_right.eq_iff

lemma eq_toPath_comp_of_length_eq_succ (p : Path a b) {n : ℕ}
    (hp : p.length = n + 1) :
    ∃ (c : V) (f : a ⟶ c) (q : Quiver.Path c b) (_ : q.length = n),
      p = f.toPath.comp q := by
  induction p generalizing n with
  | nil => simp at hp
  | @cons c d p q h =>
    cases n
    · rw [length_cons, Nat.zero_add, Nat.add_eq_right] at hp
      obtain rfl := eq_of_length_zero p hp
      obtain rfl := eq_nil_of_length_zero p hp
      exact ⟨d, q, nil, rfl, rfl⟩
    · rw [length_cons, Nat.add_right_cancel_iff] at hp
      obtain ⟨x, q'', p'', hl, rfl⟩ := h hp
      exact ⟨x, q'', p''.cons q, by simpa, rfl⟩

section Decomposition

variable {V R : Type*} [Quiver V] {a b : V} (p : Path a b)

lemma length_ne_zero_iff_eq_comp (p : Path a b) :
    p.length ≠ 0 ↔ ∃ (c : V) (e : a ⟶ c) (p' : Path c b),
      p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h_len : p.length = (p.length - 1) + 1 := by lia
    obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
    exact ⟨c, e, p', rfl, by lia⟩
  · rintro ⟨c, p', e, rfl, h⟩
    simp [h]

/-- Every non-empty path can be decomposed as an initial path plus a final edge. -/
lemma length_ne_zero_iff_eq_cons :
    p.length ≠ 0 ↔ ∃ (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · cases p with
    | nil => simp at h
    | cons p' e => exact ⟨_, p', e, rfl⟩
  · rintro ⟨c, p', e, rfl⟩
    simp

@[simp] lemma comp_toPath_eq_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    p.comp e.toPath = p.cons e :=
  rfl

end Decomposition

/-- Turn a path into a list. The list contains `a` at its head, but not `b` a priori. -/
@[simp]
def toList : ∀ {b : V}, Path a b → List V
  | _, nil => []
  | _, @cons _ _ _ c _ p _ => c :: p.toList

/-- `Quiver.Path.toList` is a contravariant functor. The inversion comes from `Quiver.Path` and
`List` having different preferred directions for adding elements. -/
@[simp]
theorem toList_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).toList = q.toList ++ p.toList
  | _, nil => by simp
  | _, @cons _ _ _ d _ q _ => by simp [toList_comp]

theorem isChain_toList_nonempty :
    ∀ {b} (p : Path a b), (p.toList).IsChain (fun x y => Nonempty (y ⟶ x))
  | _, nil => .nil
  | _, cons nil _ => .singleton _
  | _, cons (cons p g) _ => List.IsChain.cons_cons ⟨g⟩ (isChain_toList_nonempty (cons p g))

theorem isChain_cons_toList_nonempty :
    ∀ {b} (p : Path a b), (b :: p.toList).IsChain (fun x y => Nonempty (y ⟶ x))
  | _, nil => .singleton _
  | _, cons p f => p.isChain_cons_toList_nonempty.cons_cons ⟨f⟩

variable [∀ a b : V, Subsingleton (a ⟶ b)]

theorem toList_injective (a : V) : ∀ b, Injective (toList : Path a b → List V)
  | _, nil, nil, _ => rfl
  | _, nil, @cons _ _ _ c _ p f, h => by cases h
  | _, @cons _ _ _ c _ p f, nil, h => by cases h
  | _, @cons _ _ _ c _ p f, @cons _ _ _ t _ C D, h => by
    simp only [toList, List.cons.injEq] at h
    obtain ⟨rfl, hAC⟩ := h
    simp [toList_injective _ _ hAC, eq_iff_true_of_subsingleton]

@[simp]
theorem toList_inj {p q : Path a b} : p.toList = q.toList ↔ p = q :=
  (toList_injective _ _).eq_iff


section BoundedPath

variable {V : Type*} [Quiver V]

/-- A bounded path is a path with a uniform bound on its length. -/
def BoundedPaths (v w : V) (n : ℕ) : Sort _ :=
  { p : Path v w // p.length ≤ n }

/-- Bounded paths of length zero between two vertices form a subsingleton. -/
instance instSubsingletonBddPaths (v w : V) : Subsingleton (BoundedPaths v w 0) where
  allEq := fun ⟨p, hp⟩ ⟨q, hq⟩ =>
    match v, w, p, q with
    | _, _, .nil, .nil => rfl
    | _, _, .cons _ _, _ => by simp [Quiver.Path.length] at hp
    | _, _, _, .cons _ _ => by simp [Quiver.Path.length] at hq

/-- Bounded paths of length zero between two vertices have decidable equality. -/
def decidableEqBddPathsZero (v w : V) : DecidableEq (BoundedPaths v w 0) :=
  fun _ _ => isTrue <| Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- Given decidable equality on paths of length up to `n`, we can construct
decidable equality on paths of length up to `n + 1`. -/
def decidableEqBddPathsOfDecidableEq (n : ℕ) (h₁ : DecidableEq V)
    (h₂ : ∀ (v w : V), DecidableEq (v ⟶ w)) (h₃ : ∀ (v w : V), DecidableEq (BoundedPaths v w n))
    (v w : V) : DecidableEq (BoundedPaths v w (n + 1)) :=
  fun ⟨p, hp⟩ ⟨q, hq⟩ =>
    match v, w, p, q with
    | _, _, .nil, .nil => isTrue rfl
    | _, _, .nil, .cons _ _
    | _, _, .cons _ _, .nil =>
      isFalse fun h => Quiver.Path.noConfusion rfl .rfl .rfl .rfl (heq_of_eq (Subtype.mk.inj h))
    | _, _, .cons (b := v') p' α, .cons (b := v'') q' β =>
      match v', v'', h₁ v' v'' with
      | _, _, isTrue (Eq.refl _) =>
        if h : α = β then
          have hp' : p'.length ≤ n := by simp [Quiver.Path.length] at hp; lia
          have hq' : q'.length ≤ n := by simp [Quiver.Path.length] at hq; lia
          if h'' : (⟨p', hp'⟩ : BoundedPaths _ _ n) = ⟨q', hq'⟩ then
            isTrue <| by
              apply Subtype.ext
              dsimp
              rw [h, show p' = q' from Subtype.mk.inj h'']
          else
            isFalse fun h =>
              h'' <| Subtype.ext <| eq_of_heq <| (Quiver.Path.cons.inj <| Subtype.mk.inj h).2.1
        else
          isFalse fun h' =>
            h <| eq_of_heq (Quiver.Path.cons.inj <| Subtype.mk.inj h').2.2
      | _, _, isFalse h => isFalse fun h' =>
        h (Quiver.Path.cons.inj <| Subtype.mk.inj h').1

/-- Equality is decidable on all uniformly bounded paths given decidable
equality on the vertices and the arrows. -/
instance decidableEqBoundedPaths [DecidableEq V] [∀ (v w : V), DecidableEq (v ⟶ w)]
    (n : ℕ) : (v w : V) → DecidableEq (BoundedPaths v w n) :=
  n.rec decidableEqBddPathsZero
    fun n decEq => decidableEqBddPathsOfDecidableEq n inferInstance inferInstance decEq

/-- Equality is decidable on paths in a quiver given decidable equality on the vertices and
arrows. -/
instance instDecidableEq [DecidableEq V] [∀ (v w : V), DecidableEq (v ⟶ w)] :
    (v w : V) → DecidableEq (Path v w) := fun v w p q =>
  let m := max p.length q.length
  let p' : BoundedPaths v w m := ⟨p, Nat.le_max_left ..⟩
  let q' : BoundedPaths v w m := ⟨q, Nat.le_max_right ..⟩
  decidable_of_iff (p' = q') Subtype.ext_iff

end BoundedPath

end Path

end Quiver

namespace Prefunctor

open Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] (F : V ⥤q W)

/-- The image of a path under a prefunctor. -/
def mapPath {a : V} : ∀ {b : V}, Path a b → Path (F.obj a) (F.obj b)
  | _, Path.nil => Path.nil
  | _, Path.cons p e => Path.cons (mapPath p) (F.map e)

@[simp]
theorem mapPath_nil (a : V) : F.mapPath (Path.nil : Path a a) = Path.nil :=
  rfl

@[simp]
theorem mapPath_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    F.mapPath (Path.cons p e) = Path.cons (F.mapPath p) (F.map e) :=
  rfl

@[simp]
theorem mapPath_comp {a b : V} (p : Path a b) :
    ∀ {c : V} (q : Path b c), F.mapPath (p.comp q) = (F.mapPath p).comp (F.mapPath q)
  | _, Path.nil => rfl
  | c, Path.cons q e => by dsimp; rw [mapPath_comp p q]

@[simp]
theorem mapPath_toPath {a b : V} (f : a ⟶ b) : F.mapPath f.toPath = (F.map f).toPath :=
  rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
theorem mapPath_id {a b : V} : (p : Path a b) → (𝟭q V).mapPath p = p
  | Path.nil => rfl
  | Path.cons q e => by dsimp; rw [mapPath_id q]

variable {U : Type u₃} [Quiver.{v₃} U] (G : W ⥤q U)

set_option backward.defeqAttrib.useBackward true in
@[simp]
theorem mapPath_comp_apply {a b : V} (p : Path a b) :
    (F ⋙q G).mapPath p = G.mapPath (F.mapPath p) := by
  induction p with
  | nil => rfl
  | cons x y h => simp [h]

end Prefunctor
