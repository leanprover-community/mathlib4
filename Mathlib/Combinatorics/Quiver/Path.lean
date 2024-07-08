/-
Copyright (c) 2021 David Wärn,. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison
-/
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Logic.Lemmas

#align_import combinatorics.quiver.path from "leanprover-community/mathlib"@"18a5306c091183ac90884daa9373fa3b178e8607"

/-!
# Paths in quivers

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.
-/

open Function

universe v v₁ v₂ u u₁ u₂

namespace Quiver

/-- `Path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive Path {V : Type u} [Quiver.{v} V] (a : V) : V → Sort max (u + 1) v
  | nil : Path a a
  | cons : ∀ {b c : V}, Path a b → (b ⟶ c) → Path a c
#align quiver.path Quiver.Path

-- See issue lean4#2049
compile_inductive% Path

/-- An arrow viewed as a path of length one. -/
def Hom.toPath {V} [Quiver V] {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e
#align quiver.hom.to_path Quiver.Hom.toPath

namespace Path

variable {V : Type u} [Quiver V] {a b c d : V}

lemma nil_ne_cons (p : Path a b) (e : b ⟶ a) : Path.nil ≠ p.cons e :=
  fun h => by injection h
#align quiver.path.nil_ne_cons Quiver.Path.nil_ne_cons

lemma cons_ne_nil (p : Path a b) (e : b ⟶ a) : p.cons e ≠ Path.nil :=
  fun h => by injection h
#align quiver.path.cons_ne_nil Quiver.Path.cons_ne_nil

lemma obj_eq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : b = c := by injection h
#align quiver.path.obj_eq_of_cons_eq_cons Quiver.Path.obj_eq_of_cons_eq_cons

lemma heq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : HEq p p' := by injection h
#align quiver.path.heq_of_cons_eq_cons Quiver.Path.heq_of_cons_eq_cons

lemma hom_heq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : HEq e e' := by injection h
#align quiver.path.hom_heq_of_cons_eq_cons Quiver.Path.hom_heq_of_cons_eq_cons

/-- The length of a path is the number of arrows it uses. -/
def length {a : V} : ∀ {b : V}, Path a b → ℕ
  | _, nil => 0
  | _, cons p _ => p.length + 1
#align quiver.path.length Quiver.Path.length

instance {a : V} : Inhabited (Path a a) :=
  ⟨nil⟩

@[simp]
theorem length_nil {a : V} : (nil : Path a a).length = 0 :=
  rfl
#align quiver.path.length_nil Quiver.Path.length_nil

@[simp]
theorem length_cons (a b c : V) (p : Path a b) (e : b ⟶ c) : (p.cons e).length = p.length + 1 :=
  rfl
#align quiver.path.length_cons Quiver.Path.length_cons

theorem eq_of_length_zero (p : Path a b) (hzero : p.length = 0) : a = b := by
  cases p
  · rfl
  · cases Nat.succ_ne_zero _ hzero
#align quiver.path.eq_of_length_zero Quiver.Path.eq_of_length_zero

/-- Composition of paths. -/
def comp {a b : V} : ∀ {c}, Path a b → Path b c → Path a c
  | _, p, nil => p
  | _, p, cons q e => (p.comp q).cons e
#align quiver.path.comp Quiver.Path.comp

@[simp]
theorem comp_cons {a b c d : V} (p : Path a b) (q : Path b c) (e : c ⟶ d) :
    p.comp (q.cons e) = (p.comp q).cons e :=
  rfl
#align quiver.path.comp_cons Quiver.Path.comp_cons

@[simp]
theorem comp_nil {a b : V} (p : Path a b) : p.comp Path.nil = p :=
  rfl
#align quiver.path.comp_nil Quiver.Path.comp_nil

@[simp]
theorem nil_comp {a : V} : ∀ {b} (p : Path a b), Path.nil.comp p = p
  | _, nil => rfl
  | _, cons p _ => by rw [comp_cons, nil_comp p]
#align quiver.path.nil_comp Quiver.Path.nil_comp

@[simp]
theorem comp_assoc {a b c : V} :
    ∀ {d} (p : Path a b) (q : Path b c) (r : Path c d), (p.comp q).comp r = p.comp (q.comp r)
  | _, _, _, nil => rfl
  | _, p, q, cons r _ => by rw [comp_cons, comp_cons, comp_cons, comp_assoc p q r]
#align quiver.path.comp_assoc Quiver.Path.comp_assoc

@[simp]
theorem length_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).length = p.length + q.length
  | _, nil => rfl
  | _, cons _ _ => congr_arg Nat.succ (length_comp _ _)
#align quiver.path.length_comp Quiver.Path.length_comp

theorem comp_inj {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (hq : q₁.length = q₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  induction' q₁ with d₁ e₁ q₁ f₁ ih <;> obtain _ | ⟨q₂, f₂⟩ := q₂
  · exact ⟨h, rfl⟩
  · cases hq
  · cases hq
  · simp only [comp_cons, cons.injEq] at h
    obtain rfl := h.1
    obtain ⟨rfl, rfl⟩ := ih (Nat.succ.inj hq) h.2.1.eq
    rw [h.2.2.eq]
    exact ⟨rfl, rfl⟩
#align quiver.path.comp_inj Quiver.Path.comp_inj

theorem comp_inj' {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (h : p₁.length = p₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
  ⟨fun h_eq => (comp_inj <| Nat.add_left_cancel <| by simpa [h] using congr_arg length h_eq).1 h_eq,
   by rintro ⟨rfl, rfl⟩; rfl⟩
#align quiver.path.comp_inj' Quiver.Path.comp_inj'

theorem comp_injective_left (q : Path b c) : Injective fun p : Path a b => p.comp q :=
  fun _ _ h => ((comp_inj rfl).1 h).1
#align quiver.path.comp_injective_left Quiver.Path.comp_injective_left

theorem comp_injective_right (p : Path a b) : Injective (p.comp : Path b c → Path a c) :=
  fun _ _ h => ((comp_inj' rfl).1 h).2
#align quiver.path.comp_injective_right Quiver.Path.comp_injective_right

@[simp]
theorem comp_inj_left {p₁ p₂ : Path a b} {q : Path b c} : p₁.comp q = p₂.comp q ↔ p₁ = p₂ :=
  q.comp_injective_left.eq_iff
#align quiver.path.comp_inj_left Quiver.Path.comp_inj_left

@[simp]
theorem comp_inj_right {p : Path a b} {q₁ q₂ : Path b c} : p.comp q₁ = p.comp q₂ ↔ q₁ = q₂ :=
  p.comp_injective_right.eq_iff
#align quiver.path.comp_inj_right Quiver.Path.comp_inj_right

/-- Turn a path into a list. The list contains `a` at its head, but not `b` a priori. -/
@[simp]
def toList : ∀ {b : V}, Path a b → List V
  | _, nil => []
  | _, @cons _ _ _ c _ p _ => c :: p.toList
#align quiver.path.to_list Quiver.Path.toList

/-- `Quiver.Path.toList` is a contravariant functor. The inversion comes from `Quiver.Path` and
`List` having different preferred directions for adding elements. -/
@[simp]
theorem toList_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).toList = q.toList ++ p.toList
  | _, nil => by simp
  | _, @cons _ _ _ d _ q _ => by simp [toList_comp]
#align quiver.path.to_list_comp Quiver.Path.toList_comp

theorem toList_chain_nonempty :
    ∀ {b} (p : Path a b), p.toList.Chain (fun x y => Nonempty (y ⟶ x)) b
  | _, nil => List.Chain.nil
  | _, cons p f => p.toList_chain_nonempty.cons ⟨f⟩
#align quiver.path.to_list_chain_nonempty Quiver.Path.toList_chain_nonempty

variable [∀ a b : V, Subsingleton (a ⟶ b)]

theorem toList_injective (a : V) : ∀ b, Injective (toList : Path a b → List V)
  | _, nil, nil, _ => rfl
  | _, nil, @cons _ _ _ c _ p f, h => by cases h
  | _, @cons _ _ _ c _ p f, nil, h => by cases h
  | _, @cons _ _ _ c _ p f, @cons _ _ _ t _ C D, h => by
    simp only [toList, List.cons.injEq] at h
    obtain ⟨rfl, hAC⟩ := h
    simp [toList_injective _ _ hAC, eq_iff_true_of_subsingleton]
#align quiver.path.to_list_injective Quiver.Path.toList_injective

@[simp]
theorem toList_inj {p q : Path a b} : p.toList = q.toList ↔ p = q :=
  (toList_injective _ _).eq_iff
#align quiver.path.to_list_inj Quiver.Path.toList_inj

end Path

end Quiver

namespace Prefunctor

open Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] (F : V ⥤q W)

/-- The image of a path under a prefunctor. -/
def mapPath {a : V} : ∀ {b : V}, Path a b → Path (F.obj a) (F.obj b)
  | _, Path.nil => Path.nil
  | _, Path.cons p e => Path.cons (mapPath p) (F.map e)
#align prefunctor.map_path Prefunctor.mapPath

@[simp]
theorem mapPath_nil (a : V) : F.mapPath (Path.nil : Path a a) = Path.nil :=
  rfl
#align prefunctor.map_path_nil Prefunctor.mapPath_nil

@[simp]
theorem mapPath_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    F.mapPath (Path.cons p e) = Path.cons (F.mapPath p) (F.map e) :=
  rfl
#align prefunctor.map_path_cons Prefunctor.mapPath_cons

@[simp]
theorem mapPath_comp {a b : V} (p : Path a b) :
    ∀ {c : V} (q : Path b c), F.mapPath (p.comp q) = (F.mapPath p).comp (F.mapPath q)
  | _, Path.nil => rfl
  | c, Path.cons q e => by dsimp; rw [mapPath_comp p q]
#align prefunctor.map_path_comp Prefunctor.mapPath_comp

@[simp]
theorem mapPath_toPath {a b : V} (f : a ⟶ b) : F.mapPath f.toPath = (F.map f).toPath :=
  rfl
#align prefunctor.map_path_to_path Prefunctor.mapPath_toPath

end Prefunctor
