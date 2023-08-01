/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ShortExact.Abelian
import Mathlib.Data.List.MinMax
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Topology.Separation
import Mathlib.Topology.Connected

/-!

# Nöbeling's theorem

This file proves Nöbeling's theorem,

## Main result

- `Nobeling`: For `S : Profinite`, the ℤ-module `LocallyConstant S ℤ` is free.

## Implementation Details

We follow the proof of theorem 5.4 in [scholze2019condensed], ordinal induction, etc.

**TODO:** Write more details here.

## References

- [scholze2019condensed]: *Lectures on Condensed Mathematics*, 2019.

-/

universe u

section Scott
-- This section is PR #6278

variable (α : Type _) [LinearOrder α]

lemma Antitone.eventually_constant [wfa : WellFoundedLT α] (f : ℕ → α) (h : Antitone f) :
    ∃ N a, ∀ n, N ≤ n → f n = a := by
  let a := WellFounded.min ((IsWellFounded_iff α (·<·)).mp inferInstance)
    (Set.range f) (Set.range_nonempty f)
  have ha : (f ⁻¹' {a}).Nonempty
  · refine Iff.mpr Set.preimage_singleton_nonempty ?_
    exact WellFounded.min_mem _ (Set.range f) (Set.range_nonempty f)
  let N := ha.choose
  refine' ⟨N, a, _⟩
  intro n hn
  rw [← ha.choose_spec]
  refine' eq_of_le_of_not_lt (h hn) _
  rw [ha.choose_spec]
  exact WellFounded.not_lt_min _ _ _ (Set.mem_range_self n)

theorem wellFoundedLT_iff_not_strictAnti : WellFoundedLT α ↔ ∀ f : ℕ → α, ¬ StrictAnti f := by
  dsimp [WellFoundedLT]
  rw [IsWellFounded_iff, RelEmbedding.wellFounded_iff_no_descending_seq]
  constructor
  <;> intro h
  · intro f hf
    rw [isEmpty_iff] at h
    apply h
    refine' ⟨⟨f, hf.injective⟩,_⟩
    intro a b
    refine' ⟨_, fun h ↦ hf h⟩
    intro hfab
    dsimp at hfab
    by_contra hab
    simp only [gt_iff_lt, not_lt] at hab
    have := hf.antitone hab
    rw [← not_lt] at this
    exact this hfab
  · rw [isEmpty_iff]
    intro f
    apply h f.toEmbedding
    intro a b hab
    rwa [f.map_rel_iff']

variable {α}

@[simp] theorem List.cons_lt (a : α) (x y : List α) : a :: x < a :: y ↔ x < y := by
  constructor
  · intro h
    cases h
    case cons h =>
      exact h
    case rel h =>
      simp at h
  · intro h
    apply Lex.cons h

@[simp] theorem List.append_lt (x y z : List α) : x ++ y < x ++ z ↔ y < z := by
  induction x
  · case nil => rfl
  · case cons h t ih =>
      simpa

@[simp]
theorem List.head?_isNone_iff (l : List α) : l.head?.isNone ↔ l = [] := by cases l <;> simp

@[simp] theorem List.lt_nil_iff (l : List α) : ¬ l < [] := by
  cases l
  · simp
  · exact of_decide_eq_false rfl

theorem List.take_one_eq_singleton_iff (l : List α) (a : α) :
    l.take 1 = [a] ↔ l.head? = some a := by
  cases l <;> simp

theorem Option.get?_eq_some (o : Option α) (w : o.isSome) (a : α) : o.get w = a ↔ o = some a := by
  cases o
  · simp at w
  · simp

theorem List.maximum_of_length_pos_mem (l : List α) (h : 0 < l.length) :
    l.maximum_of_length_pos h ∈ l := by
  apply maximum_mem
  simp

theorem List.exists_mem_eq_maximum_of_length_pos (l : List α) (h : 0 < l.length) :
    ∃ a, a ∈ l ∧ a = l.maximum_of_length_pos h := by
  simp only [exists_eq_right]
  exact maximum_of_length_pos_mem l h

theorem List.some_get_eq_get? (l : List α) (x : Fin l.length) : some (l.get x) = l.get? x.1 := by
  rw [List.get?_eq_get]

theorem List.get_eq_get_of_take_eq_take (la lb : List α) (n m : ℕ)
    (ha : n < la.length) (hb : n < lb.length) (lt : n < m) (w : la.take m = lb.take m) :
    la.get ⟨n, ha⟩ = lb.get ⟨n, hb⟩ := by
  rw [List.get_eq_iff]
  simp only [some_get_eq_get?]
  rw [← List.take_append_drop m la, ← List.take_append_drop m lb]
  rw [List.get?_append, List.get?_append, w]
  · aesop
  · aesop

/--
Constructs the smallest monotone function larger than a given function,
defined by `leastOrderHom f n = [f 0, f 1, ..., f n].maximum_of_length_pos (by simp)`.
-/
-- One could prove `leastOrderHom_le (f : ℕ → α) (g : ℕ →o α) (w : f ≤ g) : leastOrderHom f ≤ g`,
-- and that this is a Galois connection.
-- One could generalize from `ℕ` to any `LocallyFiniteOrderBot`.
def leastOrderHom (f : ℕ → α) : ℕ →o α where
  toFun n := (List.range (n + 1)).map f |>.maximum_of_length_pos (by simp)
  monotone' n m h := by
    apply List.le_maximum_of_length_pos_of_mem
    dsimp
    obtain ⟨a, m, w⟩ :=
      List.exists_mem_eq_maximum_of_length_pos ((List.range (n + 1)).map f) (by simp)
    rw [← w]
    simp at m
    obtain ⟨b, w', rfl⟩ := m
    simp only [List.mem_map, List.mem_range]
    exact ⟨b, (lt_of_lt_of_le w' (Nat.add_le_add_right h 1)), rfl⟩

theorem le_leastOrderHom (f : ℕ → α) : f ≤ leastOrderHom f := by
  intro n
  dsimp [leastOrderHom]
  apply List.le_maximum_of_length_pos_of_mem
  simp only [List.mem_map, List.mem_range]
  exact ⟨n, Nat.lt_succ_self _, rfl⟩

namespace wellFoundedLT_sorted

variable (α)
variable [WellFoundedLT α]

def IncreasingList := { l : List α // l.Sorted (· > · ) }

instance : LinearOrder (IncreasingList α) := inferInstanceAs <| LinearOrder { _l : List α // _ }

@[simp] lemma IncreasingList.lt_iff (x y : IncreasingList α) : x < y ↔ x.1 < y.1 := Iff.rfl

def SDS := { f : ℕ → IncreasingList α // StrictAnti f }

variable {α}

def Q (n : ℕ) (L : SDS α) :=
  Σ' N, Σ' S : List α, S.length = n ∧ ∀ (m), N ≤ m → (L.1 m).1.take n = S

def P (L : SDS α) := ∀ n, Q n L

def IncreasingList.drop (l : IncreasingList α) (m : ℕ) : IncreasingList α :=
  ⟨l.1.drop m, l.2.drop⟩

def SDS.drop₁ (L : SDS α) (m : ℕ) : SDS α :=
  ⟨fun n => L.1 (n + m), fun _ _ h => L.2 (Nat.add_lt_add_right h m)⟩

def SDS.drop₂ (L : SDS α) (S : List α) (m : ℕ) (w : ∀ n, (L.1 n).1.take m = S) : SDS α :=
  ⟨fun n => (L.1 n).drop m, by
    intro a b h
    have := L.2 h
    change (L.1 b).1 < (L.1 a).1 at this
    rw [← List.take_append_drop m (L.1 a).1, ← List.take_append_drop m (L.1 b).1, w, w] at this
    simpa using this⟩

def SDS.dropQ (n : ℕ) (L : SDS α) (w : Q n L) : SDS α := by
  obtain ⟨N, S, w⟩ := w
  refine (L.drop₁ N).drop₂ S n ?_
  intro m
  exact (w.2 (m + N) (Nat.le_add_left N m))

theorem SDS.dropQ_apply (n m : ℕ) (L : SDS α) (w : Q n L) :
    ((L.dropQ n w).1 m).1 = (L.1 (m + w.1)).1.drop n :=
  rfl

variable {L : SDS α}

theorem Q_succ (n : ℕ) (L : SDS α) (w' : Q n L) (w₁ : Q 1 (L.dropQ n w')) : Q (n+1) L := by
  obtain ⟨N', S', s', w'⟩ := w'
  obtain ⟨N₁, S₁, s₁, w₁⟩ := w₁
  use N' + N₁
  use S' ++ S₁
  constructor
  · simp [s', s₁]
  intro m h
  specialize w' m (le_of_add_le_left h)
  specialize w₁ (m - N') (le_tsub_of_add_le_left h)
  simp only [SDS.dropQ_apply] at w₁
  rw [Nat.sub_add_cancel (le_of_add_le_left h)] at w₁
  rw [List.take_add]
  rw [w', w₁]

def SDS.head? (L : SDS α) : ℕ → Option α := fun n => (L.1 n).1.head?

lemma SDS.head?_isSome (L : SDS α) (n : ℕ) : (L.head? n).isSome := by
  by_contra h
  simp [SDS.head?] at h
  have := L.2 (Nat.lt_succ_self n)
  simp [h] at this

def SDS.head (L : SDS α) : ℕ → α := fun n => (L.head? n).get (L.head?_isSome n)

lemma aux (l₁ l₂ : List α) (h₁ : l₁.head?.isSome) (h₂ : l₂.head?.isSome) : l₁ < l₂ →
    l₁.head?.get h₁ ≤ l₂.head?.get h₂ := by
  match l₁, h₁, l₂, h₂ with
  | x₁ :: t₁, _, x₂ :: t₂, _ =>
    intro h
    cases h
    case cons => rfl
    case rel h =>
      exact h.le

lemma SDS.head_antitone (L : SDS α) : Antitone L.head := by
  intro a b h
  rcases lt_or_eq_of_le h with (h | rfl)
  · have := L.2 h
    simp [SDS.head, SDS.head?]
    apply aux _ _ _ _ this
  · rfl

lemma SDS.head_eventually_constant (L : SDS α) : ∃ N a, ∀ n, N ≤ n → L.head n = a :=
  Antitone.eventually_constant α _ L.head_antitone

theorem Q_one : Nonempty (Q 1 L) := by
  obtain ⟨N, a, w⟩ := L.head_eventually_constant
  apply Nonempty.intro
  use N
  use [a]
  use rfl
  intro m h
  specialize w m h
  simp [SDS.head, SDS.head?, Option.get?_eq_some] at w
  simpa [List.take_one_eq_singleton_iff]

theorem main (L : SDS α) : P L := by
  intro n
  apply Nonempty.some
  induction n using Nat.strong_induction_on generalizing L
  case h n a =>
    cases n
    case zero =>
      use 0
      use []
      use rfl
      intro m _
      simp
    case succ n =>
      cases n
      case zero =>
        apply Q_one
      case succ n =>
        apply Nonempty.intro
        apply Q_succ
        · apply Nonempty.some
          apply a
          exact Nat.one_lt_succ_succ n
        · apply Nonempty.some
          apply a
          exact Nat.lt_succ_self _

def P' (L : SDS α) :=
  ∃ g : ℕ →o ℕ, ∀ n, ∃ S : List α, S.length = n ∧ ∀ (m), g n ≤ m → (L.1 m).1.take n = S

theorem main' (L : SDS α) : P' L := by
  let this := main L
  use leastOrderHom fun n => (this n).1
  intro n
  use (this n).2.1
  use (this n).2.2.1
  intro m h
  apply (this n).2.2.2
  exact (le_leastOrderHom _ _).trans h

def P'' (L : SDS α) :=
  ∃ g : ℕ →o ℕ, ∀ (n : ℕ), ∀ (m₁ : ℕ), g n ≤ m₁ → n ≤ (L.1 m₁).1.length ∧
    ∀ m₂, g n ≤ m₂ → ∀ x, x < n → (h₁ : _) → (h₂ : _) →
      (L.1 m₁).1.get ⟨x, h₁⟩ = (L.1 m₂).1.get ⟨x, h₂⟩

theorem main'' (L : SDS α) : P'' L := by
  obtain ⟨g, w⟩ := main' L
  use g
  intro n m₁ mh₁
  constructor
  · obtain ⟨S, s, w⟩ := w n
    specialize w m₁ mh₁
    rw [←List.take_append_drop n (L.1 m₁).1]
    simp [s, w]
  · intro m₂ mh₂ x lt h₁ h₂
    obtain ⟨S, _, w⟩ := w n
    have w₁ := w m₁ mh₁
    have w₂ := w m₂ mh₂
    apply List.get_eq_get_of_take_eq_take _ _ _ _ _ _ lt
    simp [w₁, w₂]

end wellFoundedLT_sorted

open wellFoundedLT_sorted

instance wellFoundedLT_sorted [WellFoundedLT α] :
    WellFoundedLT { l : List α // l.Sorted (· > · ) } :=
  (wellFoundedLT_iff_not_strictAnti _).mpr (fun f w => by
    obtain ⟨g, h⟩ := main'' ⟨f, w⟩
    have lt_length : ∀ n, n < (f (g (n + 1))).1.length :=
      fun n => lt_of_lt_of_le (Nat.lt_succ_self n) (h (n + 1) (g (n + 1)) (le_refl _)).1
    let z : ℕ → α := fun n => (f (g (n + 1))).1.get ⟨n, lt_length n⟩
    apply (wellFoundedLT_iff_not_strictAnti α).mp ‹_› z
    intro a b lt
    calc
      z b = (f (g (b + 1))).1.get ⟨b, lt_length b⟩ := rfl
      _   < (f (g (b + 1))).1.get ⟨a, lt.trans (lt_length _)⟩ :=
              List.pairwise_iff_get.mp (f (g (b + 1))).2 _ _ lt
      _   = (f (g (a + 1))).1.get ⟨a, lt_length a⟩ :=
              ((h (a + 1) (g (a + 1)) (le_refl _)).2
                (g (b + 1)) (g.2 (Nat.succ_le_succ lt.le)) a (Nat.lt_succ_self _) _ _).symm
      _   = z a := rfl)

end Scott

namespace ModuleCat

variable {I : Type _} {J : Type _} {R : Type _} [Ring R] {N P : ModuleCat R} {v : I → N} {w : J → P}

open CategoryTheory
open CategoryTheory.Limits

section LinearIndependent

variable (hv : LinearIndependent R v) (hw : LinearIndependent R w)

variable {M : ModuleCat R} {u : I ⊕ J → M} (hu : Function.Injective u) {f : N ⟶ M}
  {g : M ⟶ P} (hse : Mono f ∧ Exact f g) (huv : u ∘ Sum.inl = f ∘ v) (huw : g ∘ u ∘ Sum.inr = w)

lemma linearIndependent_leftExact : LinearIndependent R u := by
  rw [linearIndependent_sum]
  refine' ⟨_,_,_⟩
  · rw [huv]
    refine' (LinearMap.linearIndependent_iff (f : N →ₗ[R] M) _).mpr hv
    rw [LinearMap.ker_eq_bot]
    rw [← mono_iff_injective]
    exact hse.1
  · rw [← huw] at hw
    refine' LinearIndependent.of_comp g _
    exact hw
  · rw [huv]
    have he := hse.2
    rw [exact_iff] at he
    rw [Submodule.disjoint_def]
    intro m hml hmr
    have hm : m ∈ Submodule.span R (Set.range f) :=
      Submodule.span_mono (Set.range_comp_subset_range v f) hml
    have h₁ : Set.range f ⊆ LinearMap.range f
    · rw [LinearMap.range_coe]
    have h₂ : LinearMap.range f ≤ Submodule.span R (Set.range f)
    · intro x hx
      exact Submodule.subset_span hx
    rw [Submodule.span_eq_of_le (LinearMap.range f) h₁ h₂, he] at hm
    simp only [LinearMap.mem_ker] at hm
    rw [mem_span_set] at hmr
    obtain ⟨c, ⟨hc, hsum⟩⟩ := hmr
    rw [← hsum, map_finsupp_sum] at hm
    simp only [map_smul] at hm
    rw [linearIndependent_iff'] at hw
    have hui : Function.Injective (u ∘ Sum.inr) := Function.Injective.comp hu Sum.inr_injective
    specialize hw (Finset.preimage c.support (u ∘ Sum.inr) (Set.injOn_of_injective hui _))
    dsimp [Finsupp.sum] at hm
    rw [← Finset.sum_preimage (u ∘ Sum.inr) c.support (Set.injOn_of_injective hui _) _ _] at hm
    · rw [← huw] at hw
      specialize hw (c ∘ u ∘ Sum.inr) hm
      dsimp [Finsupp.sum] at hsum
      rw [← hsum]
      apply Finset.sum_eq_zero
      intro x hx
      obtain ⟨y,hy⟩ := hc hx
      specialize hw y
      rw [← hy]
      suffices : (c ∘ u ∘ Sum.inr) y = 0
      · dsimp at this ⊢
        rw [this]
        simp only [zero_smul]
      apply hw
      simp only [Finset.mem_preimage, Function.comp_apply]
      dsimp at hy
      rwa [hy]
    · intro x hx hnx
      exfalso
      exact hnx (hc hx)

end LinearIndependent

end ModuleCat

namespace Function

open Classical

noncomputable
def ExtendBy {X Y : Type _} {C : Set X} (f : {i // i ∈ C} → Y) (junk : Y) : X → Y :=
fun x ↦ if hx : x ∈ C then f ⟨x, hx⟩ else junk

lemma restrict_extendBy_eq_self {X Y : Type _} {C : Set X} (f : {i // i ∈ C} → Y) (junk : Y) :
    C.restrict (f.ExtendBy junk) = f := by
  ext x
  dsimp [ExtendBy]
  simp only [Subtype.coe_prop, Subtype.coe_eta, dite_eq_ite, ite_true]

lemma extendBy_preimage_of_junk_ne_mem {X Y : Type _} {C : Set X} (f : {i // i ∈ C} → Y) (junk : Y)
    (s : Set Y) (hj : ¬ junk ∈ s) : (f.ExtendBy junk) ⁻¹' s = Subtype.val '' (f ⁻¹' s) := by
  ext x
  dsimp [ExtendBy]
  simp only [Set.mem_preimage, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  constructor
  <;> intro hx
  · split_ifs at hx with h
    · use h
    · exfalso
      exact hj hx
  · obtain ⟨hx,hfx⟩ := hx
    split_ifs
    exact hfx

lemma extendBy_preimage_of_junk_mem {X Y : Type _} {C : Set X} (f : {i // i ∈ C} → Y) (junk : Y)
    (s : Set Y) (hj : junk ∈ s) : (f.ExtendBy junk) ⁻¹' s = Subtype.val '' (f ⁻¹' s) ∪ Cᶜ := by
  ext x
  dsimp [ExtendBy]
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, Set.mem_compl_iff]
  constructor
  <;> intro hx
  · split_ifs at hx with h
    · left
      use h
    · right
      exact h
  · obtain ⟨hx,hfx⟩ := hx
    split_ifs
    · exact hfx
    · split_ifs
      assumption

end Function

namespace Set

open Classical

noncomputable
def piecewise' {X Y : Type _} {C : Set X} {p : X → Prop} (f : {i // i ∈ C} → Y)
    (g : (Subtype p) → Y) (junk : Y) : X → Y := C.piecewise (f.ExtendBy junk) (g.ExtendBy junk)

end Set

namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {Z : Type _}

theorem comap_comp_apply {α : Type _} [TopologicalSpace Z] (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) :
  ∀ (x : LocallyConstant Z α), comap f (comap g x) = comap (g ∘ f) x := by
  intro x
  rw [← comap_comp f g hf hg]
  rfl

noncomputable
def equiv (e : X ≃ₜ Y) : LocallyConstant X Z ≃ LocallyConstant Y Z :=
{ toFun := comap e.invFun
  invFun := comap e.toFun
  left_inv := by
    intro x
    rw [comap_comp_apply _ _ e.continuous_toFun e.continuous_invFun x]
    simp
  right_inv := by
    intro x
    rw [comap_comp_apply _ _ e.continuous_invFun e.continuous_toFun]
    simp }

@[simp]
theorem coe_comap_apply (f : X → Y) (g : LocallyConstant Y Z) (hf : Continuous f) :
    ∀ x, comap f g x = g (f x) := by
  intro x
  rw [← @Function.comp_apply _ _ _ g f x]
  rw [← coe_comap _ _ hf]

lemma comap_injective (f : X → Y) (hf: Continuous f)
    (hfs : Function.Surjective f) : Function.Injective
    ((LocallyConstant.comap f) : (LocallyConstant Y Z) → (LocallyConstant X Z)) := by
  intro a b h
  rw [LocallyConstant.ext_iff] at h
  ext y
  obtain ⟨x, hx⟩ := hfs y
  specialize h x
  rw [coe_comap_apply _ _ hf] at h
  rw [coe_comap_apply _ _ hf] at h
  rw [← hx]
  assumption

lemma isLocallyConstant_sum_elim {f : X → Z} {g : Y → Z} (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) : IsLocallyConstant (Sum.elim f g) := by
  let dZ : TopologicalSpace Z := ⊥
  haveI : DiscreteTopology Z := discreteTopology_bot Z
  rw [IsLocallyConstant.iff_continuous]
  rw [continuous_sum_elim, ← IsLocallyConstant.iff_continuous, ← IsLocallyConstant.iff_continuous]
  exact ⟨hf,hg⟩

def Sum (f : LocallyConstant X Z) (g : LocallyConstant Y Z) : LocallyConstant (X ⊕ Y) Z :=
{ toFun := Sum.elim f.toFun g.toFun
  isLocallyConstant := isLocallyConstant_sum_elim f.isLocallyConstant g.isLocallyConstant }

noncomputable
def SumEquivProd : LocallyConstant (X ⊕ Y) Z ≃ LocallyConstant X Z × LocallyConstant Y Z :=
{ toFun := fun f ↦ (f.comap Sum.inl, f.comap Sum.inr)
  invFun := fun f ↦ LocallyConstant.Sum f.1 f.2
  left_inv := by
    intro _
    ext x
    dsimp [Sum]
    rw [coe_comap _ _ continuous_inl, coe_comap _ _ continuous_inr]
    cases x
    · dsimp
    · dsimp
  right_inv := by
    intro _
    ext
    · dsimp
      rw [coe_comap_apply _ _ continuous_inl]
      rfl
    · dsimp
      rw [coe_comap_apply _ _ continuous_inr]
      rfl }

lemma closure_compl_subset {C₁ C₂ : Set X} (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ) : closure (C₁ᶜ) ⊆ C₂ := by
  have h' := Set.compl_subset_iff_union.mpr h
  rwa [← h₂.closure_subset_iff] at h'

lemma frontier_subset_inter {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ) : (C₁ ∪ C₂) ∩ (frontier C₁) ⊆ C₁ ∩ C₂ := by
  intro x hx
  rw [h] at hx
  simp only [Set.univ_inter] at hx
  rw [h₁.frontier_eq, Set.diff_eq_compl_inter] at hx
  rw [← @closure_compl _ _ C₁] at hx
  have h' := Set.compl_subset_iff_union.mpr h
  rw [← h₂.closure_subset_iff] at h'
  exact ⟨hx.2, h' hx.1⟩

open Classical

lemma isLocallyConstant_piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ)
    (f : LocallyConstant {i // i ∈ C₁} Z)
    (g : LocallyConstant {i // i ∈ C₂} Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f.toFun ⟨x, hx.1⟩ = g.toFun ⟨x, hx.2⟩)
    (junk : Z) : IsLocallyConstant (C₁.piecewise' f.toFun g.toFun junk) := by
  let dZ : TopologicalSpace Z := ⊥
  haveI : DiscreteTopology Z := discreteTopology_bot Z
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  rw [IsLocallyConstant.iff_continuous] at hf hg ⊢
  dsimp
  rw [continuous_iff_continuousOn_univ]
  rw [← h]
  dsimp [Set.piecewise']
  apply ContinuousOn.piecewise
  · intro x hx
    specialize hfg x (frontier_subset_inter h₁ h₂ h hx)
    dsimp [Function.ExtendBy]
    split_ifs with hh₁ hh₂
    · exact hfg
    · exfalso
      exact hh₂ (frontier_subset_inter h₁ h₂ h hx).2
    · exfalso
      exact hh₁ (frontier_subset_inter h₁ h₂ h hx).1
    · rfl
  · rw [h₁.closure_eq, h]
    simp only [Set.univ_inter]
    rw [continuousOn_iff_continuous_restrict]
    rwa [f.restrict_extendBy_eq_self junk]
  · rw [h]
    simp only [Set.univ_inter]
    apply ContinuousOn.mono _ (closure_compl_subset h₂ h)
    rw [continuousOn_iff_continuous_restrict]
    rwa [g.restrict_extendBy_eq_self junk]

noncomputable
def piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ)
    (f : LocallyConstant {i // i ∈ C₁} Z)
    (g : LocallyConstant {i // i ∈ C₂} Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f.toFun ⟨x, hx.1⟩ = g.toFun ⟨x, hx.2⟩)
    (junk : Z) : LocallyConstant X Z :=
{ toFun := C₁.piecewise' f.toFun g.toFun junk
  isLocallyConstant := isLocallyConstant_piecewise h₁ h₂ h f g hfg junk}

noncomputable
def ExtendBy {C : Set X} (hC : IsClopen C) (f : LocallyConstant {i // i ∈ C} Z) (junk : Z) :
    LocallyConstant X Z :=
{ toFun := f.toFun.ExtendBy junk
  isLocallyConstant := by
    intro s
    by_cases hj : junk ∈ s
    · rw [Function.extendBy_preimage_of_junk_mem _ _ _ hj]
      refine' IsOpen.union _ hC.compl.1
      exact IsOpen.isOpenMap_subtype_val hC.1 (f.toFun ⁻¹' s) (f.isLocallyConstant s)
    · rw [Function.extendBy_preimage_of_junk_ne_mem _ _ _ hj]
      exact IsOpen.isOpenMap_subtype_val hC.1 (f.toFun ⁻¹' s) (f.isLocallyConstant s) }

noncomputable
def emb_lift {e : X → Y} (hoe : OpenEmbedding e) (hce : ClosedEmbedding e)
    (f : LocallyConstant X Z) (junk : Z) : LocallyConstant Y Z :=
  let E : LocallyConstant X Z ≃ LocallyConstant (Set.range e) Z :=
    equiv (Homeomorph.ofEmbedding e hoe.toEmbedding)
  (E f).ExtendBy ⟨hoe.open_range, hce.closed_range⟩ junk

variable {R : Type _} [Ring R] [AddCommMonoid Z] [Module R Z]

noncomputable
def comapLinear (f : X → Y) (hf : Continuous f) : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z :=
{ toFun := comap f
  map_add' := by
    intro r s
    ext x
    simp
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rfl
  map_smul' := by
    intro r s
    dsimp
    ext x
    simp
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rfl }

lemma comapLinear_injective (f : X → Y) (hf : Continuous f) (hfs : Function.Surjective f) :
    LinearMap.ker (comapLinear f hf : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z) = ⊥ := by
  apply LinearMap.ker_eq_bot_of_injective
  dsimp [comapLinear]
  exact comap_injective _ hf hfs

noncomputable
def equivLinear (e : X ≃ₜ Y) : LocallyConstant X Z ≃ₗ[R] LocallyConstant Y Z :=
{ toFun := (equiv e).toFun
  map_smul' := (comapLinear _ e.continuous_invFun).map_smul'
  map_add' := by -- why doesn't (comapLinear _ e.continuous_invFun).map_add' work?
    intro r s
    ext x
    dsimp [equiv]
    have hf : Continuous ↑(e.symm) := e.continuous_invFun
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rw [coe_comap_apply _ _ hf]
    rfl
  invFun := (equiv e).invFun
  left_inv := (equiv e).left_inv
  right_inv := (equiv e).right_inv }

noncomputable
def LinearSumEquivProd :
    LocallyConstant (X ⊕ Y) Z ≃ₗ[R] LocallyConstant X Z × LocallyConstant Y Z :=
{ toFun := SumEquivProd.toFun
  map_smul' := by
    intro r f
    ext x
    · dsimp [SumEquivProd]
      rw [coe_comap _ _ continuous_inl, coe_comap_apply _ _ continuous_inl]
      dsimp
    · dsimp [SumEquivProd]
      rw [coe_comap _ _ continuous_inr, coe_comap_apply _ _ continuous_inr]
      dsimp
  map_add' := by
    intro f g
    ext x
    · dsimp [SumEquivProd]
      rw [coe_comap _ _ continuous_inl, coe_comap_apply _ _ continuous_inl,
        coe_comap_apply _ _ continuous_inl]
      dsimp
    · dsimp [SumEquivProd]
      rw [coe_comap _ _ continuous_inr, coe_comap_apply _ _ continuous_inr,
        coe_comap_apply _ _ continuous_inr]
      dsimp
  invFun := SumEquivProd.invFun
  left_inv := SumEquivProd.left_inv
  right_inv := SumEquivProd.right_inv }

end LocallyConstant

namespace List
namespace Lex

variable {α : Type u} {r : α → α → Prop}

lemma singleton_iff (a b : α) : r a b ↔ List.Lex r [a] [b] := by
  refine' ⟨List.Lex.rel,_⟩
  intro h
  by_contra h'
  cases h
  · apply not_nil_right r []
    assumption
  · apply h'
    assumption

lemma nil_le (l : List α) : List.Lex r [] l ∨ [] = l := by
  induction l with
  | nil =>
    right
    rfl
  | cons a as _ =>
    left
    apply nil

end Lex
end List

namespace NobelingProof

variable {I : Type u} [LinearOrder I] [IsWellOrder I (·<·)] (C : Set ((WithTop I) → Bool))

def BoolToZ : Bool → ℤ := (if · then 1 else 0)

variable (I)

def r : (I → Bool) → (WithTop I) → Bool := fun f i ↦ if let some a := i then f a else false

lemma r.embedding : ClosedEmbedding (r I) := by
  apply Continuous.closedEmbedding
  · apply continuous_pi
    intro i
    dsimp [r]
    cases i
    · exact continuous_const
    · exact continuous_apply _
  · intros f g hfg
    ext i
    exact congr_fun hfg i

variable {I}

def e (μ : WithTop I) : LocallyConstant {i // i ∈ C} ℤ :=
{ toFun := fun f ↦ BoolToZ (f.1 μ)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_continuous]
    refine' @Continuous.comp _ _ _ _ _ _ BoolToZ _ continuous_of_discreteTopology _
    refine' Continuous.comp (continuous_apply μ) _
    exact continuous_induced_dom }

def Products (I : Type _) [LinearOrder I] := {l : List I // l.Chain' (·>·)}

noncomputable
instance : LinearOrder (Products (WithTop I)) :=
  inferInstanceAs (LinearOrder {l : List (WithTop I) // l.Chain' (·>·)})

lemma ltIffLex (l m : Products (WithTop I)) : l < m ↔ List.Lex (·<·) l.val m.val := by
  cases l
  cases m
  rw [Subtype.mk_lt_mk]
  simp
  exact Iff.rfl

lemma transLex (l m k : List (WithTop I)) (hlm : List.Lex (·<·) l m) (hmk : List.Lex (·<·) m k) :
    List.Lex (·<·) l k :=
  (inferInstance : IsTrans (List (WithTop I)) (List.Lex (·<·))).trans _ _ _ hlm hmk

def Products.eval (l : Products (WithTop I)) := (l.1.map (e C)).prod

def Products.isGood (l : Products (WithTop I)) : Prop :=
  l.eval C ∉ Submodule.span ℤ ((Products.eval C) '' {m | m < l})

def GoodProducts := {l : Products (WithTop I) | l.isGood C}

def GoodProducts.eval (l : {l : Products (WithTop I) // l.isGood C}) :
  LocallyConstant {i // i ∈ C} ℤ := Products.eval C l.1

lemma GoodProducts.injective : Function.Injective (eval C) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  dsimp [eval] at h
  have hab : a < b ∨ a = b ∨ b < a := trichotomous_of (·<·) a b
  apply Or.elim3 hab
  · intro h'
    exfalso
    apply hb
    rw [← h]
    apply Submodule.subset_span
    use a
    exact ⟨h',rfl⟩
  · exact fun h ↦ Subtype.eq h
  · intro h'
    exfalso
    apply ha
    rw [h]
    apply Submodule.subset_span
    use b
    exact ⟨h',rfl⟩

def ModProducts := Set.range (GoodProducts.eval C)

noncomputable
def GoodProducts.equiv_modProducts : GoodProducts C ≃ ModProducts C :=
Equiv.ofInjective (eval C) (injective C)

lemma GoodProducts.equiv_toFun_eq_eval : (equiv_modProducts C).toFun =
  Set.rangeFactorization (eval C) := by rfl

lemma GoodProducts.linear_independent_iff : LinearIndependent ℤ (GoodProducts.eval C) ↔
    LinearIndependent ℤ (fun (p : ModProducts C) ↦ p.1) := by
  rw [← @Set.rangeFactorization_eq _ _ (GoodProducts.eval C), ← equiv_toFun_eq_eval C]
  exact linearIndependent_equiv (equiv_modProducts C)

def Support : Set (WithTop I) := {i : WithTop I | ∃ f ∈ C, f i}

variable (I)

def ord (i : WithTop I) : Ordinal := Ordinal.typein ((·<·) : WithTop I → WithTop I → Prop) i

noncomputable
def term {o : Ordinal} (ho : o < Ordinal.type ((·<·) : WithTop I → WithTop I → Prop)) :
    WithTop I := Ordinal.enum ((·<·) : WithTop I → WithTop I → Prop) o ho

variable {I}

noncomputable
def SwapTrue (o : Ordinal) : (WithTop I → Bool) → WithTop I → Bool :=
fun f i ↦ if ord I i = o then true else f i

lemma continuous_swapTrue (o : Ordinal) :
    Continuous (SwapTrue o : (WithTop I → Bool) → WithTop I → Bool) := by
  refine' continuous_pi _
  intro i
  dsimp [SwapTrue]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

noncomputable
def SwapFalse (o : Ordinal) : (WithTop I → Bool) → WithTop I → Bool :=
fun f i ↦ if ord I i = o then false else f i

lemma continuous_swapFalse (o : Ordinal) :
    Continuous (SwapFalse o : (WithTop I → Bool) → WithTop I → Bool) := by
  refine' continuous_pi _
  intro i
  dsimp [SwapFalse]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

noncomputable
def ProjOrd (o : Ordinal) : (WithTop I → Bool) → (WithTop I → Bool) :=
  fun c i ↦ if ord I i < o then c i else false

lemma continuous_ProjOrd (o : Ordinal) :
    Continuous (ProjOrd o : (WithTop I → Bool) → (WithTop I → Bool)) := by
  refine' continuous_pi _
  intro i
  dsimp [ProjOrd]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma isClosedMap_projOrd (o : Ordinal) :
    IsClosedMap (ProjOrd o : (WithTop I → Bool) → (WithTop I → Bool)) :=
  fun _ hF ↦ (IsCompact.isClosed (hF.isCompact.image (continuous_ProjOrd o)))

def Res (o : Ordinal) : Set (WithTop I → Bool) := (ProjOrd o) '' C

lemma projOrdC {o : Ordinal} (h : Support C ⊆ {i | ord I i < o}) (f : WithTop I → Bool)
    (hf : f ∈ C) : f = ProjOrd o f := by
  dsimp [ProjOrd]
  ext x
  split_ifs with ho
  · rfl
  · dsimp [Support] at h
    simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp] at h
    specialize h x f hf
    rw [← not_imp_not] at h
    simp only [not_lt, Bool.not_eq_true] at h
    simp only [not_lt] at ho
    exact (h ho)

lemma supportResEq (o : Ordinal) (h : Support C ⊆ {i | ord I i < o}) : C = Res C o := by
  ext f
  constructor <;>
  rintro hf
  · use f
    exact ⟨hf, (projOrdC C h f hf).symm⟩
  · obtain ⟨g, hg⟩ := hf
    rw [← projOrdC C h g hg.1] at hg
    rw [← hg.2]
    exact hg.1

lemma isClosed_Res (o : Ordinal) (hC : IsClosed C) : IsClosed (Res C o) :=
  isClosedMap_projOrd o C hC

lemma support_Res_le_o (o : Ordinal) : Support (Res C o) ⊆ {j | ord I j < o} := by
  intro j hj
  dsimp [Support, Res, ProjOrd] at hj
  simp only [Set.mem_image, exists_exists_and_eq_and, Bool.ite_eq_true_distrib] at hj
  simp only [Set.mem_setOf_eq]
  obtain ⟨_, ⟨_, h⟩⟩ := hj
  split_ifs at h
  assumption

noncomputable
def ResOnSubset (o : Ordinal) : {i // i ∈ C} → {i // i ∈ Res C o} :=
fun ⟨i, h⟩ ↦ ⟨ProjOrd o i, Set.mem_image_of_mem _ h⟩

lemma resOnSubset_eq (o : Ordinal) : Subtype.val ∘ ResOnSubset C o =
    (ProjOrd o : (WithTop I → Bool) → _) ∘ Subtype.val := by
  rfl

lemma continuous_val_comp_ResOnSubset (o : Ordinal) :
    Continuous (Subtype.val ∘ ResOnSubset C o) := by
  rw [resOnSubset_eq _]
  exact Continuous.comp (continuous_ProjOrd o) continuous_subtype_val

lemma continuous_ResOnSubset (o : Ordinal) : Continuous (ResOnSubset C o) := by
  rw [continuous_induced_rng]
  exact continuous_val_comp_ResOnSubset _ _

lemma surjective_ResOnSubset (o : Ordinal) : Function.Surjective (ResOnSubset C o) := by
  rintro ⟨i, h⟩
  obtain ⟨b, hb⟩ := h
  dsimp [ResOnSubset]
  use ⟨b, hb.1⟩
  simp_rw [← hb.2]

lemma ResMono {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) {f : WithTop I → Bool}
    (hf : ProjOrd o₂ f ∈ Res C o₂) : ProjOrd o₁ f ∈ Res C o₁ := by
  obtain ⟨c,⟨_,hc⟩⟩  := hf
  dsimp [ProjOrd] at hc
  dsimp [Res, ProjOrd]
  use c
  refine' ⟨(by assumption),_⟩
  ext i
  dsimp
  have hc' := congr_fun hc i
  split_ifs
  · split_ifs at hc' with h₁
    · exact hc'
    · exfalso
      apply h₁ (lt_of_lt_of_le (by assumption) h)
  · rfl

variable (I)

def P' (o : Ordinal) : Prop :=
  o ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop) →
  (∀ C, IsClosed C → Support C ⊆ {j : WithTop I | ord I j < o} →
    LinearIndependent ℤ (GoodProducts.eval C))

variable {I}

instance : IsWellFounded (WithTop I) (·<·) := inferInstance

instance : IsEmpty { i // i ∈ (∅ : Set (WithTop I → Bool)) } := by
  simp only [Set.mem_empty_iff_false, isEmpty_subtype, forall_const]

instance : ¬ Nontrivial (LocallyConstant { i // i ∈ (∅ : Set (WithTop I → Bool)) } ℤ) := by
  rw [nontrivial_iff]
  push_neg
  intros f g
  ext x
  exact isEmptyElim x

instance : Subsingleton (LocallyConstant { i // i ∈ (∅ : Set (WithTop I → Bool)) } ℤ) := by
  rw [subsingleton_iff]
  intros f g
  ext x
  exact isEmptyElim x

instance GoodProducts.emptyEmpty :
    IsEmpty { l // Products.isGood (∅ : Set (WithTop I → Bool)) l } := by
  rw [isEmpty_iff]
  rintro ⟨l, hl⟩
  dsimp [Products.isGood] at hl
  apply hl
  have h : Products.eval ∅ l = 0 := subsingleton_iff.mp inferInstance _ 0
  rw [h]
  exact Submodule.zero_mem _

lemma GoodProducts.linearIndependentEmpty :
    LinearIndependent ℤ (eval (∅ : Set (WithTop I → Bool))) := by
  exact linearIndependent_empty_type

def enil : Products (WithTop I) := ⟨[], by simp only [List.chain'_nil]⟩

lemma leEnilEmpty : { m : Products (WithTop I) | m < enil } = ∅ := by
  ext ⟨m, hm⟩
  refine' ⟨_,(by tauto)⟩
  rintro h
  · simp at h
    rw [ltIffLex] at h
    dsimp [enil] at h
    simp only [Set.mem_empty_iff_false]
    apply List.Lex.not_nil_right _ _ h

instance {α : Type _} [TopologicalSpace α] [Inhabited α] : Nontrivial (LocallyConstant α ℤ) := by
  use 0
  use 1
  intro h
  rw [LocallyConstant.ext_iff] at h
  apply @zero_ne_one ℤ
  exact h default

lemma evalEnilNeZero : Products.eval ({fun _ ↦ false} : Set (WithTop I → Bool)) enil ≠ 0 := by
  dsimp [Products.eval]
  exact one_ne_zero

lemma nilIsGood : Products.isGood ({fun _ ↦ false} : Set (WithTop I → Bool)) enil:= by
  intro h
  rw [leEnilEmpty] at h
  simp at h
  apply evalEnilNeZero h


lemma nilSpanTop :
    Submodule.span ℤ (Products.eval ({fun _ ↦ false} : Set (WithTop I → Bool)) '' {enil}) = ⊤ := by
  simp only [Set.image_singleton]
  dsimp [enil, Products.eval]
  rw [eq_top_iff]
  rintro f _
  rw [Submodule.mem_span]
  intro p h₁
  simp at h₁
  have : f = (f default) • (1 : LocallyConstant _ ℤ)
  · ext x
    have hd : x = default := by simp only [Set.default_coe_singleton, eq_iff_true_of_subsingleton]
    rw [hd]
    simp
    rfl
  rw [this]
  apply Submodule.smul_mem
  exact h₁

noncomputable
instance GoodProducts.singletonUnique :
  Unique { l // Products.isGood ({fun _ ↦ false} : Set (WithTop I → Bool)) l } :=
{ default := ⟨enil, nilIsGood⟩
  uniq := by
    rintro ⟨⟨l, hl⟩, hll⟩
    dsimp [default]
    ext
    dsimp [enil]
    apply Subtype.eq
    dsimp
    have : [] < l ∨ [] = l  := List.Lex.nil_le l
    cases this
    · exfalso
      apply hll
      have he : {enil} ⊆ {m | m < ⟨l,hl⟩ }
      · simp
        dsimp [enil]
        rw [Subtype.mk_lt_mk]
        assumption
      have hpe : Products.eval ({fun _ ↦ false} : Set (WithTop I → Bool)) '' {enil} ⊆
        Products.eval _ '' {m | m < ⟨l,hl⟩ } := Set.image_subset _ he
      apply Submodule.span_mono hpe
      rw [nilSpanTop]
      exact Submodule.mem_top
    · exact Eq.symm (by assumption) }

instance (α : Type _) [TopologicalSpace α] : NoZeroSMulDivisors ℤ (LocallyConstant α ℤ) := by
  constructor
  intro c f h
  by_cases hc : c = 0
  · left
    assumption
  · right
    ext x
    rw [LocallyConstant.ext_iff] at h
    apply_fun fun (y : ℤ) ↦ c * y
    · simp at h
      simp
      exact h x
    · exact mul_right_injective₀ hc

lemma GoodProducts.linearIndependentSingleton :
    LinearIndependent ℤ (eval ({fun _ ↦ false} : Set (WithTop I → Bool))) :=
  linearIndependent_unique (eval ({fun _ ↦ false} : Set (WithTop I → Bool))) evalEnilNeZero

lemma ProjOrdSelf (o : Ordinal) {f : WithTop I → Bool} (hf : f ∈ Res C o) :
    ProjOrd o f = f := by
  dsimp [ProjOrd]
  ext i
  split_ifs
  · rfl
  · obtain ⟨c,hc⟩ := hf
    rw [←congr_fun hc.2 i]
    dsimp [ProjOrd]
    rw [eq_ite_iff]
    right
    exact ⟨(by assumption), (by rfl)⟩

lemma ResMono' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) {f : WithTop I → Bool}
    (hf : f ∈ Res C o₂) : ProjOrd o₁ f ∈ Res C o₁ := by
  rw [← ProjOrdSelf C o₂ hf] at hf
  exact ResMono C h hf

noncomputable
def ResOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : {i // i ∈ Res C o₂} → {i // i ∈ Res C o₁} :=
  fun e ↦ ⟨ProjOrd o₁ e.val, ResMono' C h e.property⟩

lemma resOnSubsets_eq {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : ResOnSubset C o₁ =
    ResOnSubsets C h ∘ ResOnSubset C o₂  := by
  ext e i
  dsimp [ResOnSubsets, ResOnSubset]
  dsimp [ProjOrd]
  split_ifs with h₁ h₂
  · rfl
  · exfalso
    apply h₂ (lt_of_lt_of_le h₁ h)
  · rfl

lemma continuous_ResOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : Continuous (ResOnSubsets C h) := by
  rw [continuous_induced_rng]
  exact continuous_val_comp_ResOnSubset (Res C o₂) o₁

lemma surjective_ResOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) :
    Function.Surjective (ResOnSubsets C h) := by
  apply @Function.Surjective.of_comp _ _ _ _ (ResOnSubset C o₂)
  rw [← resOnSubsets_eq C h]
  exact surjective_ResOnSubset _ _

lemma Products.evalCons {l : List (WithTop I)} {a : WithTop I}
    (hla : (a::l).Chain' (·>·)) : Products.eval C ⟨a::l,hla⟩ =
    (e C a) * Products.eval C ⟨l,List.Chain'.sublist hla (List.tail_sublist (a::l))⟩ := by
  dsimp [eval]
  simp only [List.prod_cons]

lemma eEqe {o₁ o₂ : Ordinal} {a : WithTop I} (ha : ord I a < o₁) (h : o₁ ≤ o₂) :
    e (Res C o₁) a ∘ ResOnSubsets C h = e (Res C o₂) a := by
  ext ⟨f,hf⟩
  dsimp [e, ResOnSubsets, BoolToZ, ProjOrd]
  split_ifs
  · rfl
  · rfl

lemma eEqeC {o : Ordinal} {a : WithTop I} (ha : ord I a < o) :
    e (Res C o) a ∘ ResOnSubset C o = e C a := by
  ext ⟨f,hf⟩
  dsimp [e, ResOnSubset, BoolToZ, ProjOrd]
  split_ifs
  · rfl
  · rfl

lemma eEqe_apply {o₁ o₂ : Ordinal} {a : WithTop I} (ha : ord I a < o₁) (h : o₁ ≤ o₂) :
    ∀ x, (e (Res C o₁) a) ((ResOnSubsets C h) x) = e (Res C o₂) a x := by
  intro x
  exact congr_fun (eEqe C ha h) x

lemma eEqe_applyC {o : Ordinal} {a : WithTop I} (ha : ord I a < o) :
    ∀ x, (e (Res C o) a) ((ResOnSubset C o) x) = e C a x := by
  intro x
  exact congr_fun (eEqeC C ha) x

lemma Products.evalFac {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o₁) :
    l.eval (Res C o₁) ∘ ResOnSubsets C h = l.eval (Res C o₂) := by
  obtain ⟨l, hl⟩ := l
  induction l with
  | nil => rfl
  | cons a as ih =>
    · ext ⟨f, hf⟩
      rw [evalCons (Res C o₁) hl]
      rw [evalCons (Res C o₂) hl]
      dsimp
      specialize hlhead (List.cons_ne_nil a as)
      dsimp at hlhead
      rw [eEqe_apply C hlhead h _]
      specialize ih (List.Chain'.sublist hl (List.tail_sublist (a::as)))
      dsimp at ih
      congr! 1
      by_cases has : as = []
      · simp_rw [has]
        rfl
      · have : ord I (List.head! as) < o₁
        · rw [← List.cons_head!_tail has] at hl
          refine' lt_trans _ hlhead
          dsimp [ord]
          simp only [Ordinal.typein_lt_typein]
          have := List.Chain'.rel_head hl
          simp only [gt_iff_lt] at this
          exact this
        exact congr_fun (ih (fun _ ↦ this)) _

lemma Products.evalFacC {l : Products (WithTop I)} {o : Ordinal}
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o) :
    l.eval (Res C o) ∘ ResOnSubset C o = l.eval C := by
  obtain ⟨l, hl⟩ := l
  induction l with
  | nil => rfl
  | cons a as ih =>
    · ext ⟨f, hf⟩
      rw [evalCons (Res C o) hl]
      rw [evalCons C hl]
      dsimp
      specialize hlhead (List.cons_ne_nil a as)
      dsimp at hlhead
      rw [eEqe_applyC C hlhead]
      specialize ih (List.Chain'.sublist hl (List.tail_sublist (a::as)))
      dsimp at ih
      congr! 1
      by_cases has : as = []
      · simp_rw [has]
        rfl
      · have : ord I (List.head! as) < o
        · rw [← List.cons_head!_tail has] at hl
          refine' lt_trans _ hlhead
          dsimp [ord]
          simp only [Ordinal.typein_lt_typein]
          have := List.Chain'.rel_head hl
          simp only [gt_iff_lt] at this
          exact this
        exact congr_fun (ih (fun _ ↦ this)) _

lemma Products.head_lt_ord_of_isGood {l : Products (WithTop I)} {o : Ordinal}
    (h : l.isGood (Res C o)) : l.val ≠ [] → ord I (l.val.head!) < o := by
  intro hn
  by_contra h'
  apply h
  obtain ⟨l,hl⟩ := l
  dsimp at hn
  have hl' : List.Chain' (·>·) (l.head! :: l.tail)
  · rw [List.cons_head!_tail hn]
    exact hl
  have : (⟨l,hl⟩ : Products (WithTop I)) = ⟨l.head! :: l.tail, hl'⟩
  · simp_rw [List.cons_head!_tail hn]
  rw [this, evalCons (Res C o) hl']
  have eZero : e (Res C o) (List.head! l) = 0
  · dsimp [e]
    ext ⟨f,hf⟩
    dsimp [BoolToZ]
    dsimp [Res, ProjOrd] at hf
    obtain ⟨g, hg⟩ := hf
    rw [← hg.2]
    split_ifs
    · exfalso
      assumption
    · rfl
    · exfalso
      assumption
    · rfl
  rw [eZero]
  simp only [zero_mul, Submodule.zero_mem]

lemma Products.goodEvalFac {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) : l.eval (Res C o₁) ∘ ResOnSubsets C h = l.eval (Res C o₂) :=
  evalFac C h (head_lt_ord_of_isGood C hl)

lemma Products.goodEvalFacC {l : Products (WithTop I)} {o : Ordinal}
    (hl : l.isGood (Res C o)) : l.eval (Res C o) ∘ ResOnSubset C o = l.eval C :=
  evalFacC C (head_lt_ord_of_isGood C hl)

lemma Products.eval_comapFac {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) :
    LocallyConstant.comap (ResOnSubsets C h) (l.eval (Res C o₁)) = l.eval (Res C o₂) := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _)]
  exact congr_fun (goodEvalFac C h hl) _

lemma Products.eval_comapFacC {l : Products (WithTop I)} {o : Ordinal}
    (hl : l.isGood (Res C o)) :
    LocallyConstant.comap (ResOnSubset C o) (l.eval (Res C o)) = l.eval C := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
  exact congr_fun (goodEvalFacC C hl) _

lemma Products.eval_comapFac' {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o₁) :
    LocallyConstant.comap (ResOnSubsets C h) (l.eval (Res C o₁)) = l.eval (Res C o₂) := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _)]
  exact congr_fun (evalFac C h hlhead) _

lemma Products.eval_comapFac'C {l : Products (WithTop I)} {o : Ordinal}
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o) :
    LocallyConstant.comap (ResOnSubset C o) (l.eval (Res C o)) = l.eval C := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
  exact congr_fun (evalFacC C hlhead) _

lemma Products.lt_ord {l m : Products (WithTop I)} {o : Ordinal} (hmltl : m < l)
    (hlhead : l.val ≠ [] → ord I l.val.head! < o) : m.val ≠ [] → ord I m.val.head! < o := by
  intro hm
  rw [ltIffLex] at hmltl
  by_cases hl : l.val = []
  · exfalso
    rw [hl] at hmltl
    exact List.Lex.not_nil_right _ _ hmltl
  · suffices hml : m.val.head! ≤ l.val.head!
    · refine' lt_of_le_of_lt _ (hlhead hl)
      dsimp [ord]
      simp only [Ordinal.typein_le_typein, not_lt]
      exact hml
    rw [← List.cons_head!_tail hl] at hmltl
    rw [← List.cons_head!_tail hm] at hmltl
    by_contra hn
    simp only [not_le] at hn
    have hml : List.Lex (·<·) (l.val.head! :: l.val.tail) (m.val.head! :: m.val.tail) :=
      List.Lex.rel hn
    exact List.Lex.isAsymm.aux _ _ _ hml hmltl

lemma Products.eval_comapFacImage {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) : eval (Res C o₂) '' { m | m < l } =
    (LocallyConstant.comapLinear (ResOnSubsets C h) (continuous_ResOnSubsets _ _) :
    LocallyConstant {i // i ∈ Res C o₁} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ Res C o₂} ℤ) ''
    (eval (Res C o₁) '' { m | m < l }) := by
  dsimp [LocallyConstant.comapLinear]
  ext f
  constructor <;>
  rintro hf
  · obtain ⟨m,hm⟩ := hf
    rw [← eval_comapFac' C h (lt_ord hm.1 (head_lt_ord_of_isGood C hl))] at hm
    rw [← hm.2]
    simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
    use m
    exact ⟨hm.1, by rfl⟩
  · rw [← Set.image_comp] at hf
    obtain ⟨m,hm⟩ := hf
    dsimp at hm
    rw [eval_comapFac' C h (Products.lt_ord hm.1 (head_lt_ord_of_isGood C hl))] at hm
    rw [← hm.2]
    simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
    use m
    exact ⟨hm.1, by rfl⟩

lemma Products.isGoodMono {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) : l.isGood (Res C o₂) := by
  dsimp [isGood] at *
  intro h'
  apply hl
  rw [eval_comapFacImage C h hl] at h'
  simp only [Submodule.span_image, Submodule.mem_map] at h'
  obtain ⟨y, ⟨hy₁,hy₂⟩ ⟩ := h'
  dsimp [LocallyConstant.comapLinear] at hy₂
  rw [← eval_comapFac C h hl] at hy₂
  have hy := LocallyConstant.comap_injective _ (continuous_ResOnSubsets C h)
    (surjective_ResOnSubsets C h) hy₂
  subst hy
  assumption

lemma GoodProducts.evalFac {l : Products (WithTop I)} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (Res C o₁)) : eval (Res C o₂) ⟨l, (Products.isGoodMono C h hl)⟩ =
    eval (Res C o₁) ⟨l, hl⟩ ∘ ResOnSubsets C h :=
  (Products.goodEvalFac C h hl).symm

lemma GoodProducts.lin_smaller (o : Ordinal) : LinearIndependent ℤ (eval (Res C o)) ↔
    LinearIndependent ℤ ((LocallyConstant.comapLinear
    (ResOnSubset C o) (continuous_ResOnSubset C o) : LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ]
    LocallyConstant {i // i ∈ C} ℤ) ∘ (eval (Res C o))) :=
  (LinearMap.linearIndependent_iff (LocallyConstant.comapLinear
    (ResOnSubset C o) (continuous_ResOnSubset C o))
    (LocallyConstant.comapLinear_injective _ _ (surjective_ResOnSubset C o))).symm

def ModProducts.smaller (o : Ordinal) : Set (LocallyConstant {i // i ∈ C} ℤ) :=
  (LocallyConstant.comapLinear
    (ResOnSubset C o) (continuous_ResOnSubset C o) : LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ]
    LocallyConstant {i // i ∈ C} ℤ) '' (ModProducts (Res C o))

instance [Nonempty C] : Inhabited (Res C 0) := by
  use (fun _ ↦ false)
  dsimp [Res]
  have : C.Nonempty
  · rw [← Set.nonempty_coe_sort]
    assumption
  obtain ⟨x,hx⟩ := this
  use x
  refine' ⟨hx,_⟩
  dsimp [ProjOrd]
  ext i
  split_ifs with h
  · exfalso
    exact Ordinal.not_lt_zero _ h
  · rfl

instance [Nonempty C] : Nontrivial (LocallyConstant {i // i ∈ C} ℤ) := by
  use 0
  use 1
  intro h
  rw [LocallyConstant.ext_iff] at h
  apply @zero_ne_one ℤ
  have : C.Nonempty
  · rw [← Set.nonempty_coe_sort]
    assumption
  obtain ⟨x,hx⟩ := this
  exact h ⟨x,hx⟩

lemma evalEnilNeZeroAny [Nonempty C] : enil.eval C ≠ 0 := by
  dsimp [Products.eval]
  exact one_ne_zero

lemma nilIsGoodAny [Nonempty C] : Products.isGood C enil := by
  intro h
  rw [leEnilEmpty] at h
  simp at h
  apply evalEnilNeZeroAny C h

instance [Nonempty C] (o : Ordinal) : Nonempty (Res C o) := by
  have : C.Nonempty
  · rw [← Set.nonempty_coe_sort]
    assumption
  rw [Set.nonempty_coe_sort]
  obtain ⟨x,hx⟩ := this
  use ProjOrd o x
  dsimp [Res]
  use x

open Classical

lemma Products.limitOrdinal [Nonempty C] {o : Ordinal} (ho : o.IsLimit) (l : Products (WithTop I)) :
    l.isGood (Res C o) ↔ ∃ (o' : Ordinal), o' < o ∧ l.isGood (Res C o') := by
  constructor <;>
  rintro h
  · dsimp [Ordinal.IsLimit] at ho
    obtain ⟨l, hl⟩ := l
    induction l with
    | nil =>
      · have ho' : o ≠ 0 := ho.1
        rw [← Ordinal.pos_iff_ne_zero] at ho'
        use 0
        exact ⟨ho', nilIsGoodAny _⟩
    | cons a as _ =>
      · have := Products.head_lt_ord_of_isGood C h (List.cons_ne_nil a as)
        simp only [List.head!_cons] at this
        let o₁ := Order.succ (ord I a)
        use o₁
        refine' ⟨ho.2 _ this,_⟩
        dsimp [isGood]
        dsimp [isGood] at h
        intro he
        apply h
        have hlhead : (⟨a :: as,hl⟩ : Products (WithTop I)).val ≠ [] →
            ord I (List.head! (⟨a :: as,hl⟩ : Products (WithTop I)).val) < Order.succ (ord I a)
        · intro
          simp only [List.head!_cons, Order.lt_succ_iff_not_isMax, not_isMax, not_false_eq_true]
        rw [← eval_comapFac' C (le_of_lt (ho.2 (ord I a) this)) hlhead]
        rw [mem_span_set] at he
        obtain ⟨c, ⟨hc, hsum⟩⟩ := he
        rw [mem_span_set]
        use Finsupp.mapDomain (LocallyConstant.comap
          (ResOnSubsets C (le_of_lt (ho.2 (ord I a) this))) :
          LocallyConstant {i // i ∈ Res C o₁} ℤ → LocallyConstant {i // i ∈ Res C o} ℤ) c
        refine' ⟨_,_⟩
        · refine' (subset_trans Finsupp.mapDomain_support _) -- need "Classical" for decidability
          intro p hp
          simp only [Finset.image_val, Multiset.mem_dedup, Multiset.mem_map, Finset.mem_val] at hp
          obtain ⟨t,ht⟩ := hp
          have ht' := hc ht.1
          obtain ⟨y, hy⟩ := ht'
          rw [← hy.2] at ht
          rw [← ht.2]
          use y
          refine' ⟨hy.1,_⟩
          rw [← eval_comapFac']
          intro hnil
          obtain ⟨b, l', hbl⟩ := List.exists_cons_of_ne_nil hnil
          rw [hbl]
          simp only [List.head!_cons, Order.lt_succ_iff]
          dsimp [ord]
          simp only [Ordinal.typein_le_typein, not_lt]
          have hya : y.val < a :: as := hy.1
          rw [hbl] at hya
          cases hya
          · exact le_refl _
          · exact le_of_lt (by assumption)
        · rw [Finsupp.sum_mapDomain_index_inj
            (LocallyConstant.comap_injective _ (continuous_ResOnSubsets _ _)
            (surjective_ResOnSubsets _ _))]
          rw [← hsum]
          have hlin : LocallyConstant.comap (ResOnSubsets C (le_of_lt (ho.2 (ord I a) this))) =
              ↑(LocallyConstant.comapLinear (ResOnSubsets C (le_of_lt (ho.2 (ord I a) this)))
              (continuous_ResOnSubsets _ _) :
              LocallyConstant {i // i ∈ Res C o₁} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ Res C o} ℤ) :=
            rfl
          rw [hlin, map_finsupp_sum]
          apply Finsupp.sum_congr
          intro f _
          dsimp [LocallyConstant.comapLinear]
          ext a'
          dsimp
          rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _)]
          rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _)]
          rfl
  · obtain ⟨o',⟨ho',hl⟩⟩ := h
    exact isGoodMono C (le_of_lt ho') hl

lemma ModProducts.union {o : Ordinal} (ho : o.IsLimit) (hsC : Support C ⊆ {i | ord I i < o}) :
    ModProducts C = ⋃ (e : {o' // o' < o}), (smaller C e.val) := by
  by_cases hC : Nonempty C
  · ext p
    constructor <;>
    rintro hp
    · dsimp [smaller]
      dsimp [ModProducts] at *
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
      dsimp
      obtain ⟨⟨l,hl⟩,hp⟩ := hp
      rw [supportResEq C o hsC, Products.limitOrdinal C ho] at hl
      obtain ⟨o',ho'⟩ := hl
      use o'
      use ho'.1
      use GoodProducts.eval (Res C o') ⟨l,ho'.2⟩
      refine' ⟨_,_⟩
      · use l
        use ho'.2
      · dsimp [LocallyConstant.comapLinear]
        rw [← hp]
        dsimp [GoodProducts.eval]
        exact Products.eval_comapFacC C ho'.2
    · dsimp [ModProducts]
      simp at *
      obtain ⟨o', h⟩ := hp
      obtain ⟨f, hf⟩ := h.2
      obtain ⟨⟨⟨l, lc⟩, hl⟩, hlf⟩ := hf.1
      rw [← hlf] at hf
      rw [← hf.2]
      dsimp [LocallyConstant.comapLinear]
      use ⟨l,lc⟩
      constructor
      exact (Products.eval_comapFacC C hl).symm
      rw [supportResEq C o hsC]
      exact Products.isGoodMono C (le_of_lt h.1) hl
  · have : C = ∅
    · rw [Set.nonempty_coe_sort, Set.not_nonempty_iff_eq_empty] at hC
      assumption
    dsimp [ModProducts, smaller, LocallyConstant.comapLinear, Res]
    rw [this]
    haveI he : IsEmpty { l // Products.isGood (∅ : Set (WithTop I → Bool)) l } := inferInstance
    rw [@Set.range_eq_empty _ _ he (GoodProducts.eval ∅)]
    refine' Eq.symm _
    simp only [Set.iUnion_eq_empty, Set.image_eq_empty, Set.image_empty]
    intro e
    have hP : ProjOrd e.val '' (∅ : Set (WithTop I → Bool)) = ∅
    · simp only [Set.image_empty]
    rw [hP, @Set.range_eq_empty _ _ he (GoodProducts.eval ∅)]

def ModProducts.equiv {o : Ordinal} (ho : o.IsLimit) (hsC : Support C ⊆ {i | ord I i < o}) :
    ModProducts C ≃ ⋃ (e : {o' // o' < o}), (smaller C e.val) :=
  Equiv.Set.ofEq (union C ho hsC)

lemma ModProducts.equivFactorization {o : Ordinal} (ho : o.IsLimit)
    (hsC : Support C ⊆ {i | ord I i < o}) :
    (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) ∘ (equiv C ho hsC).toFun =
    (fun (p : ModProducts C) ↦ (p.1 : LocallyConstant {i // i ∈ C} ℤ)) := by
  rfl

lemma ModProducts.linear_independent_iff {o : Ordinal} (ho : o.IsLimit)
    (hsC : Support C ⊆ {i | ord I i < o}) : LinearIndependent ℤ (GoodProducts.eval C) ↔
    LinearIndependent ℤ (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) := by
  rw [GoodProducts.linear_independent_iff]
  rw [← equivFactorization C ho hsC]
  exact linearIndependent_equiv (equiv C ho hsC)

noncomputable
def ModProducts.equiv_smaller_toFun (o : Ordinal) : ModProducts (Res C o) → smaller C o :=
fun x ↦ ⟨(↑(LocallyConstant.comapLinear (ResOnSubset C o) (continuous_ResOnSubset _ _) :
    LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ) :
    LocallyConstant {i // i ∈ Res C o} ℤ → LocallyConstant {i // i ∈ C} ℤ) ↑x,
    by { dsimp [smaller]; use x.val; exact ⟨x.property, rfl⟩  } ⟩

lemma ModProducts.equiv_smaller_toFun_bijective (o : Ordinal) :
    Function.Bijective (equiv_smaller_toFun C o) := by
  refine' ⟨_,_⟩
  · intro a b hab
    dsimp [equiv_smaller_toFun, LocallyConstant.comapLinear] at hab
    ext1
    simp only [Subtype.mk.injEq] at hab
    exact LocallyConstant.comap_injective _ (continuous_ResOnSubset _ _)
      (surjective_ResOnSubset _ _) hab
  · rintro ⟨a,ha⟩
    obtain ⟨b,hb⟩ := ha
    use ⟨b,hb.1⟩
    dsimp [equiv_smaller_toFun]
    simp only [Subtype.mk.injEq]
    exact hb.2

noncomputable
def ModProducts.equiv_smaller (o : Ordinal) : ModProducts (Res C o) ≃ smaller C o :=
Equiv.ofBijective (equiv_smaller_toFun C o) (equiv_smaller_toFun_bijective C o)

lemma ModProducts.smaller_factorization (o : Ordinal) :
    (fun (p : smaller C o) ↦ p.1) ∘ (equiv_smaller C o).toFun =
    ↑(LocallyConstant.comapLinear (ResOnSubset C o) (continuous_ResOnSubset _ _) :
    LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ) ∘
    (fun (p : ModProducts (Res C o)) ↦ p.1) := by rfl

lemma ModProducts.smaller_linear_independent_iff (o : Ordinal) :
    LinearIndependent ℤ (GoodProducts.eval (Res C o)) ↔
    LinearIndependent ℤ (fun (p : smaller C o) ↦ p.1) := by
  rw [GoodProducts.linear_independent_iff]
  rw [← LinearMap.linearIndependent_iff (LocallyConstant.comapLinear (ResOnSubset C o)
        (continuous_ResOnSubset _ _) : LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ]
        LocallyConstant {i // i ∈ C} ℤ) (LocallyConstant.comapLinear_injective _
        (continuous_ResOnSubset _ _) (surjective_ResOnSubset _ _))]
  rw [← smaller_factorization C o]
  exact linearIndependent_equiv _

lemma ModProducts.smaller_mono {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : smaller C o₁ ⊆ smaller C o₂ := by
  intro f hf
  dsimp [smaller, LocallyConstant.comapLinear] at *
  obtain ⟨g, hg⟩ := hf
  simp only [Set.mem_image]
  use LocallyConstant.comap (ResOnSubsets C h) g
  refine' ⟨_,_⟩
  · dsimp [ModProducts]
    dsimp [ModProducts] at hg
    obtain ⟨⟨l,gl⟩, hl⟩ := hg.1
    use ⟨l, Products.isGoodMono C h gl⟩
    ext x
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _), ← hl]
    exact congr_fun (GoodProducts.evalFac _ _ _) x
  · rw [← hg.2]
    ext x
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubsets _ _)]
    congr
    exact congr_fun (resOnSubsets_eq C h).symm x

lemma DirectedS (o : Ordinal) : Directed (· ⊆ ·) (fun e ↦ ModProducts.smaller C
    e.val : {o' // o' < o} → Set (LocallyConstant { i // i ∈ C } ℤ)) := by
  rintro ⟨o₁,h₁⟩ ⟨o₂,h₂⟩
  dsimp
  have h : o₁ ≤ o₂ ∨ o₂ ≤ o₁ :=
    (inferInstance : IsTotal Ordinal ((·≤·) : Ordinal → Ordinal → Prop)).total o₁ o₂
  cases h
  · use ⟨o₂,h₂⟩ -- ⟨(Order.succ o₂), ho.2 o₂ h₂⟩
    exact ⟨ModProducts.smaller_mono C (by assumption), ModProducts.smaller_mono C (le_refl o₂)⟩
  · use ⟨o₁,h₁⟩ -- ⟨(Order.succ o₁), ho.2 o₁ h₁⟩
    exact ⟨ModProducts.smaller_mono C (le_refl o₁), ModProducts.smaller_mono C (by assumption)⟩

section Successor

variable (o : Ordinal)

variable (hC : IsClosed C) (hsC : Support C ⊆ {j | ord I j < Order.succ o}) [Nonempty C]

def GoodProducts.StartingWithMax : Set (Products (WithTop I)) :=
{l | l.isGood C ∧ l.val ≠ [] ∧ ord I l.val.head! = o}

lemma GoodProducts.union_succ : GoodProducts C = GoodProducts (Res C o) ∪ StartingWithMax C o := by
  ext ⟨l,hl⟩
  dsimp [GoodProducts, StartingWithMax]
  simp only [Set.mem_union, Set.mem_setOf_eq]
  refine' ⟨_,_⟩
  <;> intro h
  · by_cases hln : l = []
    · left
      simp_rw [hln]
      exact nilIsGoodAny (Res C o)
    · by_cases hh : ord I l.head! = o
      · right
        exact ⟨h,hln,hh⟩
      · left
        intro he
        apply h
        rw [supportResEq C (Order.succ o) hsC] at h
        have hls := Products.head_lt_ord_of_isGood C h hln
        simp only [Order.lt_succ_iff] at hls
        have hlhead : ord I (⟨l,hl⟩ : Products (WithTop I)).val.head! < o := lt_of_le_of_ne hls hh
        rw [mem_span_set]
        rw [mem_span_set] at he
        obtain ⟨c,⟨hcs,hcsum⟩⟩ := he
        use Finsupp.mapDomain (LocallyConstant.comap
          (ResOnSubset C o) :
          LocallyConstant {i // i ∈ Res C o} ℤ → LocallyConstant {i // i ∈ C} ℤ) c
        refine' ⟨_,_⟩
        · refine' (subset_trans Finsupp.mapDomain_support _) -- need "Classical" for decidability
          intro p hp
          simp only [Finset.image_val, Multiset.mem_dedup, Multiset.mem_map, Finset.mem_val] at hp
          obtain ⟨t,ht⟩ := hp
          have ht' := hcs ht.1
          obtain ⟨y, hy⟩ := ht'
          rw [← hy.2] at ht
          rw [← ht.2]
          use y
          refine' ⟨hy.1,_⟩
          rw [← Products.eval_comapFac'C]
          intro hnil
          obtain ⟨b, l', hbl⟩ := List.exists_cons_of_ne_nil hnil
          rw [hbl]
          simp only [List.head!_cons, Order.lt_succ_iff]
          dsimp [ord]
          simp only [Ordinal.typein_le_typein, not_lt]
          have hya : y.val < l := hy.1
          rw [hbl] at hya
          cases hya
          · assumption
          · refine' lt_trans _ hlhead
            dsimp [ord]
            simpa only [Ordinal.typein_lt_typein]
        · ext f
          rw [← Products.evalFacC C (fun _ ↦ hlhead)]
          rw [Finsupp.sum_mapDomain_index_inj
            (LocallyConstant.comap_injective _ (continuous_ResOnSubset _ _)
            (surjective_ResOnSubset _ _))]
          rw [← hcsum]
          congr! 1
          rw [← LocallyConstant.coe_comap _ _ (continuous_ResOnSubset _ _)]
          have hlin : LocallyConstant.comap (ResOnSubset C o) =
              ↑(LocallyConstant.comapLinear (ResOnSubset C o)
              (continuous_ResOnSubset _ _) :
              LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ) :=
            rfl
          rw [hlin, map_finsupp_sum]
          congr! 1
          apply Finsupp.sum_congr
          intro f _
          dsimp [LocallyConstant.comapLinear]
          ext a'
          dsimp
          rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
          rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
          rfl
  · refine' Or.elim h _ _
    <;> intro hh
    · have := Products.isGoodMono C (le_of_lt (Order.lt_succ o)) hh
      rwa [supportResEq C (Order.succ o) hsC]
    · exact hh.1

def GoodProducts.sum_to :
    (GoodProducts (Res C o)) ⊕ (StartingWithMax C o) → Products (WithTop I) :=
  Sum.elim Subtype.val Subtype.val

lemma GoodProducts.injective_sum_to : Function.Injective (sum_to C o) := by
  apply Function.Injective.sum_elim
  · exact Subtype.val_injective
  · exact Subtype.val_injective
  rintro ⟨a,ha⟩ ⟨b,hb⟩
  dsimp
  dsimp [GoodProducts] at ha
  dsimp [StartingWithMax] at hb
  by_cases hanil : a.val = []
  · rw [← hanil] at hb
    apply Ne.symm
    exact Subtype.ne_of_val_ne hb.2.1
  · have ha' := Products.head_lt_ord_of_isGood C ha hanil
    rw [← hb.2.2] at ha'
    dsimp [ord] at ha'
    simp only [Ordinal.typein_lt_typein] at ha'
    have := ne_of_lt ha'
    intro hab
    apply this
    rw [hab]

noncomputable
def GoodProducts.sum_to_equiv := Equiv.ofInjective (sum_to C o) (injective_sum_to C o)

lemma GoodProducts.sum_to_range :
    Set.range (sum_to C o) = GoodProducts (Res C o) ∪ StartingWithMax C o := by
  have h : Set.range (sum_to C o) = _ ∪ _ := Set.Sum.elim_range _ _
  rw [h]
  congr
  <;> ext l
  · constructor <;>
    intro hl
    · obtain ⟨m,hm⟩ := hl
      rw [← hm]
      exact m.prop
    · use ⟨l,hl⟩
  · constructor <;>
    intro hl
    · obtain ⟨m,hm⟩ := hl
      rw [← hm]
      exact m.prop
    · use ⟨l,hl⟩

noncomputable
def GoodProducts.sum_equiv : GoodProducts (Res C o) ⊕ (StartingWithMax C o) ≃ GoodProducts C :=
Equiv.trans (Equiv.trans (sum_to_equiv C o) (Equiv.Set.ofEq (sum_to_range C o)))
  (Equiv.Set.ofEq (union_succ C o hsC).symm)

lemma GoodProducts.sum_equiv_comp_eval_eq_elim : eval C ∘ (sum_equiv C o hsC).toFun =
    (Sum.elim (fun (l : GoodProducts (Res C o)) ↦ Products.eval C l.1)
    (fun (l : StartingWithMax C o) ↦ Products.eval C l.1)) := by
  ext ⟨_,_⟩
  · rfl
  · rfl

lemma GoodProducts.linearIndependent_iff_sum :
    LinearIndependent ℤ (eval C) ↔ LinearIndependent ℤ (Sum.elim
    (fun (l : GoodProducts (Res C o)) ↦ Products.eval C l.1)
    (fun (l : StartingWithMax C o) ↦ Products.eval C l.1)) := by
  rw [← linearIndependent_equiv (sum_equiv C o hsC), ← sum_equiv_comp_eval_eq_elim C o hsC]
  exact Iff.rfl

lemma GoodProducts.span_sum :
    Set.range (eval C) = Set.range (Sum.elim
    (fun (l : GoodProducts (Res C o)) ↦ Products.eval C l.1)
    (fun (l : StartingWithMax C o) ↦ Products.eval C l.1)) := by
  rw [← sum_equiv_comp_eval_eq_elim C o hsC]
  simp only [Equiv.toFun_as_coe, EquivLike.range_comp]

noncomputable
def GoodProducts.equiv_smaller : GoodProducts (Res C o) ≃ ModProducts.smaller C o :=
Equiv.trans (equiv_modProducts (Res C o)) (ModProducts.equiv_smaller C o)

lemma GoodProducts.eval_eq_comp_equiv : (fun (l : GoodProducts (Res C o)) ↦ Products.eval C l.1) =
    (fun p ↦ ↑p) ∘ ↑(equiv_smaller C o) := by
  ext p f
  dsimp [equiv_smaller, ModProducts.equiv_smaller, ModProducts.equiv_smaller_toFun,
    equiv_modProducts, eval, LocallyConstant.comapLinear]
  rw [congr_fun (Products.goodEvalFacC C p.2).symm f,
    LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
  rfl

lemma GoodProducts.linearIndependent_succ_iff :
    LinearIndependent ℤ (eval (Res C o)) ↔ LinearIndependent ℤ
    (fun (l : GoodProducts (Res C o)) ↦ Products.eval C l.1) := by
  rw [ModProducts.smaller_linear_independent_iff, ← linearIndependent_equiv (equiv_smaller C o),
    eval_eq_comp_equiv]

variable {o} (ho : o < Ordinal.type (·<· : WithTop I → WithTop I → Prop))

def C0 := C ∩ {f | f (term I ho) = false}

def C1 := C ∩ {f | f (term I ho) = true}

lemma isClosed_C0 : IsClosed (C0 C ho) := by
  refine' IsClosed.inter hC _
  have h : Continuous ((fun f ↦ f (term I ho) : ((WithTop I) → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact (continuous_iff_isClosed.mp h) {false} (isClosed_discrete _)

lemma isClosed_C1 : IsClosed (C1 C ho) := by
  refine' IsClosed.inter hC _
  have h : Continuous ((fun f ↦ f (term I ho) : ((WithTop I) → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact (continuous_iff_isClosed.mp h) {true} (isClosed_discrete _)

lemma support_C0 : Support (C0 C ho) ⊆ {j | ord I j < o} := by
  intro i hi
  dsimp [Support] at hi hsC
  simp only [Set.mem_setOf_eq]
  simp only [Order.lt_succ_iff, Set.setOf_subset_setOf, forall_exists_index, and_imp] at hsC
  obtain ⟨f, hf⟩ := hi
  dsimp [C0] at hf
  specialize hsC i f hf.1.1 hf.2
  refine' lt_of_le_of_ne hsC _
  have hf' := hf.1.2
  simp only [Set.mem_setOf_eq] at hf'
  have : i ≠ term I ho
  · refine' ne_of_apply_ne f _
    rw [hf.2, hf']
    simp
  have ht : ord I (term I ho) = o
  · dsimp [ord, term]
    simp only [Ordinal.typein_enum]
  rw [← ht]
  dsimp [ord]
  simpa only [Ordinal.typein_inj]

lemma support_C1 : Support (Res (C1 C ho) o) ⊆ {j | ord I j < o} :=
  support_Res_le_o _ _

lemma UnionEq : (C0 C ho) ∪ (C1 C ho) = C := by
  ext x
  constructor
  <;> intro hx
  · dsimp [C0, C1] at hx
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    rw [← and_or_left] at hx
    exact hx.1
  · dsimp [C0, C1]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [← and_or_left]
    refine' ⟨hx,_⟩
    by_cases h : x (term I ho) = false
    · left
      assumption
    · right
      simpa only [← Bool.not_eq_false]

def C0' : Set {i // i ∈ C} := {f | f.val ∈ C0 C ho}

def C1' : Set {i // i ∈ C} := {f | f.val ∈ C1 C ho}

lemma isOpen_false : IsOpen {f : WithTop I → Bool | f (term I ho) = false} := by
  have h : Continuous ((fun f ↦ f (term I ho) : ((WithTop I) → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact IsOpen.preimage h (isOpen_discrete {false})

lemma isOpen_true : IsOpen {f : WithTop I → Bool | f (term I ho) = true} := by
  have h : Continuous ((fun f ↦ f (term I ho) : ((WithTop I) → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact IsOpen.preimage h (isOpen_discrete {true})

lemma isClopen_C0' : IsClopen (C0' C ho) := by
  constructor
  · have := IsOpen.preimage (continuous_subtype_val : Continuous (fun (i : {i // i ∈ C}) ↦ i.val))
      (isOpen_false ho)
    suffices h : C0' C ho = Subtype.val ⁻¹' {f | f (term I ho) = false}
    · rw [h]
      exact this
    ext x
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨x.prop, hx⟩⟩
  · have := IsClosed.preimage (continuous_subtype_val : Continuous (fun (i : {i // i ∈ C}) ↦ i.val))
      (isClosed_C0 C hC ho)
    suffices h : C0' C ho = Subtype.val ⁻¹' (C0 C ho)
    · rw [h]
      exact this
    rfl

lemma isClopen_C1' : IsClopen (C1' C ho) := by
  constructor
  · have := IsOpen.preimage (continuous_subtype_val : Continuous (fun (i : {i // i ∈ C}) ↦ i.val))
      (isOpen_true ho)
    suffices h : C1' C ho = Subtype.val ⁻¹' {f | f (term I ho) = true}
    · rw [h]
      exact this
    ext x
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨x.prop, hx⟩⟩
  · have := IsClosed.preimage (continuous_subtype_val : Continuous (fun (i : {i // i ∈ C}) ↦ i.val))
      (isClosed_C1 C hC ho)
    suffices h : C1' C ho = Subtype.val ⁻¹' (C1 C ho)
    · rw [h]
      exact this
    rfl

lemma union_C0'C1'_eq_univ : (C0' C ho) ∪ (C1' C ho) = Set.univ := by
  rw [(by rfl : C0' C ho = Subtype.val ⁻¹' (C0 C ho)),
    (by rfl : C1' C ho = Subtype.val ⁻¹' (C1 C ho)),
    (by simp only [← Subtype.coe_preimage_self] :
    (Set.univ : Set {i // i ∈ C}) = Subtype.val ⁻¹' C)]
  simp only [← Set.preimage_union]
  rw [UnionEq]

def C' := C0 C ho ∩ Res (C1 C ho) o

lemma isClosed_C' : IsClosed (C' C ho) :=
IsClosed.inter (isClosed_C0 _ hC _) (isClosed_Res (C1 C ho) o (isClosed_C1 _ hC _))

lemma support_C' : Support (C' C ho) ⊆ {j | ord I j < o} := by
  dsimp [Support]
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  obtain ⟨f,hf⟩ := hi
  dsimp [C'] at hf
  have hC1 := support_C1 C ho
  dsimp [Support] at hC1
  simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp] at hC1
  exact hC1 i f hf.1.2 hf.2

def CC'₀ : {i // i ∈ C' C ho} → {i // i ∈ C} := fun g ↦ ⟨g.val,g.prop.1.1⟩

lemma continuous_CC'₀ : Continuous (CC'₀ C ho) :=
Continuous.subtype_mk continuous_subtype_val _

lemma swapTrue_mem_C1 (f : {i // i ∈ Res (C1 C ho) o}) : SwapTrue o f.val ∈ C1 C ho := by
  obtain ⟨f,hf⟩ := f
  obtain ⟨g,hg⟩ := hf
  suffices : SwapTrue o f = g
  · rw [this]
    exact hg.1
  dsimp [SwapTrue]
  ext i
  split_ifs with h
  · dsimp [C1, term] at hg
    simp_rw [← h] at hg
    dsimp [ord] at hg
    simp only [Ordinal.enum_typein, Set.mem_inter_iff, Set.mem_setOf_eq] at hg
    exact hg.1.2.symm
  · dsimp [ProjOrd] at hg
    have := congr_fun hg.2 i
    split_ifs at this with h'
    · exact this.symm
    · simp only [not_lt] at h'
      have hh := Order.succ_le_of_lt (lt_of_le_of_ne h' (Ne.symm h))
      dsimp [Support] at hsC
      simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp] at hsC
      specialize hsC i g hg.1.1
      rw [← not_imp_not] at hsC
      simp only [not_lt, Bool.not_eq_true] at hsC
      rw [← this]
      exact (hsC hh).symm

lemma swapTrue_mem_C (f : {i // i ∈ C' C ho}) : SwapTrue o f.val ∈ C := by
  suffices : SwapTrue o f.val ∈ C1 C ho
  · exact this.1
  exact (swapTrue_mem_C1 C hsC ho ⟨f.val,f.prop.2⟩)

noncomputable
def CC'₁ : {i // i ∈ C' C ho} → {i // i ∈ C} :=
fun g ↦ ⟨SwapTrue o g.val, swapTrue_mem_C C hsC ho g⟩

lemma continuous_CC'₁ : Continuous (CC'₁ C hsC ho) :=
Continuous.subtype_mk (Continuous.comp (continuous_swapTrue o) continuous_subtype_val) _

noncomputable
def Linear_CC'₀ : LocallyConstant {i // i ∈ C} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C' C ho} ℤ :=
LocallyConstant.comapLinear (CC'₀ C ho) (continuous_CC'₀ C ho)

noncomputable
def Linear_CC'₁ : LocallyConstant {i // i ∈ C} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C' C ho} ℤ :=
LocallyConstant.comapLinear (CC'₁ C hsC ho) (continuous_CC'₁ C hsC ho)

noncomputable
def Linear_CC' : LocallyConstant {i // i ∈ C} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C' C ho} ℤ :=
Linear_CC'₁ C hsC ho - Linear_CC'₀ C ho

variable (o)

noncomputable
def Linear_ResC : LocallyConstant {i // i ∈ Res C o} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ :=
LocallyConstant.comapLinear _ (continuous_ResOnSubset C o)

def GoodProducts.v : GoodProducts (Res C o) → LocallyConstant {i // i ∈ Res C o} ℤ :=
eval (Res C o)

def GoodProducts.v' : GoodProducts (Res C o) → LocallyConstant {i // i ∈ C} ℤ :=
fun l ↦ l.1.eval C

def GoodProducts.w' : StartingWithMax C o → LocallyConstant {i // i ∈ C} ℤ :=
fun l ↦ l.1.eval C

def GoodProducts.u : GoodProducts (Res C o) ⊕ StartingWithMax C o →
    LocallyConstant {i // i ∈ C} ℤ :=
Sum.elim (v' C o) (w' C o)

lemma GoodProducts.injective_u : Function.Injective (u C o) := by
  have := injective C
  have hu := union_succ C o hsC
  have hr : GoodProducts (Res C o) ⊆ GoodProducts C
  · rw [hu]
    exact Set.subset_union_left _ _
  have hs : StartingWithMax C o ⊆ GoodProducts C
  · rw [hu]
    exact Set.subset_union_right _ _
  dsimp [eval] at this
  apply Function.Injective.sum_elim
  <;> dsimp [v', w']
  · intro a b h
    have hra : (⟨a.val, hr a.prop⟩ : GoodProducts C).val = a.val := by rfl
    have hrb : (⟨b.val, hr b.prop⟩ : GoodProducts C).val = b.val := by rfl
    dsimp at h
    rw [← hra, ← hrb] at h
    ext
    specialize this h
    apply_fun fun f ↦ f.val at this
    rwa [hra, hrb] at this
  · intro a b h
    have hsa : (⟨a.val, hs a.prop⟩ : GoodProducts C).val = a.val := by rfl
    have hsb : (⟨b.val, hs b.prop⟩ : GoodProducts C).val = b.val := by rfl
    dsimp at h
    rw [← hsa, ← hsb] at h
    ext
    specialize this h
    apply_fun fun f ↦ f.val at this
    rwa [hsa, hsb] at this
  · intro a b h
    have hra : (⟨a.val, hr a.prop⟩ : GoodProducts C).val = a.val := by rfl
    have hsb : (⟨b.val, hs b.prop⟩ : GoodProducts C).val = b.val := by rfl
    rw [← hra, ← hsb] at h
    specialize this h
    apply_fun fun f ↦ f.val at this
    rw [hra, hsb] at this
    by_cases hanil : a.val.val = []
    · apply b.prop.2.1
      rwa [← this]
    · have ha' := Products.head_lt_ord_of_isGood C a.prop hanil
      simp_rw [← b.prop.2.2] at ha'
      dsimp [ord] at ha'
      simp only [Ordinal.typein_lt_typein] at ha'
      apply ne_of_lt ha'
      rw [this]

lemma GoodProducts.huv : u C o ∘ Sum.inl = Linear_ResC C o ∘ v C o := by
  dsimp [u, v, v', Linear_ResC, LocallyConstant.comapLinear, eval]
  ext1 l
  rw [← Products.eval_comapFacC C l.prop]
  rfl

variable {o}

noncomputable
def GoodProducts.w : StartingWithMax C o → LocallyConstant {i // i ∈ C' C ho} ℤ :=
Linear_CC' C hsC ho ∘ u C o ∘ Sum.inr

lemma GoodProducts.huw : Linear_CC' C hsC ho ∘ u C o ∘ Sum.inr = w C hsC ho := by rfl

lemma swapTrue_swapFalse (x : WithTop I → Bool) (hx : x ∈ Res (C1 C ho) o) :
    SwapFalse o (SwapTrue o x) = x := by
  ext i
  dsimp [SwapTrue, SwapFalse]
  split_ifs with h
  · obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    dsimp [ProjOrd]
    split_ifs with h'
    · exfalso
      exact (ne_of_lt h') h
    · rfl
  · rfl

lemma CC_comp_zero : ∀ y, (Linear_CC' C hsC ho) ((Linear_ResC C o) y) = 0 := by
  intro y
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁]
  ext x
  rw [LocallyConstant.sub_apply]
  dsimp [Linear_ResC, LocallyConstant.comapLinear]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
  suffices : ResOnSubset C o (CC'₁ C hsC ho x) = ResOnSubset C o (CC'₀ C ho x)
  · rw [this]
    simp only [sub_self]
  dsimp [CC'₀, CC'₁, ResOnSubset, ProjOrd]
  ext i
  dsimp
  split_ifs with h
  · dsimp [SwapTrue]
    split_ifs with h'
    · exfalso
      exact (ne_of_lt h) h'
    · rfl
  · rfl

lemma C0_projOrd : ∀ x, x ∈ C0 C ho → ProjOrd o x = x := by
  intro x hx
  ext i
  simp only [ProjOrd, ite_eq_left_iff, not_lt]
  intro hi
  rw [le_iff_lt_or_eq] at hi
  cases' hi with hi hi
  · simp only [Support, Order.lt_succ_iff, Set.setOf_subset_setOf, forall_exists_index,
      and_imp] at hsC
    specialize hsC i x hx.1
    rw [← not_imp_not] at hsC
    simp only [not_le, Bool.not_eq_true] at hsC
    exact (hsC hi).symm
  · simp only [C0, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    rw [← hx.2]
    congr 1
    dsimp [term]
    simp_rw [hi]
    simp only [ord, Ordinal.enum_typein]

lemma C1_projOrd : ∀ x, x ∈ C1 C ho → SwapTrue o (ProjOrd o x) = x := by
  intro x hx
  ext i
  dsimp [SwapTrue, ProjOrd]
  split_ifs with hi h
  · rw [hx.2.symm]
    congr
    dsimp [term]
    simp_rw [← hi]
    simp only [ord, Ordinal.enum_typein]
  · rfl
  · simp only [not_lt] at h
    have h' : o < ord I i := lt_of_le_of_ne h (Ne.symm hi)
    simp only [Support, Order.lt_succ_iff, Set.setOf_subset_setOf, forall_exists_index,
      and_imp] at hsC
    specialize hsC i x hx.1
    rw [← not_imp_not] at hsC
    simp only [not_le, Bool.not_eq_true] at hsC
    exact (hsC h').symm

lemma C0_eq_res : C0 C ho = Res (C0 C ho) o := by
  ext y
  constructor
  <;> intro hy
  · exact ⟨y, ⟨hy, C0_projOrd C hsC ho y hy⟩⟩
  · obtain ⟨z, hz⟩ := hy
    rw [← hz.2]
    simp only [C0, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rw [C0_projOrd C hsC ho z hz.1]
      exact hz.1.1
    · simp only [ProjOrd, ord, term, Ordinal.typein_enum, lt_self_iff_false, ite_false]

lemma mem_res_of_mem_C0 : ∀ x, x ∈ C0 C ho → x ∈ Res C o := by
  intro x hx
  exact ⟨x, ⟨hx.1,C0_projOrd C hsC ho x hx⟩⟩

lemma mem_resC0_of_mem_C0 : ∀ x, x ∈ C0 C ho → x ∈ Res (C0 C ho) o := by
  intro x hx
  rwa [← C0_eq_res C hsC ho]

lemma mem_C0_of_mem_resC0 : ∀ x, x ∈ Res (C0 C ho) o → x ∈ C0 C ho := by
  intro x hx
  rwa [C0_eq_res C hsC ho]

noncomputable
def C0_homeo : C0 C ho ≃ₜ {i : Res C o | i.val ∈ Res (C0 C ho) o} where
  toFun := fun x ↦ ⟨⟨x.val, mem_res_of_mem_C0 C hsC ho x.val x.prop⟩,
    mem_resC0_of_mem_C0 C hsC ho x.val x.prop⟩
  invFun := fun x ↦ ⟨x.val.val, mem_C0_of_mem_resC0 C hsC ho x.val.val x.prop⟩
  left_inv := by
    intro x
    dsimp
  right_inv := by
    intro x
    dsimp
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_induced_dom _) _
  continuous_invFun := by
    refine' Continuous.subtype_mk _ _
    exact Continuous.comp continuous_subtype_val continuous_subtype_val

lemma projOrd_eq_swapFalse : ∀ x, x ∈ C → ProjOrd o x = SwapFalse o x := by
  intro x hx
  ext i
  dsimp [ProjOrd, SwapFalse]
  split_ifs with hi hi' hi'
  · exfalso
    exact (ne_of_lt hi) hi'
  · simp only [Support, Order.lt_succ_iff, Set.setOf_subset_setOf, forall_exists_index,
      and_imp] at hsC
    specialize hsC i x hx
    rw [← not_imp_not] at hsC
  · rfl
  · simp only [Support, Order.lt_succ_iff, Set.setOf_subset_setOf, forall_exists_index,
      and_imp] at hsC
    specialize hsC i x hx
    rw [← not_imp_not] at hsC
    simp only [not_le, Bool.not_eq_true] at hsC
    apply Eq.symm ∘ hsC
    simp only [not_lt] at hi
    exact lt_of_le_of_ne hi (Ne.symm hi')

lemma mem_res_of_mem_C1 : ∀ x, x ∈ C1 C ho → SwapFalse o x ∈ Res C o := by
  intro x hx
  refine' ⟨x, ⟨hx.1, _⟩⟩
  exact projOrd_eq_swapFalse C hsC x hx.1

lemma mem_resC1_of_mem_C1 : ∀ x, x ∈ C1 C ho → SwapFalse o x ∈ Res (C1 C ho) o := by
  intro x hx
  refine' ⟨x, ⟨hx, _⟩⟩
  exact projOrd_eq_swapFalse C hsC x hx.1

lemma swapFalse_swapTrue (x : WithTop I → Bool) (hx : x ∈ C1 C ho) :
    SwapTrue o (SwapFalse o x) = x := by
  ext i
  dsimp [SwapTrue, SwapFalse]
  split_ifs with h
  · rw [← hx.2]
    congr
    dsimp [term]
    simp_rw [← h]
    simp only [ord, Ordinal.enum_typein]
  · rfl

lemma mem_C1_of_mem_resC1 : ∀ x, x ∈ Res (C1 C ho) o → SwapTrue o x ∈ C1 C ho := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy.2, projOrd_eq_swapFalse C hsC y hy.1.1, swapFalse_swapTrue C ho y hy.1]
  exact hy.1

noncomputable
def C1_homeo : C1 C ho ≃ₜ {i : Res C o | i.val ∈ Res (C1 C ho) o} where
  toFun := fun x ↦ ⟨⟨SwapFalse o x.val, mem_res_of_mem_C1 C hsC ho x.val x.prop⟩,
    mem_resC1_of_mem_C1 C hsC ho x.val x.prop⟩
  invFun := fun x ↦ ⟨SwapTrue o x.val.val, mem_C1_of_mem_resC1 C hsC ho x.val.val x.prop⟩
  left_inv := by
    intro x
    simp_rw [swapFalse_swapTrue C ho x.val x.prop]
  right_inv := by
    intro x
    dsimp
    simp_rw [swapTrue_swapFalse C ho x.val x.prop]
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := by
    refine' Continuous.subtype_mk _ _
    refine' Continuous.subtype_mk _ _
    refine' Continuous.comp (continuous_swapFalse o) continuous_subtype_val
  continuous_invFun := by
    refine' Continuous.subtype_mk _ _
    exact Continuous.comp (continuous_swapTrue o) (Continuous.comp continuous_subtype_val
      continuous_subtype_val)

lemma CC_exact {f : LocallyConstant {i // i ∈ C} ℤ} (hf : Linear_CC' C hsC ho f = 0) :
    ∃ y, Linear_ResC C o y = f := by
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁] at hf
  rw [sub_eq_zero] at hf
  dsimp [LocallyConstant.comapLinear] at hf
  rw [← LocallyConstant.coe_inj] at hf
  rw [LocallyConstant.coe_comap _ _ (continuous_CC'₁ _ _ _)] at hf
  rw [LocallyConstant.coe_comap _ _ (continuous_CC'₀ _ _)] at hf
  have hC₀' : IsClosed (Res (C0 C ho) o) := isClosed_Res (C0 C ho) o (isClosed_C0 C hC ho)
  have hC₁' : IsClosed (Res (C1 C ho) o) := isClosed_Res (C1 C ho) o (isClosed_C1 C hC ho)
  have hC₀ : IsClosed {i : Res C o | i.val ∈ Res (C0 C ho) o}
  · rw [isClosed_induced_iff]
    exact ⟨Res (C0 C ho) o, ⟨hC₀', rfl⟩⟩
  have hC₁ : IsClosed {i : Res C o | i.val ∈ Res (C1 C ho) o}
  · rw [isClosed_induced_iff]
    exact ⟨Res (C1 C ho) o, ⟨hC₁', rfl⟩⟩
  let e₀ : C0 C ho ≃ₜ {i : Res C o | i.val ∈ Res (C0 C ho) o} := C0_homeo C hsC ho
  let E₀ : LocallyConstant (C0 C ho) ℤ ≃ LocallyConstant _ ℤ := LocallyConstant.equiv e₀
  let e₁ : C1 C ho ≃ₜ {i : Res C o | i.val ∈ Res (C1 C ho) o} := C1_homeo C hsC ho
  let E₁ : LocallyConstant (C1 C ho) ℤ ≃ LocallyConstant _ ℤ := LocallyConstant.equiv e₁
  let C₀C : C0 C ho → {i // i ∈ C} := fun x ↦ ⟨x.val, x.prop.1⟩
  have h₀ : Continuous C₀C := Continuous.subtype_mk continuous_induced_dom _
  let C₁C : C1 C ho → {i // i ∈ C} := fun x ↦ ⟨x.val, x.prop.1⟩
  have h₁ : Continuous C₁C := Continuous.subtype_mk continuous_induced_dom _
  refine ⟨LocallyConstant.piecewise hC₀ hC₁ ?_ (E₀ (f.comap C₀C)) (E₁ (f.comap C₁C)) ?_ 0, ?_⟩
  · ext ⟨x, hx⟩
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨y, ⟨hyC, hy⟩⟩ := hx
    by_cases hyt : y (term I ho) = true
    · right
      rw [← hy]
      refine' ⟨y, ⟨⟨hyC, hyt⟩, rfl⟩⟩
    · left
      simp only [Bool.not_eq_true] at hyt
      rw [← hy]
      refine' ⟨y, ⟨⟨hyC, hyt⟩, rfl⟩⟩
  · rintro ⟨x, hrx⟩ hx
    have hx' : x ∈ C' C ho
    · refine' ⟨_, hx.2⟩
      rw [C0_eq_res C hsC ho]
      exact hx.1
    dsimp [LocallyConstant.equiv]
    rw [LocallyConstant.coe_comap_apply _ _ (Homeomorph.continuous _)]
    rw [LocallyConstant.coe_comap_apply _ _ h₀]
    rw [LocallyConstant.coe_comap_apply _ _ (Homeomorph.continuous _)]
    rw [LocallyConstant.coe_comap_apply _ _ h₁]
    exact (congrFun hf ⟨x, hx'⟩).symm
  · dsimp [Linear_ResC, LocallyConstant.comapLinear]
    ext ⟨x,hx⟩
    rw [← UnionEq C ho] at hx
    cases' hx with hx₀ hx₁
    · rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
      dsimp [LocallyConstant.piecewise, Set.piecewise', Set.piecewise]
      split_ifs with h
      · dsimp [Function.ExtendBy, LocallyConstant.equiv]
        split_ifs with h'
        · rw [LocallyConstant.coe_comap_apply _ _ (Homeomorph.continuous _)]
          rw [LocallyConstant.coe_comap_apply _ _ h₀]
          congr 1
          ext i
          dsimp [ResOnSubset] at h ⊢
          dsimp [C0_homeo]
          rw [C0_projOrd C hsC ho x hx₀]
        · exfalso
          exact h' h
      · dsimp [Function.ExtendBy, LocallyConstant.equiv]
        split_ifs with h'
        · rw [LocallyConstant.coe_comap_apply _ _ (Homeomorph.continuous _)]
          rw [LocallyConstant.coe_comap_apply _ _ h₁]
          have hx' : x ∈ C' C ho
          · refine' ⟨hx₀, _⟩
            rwa [← C0_projOrd C hsC ho x hx₀]
          dsimp [ResOnSubset]
          simp_rw [C0_projOrd C hsC ho x hx₀]
          exact congrFun hf ⟨x, hx'⟩
        · exfalso
          apply h
          exact ⟨x, ⟨hx₀, rfl⟩⟩
    · rw [LocallyConstant.coe_comap_apply _ _ (continuous_ResOnSubset _ _)]
      dsimp [LocallyConstant.piecewise, Set.piecewise', Set.piecewise]
      split_ifs with h
      · dsimp [Function.ExtendBy, LocallyConstant.equiv]
        split_ifs with h'
        · rw [LocallyConstant.coe_comap_apply _ _ (Homeomorph.continuous _)]
          rw [LocallyConstant.coe_comap_apply _ _ h₀]
          dsimp [C0_homeo]
          have hx' : ProjOrd o x ∈ C' C ho
          · refine' ⟨_, ⟨x, ⟨hx₁, rfl⟩⟩⟩
            rwa [C0_eq_res C hsC ho]
          have := congrFun hf ⟨ProjOrd o x, hx'⟩
          dsimp [ResOnSubset]
          dsimp [CC'₁] at this
          simp_rw [C1_projOrd C hsC ho x hx₁] at this
          exact this.symm
        · exfalso
          exact h' h
      · dsimp [Function.ExtendBy, LocallyConstant.equiv]
        split_ifs with h'
        · rw [LocallyConstant.coe_comap_apply _ _ (Homeomorph.continuous _)]
          rw [LocallyConstant.coe_comap_apply _ _ h₁]
          congr 1
          ext i
          dsimp [ResOnSubset] at h ⊢
          dsimp [C1_homeo]
          rw [C1_projOrd C hsC ho x hx₁]
        · exfalso
          apply h'
          exact ⟨x, ⟨hx₁, rfl⟩⟩

noncomputable
def C1_homeo' : C1' C ho ≃ₜ {i : Res C o | i.val ∈ Res (C1 C ho) o} where
  toFun := fun x ↦ ⟨⟨SwapFalse o x.val, mem_res_of_mem_C1 C hsC ho x.val x.prop⟩,
    mem_resC1_of_mem_C1 C hsC ho x.val x.prop⟩
  invFun := fun x ↦ ⟨⟨SwapTrue o x.val.val,
    (swapTrue_mem_C1 C hsC ho ⟨x.val, x.prop⟩).1⟩, mem_C1_of_mem_resC1 C hsC ho x.val.val x.prop⟩
  left_inv := by
    intro x
    simp_rw [swapFalse_swapTrue C ho x.val x.prop]
  right_inv := by
    intro x
    dsimp
    simp_rw [swapTrue_swapFalse C ho x.val x.prop]
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := by
    refine' Continuous.subtype_mk _ _
    refine' Continuous.subtype_mk _ _
    refine' Continuous.comp (continuous_swapFalse o) _
    exact Continuous.comp continuous_subtype_val continuous_subtype_val
  continuous_invFun := by
    refine' Continuous.subtype_mk _ _
    refine' Continuous.subtype_mk _ _
    exact Continuous.comp (continuous_swapTrue o) (Continuous.comp continuous_subtype_val
      continuous_subtype_val)

lemma LocallyConstant.LeftExact : CategoryTheory.Mono (ModuleCat.ofHom (Linear_ResC C o)) ∧
  CategoryTheory.Exact
    (ModuleCat.ofHom (Linear_ResC C o))
    (ModuleCat.ofHom (Linear_CC' C hsC ho)) :=
{ left := by
    rw [ModuleCat.mono_iff_injective]
    exact LocallyConstant.comap_injective (ResOnSubset C o)
      (continuous_ResOnSubset C o) (surjective_ResOnSubset C o)
  right := by
    rw [ModuleCat.exact_iff]
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    <;> intro hf
    · obtain ⟨y,hy⟩ := hf
      rw [← hy]
      dsimp [ModuleCat.ofHom]
      exact CC_comp_zero _ _ _ y
    · exact CC_exact _ hC _ ho hf }

lemma swapTrue_eq_true : ∀ x, SwapTrue o x (term I ho) = true := by
  intro x
  dsimp [SwapTrue]
  split_ifs with h
  · rfl
  · dsimp [ord, term] at h
    simp only [Ordinal.typein_enum, not_true] at h

lemma mem_C'_eq_false : ∀ x, x ∈ C' C ho → x (term I ho) = false := by
  rintro x ⟨_,⟨y,⟨_,hy⟩⟩⟩
  rw [← hy]
  dsimp [ProjOrd]
  split_ifs with h
  · dsimp [ord, term] at h
    simp only [Ordinal.typein_enum, lt_self_iff_false] at h
  · rfl

lemma eo_eq_one : Linear_CC' C hsC ho (e C (term I ho)) = 1 := by
  ext x
  dsimp [Linear_CC', Linear_CC'₁, Linear_CC'₀, LocallyConstant.comapLinear]
  rw [LocallyConstant.sub_apply]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)]
  dsimp [CC'₀, CC'₁, e, BoolToZ]
  split_ifs with h₀ h₁
  · exfalso
    rwa [mem_C'_eq_false C ho x x.prop, Bool.coe_false] at h₁
  · rfl
  · exfalso
    exact h₀ (swapTrue_eq_true ho x)
  · exfalso
    exact h₀ (swapTrue_eq_true ho x)

def LC_eval (x : {i // i ∈ C}) : (LocallyConstant {i // i ∈ C} ℤ) → ℤ :=
fun f ↦ f x

def Products.Apply (l : Products (WithTop I)) (x : {i // i ∈ C}) : List ℤ :=
List.map ((LC_eval C x) ∘ (e C)) l.val

def List.Apply (l : List (WithTop I)) (x : {i // i ∈ C}) : List ℤ :=
List.map ((LC_eval C x) ∘ (e C)) l

lemma Products.eval_apply (l : Products (WithTop I)) (x : {i // i ∈ C}) :
    l.eval C x = List.prod (Apply C l x) := by
  dsimp [eval, Apply, LC_eval]
  obtain ⟨l,hl⟩ := l
  induction l with
  | nil => rfl
  | cons a as ih =>
    · simp only [List.map, List.prod_cons, LocallyConstant.coe_mul, Pi.mul_apply,
        Function.comp_apply, mul_eq_mul_left_iff]
      specialize ih (List.Chain'.sublist hl (List.tail_sublist (a::as)))
      left
      exact ih

def List.eval (l : List (WithTop I)) := (l.map (e C)).prod

lemma List.eval_apply (l : List (WithTop I)) (x : {i // i ∈ C}) :
    eval C l x = List.prod (Apply C l x) := by
  dsimp [eval, Apply, LC_eval]
  induction l with
  | nil => rfl
  | cons a as ih =>
    · simp only [List.map, List.prod_cons, LocallyConstant.coe_mul, Pi.mul_apply,
        Function.comp_apply, mul_eq_mul_left_iff]
      left
      exact ih

lemma Products.eval_eq (l : Products (WithTop I)) (x : {i // i ∈ C}) :
    l.eval C x = if ∀ i, i ∈ l.val → (x.val i = true) then 1 else 0 := by
  rw [eval_apply]
  split_ifs with h
  · dsimp [Apply]
    suffices : ∀ y, y ∈ List.map (LC_eval C x ∘ e C) l.val → y = 1
    · exact List.prod_eq_one this
    intro y hy
    simp only [List.mem_map, Function.comp_apply] at hy
    obtain ⟨i,hi⟩ := hy
    specialize h i hi.1
    dsimp [LC_eval, e, BoolToZ] at hi
    rw [← hi.2]
    simp only [ite_eq_left_iff]
    exact fun hx ↦ hx h
  · simp only [List.prod_eq_zero_iff]
    dsimp [Apply]
    simp only [List.mem_map, Function.comp_apply]
    push_neg at h
    obtain ⟨i,hi⟩ := h
    use i
    refine' ⟨hi.1,_⟩
    dsimp [LC_eval, e, BoolToZ]
    simp only [ite_eq_right_iff]
    exact hi.2

lemma List.eval_eq (l : List (WithTop I)) (x : {i // i ∈ C}) :
    eval C l x = if ∀ i, i ∈ l → (x.val i = true) then 1 else 0 := by
  rw [eval_apply]
  split_ifs with h
  · dsimp [Apply]
    apply List.prod_eq_one
    intro y hy
    simp only [List.mem_map, Function.comp_apply] at hy
    obtain ⟨i,hi⟩ := hy
    specialize h i hi.1
    dsimp [LC_eval, e, BoolToZ] at hi
    rw [← hi.2]
    simp only [ite_eq_left_iff]
    exact fun hx ↦ hx h
  · simp only [List.prod_eq_zero_iff]
    dsimp [Apply]
    simp only [List.mem_map, Function.comp_apply]
    push_neg at h
    obtain ⟨i,hi⟩ := h
    use i
    refine' ⟨hi.1,_⟩
    dsimp [LC_eval, e, BoolToZ]
    simp only [ite_eq_right_iff]
    exact hi.2

lemma List.eval_eq_unapply (x : {i // i ∈ C}) :
    (fun (l : {q : Products (WithTop I) | term I ho ∉ q.val}) (a : ℤ) ↦
    a • (eval C (term I ho :: l.val.val) x)) =
    fun l a ↦ a * (if ∀ i, i ∈ (term I ho :: l.val.val) → (x.val i = true) then 1 else 0) := by
  ext l
  rw [eval_eq C (term I ho :: l.val.val) x]
  simp

def Products.Tail (l : Products (WithTop I)) : Products (WithTop I) :=
⟨l.val.tail, List.Chain'.tail l.prop⟩

def GoodProducts.MaxTail (l : StartingWithMax C o) : Products (WithTop I) :=
l.val.Tail

lemma Products.max_eq_o_cons_tail (l : Products (WithTop I)) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) : l.val = term I ho :: l.Tail.val := by
  rw [← List.cons_head!_tail hl, hlh]
  rfl

lemma GoodProducts.max_eq_o_cons_tail (l : StartingWithMax C o) :
    l.val.val = (term I ho) :: (MaxTail C l).val := by
  rw [← List.cons_head!_tail l.prop.2.1]
  dsimp [MaxTail]
  congr
  dsimp [term]
  simp_rw [← l.prop.2.2]
  dsimp [ord]
  simp only [Ordinal.enum_typein]

lemma Products.max_eq_eval (l : Products (WithTop I)) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) :
    Linear_CC' C hsC ho (l.eval C) = l.Tail.eval (C' C ho) := by
  have hl' : l.val = (term I ho) :: l.Tail.val := max_eq_o_cons_tail ho l hl hlh
  have hlc : ((term I ho) :: l.Tail.val).Chain' (·>·)
  · rw [← hl']
    exact l.prop
  have hl : l = ⟨(term I ho) :: l.Tail.val, hlc⟩
  · simp_rw [← hl']
    rfl
  rw [hl]
  rw [Products.evalCons]
  ext x
  dsimp [Linear_CC', Linear_CC'₁, Linear_CC'₀, LocallyConstant.comapLinear]
  rw [LocallyConstant.sub_apply]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)]
  dsimp [CC'₀, CC'₁]
  rw [Products.eval_eq]
  rw [Products.eval_eq]
  rw [Products.eval_eq]
  simp only [mul_ite, mul_one, mul_zero]
  have hi' : ∀ i, i ∈ l.Tail.val → (x.val i = SwapTrue o x.val i)
  · intro i hi
    dsimp [SwapTrue]
    split_ifs with h₁
    · exfalso
      suffices : i < term I ho
      · dsimp [term] at this
        simp_rw [← h₁] at this
        dsimp [ord] at this
        simp only [Ordinal.enum_typein, lt_self_iff_false] at this
      rw [← gt_iff_lt]
      apply List.Chain.rel _ hi
      exact hlc
    · rfl
  split_ifs with h₁ h₂ h₂ h₃ h₄ h₅ h₆
  <;> dsimp [e, BoolToZ]
  · split_ifs with hh₁ hh₂
    · exfalso
      rwa [mem_C'_eq_false C ho x x.prop, Bool.coe_false] at hh₂
    · rfl
    · exfalso
      exact hh₁ (swapTrue_eq_true _ _)
    · exfalso
      exact hh₁ (swapTrue_eq_true _ _)
  · push_neg at h₂
    obtain ⟨i, hi⟩ := h₂
    specialize h₁ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [hi']
  · push_neg at h₂
    obtain ⟨i, hi⟩ := h₂
    specialize h₁ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [hi']
  · push_neg at h₂
    obtain ⟨i, hi⟩ := h₂
    specialize h₁ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [hi']
  · push_neg at h₁
    obtain ⟨i, hi⟩ := h₁
    specialize h₄ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [← hi']
  · push_neg at h₁
    obtain ⟨i, hi⟩ := h₁
    specialize h₄ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [← hi']
  · push_neg at h₁
    obtain ⟨i, hi⟩ := h₁
    specialize h₆ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [← hi']
  · rfl

lemma Products.max_eq_eval_unapply :
    Set.restrict {l : Products (WithTop I) | term I ho ∉ l.val} (Products.eval (C' C ho)) =
    Linear_CC' C hsC ho ∘ (fun (l : {l : Products (WithTop I) | term I ho ∉ l.val}) ↦
    (List.eval C (term I ho :: l.val.val)))
    := by
  ext l x
  dsimp [Linear_CC', Linear_CC'₁, Linear_CC'₀, LocallyConstant.comapLinear]
  rw [LocallyConstant.sub_apply]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)]
  dsimp [CC'₀, CC'₁]
  simp only [List.prod_cons, LocallyConstant.coe_mul, Pi.mul_apply]
  rw [Products.eval_eq]
  rw [List.eval_eq]
  rw [List.eval_eq]
  simp only [ite_mul, one_mul, zero_mul]
  have htx : x.val (term I ho) = false := x.prop.1.2
  have hxs : ∀ i, i ∈ l.val.val → x.val i = SwapTrue o x i
  · intro i hi
    dsimp [SwapTrue]
    split_ifs with h₁
    · exfalso
      suffices : i ≠ term I ho
      · apply this
        dsimp [term]
        simp_rw [← h₁]
        simp only [ord, Ordinal.enum_typein]
      intro hit
      apply l.prop
      simp_rw [← hit]
      exact hi
    · rfl
  have hst : SwapTrue o x (term I ho) = true
  · dsimp [SwapTrue]
    split_ifs with h
    · rfl
    · exfalso
      apply h
      simp only [ord, term, Ordinal.typein_enum]
  split_ifs with h₁ h₂ h₂ h₃ h₄ h₅ h₆
  <;> dsimp [e, BoolToZ]
  · exfalso
    specialize h₂ (term I ho) (by simp only [List.mem_cons, true_or])
    rw [Bool.eq_false_iff] at htx
    exact htx h₂
  · rfl
  · exfalso
    specialize h₃ (term I ho) (by simp only [List.mem_cons, true_or])
    rw [Bool.eq_false_iff] at htx
    exact htx h₃
  · exfalso
    apply h₂
    intro i hi
    simp only [List.find?, List.mem_cons] at hi
    cases' hi with hi hi
    · rw [hi]
      exact hst
    · rw [← hxs i hi]
      exact h₁ i hi
  · rfl
  · push_neg at h₁
    exfalso
    obtain ⟨i, ⟨hi, hit⟩⟩ := h₁
    apply hit
    rw [hxs i hi]
    apply h₄
    right
    exact hi
  · exfalso
    apply h₄
    intro i hi
    simp only [List.find?, List.mem_cons] at hi
    cases' hi with hi hi
    · rw [hi]
      exact hst
    · rw [← hxs i hi]
      exact h₆ i (List.mem_cons_of_mem _ hi)
  · rfl

lemma GoodProducts.max_eq_eval (l : StartingWithMax C o) :
    Linear_CC' C hsC ho (l.val.eval C) = (MaxTail C l).eval (C' C ho) := by
  have hl' : l.val.val = (term I ho) :: (MaxTail C l).val := max_eq_o_cons_tail C ho l
  have hlc : ((term I ho) :: (MaxTail C l).val).Chain' (·>·)
  · rw [← hl']
    exact l.val.prop
  have hl : l.val = ⟨(term I ho) :: (MaxTail C l).val, hlc⟩
  · simp_rw [← hl']
    rfl
  rw [hl]
  rw [Products.evalCons]
  ext x
  dsimp [Linear_CC', Linear_CC'₁, Linear_CC'₀, LocallyConstant.comapLinear]
  rw [LocallyConstant.sub_apply]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)]
  dsimp [CC'₀, CC'₁]
  rw [Products.eval_eq]
  rw [Products.eval_eq]
  rw [Products.eval_eq]
  simp only [mul_ite, mul_one, mul_zero]
  have hi' : ∀ i, i ∈ (MaxTail C l).val → (x.val i = SwapTrue o x.val i)
  · intro i hi
    dsimp [SwapTrue]
    split_ifs with h₁
    · exfalso
      suffices : i < term I ho
      · dsimp [term] at this
        simp_rw [← h₁] at this
        dsimp [ord] at this
        simp only [Ordinal.enum_typein, lt_self_iff_false] at this
      rw [← gt_iff_lt]
      apply List.Chain.rel _ hi
      exact hlc
    · rfl
  split_ifs with h₁ h₂ h₂
  <;> dsimp [e, BoolToZ]
  · split_ifs with hh₁ hh₂
    · exfalso
      rwa [mem_C'_eq_false C ho x x.prop, Bool.coe_false] at hh₂
    · rfl
    · exfalso
      exact hh₁ (swapTrue_eq_true _ _)
    · exfalso
      exact hh₁ (swapTrue_eq_true _ _)
  · push_neg at h₂
    obtain ⟨i, hi⟩ := h₂
    specialize h₁ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [hi']
  · push_neg at h₁
    obtain ⟨i, hi⟩ := h₁
    specialize h₂ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [← hi']
  · rfl

lemma GoodProducts.max_eq_eval_unapply :
    (Linear_CC' C hsC ho) ∘ (fun (l : StartingWithMax C o) ↦ Products.eval C l.val) =
    (fun l ↦ (MaxTail C l).eval (C' C ho)) := by
  ext1 l
  exact max_eq_eval _ _ _ _

lemma Products.head_lt_ord_of_isGood' {l : Products (WithTop I)}
    (h : l.isGood (C' C ho)) : l.val ≠ [] → ord I (l.val.head!) < o := by
  intro hn
  by_contra h'
  apply h
  obtain ⟨l,hl⟩ := l
  dsimp at hn
  have hl' : List.Chain' (·>·) (l.head! :: l.tail)
  · rw [List.cons_head!_tail hn]
    exact hl
  have : (⟨l,hl⟩ : Products (WithTop I)) = ⟨l.head! :: l.tail, hl'⟩
  · simp_rw [List.cons_head!_tail hn]
  rw [this, evalCons (C' C ho) hl']
  have eZero : e (C' C ho) (List.head! l) = 0
  · dsimp [e]
    ext ⟨f,hf⟩
    dsimp [BoolToZ]
    dsimp [C',Res, ProjOrd] at hf
    obtain ⟨g, hg⟩ := hf.2
    rw [← hg.2]
    split_ifs
    · exfalso
      assumption
    · rfl
    · exfalso
      assumption
    · rfl
  rw [eZero]
  simp only [zero_mul, Submodule.zero_mem]

lemma GoodProducts.cons_o_chain' (l : GoodProducts (C' C ho)) :
    (term I ho :: l.val.val).Chain' (·>·) := by
  by_cases hl : l.val.val = []
  · rw [hl]
    simp only [List.chain'_singleton]
  · rw [List.chain'_cons']
    refine' ⟨_,l.val.prop⟩
    intro y hy
    have hy' := List.eq_cons_of_mem_head? hy
    have h := Products.head_lt_ord_of_isGood' C ho l.prop hl
    rw [hy'] at h
    dsimp [term]
    rw [← List.head!_cons y (List.tail l.val.val)]
    simp only [gt_iff_lt]
    rw [← Ordinal.typein_lt_typein (·<·)]
    dsimp [ord] at h
    simpa only [List.head!_cons, Ordinal.typein_enum]

def LocconstEval (x : {i // i ∈ C}) : LocallyConstant {i // i ∈ C} ℤ →ₗ[ℤ]  ℤ where
  toFun f := f x
  map_add' := by
    intro f g
    simp only [LocallyConstant.coe_add, Pi.add_apply]
  map_smul' := by
    intro a f
    simp only [zsmul_eq_mul, LocallyConstant.coe_mul, Pi.mul_apply, eq_intCast, Int.cast_id,
      smul_eq_mul, mul_eq_mul_right_iff]
    left
    rfl

def LocconstEvalMul (x : {i // i ∈ C}) : LocallyConstant {i // i ∈ C} ℤ →*  ℤ where
  toFun f := f x
  map_mul' := by
    intro f g
    simp only [LocallyConstant.coe_mul, Pi.mul_apply]
  map_one' := by
    rfl



noncomputable
def GoodProducts.finsupp (c : List (WithTop I) →₀ ℤ) :
    {q : Products (WithTop I) | term I ho ∉ q.val} →₀ ℤ :=
    let f : {q : {q : Products (WithTop I) | term I ho ∉ q.val} |
        term I ho :: q.val.val ∈ c.support} → c.support :=
      fun q ↦ ⟨term I ho :: q.val.val.val, q.prop⟩
    have hf : f.Injective := by
      intro a b hab
      ext
      rw [Subtype.ext_iff, List.cons_eq_cons] at hab
      exact Subtype.ext hab.2
    let g : {q : {q : Products (WithTop I) | term I ho ∉ q.val} |
        q.val.val ∈ c.support ∧ term I ho :: q.val.val ∉ c.support} → c.support :=
      fun q ↦ ⟨q.val.val.val, q.prop.1⟩
    have hg : g.Injective := by
      intro a b hab
      ext
      rw [Subtype.ext_iff] at hab
      exact Subtype.ext hab
    haveI hFf : Fintype {q : {q : Products (WithTop I) | term I ho ∉ q.val} |
        term I ho :: q.val.val ∈ c.support} :=
      Fintype.ofInjective f hf
    haveI hFg : Fintype {q : {q : Products (WithTop I) | term I ho ∉ q.val} |
        q.val.val ∈ c.support ∧ term I ho :: q.val.val ∉ c.support} :=
      Fintype.ofInjective g hg
{ support :=
  {q | term I ho :: q.val.val ∈ c.support}.toFinset ∪
  {q | q.val.val ∈ c.support ∧ term I ho :: q.val.val ∉ c.support}.toFinset
  toFun := fun q ↦ if term I ho :: q.val.val ∈ c.support then
      c (term I ho :: q.val.val) else (if q.val.val ∈ c.support then c q.val.val else 0)
  mem_support_toFun := by
    intro q
    constructor
    <;> intro hq
    · dsimp at *
      split_ifs with h hh
      · simp only [Finsupp.mem_support_iff, ne_eq] at h
        exact h
      · simp only [Finsupp.mem_support_iff, ne_eq] at hh
        exact hh
      · simp only [Finset.mem_union] at hq
        cases' hq with hq hq
        · exfalso
          have := @Set.mem_toFinset _ _ hFf q
          exact h (this.mp hq)
        · exfalso
          have := @Set.mem_toFinset _ _ hFg q
          exact hh (this.mp hq).1
    · dsimp at *
      split_ifs at hq with h hh
      · simp only [Finset.mem_union]
        left
        have := @Set.mem_toFinset _ _ hFf q
        exact this.mpr h
      · simp only [Finset.mem_union]
        right
        have := @Set.mem_toFinset _ _ hFg q
        exact this.mpr ⟨hh, h⟩
      · exfalso
        exact hq rfl
}

lemma GoodProducts.term_not_mem (l : GoodProducts (C' C ho)) (y : Products (WithTop I))
    (hy : y < l.val) : term I ho ∉ y.val := by
  cases' y with y hh
  induction y with
  | nil =>
    · simp only [List.not_mem_nil, not_false_eq_true]
  | cons a as ih =>
    · rw [List.mem_cons, not_or]
      refine' ⟨_,_⟩
      · intro h
        have hy : a :: as < l.val.val := hy
        by_cases hlnil : l.val.val = []
        · rw [hlnil] at hy
          exact List.Lex.not_nil_right _ _ hy
        · rw [← h, ← List.cons_head!_tail hlnil] at hy
          suffices : List.head! l.val.val :: List.tail l.val.val < term I ho :: as
          · simp only [← not_le] at this
            exact this (le_of_lt hy)
          apply List.Lex.rel
          have hlc := cons_o_chain' C ho l
          rw [← List.cons_head!_tail hlnil] at hlc
          have := List.Chain'.rel_head hlc
          exact this
      · have := List.Chain'.tail hh
        simp only [List.tail_cons] at this
        specialize ih this
        apply ih
        refine' lt_trans _ hy
        suffices : as < a :: as
        · exact this
        by_cases has : as = []
        · rw [has]
          apply List.Lex.nil
        · rw [← List.cons_head!_tail has] at hh ⊢
          apply List.Lex.rel
          have := List.Chain'.rel_head hh
          exact this

lemma GoodProducts.cons_o_mem_startingWithMax_range (l : GoodProducts (C' C ho)) :
    Products.eval (C' C ho) '' {m_1 | m_1 < l.val} =
    Set.restrict {l : Products (WithTop I) | term I ho ∉ l.val} (Products.eval (C' C ho)) ''
    {m_1 : {l : Products (WithTop I) | term I ho ∉ l.val} | m_1.val < l.val} := by
  ext x
  constructor
  <;> intro hx
  · obtain ⟨y, hy⟩ := hx
    have hy' : term I ho ∉ y.val := term_not_mem C ho l y hy.1
    refine' ⟨⟨y, hy'⟩, ⟨hy.1,_⟩⟩
    rw [← hy.2]
    rfl
  · obtain ⟨y, hy⟩ := hx
    refine' ⟨y.val, ⟨hy.1, _⟩⟩
    rw [← hy.2]
    rfl

lemma GoodProducts.maxTail_isGood (l : StartingWithMax C o)
    (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (Res C o)))) : (MaxTail C l).isGood (C' C ho) := by
  intro h
  rw [Finsupp.mem_span_image_iff_total, ← max_eq_eval C hsC ho] at h
  obtain ⟨m, ⟨hmmem, hmsum⟩⟩ := h
  rw [Finsupp.total_apply] at hmsum
  have : (Linear_CC' C hsC ho) (l.val.eval C) = (Linear_CC' C hsC ho)
    (Finsupp.sum m fun i a ↦ a • ((term I ho :: i.1).map (e C)).prod)
  · rw [← hmsum]
    simp only [LinearMap.map_finsupp_sum]
    apply Finsupp.sum_congr
    intro q hq
    rw [LinearMap.map_smul]
    rw [Finsupp.mem_supported] at hmmem
    have hx'' : q < MaxTail C l := hmmem hq
    have : ∃ (p : Products (WithTop I)), p.val ≠ [] ∧ p.val.head! = term I ho ∧ q = p.Tail
    · refine' ⟨⟨term I ho :: q.val, _⟩, ⟨_, _, _⟩⟩
      · rw [List.chain'_cons']
        refine' ⟨_, q.prop⟩
        cases' q with x' x'prop
        induction x' with
        | nil =>
          · intro y hy
            simp only [List.head?_nil, Option.mem_def] at hy
        | cons a as _ =>
          · intro y hy
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
            rw [← hy]
            by_cases hM : (MaxTail C l).val = []
            · have : a :: as < []
              · rw [← hM]
                exact hx''
              exfalso
              exact List.Lex.not_nil_right _ _ this
            · obtain ⟨b, L, hbL⟩ := List.exists_cons_of_ne_nil hM
              have : a :: as < b :: L
              · rw [← hbL]
                exact hx''
              have hab : a ≤ b
              · by_contra hab
                simp only [not_le] at hab
                have habs : b :: L < a :: as := List.Lex.rel hab
                simp only [← not_le] at habs
                exact habs (le_of_lt this)
              refine' lt_of_le_of_lt hab _
              have hll : l.val.val = term I ho :: b :: L
              · rw [max_eq_o_cons_tail C ho l, hbL]
              have hlp := l.val.prop
              rw [hll, List.chain'_cons] at hlp
              exact hlp.1
      · exact List.cons_ne_nil _ _
      · simp only [List.head!_cons]
      · simp only [Products.Tail, List.tail_cons, Subtype.coe_eta]
    obtain ⟨p, hp⟩ := this
    rw [hp.2.2, ← Products.max_eq_eval C hsC ho p hp.1 hp.2.1]
    dsimp [Products.eval]
    rw [Products.max_eq_o_cons_tail ho p hp.1 hp.2.1]
    rfl
  have hse := (LocallyConstant.LeftExact C hC hsC ho).2
  rw [ModuleCat.exact_iff] at hse
  dsimp [ModuleCat.ofHom] at hse
  rw [← LinearMap.sub_mem_ker_iff, ← hse] at this
  obtain ⟨(n : LocallyConstant {i // i ∈ Res C o} ℤ), hn⟩ := this
  rw [eq_sub_iff_add_eq] at hn
  have hn' := h₁ (Submodule.mem_top : n ∈ ⊤)
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn'
  obtain ⟨w,hc⟩ := hn'
  rw [← hc, map_finsupp_sum] at hn
  apply l.prop.1
  rw [← hn]
  apply Submodule.add_mem
  · rw [Finsupp.mem_span_image_iff_total]
    let f : GoodProducts (Res C o) → Products (WithTop I) := fun l ↦ l.val
    have hfi : f.Injective := fun _ _ h ↦ Subtype.ext h
    let v : Products (WithTop I) →₀ ℤ := w.mapDomain f
    refine' ⟨v, ⟨_, _⟩⟩
    · rw [Finsupp.mem_supported, Finsupp.mapDomain_support_of_injective hfi]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finsupp.mem_support_iff,
        ne_eq, Subtype.exists, exists_and_right, exists_eq_right] at hx
      simp only [Set.mem_setOf_eq]
      obtain ⟨hx, hx'⟩ := hx
      by_cases hxnil : x.val = []
      · cases' x with x _
        suffices : [] < l.val.val
        · rw [← hxnil] at this
          exact this
        rw [max_eq_o_cons_tail C ho l]
        exact List.Lex.nil
      · have := Products.head_lt_ord_of_isGood C hx hxnil
        suffices : x.val < l.val.val
        · exact this
        rw [max_eq_o_cons_tail C ho l, ← List.cons_head!_tail hxnil]
        apply List.Lex.rel
        have hto : ord I (term I ho) = o
        · simp only [ord, term, Ordinal.typein_enum]
        rw [← hto] at this
        simp only [ord, Ordinal.typein_lt_typein] at this
        exact this
    · rw [Finsupp.total_apply, Finsupp.sum_mapDomain_index_inj hfi]
      congr
      ext q r x
      rw [LinearMap.map_smul]
      dsimp [Linear_ResC, LocallyConstant.comapLinear]
      rw [← Products.eval_comapFacC C q.prop]
      rfl
  · rw [Finsupp.mem_span_image_iff_total]
    let f : Products (WithTop I) → List (WithTop I) := fun q ↦ term I ho :: q.val
    have hfi : Function.Injective f
    · intro a b hab
      exact Subtype.ext (List.tail_eq_of_cons_eq hab)
    let m' : List (WithTop I) →₀ ℤ := m.mapDomain f
    let g : Products (WithTop I) → List (WithTop I) := fun q ↦ q.val
    have hg : Function.Injective g
    · intro a b hab
      exact Subtype.ext hab
    let c : Products (WithTop I) →₀ ℤ := m'.comapDomain g (hg.injOn _)
    refine' ⟨c,⟨_, _⟩⟩
    · rw [Finsupp.mem_supported] at hmmem ⊢
      simp only [Finsupp.comapDomain_support, Finset.coe_preimage]
      have hm' : m'.support ⊆ Finset.image _ m.support := Finsupp.mapDomain_support
      refine' subset_trans (Set.preimage_mono hm') _
      simp only [Finset.image_val, Multiset.mem_dedup, Multiset.mem_map, Finset.mem_val]
      intro q hq
      simp only [Set.mem_preimage] at hq
      obtain ⟨a, ha⟩ := hq
      have ha' : a < MaxTail C l := hmmem ha.1
      simp only [Set.mem_setOf_eq, gt_iff_lt]
      suffices hql : q.val < l.val.val
      · exact hql
      rw [← ha.2, max_eq_o_cons_tail C ho]
      exact List.Lex.cons ha'
    · rw [Finsupp.total_apply]
      dsimp
      have hf : Set.BijOn g (g ⁻¹' m'.support) m'.support
      · refine' ⟨_,_,_⟩
        · intro x hx
          exact hx
        · exact Function.Injective.injOn hg _
        · intro x hx
          rw [Finsupp.mapDomain_support_of_injOn m (Function.Injective.injOn hfi _)] at hx ⊢
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
          obtain ⟨x', hx'⟩ := hx
          rw [Finsupp.mem_supported] at hmmem
          have hx'' : x' < MaxTail C l := hmmem hx'.1
          refine' ⟨⟨x,_⟩,⟨_,_⟩⟩
          · rw [← hx'.2, List.chain'_cons']
            refine' ⟨_, x'.prop⟩
            cases' x' with x' x'prop
            induction x' with
            | nil =>
              · intro y hy
                simp only [List.head?_nil, Option.mem_def] at hy
            | cons a as _ =>
              · intro y hy
                simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
                rw [← hy]
                by_cases hM : (MaxTail C l).val = []
                · have : a :: as < []
                  · rw [← hM]
                    exact hx''
                  exfalso
                  exact List.Lex.not_nil_right _ _ this
                · obtain ⟨b, L, hbL⟩ := List.exists_cons_of_ne_nil hM
                  have : a :: as < b :: L
                  · rw [← hbL]
                    exact hx''
                  have hab : a ≤ b
                  · by_contra hab
                    simp only [not_le] at hab
                    have habs : b :: L < a :: as := List.Lex.rel hab
                    simp only [← not_le] at habs
                    exact habs (le_of_lt this)
                  refine' lt_of_le_of_lt hab _
                  have hll : l.val.val = term I ho :: b :: L
                  · rw [max_eq_o_cons_tail C ho l, hbL]
                  have hlp := l.val.prop
                  rw [hll, List.chain'_cons] at hlp
                  exact hlp.1
          · simp only [Finset.coe_image, Set.mem_preimage, Set.mem_image, Finset.mem_coe]
            refine' ⟨x', hx'⟩
          · rfl
      let g' := fun (i : List (WithTop I)) (a : ℤ) ↦ a • (i.map (e C)).prod
      have hf' : (fun (i : Products (WithTop I)) (a : ℤ) ↦ a • i.eval C) = g' ∘ g := by rfl
      rw [hf']
      rw [Finsupp.sum_comapDomain g m' _ hf]
      dsimp
      rw [Finsupp.sum_mapDomain_index_inj hfi]
      rfl

lemma eEqeSubset {a : WithTop I} (V : Set (WithTop I → Bool)) (hV : V ⊆ C) :
    e C a ∘ (fun (v : V) ↦ (⟨v.val, hV v.prop⟩ : C)) = e V a := by
  ext ⟨f,hf⟩
  rfl

lemma eEqe_applySubset {a : WithTop I} (V : Set (WithTop I → Bool)) (hV : V ⊆ C) :
    ∀ x, (e C a) ((fun (v : V) ↦ (⟨v.val, hV v.prop⟩ : C)) x) = e V a x := by
  intro x
  exact congr_fun (eEqeSubset C V hV) x

lemma Products.evalFacSubset (V : Set (WithTop I → Bool)) (hV : V ⊆ C) (l : Products (WithTop I)) :
    l.eval C ∘ (fun (v : V) ↦ (⟨v.val, hV v.prop⟩ : C)) = l.eval V := by
  obtain ⟨l, hl⟩ := l
  induction l with
  | nil => rfl
  | cons a as ih =>
    · ext ⟨f, hf⟩
      rw [evalCons V hl]
      rw [evalCons C hl]
      dsimp
      rw [← eEqe_applySubset C V hV]
      specialize ih (List.Chain'.sublist hl (List.tail_sublist (a::as)))
      dsimp at ih
      congr! 1
      by_cases has : as = []
      · simp_rw [has]
        rfl
      · exact congr_fun ih ⟨f, hf⟩

lemma GoodProducts.isGood_subset (V : Set (WithTop I → Bool)) (hV : V ⊆ C)
    (l : Products (WithTop I)) (hlV : l.isGood V) : l.isGood C := by
  intro h
  apply hlV
  rw [Finsupp.mem_span_image_iff_total] at h ⊢
  obtain ⟨c, ⟨hs, h⟩⟩ := h
  refine' ⟨c, ⟨hs,_⟩⟩
  ext x
  rw [← Products.evalFacSubset C V hV l, ← h, Finsupp.total_apply, Finsupp.total_apply]
  dsimp
  have hhV : ∀ α (map : α → LocallyConstant {i // i ∈ V} ℤ) (d : α →₀ ℤ),
      (d.sum (fun i (a : ℤ) ↦ a • map i)) x = d.sum (fun i a ↦ a • map i x) :=
    fun _ _ _ ↦ map_finsupp_sum (LocconstEval V x) _ _
  have hhC : ∀ α (map : α → LocallyConstant {i // i ∈ C} ℤ) (d : α →₀ ℤ),
      (d.sum (fun i (a : ℤ) ↦ a • map i)) ⟨x.val, hV x.prop⟩ = d.sum (fun i a ↦ a • map i
      ⟨x.val, hV x.prop⟩) :=
    fun _ _ _ ↦ map_finsupp_sum (LocconstEval C ⟨x.val, hV x.prop⟩) _ _
  rw [hhV, hhC]
  congr
  ext
  rw [← Products.evalFacSubset C V hV _]
  rfl

noncomputable
def GoodProducts.StartingWithMaxFunToGood (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (Res C o)))) :
    StartingWithMax C o → GoodProducts (C' C ho) :=
  fun l ↦ ⟨MaxTail C l, maxTail_isGood C hC hsC ho l h₁⟩

lemma GoodProducts.StartingWithMaxFunToGoodInj
    (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (Res C o)))) :
    (StartingWithMaxFunToGood C hC hsC ho h₁).Injective := by
  intro m n h
  apply Subtype.ext ∘ Subtype.ext
  rw [Subtype.ext_iff] at h
  dsimp [StartingWithMaxFunToGood] at h
  rw [max_eq_o_cons_tail C ho m, max_eq_o_cons_tail C ho n, h]

lemma GoodProducts.hhw (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (Res C o)))) :
    LinearIndependent ℤ (eval (C' C ho)) → LinearIndependent ℤ (w C hsC ho) := by
  dsimp [w, u, w']
  rw [max_eq_eval_unapply C hsC ho]
  intro h
  let f := StartingWithMaxFunToGood C hC hsC ho h₁
  have hf : f.Injective := StartingWithMaxFunToGoodInj C hC hsC ho h₁
  have hh : (fun l ↦ Products.eval (C' C ho) (MaxTail C l)) = eval (C' C ho) ∘ f := rfl
  rw [hh]
  exact h.comp f hf

end Successor

lemma GoodProducts.P0 : P' I 0 := by
  dsimp [P']
  intro _ C _ hsC
  dsimp [Support] at hsC
  have : C ⊆ {(fun _ ↦ false)}
  · intro c hc
    simp
    ext x
    simp at hsC
    specialize hsC x c hc
    rw [Bool.eq_false_iff]
    intro ht
    apply Ordinal.not_lt_zero (ord I x)
    exact hsC ht
  rw [Set.subset_singleton_iff_eq] at this
  rcases this
  · subst C
    exact linearIndependentEmpty
  · subst C
    exact linearIndependentSingleton


lemma Products.sorted (l : Products (WithTop I)) : l.val.Sorted (· > ·) := by
  have := l.prop
  rw [List.chain'_iff_pairwise] at this
  exact this

def Products_emb : Products (WithTop I) ↪o {l : List (WithTop I) // l.Sorted (· > ·)} where
  toFun := fun l ↦ ⟨l.val, l.sorted⟩
  inj' := by
    intro l m h
    rw [Subtype.ext_iff] at h
    exact Subtype.ext h
  map_rel_iff' := Iff.rfl

instance : WellFoundedLT (Products (WithTop I)) where
  wf := (@Products_emb I _).wellFounded IsWellFounded.wf

instance : IsWellFounded (Products (WithTop I)) (·<·) := inferInstance

def L (l : Products (WithTop I)) : Prop :=
  l.eval C ∈ Submodule.span ℤ (Set.range (GoodProducts.eval C))

lemma Ll : ∀ l, L C l := by
  intro i
  apply IsWellFounded.induction (·<· : Products (WithTop I) → Products (WithTop I) → Prop)
  intro l h
  dsimp [L]
  by_cases hl : l.isGood C
  · apply Submodule.subset_span
    exact ⟨⟨l, hl⟩, rfl⟩
  · simp only [Products.isGood, not_not] at hl
    suffices : Products.eval C '' {m | m < l} ⊆ Submodule.span ℤ (Set.range (GoodProducts.eval C))
    · rw [← Submodule.span_le] at this
      exact this hl
    intro a ha
    obtain ⟨m, hm⟩ := ha
    rw [← hm.2]
    exact h m hm.1

lemma GoodProducts.span_iff_products : ⊤ ≤ Submodule.span ℤ (Set.range (eval C)) ↔
    ⊤ ≤ Submodule.span ℤ (Set.range (Products.eval C)) := by
  constructor
  · intro h
    refine' le_trans h _
    apply Submodule.span_mono
    intro a ha
    obtain ⟨b, hb⟩ := ha
    refine' ⟨b.val, hb⟩
  · intro h
    refine' le_trans h _
    rw [Submodule.span_le]
    intro f hf
    obtain ⟨l,hl⟩ := hf
    rw [← hl]
    exact Ll C l

section Span
section Fin

variable (J : Finset (WithTop I))

def ProjFin : (WithTop I → Bool) → (WithTop I → Bool) :=
  fun f i ↦ if i ∈ J then f i else false

lemma continuous_projFin :
    Continuous (ProjFin J : (WithTop I → Bool) → (WithTop I → Bool)) := by
  refine' continuous_pi _
  intro i
  dsimp [ProjFin]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma isClosedMap_projFin :
    IsClosedMap (ProjFin J : (WithTop I → Bool) → (WithTop I → Bool)) :=
  fun _ hF ↦ (IsCompact.isClosed (hF.isCompact.image (continuous_projFin J)))

def ResFin := (ProjFin J) '' C

lemma isClosed_resFin (hC : IsClosed C) : IsClosed (ResFin C J) :=
  isClosedMap_projFin J C hC

noncomputable
def ResFinSubset : {i // i ∈ C} → {i // i ∈ ResFin C J} :=
fun ⟨i, h⟩ ↦ ⟨ProjFin J i, Set.mem_image_of_mem _ h⟩

lemma resFinSubset_eq : Subtype.val ∘ ResFinSubset C J =
    (ProjFin J : (WithTop I → Bool) → _) ∘ Subtype.val := by
  rfl

lemma continuous_val_comp_resFinSubset :
    Continuous (Subtype.val ∘ ResFinSubset C J) := by
  rw [resFinSubset_eq _]
  exact Continuous.comp (continuous_projFin J) continuous_subtype_val

lemma continuous_resFinSubset : Continuous (ResFinSubset C J) := by
  rw [continuous_induced_rng]
  exact continuous_val_comp_resFinSubset _ _

lemma surjective_resFinSubset :
    Function.Surjective (ResFinSubset C J) := by
  rintro ⟨i, ⟨b, hb⟩⟩
  dsimp [ResFinSubset]
  use ⟨b, hb.1⟩
  simp_rw [← hb.2]

noncomputable
def LinearResFin :
    LocallyConstant {i // i ∈ ResFin C J} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ :=
LocallyConstant.comapLinear _ (continuous_resFinSubset C J)

lemma eFin {a : WithTop I} (ha : a ∈ J) :
    e (ResFin C J) a ∘ ResFinSubset C J = e C a := by
  ext ⟨f,hf⟩
  dsimp [e, ResFinSubset, BoolToZ, ProjFin]
  split_ifs
  · rfl
  · rfl

lemma eFin_apply {a : WithTop I} (ha : a ∈ J) :
    ∀ x, (e (ResFin C J) a) ((ResFinSubset C J) x) = e C a x := by
  intro x
  exact congr_fun (eFin C J ha) x

lemma Products.evalFacFin {l : Products (WithTop I)}
    (h : ∀ a, a ∈ l.val → a ∈ J) :
    l.eval (ResFin C J) ∘ ResFinSubset C J = l.eval C := by
  ext x
  dsimp [ResFinSubset]
  rw [Products.eval_eq, Products.eval_eq]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exfalso
    apply h₂
    intro i hi
    rw [← h₁ i hi]
    dsimp [ProjFin]
    split_ifs with h'
    · rfl
    · exfalso
      exact h' (h i hi)
  · exfalso
    apply h₁
    intro i hi
    rw [← h₂ i hi]
    dsimp [ProjFin]
    split_ifs with h'
    · rfl
    · exfalso
      exact h' (h i hi)
  · rfl

lemma Products.mem_J_of_isGood {l : Products (WithTop I)}
    (h : l.isGood (ResFin C J)) : ∀ a, a ∈ l.val → a ∈ J := by
  intro i hi
  by_contra h'
  apply h
  suffices : eval (ResFin C J) l = 0
  · rw [this]
    exact Submodule.zero_mem _
  ext x
  rw [eval_eq]
  split_ifs with h
  · exfalso
    apply h'
    specialize h i hi
    obtain ⟨y, hy⟩ := x.prop
    rw [← hy.2] at h
    simp only [ProjFin, Bool.ite_eq_true_distrib, if_false_right_eq_and] at h
    exact h.1
  · rfl

lemma Products.goodEvalFacFin {l : Products (WithTop I)}
    (hl : l.isGood (ResFin C J)) : l.eval (ResFin C J) ∘ ResFinSubset C J = l.eval C :=
  evalFacFin C J (mem_J_of_isGood C J hl)

lemma Products.eval_comapFacFin {l : Products (WithTop I)}
    (hl : l.isGood (ResFin C J)) :
    LocallyConstant.comap (ResFinSubset C J) (l.eval (ResFin C J)) = l.eval C := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_resFinSubset C J)]
  exact congr_fun (goodEvalFacFin C J hl) _

lemma linearResFin_of_eval (l : Products (WithTop I)) (hl : l.isGood (ResFin C J)) :
    l.eval C = LinearResFin C J (l.eval (ResFin C J)) := by
  rw [← Products.eval_comapFacFin C J hl]
  rfl

lemma injective_linearResFin : Function.Injective (LinearResFin C J) :=
LocallyConstant.comap_injective (ResFinSubset C J) (continuous_resFinSubset C J)
  (surjective_resFinSubset C J)

def Products.ofElementSet (x : ResFin C J) : Set (WithTop I) := {i | x.val i = true}

lemma mem_J_of_x_true (x : ResFin C J) (i : WithTop I) : x.val i = true → i ∈ J := by
  intro hi
  obtain ⟨y, hx⟩ := x.prop
  rw [← hx.2] at hi
  simp only [ProjFin, Bool.ite_eq_true_distrib, if_false_right_eq_and] at hi
  exact hi.1

def Products.ofElementFun (x : ResFin C J) : ofElementSet C J x → J :=
fun ⟨i, hi⟩ ↦ ⟨i, mem_J_of_x_true C J x i hi⟩

lemma Products.ofElementFunInjective (x : ResFin C J) :
    Function.Injective (ofElementFun C J x) := by
  intro i j h
  rw [Subtype.ext_iff] at h
  exact Subtype.ext h

noncomputable
instance (x : ResFin C J) : Fintype (Products.ofElementSet C J x) :=
Fintype.ofInjective (Products.ofElementFun C J x) (Products.ofElementFunInjective C J x)

noncomputable
def Products.ofElementFinset (x : ResFin C J) := (ofElementSet C J x).toFinset

noncomputable
def Products.ofElementList (x : ResFin C J) :=
  List.insertionSort (·≥·) (ofElementFinset C J x).toList

lemma Products.ofElement_chain'_ge (x : ResFin C J) :
    (ofElementList C J x).Chain' (·≥· : WithTop I → WithTop I → Prop) := by
  rw [List.chain'_iff_pairwise]
  exact List.sorted_insertionSort _ _

lemma Products.ofElement_chain'_gt (x : ResFin C J) :
    (ofElementList C J x).Chain' (·>· : WithTop I → WithTop I → Prop) := by
  rw [List.chain'_iff_pairwise]
  have : ∀ (a b : WithTop I), a > b ↔ a ≥ b ∧ a ≠ b
  · intro a b
    rw [gt_iff_lt, lt_iff_le_and_ne]
    exact Iff.and Iff.rfl ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
  have hr : (·>· : WithTop I → WithTop I → Prop) = (fun a b ↦ a ≥ b ∧ a ≠ b)
  · ext a b
    exact this a b
  rw [hr, List.pairwise_and_iff]
  refine' ⟨List.chain'_iff_pairwise.mp (ofElement_chain'_ge C J x), _⟩
  have hn := (ofElementFinset C J x).nodup_toList
  have h := List.perm_insertionSort (·≥·) (ofElementFinset C J x).toList
  rw [List.Perm.nodup_iff h.symm] at hn
  exact hn

noncomputable
def Products.ofElement (x : ResFin C J) : Products (WithTop I) :=
⟨ofElementList C J x, ofElement_chain'_gt C J x⟩

noncomputable
instance : Fintype (ResFin C J) := by
  haveI : Fintype (J → Bool) := inferInstance
  let f : ResFin C J → (J → Bool) := fun x j ↦ x.val j.val
  refine' Fintype.ofInjective f _
  intro x y h
  ext i
  by_cases hi : i ∈ J
  · exact congrFun h ⟨i, hi⟩
  · obtain ⟨x', hx⟩ := x.prop
    obtain ⟨y', hy⟩ := y.prop
    rw [← hx.2, ← hy.2]
    dsimp [ProjFin]
    split_ifs with hh
    · exfalso
      exact hi hh
    · rfl

noncomputable
def Finsupp.resFin_to_Z (f : LocallyConstant {i // i ∈ ResFin C J} ℤ) : ResFin C J →₀ ℤ :=
  Finsupp.onFinset (Finset.univ) f.toFun (fun _ _ ↦ Finset.mem_univ _)

noncomputable
def Products.finsuppOfElement (f : LocallyConstant {i // i ∈ ResFin C J} ℤ) :
    Products (WithTop I) →₀ ℤ :=
  (Finsupp.resFin_to_Z C J f).mapDomain (ofElement C J)

noncomputable
def SpanFinBasis (x : ResFin C J) : LocallyConstant {i // i ∈ ResFin C J} ℤ where
  toFun := fun y ↦ if y = x then 1 else 0
  isLocallyConstant := by
    haveI : DiscreteTopology (ResFin C J) := discrete_of_t1_of_finite
    exact IsLocallyConstant.of_discrete _

lemma SpanFin.spanFin : ⊤ ≤ Submodule.span ℤ (Set.range (SpanFinBasis C J)) := by
  intro f _
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  use Finsupp.resFin_to_Z C J f
  ext x
  have hhh : ∀ α (map : α → LocallyConstant {i // i ∈ ResFin C J} ℤ) (d : α →₀ ℤ),
      (d.sum (fun i (a : ℤ) ↦ a • map i)) x = d.sum (fun i a ↦ a • map i x) :=
    fun _ _ _ ↦ map_finsupp_sum (LocconstEval (ResFin C J) x) _ _
  rw [hhh]
  simp only [Finsupp.resFin_to_Z, LocallyConstant.toFun_eq_coe, SpanFinBasis,
    LocallyConstant.coe_mk, smul_eq_mul, mul_ite, mul_one, mul_zero, Finsupp.sum_ite_eq,
    Finsupp.mem_support_iff, Finsupp.onFinset_apply, ne_eq, ite_not,
    ite_eq_right_iff]
  exact fun h ↦ h.symm

def MapForList (x : ResFin C J) : WithTop I → LocallyConstant {i // i ∈ ResFin C J} ℤ :=
  fun i ↦ if x.val i = true then e (ResFin C J) i else (1 - (e (ResFin C J) i))

def ListOfElementForProd (x : ResFin C J) : List (LocallyConstant {i // i ∈ ResFin C J} ℤ) :=
List.map (MapForList C J x) (J.sort (·≥·))

lemma listProd_apply (x : C) (l : List (LocallyConstant {i // i ∈ C} ℤ)) :
    l.prod x = (l.map (LocconstEvalMul C x)).prod := by
  rw [← map_list_prod (LocconstEvalMul C x) l]
  rfl

lemma listProd_eq_basis (x : ResFin C J) :
    (ListOfElementForProd C J x).prod = SpanFinBasis C J x := by
  ext y
  dsimp [SpanFinBasis]
  split_ifs with h
  · rw [listProd_apply (ResFin C J) y _]
    apply List.prod_eq_one
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨a, ha⟩ := hn
    rw [← ha.2]
    dsimp [LocconstEvalMul]
    rw [h]
    dsimp [ListOfElementForProd] at ha
    simp only [List.mem_map] at ha
    obtain ⟨b, hb⟩ := ha.1
    rw [← hb.2]
    dsimp [MapForList]
    split_ifs with hh
    · simp only [e, BoolToZ, LocallyConstant.coe_mk, ite_eq_left_iff]
      exact fun h' ↦ h' hh
    · rw [LocallyConstant.sub_apply]
      simp only [LocallyConstant.coe_one, Pi.one_apply, e, BoolToZ, LocallyConstant.coe_mk,
        sub_eq_self, ite_eq_right_iff]
      exact hh
  · rw [listProd_apply (ResFin C J) y _]
    apply List.prod_eq_zero
    simp only [List.mem_map]
    have h' : y.val ≠ x.val
    · intro hh
      apply h
      exact Subtype.ext hh
    rw [Function.ne_iff] at h'
    obtain ⟨a, ha⟩ := h'
    by_cases hx : x.val a = true
    · refine' ⟨e (ResFin C J) a, ⟨_, _⟩⟩
      · simp only [ListOfElementForProd, List.mem_map]
        refine' ⟨a, ⟨_, _⟩⟩
        · simp only [Finset.mem_sort]
          obtain ⟨z, hz⟩ := x.prop
          rw [← hz.2, ProjFin] at hx
          simp only [Bool.ite_eq_true_distrib, if_false_right_eq_and] at hx
          exact hx.1
        · simp only [MapForList, ite_eq_left_iff]
          intro hxa
          exfalso
          exact hxa hx
      · simp only [LocconstEvalMul, e, BoolToZ, MonoidHom.coe_mk, OneHom.coe_mk,
          LocallyConstant.coe_mk, ite_eq_right_iff]
        rw [hx] at ha
        exact ha
    · refine' ⟨1 - (e (ResFin C J) a), ⟨_, _⟩⟩
      · simp only [ListOfElementForProd, List.mem_map]
        refine' ⟨a, ⟨_, _⟩⟩
        · simp only [Finset.mem_sort]
          obtain ⟨z, hz⟩ := y.prop
          simp only [Bool.not_eq_true] at hx
          rw [hx, ne_eq, Bool.not_eq_false] at ha
          rw [← hz.2, ProjFin] at ha
          simp only [Bool.ite_eq_true_distrib, if_false_right_eq_and] at ha
          exact ha.1
        · simp only [MapForList, ite_eq_right_iff]
          intro hxa
          exfalso
          exact hx hxa
      · simp only [LocconstEvalMul, e, BoolToZ, MonoidHom.coe_mk, OneHom.coe_mk,
          LocallyConstant.coe_mk, ite_eq_right_iff]
        rw [LocallyConstant.sub_apply]
        simp only [LocallyConstant.coe_one, Pi.one_apply, LocallyConstant.coe_mk]
        rw [sub_eq_zero]
        apply Eq.symm
        simp only [ite_eq_left_iff, Bool.not_eq_true]
        simp only [Bool.not_eq_true] at hx
        rw [hx] at ha
        exact ha

def LocConstMulLinear (f : LocallyConstant {i // i ∈ C} ℤ) :
    LocallyConstant {i // i ∈ C} ℤ →ₗ[ℤ] LocallyConstant {i // i ∈ C} ℤ where
  toFun := fun g ↦ f * g
  map_add' := by
    intro a b
    ext x
    simp only [LocallyConstant.coe_mul, LocallyConstant.coe_add, Pi.mul_apply, Pi.add_apply]
    exact Int.mul_add _ _ _
  map_smul' := by
    intro r a
    ext x
    simp only [zsmul_eq_mul, LocallyConstant.coe_mul, Pi.mul_apply, eq_intCast, Int.cast_id]
    exact Int.mul_left_comm _ _ _

lemma GoodProducts.spanFin : ⊤ ≤ Submodule.span ℤ (Set.range (eval (ResFin C J))) := by
  rw [span_iff_products]
  refine' le_trans (SpanFin.spanFin C J) _
  rw [Submodule.span_le]
  intro f hf
  obtain ⟨x, hx⟩ := hf
  rw [← hx, ← listProd_eq_basis]
  let l := J.sort (·≥·)
  have hlge : l.Chain' (·≥·)
  · rw [List.chain'_iff_pairwise]
    exact J.sort_sorted (·≥·)
  have hl : l.Chain' (·>·)
  · rw [List.chain'_iff_pairwise]
    dsimp
    have : ∀ (a b : WithTop I), a > b ↔ a ≥ b ∧ a ≠ b
    · intro a b
      rw [gt_iff_lt, lt_iff_le_and_ne]
      exact Iff.and Iff.rfl ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
    have hr : (·>· : WithTop I → WithTop I → Prop) = (fun a b ↦ a ≥ b ∧ a ≠ b)
    · ext a b
      exact this a b
    rw [hr, List.pairwise_and_iff]
    refine' ⟨List.chain'_iff_pairwise.mp hlge, _⟩
    have hn := J.nodup_toList
    have h := Finset.sort_perm_toList (·≥·) J
    rw [List.Perm.nodup_iff h.symm] at hn
    exact hn
  dsimp [ListOfElementForProd]
  suffices : l.Chain' (·>·) → (l.map (MapForList C J x)).prod ∈
      Submodule.span ℤ ((Products.eval (ResFin C J)) '' {m | m.val ≤ l})
  · exact Submodule.span_mono (Set.image_subset_range _ _) (this hl)
  induction l with
  | nil =>
    · intro _
      apply Submodule.subset_span
      refine' ⟨⟨[], List.chain'_nil⟩,⟨_, rfl⟩⟩
      left
      rfl
  | cons a as ih =>
    · rw [List.map_cons, List.prod_cons]
      by_cases h : x.val a = true
      · have : MapForList C J x a = e (ResFin C J) a
        · simp only [MapForList, ite_eq_left_iff]
          intro hxa
          exfalso
          exact hxa h
        rw [this]
        intro ha
        rw [List.chain'_cons'] at ha
        specialize ih ha.2
        rw [← List.chain'_cons'] at ha
        rw [Finsupp.mem_span_image_iff_total] at ih
        obtain ⟨c, hc⟩ := ih
        rw [Finsupp.mem_supported, Finsupp.total_apply] at hc
        rw [← hc.2]
        have hmap := fun g ↦ map_finsupp_sum (LocConstMulLinear (ResFin C J) (e (ResFin C J) a)) c g
        dsimp [LocConstMulLinear] at hmap
        rw [hmap]
        apply Submodule.finsupp_sum_mem
        intro m hm
        have hsm := (LocConstMulLinear (ResFin C J) (e (ResFin C J) a)).map_smul
        dsimp [LocConstMulLinear] at hsm
        rw [hsm]
        apply Submodule.smul_mem
        apply Submodule.subset_span
        have hmas : m.val ≤ as
        · apply hc.1
          simp only [Finset.mem_coe, Finsupp.mem_support_iff]
          exact hm
        refine' ⟨⟨a :: m.val, _⟩, ⟨_, _⟩⟩
        · by_cases hmnil : m.val = []
          · rw [hmnil]
            simp only [List.chain'_singleton]
          · rw [← List.cons_head!_tail hmnil, List.chain'_cons]
            refine' ⟨_,_⟩
            · have hasnil : as ≠ []
              · intro hna
                apply hmnil
                rw [hna, le_iff_lt_or_eq] at hmas
                cases' hmas with hmas hmas
                · exfalso
                  apply List.Lex.not_nil_right (·<·) m.val
                  exact hmas
                · exact hmas
              rw [← List.cons_head!_tail hasnil, List.chain'_cons] at ha
              refine' gt_of_gt_of_ge ha.1 _
              rw [ge_iff_le, le_iff_lt_or_eq]
              rw [le_iff_lt_or_eq] at hmas
              cases' hmas with hmas hmas
              · rw [← le_iff_lt_or_eq]
                by_contra hh
                simp only [not_le] at hh
                rw [← List.cons_head!_tail hmnil, ← List.cons_head!_tail hasnil, ← not_le] at hmas
                apply hmas
                apply le_of_lt
                exact (Iff.mp (List.lt_iff_lex_lt _ _) (List.lt.head _ _ hh))
              · right
                rw [hmas]
            · rw [List.cons_head!_tail hmnil]
              exact m.prop
        · simp only [Set.mem_setOf_eq]
          rw [le_iff_lt_or_eq] at hmas ⊢
          cases' hmas with hmas hmas
          · left
            have haa : ¬(a < a) := gt_irrefl a
            exact Iff.mp (List.lt_iff_lex_lt _ _) (List.lt.tail haa haa
              (Iff.mpr (List.lt_iff_lex_lt _ _) hmas))
          · right
            rw [hmas]
        · simp only [Products.eval, List.map, List.prod_cons]
      · have : MapForList C J x a = 1 - (e (ResFin C J) a)
        · simp only [MapForList, ite_eq_right_iff]
          intro hxa
          exfalso
          exact h hxa
        rw [this]
        intro ha
        rw [List.chain'_cons'] at ha
        specialize ih ha.2
        rw [← List.chain'_cons'] at ha
        rw [Finsupp.mem_span_image_iff_total] at ih
        obtain ⟨c, hc⟩ := ih
        rw [Finsupp.mem_supported, Finsupp.total_apply] at hc
        rw [← hc.2]
        have hmap := fun g ↦ map_finsupp_sum (LocConstMulLinear (ResFin C J) (e (ResFin C J) a)) c g
        dsimp [LocConstMulLinear] at hmap
        ring_nf
        rw [hmap]
        apply Submodule.add_mem
        · apply Submodule.neg_mem
          apply Submodule.finsupp_sum_mem
          intro m hm
          have hsm := (LocConstMulLinear (ResFin C J) (e (ResFin C J) a)).map_smul
          dsimp [LocConstMulLinear] at hsm
          rw [hsm]
          apply Submodule.smul_mem
          apply Submodule.subset_span
          have hmas : m.val ≤ as
          · apply hc.1
            simp only [Finset.mem_coe, Finsupp.mem_support_iff]
            exact hm
          refine' ⟨⟨a :: m.val, _⟩, ⟨_, _⟩⟩
          · by_cases hmnil : m.val = []
            · rw [hmnil]
              simp only [List.chain'_singleton]
            · rw [← List.cons_head!_tail hmnil, List.chain'_cons]
              refine' ⟨_,_⟩
              · have hasnil : as ≠ []
                · intro hna
                  apply hmnil
                  rw [hna, le_iff_lt_or_eq] at hmas
                  cases' hmas with hmas hmas
                  · exfalso
                    apply List.Lex.not_nil_right (·<·) m.val
                    exact hmas
                  · exact hmas
                rw [← List.cons_head!_tail hasnil, List.chain'_cons] at ha
                refine' gt_of_gt_of_ge ha.1 _
                rw [ge_iff_le, le_iff_lt_or_eq]
                rw [le_iff_lt_or_eq] at hmas
                cases' hmas with hmas hmas
                · rw [← le_iff_lt_or_eq]
                  by_contra hh
                  simp only [not_le] at hh
                  rw [← List.cons_head!_tail hmnil, ← List.cons_head!_tail hasnil, ← not_le] at hmas
                  apply hmas
                  apply le_of_lt
                  exact (Iff.mp (List.lt_iff_lex_lt _ _) (List.lt.head _ _ hh))
                · right
                  rw [hmas]
              · rw [List.cons_head!_tail hmnil]
                exact m.prop
          · simp only [Set.mem_setOf_eq]
            rw [le_iff_lt_or_eq] at hmas ⊢
            cases' hmas with hmas hmas
            · left
              have haa : ¬(a < a) := gt_irrefl a
              exact Iff.mp (List.lt_iff_lex_lt _ _) (List.lt.tail haa haa
                (Iff.mpr (List.lt_iff_lex_lt _ _) hmas))
            · right
              rw [hmas]
          · simp only [Products.eval, List.map, List.prod_cons]
        · apply Submodule.finsupp_sum_mem
          intro m hm
          apply Submodule.smul_mem
          apply Submodule.subset_span
          have hmas : m.val ≤ as
          · apply hc.1
            simp only [Finset.mem_coe, Finsupp.mem_support_iff]
            exact hm
          refine' ⟨m, ⟨_, rfl⟩⟩
          simp only [Set.mem_setOf_eq]
          refine' le_trans hmas _
          by_cases hasnil : as = []
          · rw [hasnil]
            apply le_of_lt
            exact List.nil_lt_cons a []
          · apply le_of_lt
            rw [← List.cons_head!_tail hasnil] at ha ⊢
            rw [List.chain'_cons] at ha
            have hlex := List.lt.head as.tail (as.head! :: as.tail) ha.1
            exact (Iff.mp (List.lt_iff_lex_lt _ _) hlex)

end Fin
section JointlySurjectiveFin

open CategoryTheory
open CategoryTheory.Limits
open Opposite

instance FinsetsCofiltered :
  IsFiltered (Finset (WithTop I)) where
    cocone_objs := by
      intro X Y
      refine' ⟨X ∪ Y, homOfLE (Finset.subset_union_left X Y),
        homOfLE (Finset.subset_union_right X Y), trivial⟩
    cocone_maps := by
      intro X Y f g
      refine' ⟨Y, 𝟙 Y, _⟩
      rw [(Preorder.Preorder.subsingleton_hom X Y).allEq f g]
    Nonempty := inferInstance

lemma mem_resFinSubset {J K : Finset (WithTop I)} (h : J ⊆ K) (x : ResFin C K) :
    ProjFin J x.val ∈ ResFin C J := by
  obtain ⟨y, hy⟩ := x.prop
  refine' ⟨y, ⟨hy.1, _⟩⟩
  dsimp [ProjFin]
  ext i
  split_ifs with hh
  · rw [← hy.2]
    apply Eq.symm
    simp only [ProjFin, ite_eq_left_iff]
    intro hK
    exfalso
    exact hK (h hh)
  · rfl

def ResFinSubsets {J K : Finset (WithTop I)} (h : J ⊆ K) : ResFin C K → ResFin C J :=
fun x ↦ ⟨ProjFin J x.val, mem_resFinSubset C h x⟩

lemma continuous_resFinSubsets {J K : Finset (WithTop I)} (h : J ⊆ K) :
    Continuous (ResFinSubsets C h) := by
  haveI : DiscreteTopology (ResFin C K) := discrete_of_t1_of_finite
  exact continuous_of_discreteTopology

lemma resFinSubsets_eq_id (J : Finset (WithTop I)) : ResFinSubsets C (subset_refl J) = id := by
  ext x i
  simp only [id_eq, ResFinSubsets, ProjFin, ite_eq_left_iff]
  obtain ⟨y, hy⟩ := x.prop
  rw [← hy.2]
  intro hijn
  apply Eq.symm
  simp only [ProjFin, ite_eq_right_iff]
  intro hij
  exfalso
  exact hijn hij

lemma resFinSubsets_eq_comp {J K L : Finset (WithTop I)} (hJK : J ⊆ K) (hKL : K ⊆ L) :
    ResFinSubsets C hJK ∘ ResFinSubsets C hKL = ResFinSubsets C (subset_trans hJK hKL) := by
  ext x i
  simp only [ResFinSubsets, Function.comp_apply, ProjFin]
  split_ifs with h hh
  · rfl
  · exfalso
    exact hh (hJK h)
  · rfl

lemma resFinSubsets_comp_resFinSubset {J K : Finset (WithTop I)} (h : J ⊆ K) :
    ResFinSubsets C h ∘ ResFinSubset C K = ResFinSubset C J := by
  ext x i
  simp only [ResFinSubsets, ResFinSubset, Function.comp_apply, ProjFin]
  split_ifs with hh hh'
  · rfl
  · exfalso
    exact hh' (h hh)
  · rfl

noncomputable
def CResFinSubset (J : Finset (WithTop I)) : C(C, ResFin C J) :=
  ⟨ResFinSubset C J, continuous_resFinSubset _ _⟩

noncomputable
def CResFinSubsets {J K : Finset (WithTop I)} (h : J ⊆ K) : C(ResFin C K, ResFin C J) :=
  ⟨ResFinSubsets C h, continuous_resFinSubsets _ _⟩

lemma cresFinSubsets_comp_cresFinSubset {J K : Finset (WithTop I)} (h : J ⊆ K) :
    ContinuousMap.comp (CResFinSubsets C h) (CResFinSubset C K) = CResFinSubset C J := by
  dsimp [CResFinSubset]
  ext a
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [← resFinSubsets_comp_resFinSubset C h]
  rfl

noncomputable
def FinsetsToProfinite :
    (Finset (WithTop I))ᵒᵖ ⥤ Profinite.{u} where
  obj J := Profinite.of (ResFin C (unop J))
  map := @fun J K h ↦ ⟨(ResFinSubsets C (leOfHom h.unop)), continuous_resFinSubsets _ _⟩
  map_id := by
    intro _
    dsimp
    simp_rw [resFinSubsets_eq_id]
    rfl
  map_comp := by
    intros
    dsimp
    congr
    dsimp
    rw [resFinSubsets_eq_comp]

instance CCompact (hC : IsClosed C) :
    CompactSpace C := by
  rw [← isCompact_iff_compactSpace]
  exact hC.isCompact

noncomputable
def FinsetsCone (hC : IsClosed C) :
    Cone (FinsetsToProfinite C) :=
{ pt := @Profinite.of {i // i ∈ C} _ (CCompact C hC) _ _
  π :=
  { app := fun J ↦ ⟨ResFinSubset C J.unop, continuous_resFinSubset _ _⟩
    naturality := by
      intro J K h
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      congr
      dsimp [FinsetsToProfinite, ResFinSubset, ResFinSubsets]
      congr
      ext x i
      dsimp [ProjFin]
      split_ifs with hh hhh
      · rfl
      · exfalso
        exact hhh (leOfHom h.unop hh)
      · rfl } }

lemma C_eq_of_forall_proj_eq (a b : C) (h : ∀ J, ResFinSubset C J a = ResFinSubset C J b) :
    a = b := by
  ext i
  specialize h {i}
  dsimp [ResFinSubset, ProjFin] at h
  rw [Subtype.ext_iff] at h
  have hh := congr_fun h i
  dsimp at hh
  split_ifs at hh with hhh
  · exact hh
  · exfalso
    apply hhh
    simp only [Finset.mem_singleton]

open Profinite in
instance isIso_finsetsCone_lift (hC : IsClosed C) :
    IsIso ((limitConeIsLimit (FinsetsToProfinite C)).lift (FinsetsCone C hC)) :=
  haveI : CompactSpace {i // i ∈ C} := CCompact C hC
  isIso_of_bijective _
    (by
      refine' ⟨fun a b h ↦ _, fun a ↦ _⟩
      · refine' C_eq_of_forall_proj_eq C a b (fun J ↦ _)
        apply_fun fun f : (limitCone (FinsetsToProfinite C)).pt => f.val (op J) at h
        exact h
      · suffices : ∃ (x : C), ∀ (J : Finset (WithTop I)), ResFinSubset C J x = a.val (op J)
        · obtain ⟨b, hb⟩ := this
          use b
          apply Subtype.ext
          apply funext
          rintro J
          exact hb (unop J)
        have hc : ∀ J s, IsClosed ((ResFinSubset C J) ⁻¹' s)
        · intro J s
          refine' IsClosed.preimage (continuous_resFinSubset C J) _
          haveI : DiscreteTopology (ResFin C J) := discrete_of_t1_of_finite
          exact isClosed_discrete _
        have H₁ : ∀ Q₁ Q₂, Q₁ ≤ Q₂ →
            ResFinSubset C Q₁ ⁻¹' {a.val (op Q₁)} ⊇ ResFinSubset C Q₂ ⁻¹' {a.val (op Q₂)}
        · intro J K h x hx
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
          rw [← resFinSubsets_comp_resFinSubset C h, Function.comp_apply,
            hx, ← a.prop (homOfLE h).op]
          rfl
        obtain ⟨x, hx⟩ : Set.Nonempty (⋂ J, ResFinSubset C J ⁻¹' {a.val (op J)}) :=
          IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed
            (fun J : Finset (WithTop I) => ResFinSubset C J ⁻¹' {a.val (op J)}) (directed_of_sup H₁)
            (fun J => (Set.singleton_nonempty _).preimage (surjective_resFinSubset _ _))
            (fun J => (hc J {a.val (op J)}).isCompact) fun J => hc J _
        exact ⟨x, Set.mem_iInter.1 hx⟩
      )

noncomputable
def isoFinsetsConeLift (hC : IsClosed C) :
    @Profinite.of {i // i ∈ C} _ (CCompact C hC) _ _ ≅
    (Profinite.limitCone (FinsetsToProfinite C)).pt :=
  asIso <| (Profinite.limitConeIsLimit _).lift (FinsetsCone C hC)

noncomputable
def asLimitFinsetsConeIso (hC : IsClosed C) : FinsetsCone C hC ≅ Profinite.limitCone _ :=
  Limits.Cones.ext (isoFinsetsConeLift _ hC) fun _ => rfl

noncomputable
def finsetsCone_isLimit (hC : IsClosed C) : CategoryTheory.Limits.IsLimit (FinsetsCone C hC) :=
  Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitFinsetsConeIso C hC).symm

lemma fin_comap_jointlySurjective
    (hC : IsClosed C)
    (f : LocallyConstant {i // i ∈ C} ℤ) : ∃ (J : Finset (WithTop I))
    (g : LocallyConstant {i // i ∈ ResFin C J} ℤ), f = g.comap (ResFinSubset C J) := by
  obtain ⟨J, g, h⟩ := @Profinite.exists_locallyConstant (Finset (WithTop I))ᵒᵖ _
    _ _ (FinsetsCone C hC) _
    (finsetsCone_isLimit C hC) f
  exact ⟨(unop J), g, h⟩

end JointlySurjectiveFin

lemma GoodProducts.spanAux (hC : IsClosed C) :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval C)) := by
  rw [span_iff_products]
  intro f _
  have hf : ∃ K f', f = LinearResFin C K f' := fin_comap_jointlySurjective C hC f
  obtain ⟨K, f', hf⟩ := hf
  rw [hf]
  have hf' := spanFin C K (Submodule.mem_top : f' ∈ ⊤)
  have := Submodule.apply_mem_span_image_of_mem_span (LinearResFin C K) hf'
  refine' Submodule.span_mono _ this
  intro l hl
  obtain ⟨y, ⟨m, hm⟩, hy⟩ := hl
  rw [← hm] at hy
  rw [← hy]
  exact ⟨m.val, linearResFin_of_eval C K m.val m.prop⟩

end Span

lemma GoodProducts.Plimit :
    ∀ (o : Ordinal), Ordinal.IsLimit o → (∀ (o' : Ordinal), o' < o → P' I o') → P' I o := by
  intro o ho h
  dsimp [P'] at *
  intro hho
  intro C hC hsC
  rw [ModProducts.linear_independent_iff C ho hsC]
  refine' linearIndependent_iUnion_of_directed (DirectedS C o) _
  rintro ⟨o', ho'⟩
  have hho' : o' < Ordinal.type (·<· : WithTop I → WithTop I → Prop) :=
    lt_of_lt_of_le ho' hho
  specialize h o' ho' (le_of_lt hho')
  have h' := h (Res C o') (isClosed_Res C o' hC) (support_Res_le_o C o')
  rw [ModProducts.smaller_linear_independent_iff] at h'
  exact h'

lemma GoodProducts.linearIndependentAux (i : WithTop I) : P' I (ord I i) := by
  refine' Ordinal.limitRecOn (ord I i) P0 _
      (fun o ho h ↦ (GoodProducts.Plimit o ho (fun o' ho' ↦ (h o' ho'))))
  intro o h
  dsimp [P'] at *
  intro ho C hC hsC
  have ho' : o < Ordinal.type (·<· : WithTop I → WithTop I → Prop) :=
    lt_of_lt_of_le (Order.lt_succ _) ho
  by_cases hnC : Nonempty C
  · rw [linearIndependent_iff_sum C o hsC]
    suffices : LinearIndependent ℤ (u C o)
    · exact this
    refine' ModuleCat.linearIndependent_leftExact _ _ _
        (LocallyConstant.LeftExact C hC hsC ho') (huv C o) (huw C hsC ho')
    · refine h (le_of_lt ho') (Res C o) (isClosed_Res C o hC) (support_Res_le_o C o)
    · have h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (Res C o))) :=
        spanAux (Res C o) (isClosed_Res C o hC)
      apply (hhw C hC hsC ho' h₁)
      -- rw [← hw C hC hsC ho' h₁]
      refine h (le_of_lt ho') (C' C ho') (isClosed_C' C hC ho') (support_C' C ho')
    · exact injective_u C o hsC
  · rw [Set.nonempty_coe_sort, Set.not_nonempty_iff_eq_empty] at hnC
    subst hnC
    specialize h (le_of_lt ho') ∅ hC
    apply h
    dsimp [Support]
    intro i hi
    simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false] at hi

variable {C₁ : Set (I → Bool)}

lemma isClosedInWithTop (hC₁ : IsClosed C₁) : IsClosed ((r I) '' C₁) :=
(r.embedding I).toEmbedding.toInducing.isClosedMap (r.embedding I).closed_range C₁ hC₁

lemma supportTop (C₁ : Set (I → Bool)) : Support ((r I) '' C₁) ⊆ {j | ord I j < ord I ⊤} := by
  dsimp [Support]
  intro i hi
  obtain ⟨f, hf⟩ := hi
  obtain ⟨c, hc⟩ := hf.1
  rw [← hc.2] at hf
  dsimp [r] at hf
  cases i
  · dsimp at hf
    exfalso
    exact Bool.not_false' hf.2
  · dsimp at hf
    dsimp
    rw [← WithTop.none_eq_top]
    simp only [ord, Ordinal.typein_lt_typein, WithTop.some_lt_none]

lemma ordITop : ord I ⊤ ≤ Ordinal.type (·<· : WithTop I → WithTop I → Prop) := by
  exact le_of_lt (Ordinal.typein_lt_type _ _)

lemma GoodProducts.linearIndependent (hC₁ : IsClosed C₁) :
  LinearIndependent ℤ (GoodProducts.eval ((r I) '' C₁)) :=
GoodProducts.linearIndependentAux ⊤ (le_of_lt (Ordinal.typein_lt_type _ _))
  ((r I) '' C₁) (isClosedInWithTop hC₁) (supportTop C₁)

lemma GoodProducts.span (hC₁ : IsClosed C₁)  :
    ⊤ ≤ Submodule.span ℤ (Set.range (GoodProducts.eval ((r I) '' C₁))) :=
GoodProducts.spanAux ((r I) '' C₁) (isClosedInWithTop hC₁)

noncomputable
def GoodProducts.Basis (hC₁ : IsClosed C₁) :
    Basis (GoodProducts ((r I) '' C₁)) ℤ (LocallyConstant {i // i ∈ ((r I) '' C₁)} ℤ) :=
Basis.mk (GoodProducts.linearIndependent hC₁) (GoodProducts.span hC₁)

lemma closedFree (hC₁ : IsClosed C₁) :
    Module.Free ℤ (LocallyConstant {i // i ∈ ((r I) '' C₁)} ℤ) :=
Module.Free.of_basis $ GoodProducts.Basis hC₁

variable {S : Profinite} {ι : S → I → Bool} (hι : ClosedEmbedding ι)

noncomputable
def homeoClosed₁ : S ≃ₜ Set.range ι := Homeomorph.ofEmbedding ι hι.toEmbedding

def rι.embedding : ClosedEmbedding (r I ∘ ι) := ClosedEmbedding.comp (r.embedding I) hι

noncomputable
def homeoClosed₂ : S ≃ₜ Set.range (r I ∘ ι) :=
Homeomorph.ofEmbedding (r I ∘ ι) (rι.embedding hι).toEmbedding

def homeoRange : Set.range (r I ∘ ι) ≃ₜ r I '' Set.range ι := by
  rw [Set.range_comp]
  exact Homeomorph.refl _

def setHomeoSubtype {X : Type _} [TopologicalSpace X] (s : Set X) : s ≃ₜ {x // x ∈ s} :=
{ toFun := fun x ↦ ⟨x.val, x.prop⟩
  invFun := fun x ↦ x
  left_inv := by
    intro x
    dsimp
  right_inv := by
    intro x
    dsimp }

noncomputable
def homeoClosed : S ≃ₜ { i // i ∈ r I '' Set.range ι } :=
(homeoClosed₂ hι).trans (homeoRange.trans (setHomeoSubtype (r I '' Set.range ι)))

noncomputable
def locConstIso (hι : ClosedEmbedding ι) :
  (LocallyConstant S ℤ) ≃ₗ[ℤ] (LocallyConstant { i // i ∈ r I '' Set.range ι } ℤ) :=
LocallyConstant.equivLinear (homeoClosed hι)

lemma Nobeling : Module.Free ℤ (LocallyConstant S ℤ) := Module.Free.of_equiv'
  (closedFree hι.closed_range) (locConstIso hι).symm

end NobelingProof

variable (S : Profinite.{u})

open Classical

noncomputable
def Nobeling.ι : S → ({C : Set S // IsClopen C} → Bool) := fun s C => decide (s ∈ C.1)

instance totally_separated_of_totally_disconnected_compact_hausdorff (α : Type _)
    [TopologicalSpace α] [CompactSpace α] [TotallyDisconnectedSpace α] [T2Space α] :
    TotallySeparatedSpace α := by
  rwa [← compact_t2_tot_disc_iff_tot_sep]

lemma Nobeling.embedding : ClosedEmbedding (Nobeling.ι S) := by
  apply Continuous.closedEmbedding
  · dsimp [ι]
    refine' continuous_pi _
    intro C
    rw [← IsLocallyConstant.iff_continuous]
    refine' ((IsLocallyConstant.tfae _).out 0 3).mpr _
    rintro ⟨⟩
    · have : (fun a ↦ decide (a ∈ C.1)) ⁻¹' {false} = C.1ᶜ
      · ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff,
          decide_eq_false_iff_not, Set.mem_compl_iff]
      · rw [this]
        refine' IsClopen.isOpen _
        simp only [isClopen_compl_iff]
        exact C.2
    · have : (fun a ↦ decide (a ∈ C.1)) ⁻¹' {true} = C.1
      · ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
      · rw [this]
        refine' IsClopen.isOpen _
        exact C.2
  · intro a b hab
    by_contra hnab
    have h' := exists_clopen_of_totally_separated hnab
    obtain ⟨C, hC, h₁⟩ := h'
    apply h₁.2
    have ha : ι S a ⟨C, hC⟩ = decide (a ∈ C) := rfl
    have hb : ι S b ⟨C, hC⟩ = decide (b ∈ C) := rfl
    apply of_decide_eq_true
    rw [← hb, ← hab, ha]
    apply decide_eq_true
    exact h₁.1

theorem Nobeling : Module.Free ℤ (LocallyConstant S ℤ) :=
@NobelingProof.Nobeling {C : Set S // IsClopen C} (IsWellOrder.linearOrder WellOrderingRel)
  WellOrderingRel.isWellOrder S (Nobeling.ι S) (Nobeling.embedding S)
