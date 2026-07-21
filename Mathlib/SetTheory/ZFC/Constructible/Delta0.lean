/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Def

/-!
# Bounded formulas for the constructible hierarchy

This file introduces an intrinsically scoped syntax for `Δ₀` formulas in the
language of set theory.  Quantifiers are bounded syntactically.  The syntax is
translated to `Constructible.FOFormula`, and its semantics is proved absolute
between a transitive `ZFSet` and the ambient `ZFSet` universe.
-/

@[expose] public section

universe u

namespace Constructible

/-- Prepend one coordinate to a tuple. -/
def tupleCons {A : Type u} {n : Nat} (x : A) (s : Tuple A n) :
    Tuple A (n + 1) :=
  Fin.cases x s

@[simp]
theorem tupleCons_zero {A : Type u} {n : Nat} (x : A) (s : Tuple A n) :
    tupleCons x s 0 = x := by
  simp [tupleCons]

@[simp]
theorem tupleCons_succ {A : Type u} {n : Nat} (x : A) (s : Tuple A n)
    (i : Fin n) : tupleCons x s i.succ = s i := by
  simp [tupleCons]

/-- Appending a final coordinate commutes with prepending a first one. -/
@[simp, nolint simpNF]
theorem snoc_tupleCons {A : Type u} {n : Nat}
    (head : A) (s : Tuple A n) (last : A) :
    snoc (tupleCons head s) last = tupleCons head (snoc s last) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [snoc_last]
    change last = tupleCons head (snoc s last) (Fin.last n).succ
    rw [tupleCons_succ, snoc_last]
  · rw [snoc_castSucc]
    refine Fin.cases ?_ (fun k => ?_) j
    · change head = tupleCons head (snoc s last) 0
      rw [tupleCons_zero]
    · change
        tupleCons head s k.succ =
          tupleCons head (snoc s last) (k.castSucc).succ
      rw [tupleCons_succ, tupleCons_succ, snoc_castSucc]

/--
Intrinsically scoped bounded formulas.  In `boundedEx i φ`, the new witness is
the last variable of `φ` and is required to belong to the old variable `i`.
-/
inductive Delta0Formula : Nat → Type
  | mem {n : Nat} (i j : Fin n) : Delta0Formula n
  | eq {n : Nat} (i j : Fin n) : Delta0Formula n
  | neg {n : Nat} (φ : Delta0Formula n) : Delta0Formula n
  | conj {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n
  | boundedEx {n : Nat} (i : Fin n) (φ : Delta0Formula (n + 1)) :
      Delta0Formula n

namespace Delta0Formula

/-- Tarskian semantics for bounded formulas over a relation `E`. -/
@[simp]
def Satisfies {A : Type u} (E : A → A → Prop) :
    {n : Nat} → Delta0Formula n → Tuple A n → Prop
  | _, .mem i j, s => E (s i) (s j)
  | _, .eq i j, s => s i = s j
  | _, .neg φ, s => ¬Satisfies E φ s
  | _, .conj φ ψ, s => Satisfies E φ s ∧ Satisfies E ψ s
  | _, .boundedEx i φ, s =>
      ∃ x : A, E x (s i) ∧ Satisfies E φ (snoc s x)

/-- Forget boundedness annotations and regard a `Δ₀` formula as an `FOFormula`. -/
def toFO : {n : Nat} → Delta0Formula n → FOFormula n
  | _, .mem i j => .mem i j
  | _, .eq i j => .eq i j
  | _, .neg φ => .neg (toFO φ)
  | _, .conj φ ψ => .conj (toFO φ) (toFO ψ)
  | _, .boundedEx i φ => FOFormula.boundedEx i (toFO φ)

/--
Relativize every unbounded quantifier of an `FOFormula` to the set stored in
coordinate zero.  The original variable `i` is consequently moved to
coordinate `i.succ`.
-/
def relativize : {n : Nat} → FOFormula n → Delta0Formula (n + 1)
  | _, .mem i j => .mem i.succ j.succ
  | _, .eq i j => .eq i.succ j.succ
  | _, .neg φ => .neg (relativize φ)
  | _, .conj φ ψ => .conj (relativize φ) (relativize ψ)
  | _, .ex φ => .boundedEx 0 (relativize φ)

/-- The translation to unrestricted first-order syntax preserves semantics. -/
@[simp]
theorem satisfies_toFO {A : Type u} (E : A → A → Prop)
    {n : Nat} (φ : Delta0Formula n) (s : Tuple A n) :
    FOFormula.Satisfies E φ.toFO s ↔ Satisfies E φ s := by
  induction φ with
  | mem i j => rfl
  | eq i j => rfl
  | neg φ ih => simp [toFO, ih]
  | conj φ ψ ihφ ihψ => simp [toFO, ihφ, ihψ]
  | boundedEx i φ ih => simp [toFO, ih]

/-- Bounded disjunction. -/
def disj {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n :=
  .neg (.conj (.neg φ) (.neg ψ))

/-- Material implication as a derived bounded connective. -/
def imp {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n :=
  disj (.neg φ) ψ

/-- Logical equivalence as a derived bounded connective. -/
def biimp {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n :=
  .conj (imp φ ψ) (imp ψ φ)

/-- Bounded universal quantification. -/
def boundedAll {n : Nat} (i : Fin n) (φ : Delta0Formula (n + 1)) :
    Delta0Formula n :=
  .neg (.boundedEx i (.neg φ))

@[simp]
theorem satisfies_disj {A : Type u} {E : A → A → Prop}
    {n : Nat} {φ ψ : Delta0Formula n} {s : Tuple A n} :
    Satisfies E (disj φ ψ) s ↔ Satisfies E φ s ∨ Satisfies E ψ s := by
  classical
  simp only [disj, Satisfies]
  tauto

@[simp]
theorem satisfies_imp {A : Type u} {E : A → A → Prop}
    {n : Nat} {φ ψ : Delta0Formula n} {s : Tuple A n} :
    Satisfies E (imp φ ψ) s ↔
      (Satisfies E φ s → Satisfies E ψ s) := by
  classical
  simp [imp]
  tauto

@[simp]
theorem satisfies_biimp {A : Type u} {E : A → A → Prop}
    {n : Nat} {φ ψ : Delta0Formula n} {s : Tuple A n} :
    Satisfies E (biimp φ ψ) s ↔
      (Satisfies E φ s ↔ Satisfies E ψ s) := by
  classical
  simp [biimp]
  tauto

@[simp]
theorem satisfies_boundedAll {A : Type u} {E : A → A → Prop}
    {n : Nat} {i : Fin n} {φ : Delta0Formula (n + 1)} {s : Tuple A n} :
    Satisfies E (boundedAll i φ) s ↔
      ∀ x : A, E x (s i) → Satisfies E φ (snoc s x) := by
  classical
  simp [boundedAll]

/-- Extend a variable renaming under a new last bounded variable. -/
abbrev liftRename {n m : Nat} (ρ : Fin n → Fin m) :
    Fin (n + 1) → Fin (m + 1) :=
  FOFormula.liftRename ρ

/-- Rename all free variables of a bounded formula. -/
def rename {n m : Nat} (ρ : Fin n → Fin m) :
    Delta0Formula n → Delta0Formula m
  | .mem i j => .mem (ρ i) (ρ j)
  | .eq i j => .eq (ρ i) (ρ j)
  | .neg φ => .neg (rename ρ φ)
  | .conj φ ψ => .conj (rename ρ φ) (rename ρ ψ)
  | .boundedEx i φ => .boundedEx (ρ i) (rename (liftRename ρ) φ)

/-- Renaming bounded formulas composes their assignments. -/
@[simp]
theorem satisfies_rename {A : Type u} (E : A → A → Prop)
    {n m : Nat} (φ : Delta0Formula n) (ρ : Fin n → Fin m)
    (s : Tuple A m) :
    Satisfies E (rename ρ φ) s ↔
      Satisfies E φ (fun i => s (ρ i)) := by
  induction φ generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg φ ih => simp [rename, ih]
  | conj φ ψ ihφ ihψ => simp [rename, ihφ, ihψ]
  | boundedEx i φ ih =>
      simp only [rename, Satisfies, ih]
      constructor
      · rintro ⟨x, hx, hφ⟩
        rw [FOFormula.snoc_comp_liftRename] at hφ
        exact ⟨x, hx, hφ⟩
      · rintro ⟨x, hx, hφ⟩
        refine ⟨x, hx, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hφ

/-! ## Absoluteness -/

/-- Forget subtype proofs in an assignment into `ZFCarrier a`. -/
def val {a : ZFSet.{u}} {n : Nat} (s : Tuple (ZFCarrier a) n) :
    Tuple ZFSet.{u} n :=
  fun i => (s i).1

@[simp]
theorem val_apply {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (i : Fin n) :
    val s i = (s i).1 :=
  rfl

/-- Taking underlying values commutes with appending one subtype element. -/
@[simp, nolint simpNF]
theorem val_snoc {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (x : ZFCarrier a) :
    val (snoc s x) = snoc (val s) x.1 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/--
Correctness of relativization: evaluation in the ambient `ZFSet` universe,
with every quantifier bounded by coordinate zero, is exactly evaluation in
the carrier structure `(a, ∈)`.
-/
theorem satisfies_relativize (a : ZFSet.{u}) {n : Nat}
    (φ : FOFormula n) (s : Tuple (ZFCarrier a) n) :
    Satisfies (fun x y : ZFSet.{u} => x ∈ y) (relativize φ)
        (tupleCons a (val s)) ↔
      FOFormula.Satisfies (zfCarrierMem a) φ s := by
  induction φ with
  | mem i j => rfl
  | eq i j =>
      change (s i).1 = (s j).1 ↔ s i = s j
      exact Subtype.coe_injective.eq_iff
  | neg φ ih => exact not_congr (ih s)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ s) (ihψ s)
  | ex φ ih =>
      constructor
      · rintro ⟨x, hxa, hx⟩
        refine ⟨⟨x, hxa⟩, ?_⟩
        apply (ih (snoc s ⟨x, hxa⟩)).mp
        simpa only [val_snoc, snoc_tupleCons] using hx
      · rintro ⟨x, hx⟩
        refine ⟨x.1, x.2, ?_⟩
        have hdelta := (ih (snoc s x)).mpr hx
        simpa only [val_snoc, snoc_tupleCons] using hdelta

/-- Relativization correctness after translation back to `FOFormula`. -/
theorem satisfies_toFO_relativize (a : ZFSet.{u}) {n : Nat}
    (φ : FOFormula n) (s : Tuple (ZFCarrier a) n) :
    FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y)
        (relativize φ).toFO (tupleCons a (val s)) ↔
      FOFormula.Satisfies (zfCarrierMem a) φ s := by
  rw [satisfies_toFO, satisfies_relativize]

/--
Every member of `DefZF a` is described in the ambient universe by a `Δ₀`
formula whose zeroth coordinate is the bound `a`.  Conversely, such a
relativized description gives a member of `DefZF a`.
-/
theorem mem_DefZF_iff_exists_relativized {a z : ZFSet.{u}} :
    z ∈ DefZF a ↔
      z ⊆ a ∧
        ∃ n : Nat, ∃ s : Tuple (ZFCarrier a) n,
          ∃ φ : FOFormula (n + 1),
            ∀ x : ZFCarrier a,
              x.1 ∈ z ↔
                Satisfies (fun u v : ZFSet.{u} => u ∈ v) (relativize φ)
                  (snoc (tupleCons a (val s)) x.1) := by
  rw [mem_DefZF_iff_exists_satisfies]
  constructor
  · rintro ⟨hza, n, s, φ, hφ⟩
    refine ⟨hza, n, s, φ, ?_⟩
    intro x
    have hrel :
        Satisfies (fun u v : ZFSet.{u} => u ∈ v) (relativize φ)
            (snoc (tupleCons a (val s)) x.1) ↔
          FOFormula.Satisfies (zfCarrierMem a) φ (snoc s x) := by
      simpa only [val_snoc, snoc_tupleCons] using
        (satisfies_relativize a φ (snoc s x))
    exact (hφ x).trans hrel.symm
  · rintro ⟨hza, n, s, φ, hφ⟩
    refine ⟨hza, n, s, φ, ?_⟩
    intro x
    have hrel :
        Satisfies (fun u v : ZFSet.{u} => u ∈ v) (relativize φ)
            (snoc (tupleCons a (val s)) x.1) ↔
          FOFormula.Satisfies (zfCarrierMem a) φ (snoc s x) := by
      simpa only [val_snoc, snoc_tupleCons] using
        (satisfies_relativize a φ (snoc s x))
    exact (hφ x).trans hrel

/--
`Δ₀` formulas are absolute between a transitive set and the ambient ZFC
universe, for assignments whose entries lie in that set.
-/
theorem satisfies_absolute {a : ZFSet.{u}} (ha : a.IsTransitive)
    {n : Nat} (φ : Delta0Formula n) (s : Tuple (ZFCarrier a) n) :
    Satisfies (zfCarrierMem a) φ s ↔
      Satisfies (fun x y : ZFSet.{u} => x ∈ y) φ (val s) := by
  induction φ with
  | mem i j => rfl
  | eq i j => exact Subtype.ext_iff
  | neg φ ih => simp only [Satisfies, ih]
  | conj φ ψ ihφ ihψ => simp only [Satisfies, ihφ, ihψ]
  | boundedEx i φ ih =>
      constructor
      · rintro ⟨x, hx, hφ⟩
        refine ⟨x.1, hx, ?_⟩
        have habs := (ih (snoc s x)).mp hφ
        simpa only [val_snoc] using habs
      · rintro ⟨x, hx, hφ⟩
        have hxa : x ∈ a := ha.mem_trans hx (s i).2
        let xa : ZFCarrier a := ⟨x, hxa⟩
        refine ⟨xa, hx, ?_⟩
        apply (ih (snoc s xa)).mpr
        simpa only [val_snoc, xa] using hφ

/-- Absoluteness after embedding a bounded formula into `FOFormula`. -/
theorem satisfies_toFO_absolute {a : ZFSet.{u}} (ha : a.IsTransitive)
    {n : Nat} (φ : Delta0Formula n) (s : Tuple (ZFCarrier a) n) :
    FOFormula.Satisfies (zfCarrierMem a) φ.toFO s ↔
      FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y) φ.toFO (val s) := by
  rw [satisfies_toFO, satisfies_toFO, satisfies_absolute ha]

end Delta0Formula

end Constructible
