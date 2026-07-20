/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.ZFC.Ordinal

/-!
# The relation-algebra definition of `Def`

This file formalizes the relation-algebra presentation of first-order
definability:

* `D 0 A n` consists of the atomic membership and equality relations;
* `D (k+1) A n` is closed under complement, intersection, and existential
  projection, using relations from stage `k`;
* `Df A n` is the union of all finite stages;
* `definablePowerset A` consists of the sections of relations in `Df` obtained
  by fixing finitely many parameters.

Here the underlying set `a` is represented by a Lean type `A`, equipped with
the binary relation which plays the role of membership.  Thus `Tuple A n` is
the type-theoretic counterpart of `a^n`.
-/

@[expose] public section

open Set

universe u

namespace Constructible

/-- An ordered `n`-tuple of elements of `A`. -/
abbrev Tuple (A : Type u) (n : Nat) := Fin n → A

/-- An `n`-ary relation on `A`. -/
abbrev Rel (A : Type u) (n : Nat) := Set (Tuple A n)

/-- Append one element as the last coordinate of a tuple. -/
def snoc {A : Type u} {n : Nat} (s : Tuple A n) (x : A) : Tuple A (n + 1) :=
  Fin.lastCases x s

@[simp]
theorem snoc_castSucc {A : Type u} {n : Nat} (s : Tuple A n) (x : A)
    (i : Fin n) : snoc s x i.castSucc = s i := by
  simp [snoc]

@[simp]
theorem snoc_last {A : Type u} {n : Nat} (s : Tuple A n) (x : A) :
    snoc s x (Fin.last n) = x := by
  simp [snoc]

/-! ## An independent syntax and satisfaction relation -/

/--
Intrinsically scoped first-order formulas in the language of set theory.

`FOFormula n` is scoped in a context of `n` available variables.  The
existential quantifier binds the new last coordinate, so its body has `n + 1`
available variables.  Negation,
conjunction, and existential quantification form a functionally complete basis
for classical first-order logic.
-/
inductive FOFormula : Nat → Type
  | mem {n : Nat} (i j : Fin n) : FOFormula n
  | eq {n : Nat} (i j : Fin n) : FOFormula n
  | neg {n : Nat} (φ : FOFormula n) : FOFormula n
  | conj {n : Nat} (φ ψ : FOFormula n) : FOFormula n
  | ex {n : Nat} (φ : FOFormula (n + 1)) : FOFormula n

namespace FOFormula

/-- Tarskian satisfaction for a tuple assignment in a structure `(A, E)`. -/
@[simp]
def Satisfies {A : Type u} (E : A → A → Prop) :
    {n : Nat} → FOFormula n → Tuple A n → Prop
  | _, .mem i j, s => E (s i) (s j)
  | _, .eq i j, s => s i = s j
  | _, .neg φ, s => ¬Satisfies E φ s
  | _, .conj φ ψ, s => Satisfies E φ s ∧ Satisfies E ψ s
  | _, .ex φ, s => ∃ x : A, Satisfies E φ (snoc s x)

/-- The relation denoted by a formula in `(A, E)`. -/
def semanticRel {A : Type u} (E : A → A → Prop) {n : Nat}
    (φ : FOFormula n) : Rel A n :=
  {s | Satisfies E φ s}

@[simp]
theorem mem_semanticRel_iff {A : Type u} {E : A → A → Prop}
    {n : Nat} {φ : FOFormula n} {s : Tuple A n} :
    s ∈ semanticRel E φ ↔ Satisfies E φ s :=
  Iff.rfl

/-- Disjunction as a derived connective. -/
def disj {n : Nat} (φ ψ : FOFormula n) : FOFormula n :=
  .neg (.conj (.neg φ) (.neg ψ))

/-- Material implication as a derived connective. -/
def imp {n : Nat} (φ ψ : FOFormula n) : FOFormula n :=
  disj (.neg φ) ψ

/-- Logical equivalence as a derived connective. -/
def biimp {n : Nat} (φ ψ : FOFormula n) : FOFormula n :=
  .conj (imp φ ψ) (imp ψ φ)

/-- Universal quantification as a derived connective. -/
def all {n : Nat} (φ : FOFormula (n + 1)) : FOFormula n :=
  .neg (.ex (.neg φ))

@[simp]
theorem satisfies_disj {A : Type u} {E : A → A → Prop} {n : Nat}
    {φ ψ : FOFormula n} {s : Tuple A n} :
    Satisfies E (disj φ ψ) s ↔ Satisfies E φ s ∨ Satisfies E ψ s := by
  classical
  change
    (¬(¬Satisfies E φ s ∧ ¬Satisfies E ψ s)) ↔
      Satisfies E φ s ∨ Satisfies E ψ s
  constructor
  · intro h
    by_cases hφ : Satisfies E φ s
    · exact Or.inl hφ
    · exact Or.inr (Classical.byContradiction fun hψ => h ⟨hφ, hψ⟩)
  · rintro (hφ | hψ) h
    · exact h.1 hφ
    · exact h.2 hψ

@[simp]
theorem satisfies_imp {A : Type u} {E : A → A → Prop} {n : Nat}
    {φ ψ : FOFormula n} {s : Tuple A n} :
    Satisfies E (imp φ ψ) s ↔
      (Satisfies E φ s → Satisfies E ψ s) := by
  classical
  simp only [imp, satisfies_disj, Satisfies]
  tauto

@[simp]
theorem satisfies_biimp {A : Type u} {E : A → A → Prop} {n : Nat}
    {φ ψ : FOFormula n} {s : Tuple A n} :
    Satisfies E (biimp φ ψ) s ↔
      (Satisfies E φ s ↔ Satisfies E ψ s) := by
  classical
  simp only [biimp, Satisfies, satisfies_imp]
  tauto

@[simp]
theorem satisfies_all {A : Type u} {E : A → A → Prop} {n : Nat}
    {φ : FOFormula (n + 1)} {s : Tuple A n} :
    Satisfies E (all φ) s ↔ ∀ x : A, Satisfies E φ (snoc s x) := by
  classical
  change
    (¬∃ x : A, ¬Satisfies E φ (snoc s x)) ↔
      ∀ x : A, Satisfies E φ (snoc s x)
  constructor
  · intro h x
    exact Classical.byContradiction fun hx => h ⟨x, hx⟩
  · intro h hex
    rcases hex with ⟨x, hx⟩
    exact hx (h x)

/-! ### Variable management -/

/-- Extend a renaming across the new last variable bound by `ex`. -/
def liftRename {n m : Nat} (ρ : Fin n → Fin m) :
    Fin (n + 1) → Fin (m + 1) :=
  Fin.lastCases (Fin.last m) (fun i => (ρ i).castSucc)

@[simp]
theorem liftRename_castSucc {n m : Nat} (ρ : Fin n → Fin m) (i : Fin n) :
    liftRename ρ i.castSucc = (ρ i).castSucc := by
  simp [liftRename]

@[simp]
theorem liftRename_last {n m : Nat} (ρ : Fin n → Fin m) :
    liftRename ρ (Fin.last n) = Fin.last m := by
  simp [liftRename]

/-- Rename all available variables, preserving variables bound by `ex`. -/
def rename {n m : Nat} (ρ : Fin n → Fin m) : FOFormula n → FOFormula m
  | .mem i j => .mem (ρ i) (ρ j)
  | .eq i j => .eq (ρ i) (ρ j)
  | .neg φ => .neg (rename ρ φ)
  | .conj φ ψ => .conj (rename ρ φ) (rename ρ ψ)
  | .ex φ => .ex (rename (liftRename ρ) φ)

theorem snoc_comp_liftRename {A : Type u} {n m : Nat}
    (ρ : Fin n → Fin m) (s : Tuple A m) (x : A) :
    (fun i => snoc s x (liftRename ρ i)) = snoc (fun i => s (ρ i)) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Renaming a formula is semantically composition of its assignment. -/
@[simp]
theorem satisfies_rename {A : Type u} (E : A → A → Prop)
    {n m : Nat} (φ : FOFormula n) (ρ : Fin n → Fin m)
    (s : Tuple A m) :
    Satisfies E (rename ρ φ) s ↔
      Satisfies E φ (fun i => s (ρ i)) := by
  induction φ generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg φ ih => simp [rename, ih]
  | conj φ ψ ihφ ihψ => simp [rename, ihφ, ihψ]
  | ex φ ih =>
      simp only [rename, Satisfies, ih]
      constructor
      · rintro ⟨x, hx⟩
        have hassign :
            (fun i => snoc s x (liftRename ρ i)) =
              snoc (fun i => s (ρ i)) x :=
          snoc_comp_liftRename ρ s x
        exact ⟨x, by simpa only [hassign] using hx⟩
      · rintro ⟨x, hx⟩
        have hassign :
            (fun i => snoc s x (liftRename ρ i)) =
              snoc (fun i => s (ρ i)) x :=
          snoc_comp_liftRename ρ s x
        exact ⟨x, by simpa only [hassign] using hx⟩

/-- Add one unused last variable to the context of a formula. -/
def weaken {n : Nat} (φ : FOFormula n) : FOFormula (n + 1) :=
  rename Fin.castSucc φ

@[simp]
theorem satisfies_weaken {A : Type u} (E : A → A → Prop)
    {n : Nat} (φ : FOFormula n) (s : Tuple A n) (x : A) :
    Satisfies E (weaken φ) (snoc s x) ↔ Satisfies E φ s := by
  rw [weaken, satisfies_rename]
  have hassign : (fun i => snoc s x i.castSucc) = s := by
    funext i
    exact snoc_castSucc s x i
  simp only [hassign]

/-! ### Bounded quantifiers -/

/-- `∃ x ∈ s i, φ`, with the witness bound as the new last variable. -/
def boundedEx {n : Nat} (i : Fin n) (φ : FOFormula (n + 1)) : FOFormula n :=
  .ex (.conj (.mem (Fin.last n) i.castSucc) φ)

@[simp]
theorem satisfies_boundedEx {A : Type u} {E : A → A → Prop}
    {n : Nat} {i : Fin n} {φ : FOFormula (n + 1)} {s : Tuple A n} :
    Satisfies E (boundedEx i φ) s ↔
      ∃ x : A, E x (s i) ∧ Satisfies E φ (snoc s x) := by
  simp [boundedEx]

/-- `∀ x ∈ s i, φ`, with the witness bound as the new last variable. -/
def boundedAll {n : Nat} (i : Fin n) (φ : FOFormula (n + 1)) : FOFormula n :=
  .neg (boundedEx i (.neg φ))

@[simp]
theorem satisfies_boundedAll {A : Type u} {E : A → A → Prop}
    {n : Nat} {i : Fin n} {φ : FOFormula (n + 1)} {s : Tuple A n} :
    Satisfies E (boundedAll i φ) s ↔
      ∀ x : A, E x (s i) → Satisfies E φ (snoc s x) := by
  classical
  simp [boundedAll]

end FOFormula

section Atomic

variable {A : Type u} (E : A → A → Prop)

/-- The atomic relation `x_i ∈ x_j`, with `E` interpreting membership. -/
def memRel (n : Nat) (i j : Fin n) : Rel A n :=
  {s | E (s i) (s j)}

/-- The atomic relation `x_i = x_j`. -/
def eqRel (n : Nat) (i j : Fin n) : Rel A n :=
  {s | s i = s j}

/-- Existential projection deleting the last coordinate. -/
def existsProj {n : Nat} (r : Rel A (n + 1)) : Rel A n :=
  {s | ∃ x : A, snoc s x ∈ r}

@[simp]
theorem mem_existsProj {n : Nat} (r : Rel A (n + 1)) (s : Tuple A n) :
    s ∈ existsProj r ↔ ∃ x : A, snoc s x ∈ r :=
  Iff.rfl

/-- Stage zero: precisely the atomic membership and equality relations. -/
def DZero (n : Nat) : Set (Rel A n) :=
  {r |
    (∃ i j : Fin n, r = memRel E n i j) ∨
      ∃ i j : Fin n, r = eqRel n i j}

/--
`D k n`, the relations of arity `n` generated in at most `k` closure stages.

The recursive call in the projection clause has arity `n+1`, but its stage is
`k`; hence recursion is structural on the first argument.
-/
def D : (k n : Nat) → Set (Rel A n)
  | 0, n => DZero E n
  | k + 1, n =>
      {r |
        r ∈ D k n ∨
        (∃ t, t ∈ D k n ∧ r = tᶜ) ∨
        (∃ t v, t ∈ D k n ∧ v ∈ D k n ∧ r = t ∩ v) ∨
        (∃ t, t ∈ D k (n + 1) ∧ r = existsProj t)}

@[simp]
theorem mem_D_zero_iff {n : Nat} {r : Rel A n} :
    r ∈ D E 0 n ↔
      (∃ i j : Fin n, r = memRel E n i j) ∨
        ∃ i j : Fin n, r = eqRel n i j :=
  Iff.rfl

@[simp]
theorem mem_D_succ_iff {k n : Nat} {r : Rel A n} :
    r ∈ D E (k + 1) n ↔
      r ∈ D E k n ∨
      (∃ t, t ∈ D E k n ∧ r = tᶜ) ∨
      (∃ t v, t ∈ D E k n ∧ v ∈ D E k n ∧ r = t ∩ v) ∨
      (∃ t, t ∈ D E k (n + 1) ∧ r = existsProj t) :=
  Iff.rfl

/-- `Df A n = ⋃ k, D k A n`. -/
def Df (n : Nat) : Set (Rel A n) :=
  {r | ∃ k : Nat, r ∈ D E k n}

@[simp]
theorem mem_Df_iff {n : Nat} {r : Rel A n} :
    r ∈ Df E n ↔ ∃ k : Nat, r ∈ D E k n :=
  Iff.rfl

theorem D_subset_succ (k n : Nat) : D E k n ⊆ D E (k + 1) n := by
  intro r hr
  exact Or.inl hr

theorem D_mono_stage {k l n : Nat} (hkl : k ≤ l) : D E k n ⊆ D E l n := by
  induction l, hkl using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ l hkl ih => exact Set.Subset.trans ih (D_subset_succ E l n)

theorem D_subset_Df (k n : Nat) : D E k n ⊆ Df E n := by
  intro r hr
  exact ⟨k, hr⟩

theorem Df_compl {n : Nat} {r : Rel A n} (hr : r ∈ Df E n) : rᶜ ∈ Df E n := by
  rcases hr with ⟨k, hk⟩
  exact ⟨k + 1, Or.inr (Or.inl ⟨r, hk, rfl⟩)⟩

theorem Df_inter {n : Nat} {r t : Rel A n}
    (hr : r ∈ Df E n) (ht : t ∈ Df E n) : r ∩ t ∈ Df E n := by
  rcases hr with ⟨k, hk⟩
  rcases ht with ⟨l, hl⟩
  let m := max k l
  have hkm : r ∈ D E m n := D_mono_stage E (Nat.le_max_left k l) hk
  have hlm : t ∈ D E m n := D_mono_stage E (Nat.le_max_right k l) hl
  exact ⟨m + 1, Or.inr (Or.inr (Or.inl ⟨r, t, hkm, hlm, rfl⟩))⟩

theorem Df_existsProj {n : Nat} {r : Rel A (n + 1)}
    (hr : r ∈ Df E (n + 1)) : existsProj r ∈ Df E n := by
  rcases hr with ⟨k, hk⟩
  exact ⟨k + 1, Or.inr (Or.inr (Or.inr ⟨r, hk, rfl⟩))⟩

/-! ### Equivalence with first-order formula semantics -/

@[simp]
theorem semanticRel_mem {n : Nat} (i j : Fin n) :
    FOFormula.semanticRel E (.mem i j) = memRel E n i j :=
  rfl

@[simp]
theorem semanticRel_eq {n : Nat} (i j : Fin n) :
    FOFormula.semanticRel E (.eq i j) = eqRel n i j :=
  rfl

@[simp]
theorem semanticRel_neg {n : Nat} (φ : FOFormula n) :
    FOFormula.semanticRel E (.neg φ) = (FOFormula.semanticRel E φ)ᶜ :=
  rfl

@[simp]
theorem semanticRel_conj {n : Nat} (φ ψ : FOFormula n) :
    FOFormula.semanticRel E (.conj φ ψ) =
      FOFormula.semanticRel E φ ∩ FOFormula.semanticRel E ψ :=
  rfl

@[simp]
theorem semanticRel_ex {n : Nat} (φ : FOFormula (n + 1)) :
    FOFormula.semanticRel E (.ex φ) =
      existsProj (FOFormula.semanticRel E φ) :=
  rfl

/-- Soundness: the semantics of every formula belongs to `Df`. -/
theorem semanticRel_mem_Df {n : Nat} (φ : FOFormula n) :
    FOFormula.semanticRel E φ ∈ Df E n := by
  induction φ with
  | mem i j =>
      exact D_subset_Df E 0 _ (Or.inl ⟨i, j, rfl⟩)
  | eq i j =>
      exact D_subset_Df E 0 _ (Or.inr ⟨i, j, rfl⟩)
  | neg φ ih =>
      simpa using Df_compl E ih
  | conj φ ψ ihφ ihψ =>
      simpa using Df_inter E ihφ ihψ
  | ex φ ih =>
      simpa using Df_existsProj E ih

/--
Stagewise completeness: every relation produced at a finite stage is the
semantics of an intrinsically scoped first-order formula.
-/
theorem exists_formula_of_mem_D (k : Nat) {n : Nat} {r : Rel A n}
    (hr : r ∈ D E k n) :
    ∃ φ : FOFormula n, r = FOFormula.semanticRel E φ := by
  induction k generalizing n r with
  | zero =>
      rcases (mem_D_zero_iff (E := E)).mp hr with
        ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩
      · exact ⟨.mem i j, rfl⟩
      · exact ⟨.eq i j, rfl⟩
  | succ k ih =>
      rcases (mem_D_succ_iff (E := E)).mp hr with
        hr | ⟨t, ht, rfl⟩ | ⟨t, v, ht, hv, rfl⟩ | ⟨t, ht, rfl⟩
      · exact ih hr
      · rcases ih ht with ⟨φ, rfl⟩
        exact ⟨.neg φ, by simp⟩
      · rcases ih ht with ⟨φ, rfl⟩
        rcases ih hv with ⟨ψ, rfl⟩
        exact ⟨.conj φ ψ, by simp⟩
      · rcases ih ht with ⟨φ, rfl⟩
        exact ⟨.ex φ, by simp⟩

/--
Full semantic equivalence: `Df E n` consists exactly of the relations denoted
by `n`-variable first-order formulas in the language `{∈, =}`.
-/
theorem mem_Df_iff_exists_formula {n : Nat} {r : Rel A n} :
    r ∈ Df E n ↔
      ∃ φ : FOFormula n, r = FOFormula.semanticRel E φ := by
  constructor
  · rintro ⟨k, hk⟩
    exact exists_formula_of_mem_D E k hk
  · rintro ⟨φ, rfl⟩
    exact semanticRel_mem_Df E φ

/-- Extensional, pointwise satisfaction form of `mem_Df_iff_exists_formula`. -/
theorem mem_Df_iff_exists_satisfies {n : Nat} {r : Rel A n} :
    r ∈ Df E n ↔
      ∃ φ : FOFormula n,
        ∀ s : Tuple A n, s ∈ r ↔ FOFormula.Satisfies E φ s := by
  constructor
  · intro hr
    rcases (mem_Df_iff_exists_formula (E := E)).mp hr with ⟨φ, rfl⟩
    exact ⟨φ, fun _ => Iff.rfl⟩
  · rintro ⟨φ, hφ⟩
    apply (mem_Df_iff_exists_formula (E := E)).mpr
    refine ⟨φ, Set.ext ?_⟩
    intro s
    exact hφ s

/-- Set-level restatement: `Df` is the range of formula semantics. -/
theorem Df_eq_range_semanticRel (n : Nat) :
    Df E n = Set.range (FOFormula.semanticRel E : FOFormula n → Rel A n) := by
  ext r
  rw [mem_Df_iff_exists_formula]
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨φ, rfl⟩

/-- A section of an `(n+1)`-ary relation after fixing its first `n` entries. -/
def relSection {n : Nat} (r : Rel A (n + 1)) (s : Tuple A n) : Set A :=
  {x | snoc s x ∈ r}

/--
The definable-powerset operation associated to `Df`. Parameters are represented
by the tuple `s`; the defining relation itself is parameter-free and belongs to
`Df E (n+1)`.
-/
def definablePowerset : Set (Set A) :=
  {x |
    ∃ n : Nat, ∃ s : Tuple A n, ∃ r : Rel A (n + 1),
      r ∈ Df E (n + 1) ∧ x = relSection r s}

@[simp]
theorem mem_definablePowerset_iff {x : Set A} :
    x ∈ definablePowerset E ↔
      ∃ n : Nat, ∃ s : Tuple A n, ∃ r : Rel A (n + 1),
        r ∈ Df E (n + 1) ∧ x = relSection r s :=
  Iff.rfl

/--
Formula-and-satisfaction characterization of `definablePowerset`: a subset is
definable exactly when one formula, with a finite tuple of parameters, defines
membership in it.
-/
theorem mem_definablePowerset_iff_exists_satisfies {x : Set A} :
    x ∈ definablePowerset E ↔
      ∃ n : Nat, ∃ s : Tuple A n, ∃ φ : FOFormula (n + 1),
        ∀ y : A, y ∈ x ↔ FOFormula.Satisfies E φ (snoc s y) := by
  constructor
  · rintro ⟨n, s, r, hr, rfl⟩
    rcases (mem_Df_iff_exists_formula (E := E)).mp hr with ⟨φ, rfl⟩
    exact ⟨n, s, φ, fun _ => Iff.rfl⟩
  · rintro ⟨n, s, φ, hφ⟩
    refine ⟨n, s, FOFormula.semanticRel E φ, semanticRel_mem_Df E φ, ?_⟩
    ext y
    exact hφ y

end Atomic

/-! ## Specialization to Mathlib's ZFC universe -/

section ZFC

/-!
### An internal `ZFSet` version of the definable-powerset operation

The following construction uses the powerset and separation operations of
`ZFSet`.  Consequently `DefZF a` is itself a genuine ZFC set, not merely an
external Lean predicate on `ZFSet`.
-/

/-- The subtype consisting of the members of the ZFC set `a`. -/
abbrev ZFCarrier (a : ZFSet.{u}) := {x : ZFSet.{u} // x ∈ a}

/-- Membership in `a`, regarded as a relation on its subtype of elements. -/
def zfCarrierMem (a : ZFSet.{u}) : ZFCarrier a → ZFCarrier a → Prop :=
  fun x y => x.1 ∈ y.1

/-- Regard `z` as an external subset of the subtype `ZFCarrier a`. -/
def zfSubsetAsCarrier (a z : ZFSet.{u}) : Set (ZFCarrier a) :=
  {x | x.1 ∈ z}

/-- Represent a subset of the members of `a` by separation on `a`. -/
noncomputable def representZFSubset (a : ZFSet.{u})
    (s : Set (ZFCarrier a)) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ hx : x ∈ a, (⟨x, hx⟩ : ZFCarrier a) ∈ s) a

@[simp]
theorem mem_representZFSubset_iff (a : ZFSet.{u})
    (s : Set (ZFCarrier a)) (x : ZFSet.{u}) :
    x ∈ representZFSubset a s ↔
      ∃ hx : x ∈ a, (⟨x, hx⟩ : ZFCarrier a) ∈ s := by
  simp [representZFSubset]

theorem representZFSubset_subset (a : ZFSet.{u})
    (s : Set (ZFCarrier a)) : representZFSubset a s ⊆ a := by
  intro x hx
  exact (mem_representZFSubset_iff a s x).mp hx |>.1

@[simp]
theorem zfSubsetAsCarrier_representZFSubset (a : ZFSet.{u})
    (s : Set (ZFCarrier a)) :
    zfSubsetAsCarrier a (representZFSubset a s) = s := by
  ext x
  simp [zfSubsetAsCarrier]

/--
The genuine internal definable-powerset operation on Mathlib's ZFC sets.

An element `z` of `a.powerset` is retained exactly when the corresponding
subset of `(a, ∈)` belongs to the relation-algebraic `definablePowerset`.
-/
noncomputable def DefZF (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep
    (fun z =>
      zfSubsetAsCarrier a z ∈ definablePowerset (zfCarrierMem a))
    a.powerset

@[simp]
theorem mem_DefZF_iff {a z : ZFSet.{u}} :
    z ∈ DefZF a ↔
      z ⊆ a ∧
        zfSubsetAsCarrier a z ∈ definablePowerset (zfCarrierMem a) := by
  simp [DefZF]

/--
`DefZF` stated entirely through formula satisfaction over the structure
`(a, ∈)`.  The condition `z ⊆ a` remains essential: the carrier semantics only
observes elements of `a`.
-/
theorem mem_DefZF_iff_exists_satisfies {a z : ZFSet.{u}} :
    z ∈ DefZF a ↔
      z ⊆ a ∧
        ∃ n : Nat, ∃ s : Tuple (ZFCarrier a) n,
          ∃ φ : FOFormula (n + 1),
            ∀ x : ZFCarrier a,
              x.1 ∈ z ↔
                FOFormula.Satisfies (zfCarrierMem a) φ (snoc s x) := by
  rw [mem_DefZF_iff]
  constructor
  · rintro ⟨hza, hdef⟩
    refine ⟨hza, ?_⟩
    simpa [zfSubsetAsCarrier] using
      (mem_definablePowerset_iff_exists_satisfies
        (E := zfCarrierMem a)).mp hdef
  · rintro ⟨hza, hdef⟩
    refine ⟨hza, ?_⟩
    apply (mem_definablePowerset_iff_exists_satisfies
      (E := zfCarrierMem a)).mpr
    simpa [zfSubsetAsCarrier] using hdef

theorem DefZF_subset_powerset (a : ZFSet.{u}) : DefZF a ⊆ a.powerset := by
  intro z hz
  exact ZFSet.mem_powerset.mpr ((mem_DefZF_iff.mp hz).1)

/-- Every relation-algebraically definable subset has an internal representative. -/
theorem representZFSubset_mem_DefZF {a : ZFSet.{u}}
    {s : Set (ZFCarrier a)}
    (hs : s ∈ definablePowerset (zfCarrierMem a)) :
    representZFSubset a s ∈ DefZF a := by
  rw [mem_DefZF_iff]
  exact ⟨representZFSubset_subset a s, by simpa using hs⟩

/-- Every member of `DefZF a` has a definable internal representation. -/
theorem exists_definable_representation_of_mem_DefZF {a z : ZFSet.{u}}
    (hz : z ∈ DefZF a) :
    ∃ s : Set (ZFCarrier a),
      s ∈ definablePowerset (zfCarrierMem a) ∧
        z = representZFSubset a s := by
  refine ⟨zfSubsetAsCarrier a z, (mem_DefZF_iff.mp hz).2, ?_⟩
  apply ZFSet.ext
  intro x
  have hza : z ⊆ a := (mem_DefZF_iff.mp hz).1
  constructor
  · intro hx
    exact (mem_representZFSubset_iff a (zfSubsetAsCarrier a z) x).mpr
      ⟨hza hx, by simpa [zfSubsetAsCarrier] using hx⟩
  · intro hx
    rcases (mem_representZFSubset_iff a (zfSubsetAsCarrier a z) x).mp hx with
      ⟨_, hxz⟩
    simpa [zfSubsetAsCarrier] using hxz

/-! ### Basic structural properties of `DefZF` -/

/-- The whole carrier is definable over itself by the formula `x = x`. -/
theorem self_mem_DefZF (a : ZFSet.{u}) : a ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  refine ⟨Set.Subset.rfl, 0, (fun i => Fin.elim0 i),
    .eq (Fin.last 0) (Fin.last 0), ?_⟩
  intro x
  simp

/-- Pairing is available at the next definability stage. -/
theorem pair_mem_DefZF {a x y : ZFSet.{u}} (hx : x ∈ a) (hy : y ∈ a) :
    ({x, y} : ZFSet.{u}) ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sx : ZFCarrier a := ⟨x, hx⟩
  let sy : ZFCarrier a := ⟨y, hy⟩
  let params : Tuple (ZFCarrier a) 2 := ![sx, sy]
  let φ : FOFormula 3 :=
    FOFormula.disj
      (.eq (Fin.last 2) (Fin.castSucc (0 : Fin 2)))
      (.eq (Fin.last 2) (Fin.castSucc (1 : Fin 2)))
  refine ⟨?_, 2, params, φ, ?_⟩
  · intro z hz
    rcases ZFSet.mem_pair.mp hz with rfl | rfl
    · exact hx
    · exact hy
  · intro z
    rw [ZFSet.mem_pair, FOFormula.satisfies_disj]
    change
      (z.1 = x ∨ z.1 = y) ↔
        (snoc params z (Fin.last 2) =
            snoc params z (Fin.castSucc (0 : Fin 2)) ∨
          snoc params z (Fin.last 2) =
            snoc params z (Fin.castSucc (1 : Fin 2)))
    simp only [snoc_last, snoc_castSucc]
    simp [params, sx, sy, Subtype.ext_iff]

/--
Internal union is definable over a transitive carrier.  Transitivity is used
both to show that `⋃₀ x` is a subset of the carrier and to regard the
bound witness in `∃ t, t ∈ x ∧ z ∈ t` as an element of `ZFCarrier a`.
-/
theorem sUnion_mem_DefZF {a x : ZFSet.{u}}
    (ha : a.IsTransitive) (hx : x ∈ a) :
    ZFSet.sUnion x ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sx : ZFCarrier a := ⟨x, hx⟩
  let params : Tuple (ZFCarrier a) 1 := ![sx]
  let φ : FOFormula 2 :=
    .ex (.conj
      (.mem (2 : Fin 3) (0 : Fin 3))
      (.mem (1 : Fin 3) (2 : Fin 3)))
  refine ⟨?_, 1, params, φ, ?_⟩
  · intro z hz
    rcases ZFSet.mem_sUnion.mp hz with ⟨t, htx, hzt⟩
    exact ha.mem_trans hzt (ha.mem_trans htx hx)
  · intro z
    change
      z.1 ∈ ZFSet.sUnion x ↔
        ∃ t : ZFCarrier a, t.1 ∈ x ∧ z.1 ∈ t.1
    constructor
    · intro hz
      rcases ZFSet.mem_sUnion.mp hz with ⟨t, htx, hzt⟩
      exact ⟨⟨t, ha.mem_trans htx hx⟩, htx, hzt⟩
    · rintro ⟨t, htx, hzt⟩
      exact ZFSet.mem_sUnion.mpr ⟨t.1, htx, hzt⟩

/-- Binary intersection is definable over a transitive carrier. -/
theorem inter_mem_DefZF {a x y : ZFSet.{u}}
    (ha : a.IsTransitive) (hx : x ∈ a) (hy : y ∈ a) :
    x ∩ y ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sx : ZFCarrier a := ⟨x, hx⟩
  let sy : ZFCarrier a := ⟨y, hy⟩
  let params : Tuple (ZFCarrier a) 2 := ![sx, sy]
  let φ : FOFormula 3 :=
    .conj
      (.mem (Fin.last 2) (Fin.castSucc (0 : Fin 2)))
      (.mem (Fin.last 2) (Fin.castSucc (1 : Fin 2)))
  refine ⟨?_, 2, params, φ, ?_⟩
  · intro z hz
    exact ha.mem_trans (ZFSet.mem_inter.mp hz).1 hx
  · intro z
    rw [ZFSet.mem_inter]
    change
      (z.1 ∈ x ∧ z.1 ∈ y) ↔
        ((snoc params z (Fin.last 2)).1 ∈
            (snoc params z (Fin.castSucc (0 : Fin 2))).1 ∧
          (snoc params z (Fin.last 2)).1 ∈
            (snoc params z (Fin.castSucc (1 : Fin 2))).1)
    simp only [snoc_last, snoc_castSucc]
    rfl

/-- Set difference is definable over a transitive carrier. -/
theorem sdiff_mem_DefZF {a x y : ZFSet.{u}}
    (ha : a.IsTransitive) (hx : x ∈ a) (hy : y ∈ a) :
    x \ y ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sx : ZFCarrier a := ⟨x, hx⟩
  let sy : ZFCarrier a := ⟨y, hy⟩
  let params : Tuple (ZFCarrier a) 2 := ![sx, sy]
  let φ : FOFormula 3 :=
    .conj
      (.mem (Fin.last 2) (Fin.castSucc (0 : Fin 2)))
      (.neg (.mem (Fin.last 2) (Fin.castSucc (1 : Fin 2))))
  refine ⟨?_, 2, params, φ, ?_⟩
  · intro z hz
    exact ha.mem_trans (ZFSet.mem_sdiff.mp hz).1 hx
  · intro z
    rw [ZFSet.mem_sdiff]
    change
      (z.1 ∈ x ∧ z.1 ∉ y) ↔
        ((snoc params z (Fin.last 2)).1 ∈
            (snoc params z (Fin.castSucc (0 : Fin 2))).1 ∧
          (snoc params z (Fin.last 2)).1 ∉
            (snoc params z (Fin.castSucc (1 : Fin 2))).1)
    simp only [snoc_last, snoc_castSucc]
    rfl

@[simp]
theorem DefZF_empty : DefZF (∅ : ZFSet.{u}) = {∅} := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    have hz0 : z = ∅ := (ZFSet.eq_empty z).2 fun y hy =>
      ZFSet.notMem_empty y ((mem_DefZF_iff.mp hz).1 hy)
    simp [hz0]
  · intro hz
    have hz0 : z = ∅ := by simpa using hz
    simpa [hz0] using self_mem_DefZF (∅ : ZFSet.{u})

/--
Every element of a transitive set is a definable subset of that set, using the
element itself as a parameter in the formula `y ∈ p`.
-/
theorem mem_DefZF_of_mem {a x : ZFSet.{u}} (ha : a.IsTransitive)
    (hx : x ∈ a) : x ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  refine ⟨ha.subset_of_mem hx, 1, (fun _ => ⟨x, hx⟩),
    .mem (Fin.last 1) (Fin.castSucc (0 : Fin 1)), ?_⟩
  intro y
  change y.1 ∈ x ↔ y.1 ∈ x
  rfl

/-- A transitive set is contained in its definable powerset. -/
theorem ZFSet.IsTransitive.subset_DefZF {a : ZFSet.{u}}
    (ha : a.IsTransitive) : a ⊆ DefZF a := by
  intro x hx
  exact mem_DefZF_of_mem ha hx

/-- The definable powerset of a transitive set is again transitive. -/
theorem ZFSet.IsTransitive.defZF {a : ZFSet.{u}}
    (ha : a.IsTransitive) : (DefZF a).IsTransitive := by
  intro z hz x hx
  have hza : z ⊆ a := (mem_DefZF_iff.mp hz).1
  exact mem_DefZF_of_mem ha (hza hx)

/--
Inflationarity of `DefZF` is equivalent to transitivity of its argument.
This records the exact hypothesis for monotonicity of `LStageZF`.
-/
theorem subset_DefZF_iff_isTransitive {a : ZFSet.{u}} :
    a ⊆ DefZF a ↔ a.IsTransitive := by
  constructor
  · intro h
    rw [ZFSet.isTransitive_iff_subset_powerset]
    exact h.trans (DefZF_subset_powerset a)
  · exact fun ha => ZFSet.IsTransitive.subset_DefZF ha

/-!
### The internally represented constructible hierarchy

Every value of `LStageZF` is an actual `ZFSet`.  At a limit ordinal `l`, the
index type `Set.Iio l` is small in universe `u`; `replacementRangeZF` first
forms the range of the preceding levels as a ZFC set and `limitUnionZF` then
applies internal union.
-/

/--
The value used by replacement on an internal ordinal code.  On an element
`β.toZFSet ∈ l.toZFSet` this is exactly `Xs β`.
-/
noncomputable def replacementValueZF (l : Ordinal.{u})
    (Xs : ∀ β < l, ZFSet.{u}) (z : ZFSet.{u}) : ZFSet.{u} :=
  if hz : z.rank < l then Xs z.rank hz else ∅

/--
The replacement image of the internal ordinal `l.toZFSet` under the family
`Xs`.  Thus this is an actual `ZFSet` containing exactly the preceding stages.
-/
noncomputable def replacementRangeZF (l : Ordinal.{u})
    (Xs : ∀ β < l, ZFSet.{u}) : ZFSet.{u} := by
  let f := replacementValueZF l Xs
  letI : ZFSet.Definable₁ f :=
    Classical.allZFSetDefinable (fun s => f (s 0))
  exact ZFSet.image f l.toZFSet

@[simp]
theorem mem_replacementRangeZF_iff {l : Ordinal.{u}}
    {Xs : ∀ β < l, ZFSet.{u}} {x : ZFSet.{u}} :
    x ∈ replacementRangeZF l Xs ↔
      ∃ β, ∃ hβ : β < l, Xs β hβ = x := by
  simp only [replacementRangeZF, ZFSet.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases Ordinal.mem_toZFSet_iff.mp hz with ⟨β, hβ, rfl⟩
    exact ⟨β, hβ, by simp [replacementValueZF, hβ]⟩
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨β.toZFSet, ?_, ?_⟩
    · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hβ
    · simp [replacementValueZF, hβ]

/-- Internal union of the replacement range of all earlier stages. -/
noncomputable def limitUnionZF (l : Ordinal.{u})
    (Xs : ∀ β < l, ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (replacementRangeZF l Xs)

@[simp]
theorem mem_limitUnionZF_iff {l : Ordinal.{u}}
    {Xs : ∀ β < l, ZFSet.{u}} {x : ZFSet.{u}} :
    x ∈ limitUnionZF l Xs ↔
      ∃ β, ∃ hβ : β < l, x ∈ Xs β hβ := by
  simp [limitUnionZF]

/-- A union of a transitive family of stages is transitive. -/
theorem limitUnionZF_isTransitive {l : Ordinal.{u}}
    {Xs : ∀ β < l, ZFSet.{u}}
    (hXs : ∀ β hβ, (Xs β hβ).IsTransitive) :
    (limitUnionZF l Xs).IsTransitive := by
  intro y hy z hz
  rcases mem_limitUnionZF_iff.mp hy with ⟨β, hβ, hyβ⟩
  exact mem_limitUnionZF_iff.mpr
    ⟨β, hβ, (hXs β hβ).mem_trans hz hyβ⟩

/--
The internally represented constructible hierarchy:

* `LStageZF 0 = ∅`;
* `LStageZF (α + 1) = DefZF (LStageZF α)`;
* `LStageZF l = ⋃ β < l, LStageZF β` at a nonzero limit `l`.
-/
noncomputable def LStageZF (α : Ordinal.{u}) : ZFSet.{u} :=
  α.limitRecOn
    ∅
    (fun _ a => DefZF a)
    (fun l _ Ls => limitUnionZF l Ls)

@[simp]
theorem LStageZF_zero : LStageZF (0 : Ordinal.{u}) = ∅ := by
  simp [LStageZF]

theorem LStageZF_succ (α : Ordinal.{u}) :
    LStageZF (Order.succ α) = DefZF (LStageZF α) := by
  change
    Ordinal.limitRecOn (Order.succ α) ∅ (fun _ a => DefZF a)
        (fun l _ Ls => limitUnionZF l Ls) =
      DefZF
        (Ordinal.limitRecOn α ∅ (fun _ a => DefZF a)
          (fun l _ Ls => limitUnionZF l Ls))
  rw [Order.succ_eq_add_one, Ordinal.limitRecOn_add_one]

theorem LStageZF_limit {l : Ordinal.{u}} (hl : Order.IsSuccLimit l) :
    LStageZF l = limitUnionZF l (fun β _ => LStageZF β) := by
  simp only [LStageZF, Ordinal.limitRecOn_limit l _ _ _ hl]

@[simp]
theorem mem_LStageZF_limit_iff {l : Ordinal.{u}} (hl : Order.IsSuccLimit l)
    {x : ZFSet.{u}} :
    x ∈ LStageZF l ↔ ∃ β < l, x ∈ LStageZF β := by
  rw [LStageZF_limit hl]
  simp

/-- Every level of the constructible hierarchy is a transitive ZFC set. -/
theorem LStageZF_isTransitive (α : Ordinal.{u}) :
    (LStageZF α).IsTransitive := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      rw [LStageZF_zero]
      exact ZFSet.isTransitive_empty
  | add_one α ih =>
      rw [← Order.succ_eq_add_one, LStageZF_succ]
      exact ZFSet.IsTransitive.defZF ih
  | limit l hl ih =>
      rw [LStageZF_limit hl]
      exact limitUnionZF_isTransitive (fun β hβ => ih β hβ)

/-- Each constructible level is contained in its successor. -/
theorem LStageZF_subset_succ (α : Ordinal.{u}) :
    LStageZF α ⊆ LStageZF (Order.succ α) := by
  rw [LStageZF_succ]
  exact ZFSet.IsTransitive.subset_DefZF (LStageZF_isTransitive α)

/-- Each level itself occurs as an element of its successor level. -/
theorem LStageZF_mem_succ (α : Ordinal.{u}) :
    LStageZF α ∈ LStageZF (Order.succ α) := by
  rw [LStageZF_succ]
  exact self_mem_DefZF (LStageZF α)

/-- The constructible hierarchy is monotone in its ordinal index. -/
theorem LStageZF_mono :
    Monotone (LStageZF : Ordinal.{u} → ZFSet.{u}) := by
  intro α β hαβ
  induction β using Ordinal.limitRecOn generalizing α with
  | zero =>
      have hα : α = 0 := le_antisymm hαβ bot_le
      subst α
      exact le_rfl
  | add_one β ih =>
      rw [← Order.succ_eq_add_one] at hαβ ⊢
      rcases Order.le_succ_iff_eq_or_le.mp hαβ with h | h
      · subst α
        exact le_rfl
      · exact (ih h).trans (LStageZF_subset_succ β)
  | limit l hl ih =>
      rcases hαβ.eq_or_lt with h | h
      · subst α
        exact le_rfl
      · intro x hx
        exact (mem_LStageZF_limit_iff hl).mpr ⟨α, h, hx⟩

/-- Earlier levels occur as elements of every strictly later level. -/
theorem LStageZF_mem_of_lt {α β : Ordinal.{u}} (hαβ : α < β) :
    LStageZF α ∈ LStageZF β := by
  exact LStageZF_mono (Order.succ_le_of_lt hαβ)
    (LStageZF_mem_succ α)

/-- Distinct ordinal indices give distinct internally represented levels. -/
theorem LStageZF_ne_of_lt {α β : Ordinal.{u}} (hαβ : α < β) :
    LStageZF α ≠ LStageZF β := by
  intro hEq
  have hself := LStageZF_mem_of_lt hαβ
  rw [hEq] at hself
  exact ZFSet.mem_irrefl _ hself

/-- The internally represented constructible hierarchy is strictly increasing. -/
theorem LStageZF_strictMono :
    StrictMono (LStageZF : Ordinal.{u} → ZFSet.{u}) := by
  intro α β hαβ
  exact lt_of_le_of_ne (LStageZF_mono hαβ.le)
    (LStageZF_ne_of_lt hαβ)

/-- The constructible universe `L`, represented externally because it is a proper class. -/
def ConstructibleUniverse : Set ZFSet.{u} :=
  {x | ∃ α : Ordinal.{u}, x ∈ LStageZF α}

/-- The constructible universe `L`, represented externally as a class. -/
abbrev L : Set ZFSet.{u} := ConstructibleUniverse

/-- A ZFC set is constructible when it occurs in some internal level. -/
def IsConstructible (x : ZFSet.{u}) : Prop :=
  x ∈ L

theorem mem_constructibleUniverse_iff {x : ZFSet.{u}} :
    x ∈ ConstructibleUniverse ↔ ∃ α : Ordinal.{u}, x ∈ LStageZF α :=
  Iff.rfl

@[simp]
theorem mem_L_iff {x : ZFSet.{u}} :
    x ∈ L ↔ ∃ α : Ordinal.{u}, x ∈ LStageZF α :=
  Iff.rfl

@[simp]
theorem isConstructible_iff {x : ZFSet.{u}} :
    IsConstructible x ↔ ∃ α : Ordinal.{u}, x ∈ LStageZF α :=
  Iff.rfl

theorem LStageZF_subset_constructibleUniverse (α : Ordinal.{u}) :
    (LStageZF α : Set ZFSet.{u}) ⊆ ConstructibleUniverse := by
  intro x hx
  exact ⟨α, hx⟩

/-- Every internally represented level is itself constructible. -/
theorem LStageZF_mem_L (α : Ordinal.{u}) : LStageZF α ∈ L := by
  exact ⟨Order.succ α, LStageZF_mem_succ α⟩

/-- The empty set belongs to the constructible universe. -/
theorem empty_mem_L : (∅ : ZFSet.{u}) ∈ L := by
  simpa using LStageZF_mem_L (0 : Ordinal.{u})

/-- Any two constructible sets occur together in a common level. -/
theorem exists_common_LStage {x y : ZFSet.{u}} (hx : x ∈ L) (hy : y ∈ L) :
    ∃ α : Ordinal.{u}, x ∈ LStageZF α ∧ y ∈ LStageZF α := by
  rcases hx with ⟨α, hxα⟩
  rcases hy with ⟨β, hyβ⟩
  exact ⟨max α β,
    LStageZF_mono (le_max_left α β) hxα,
    LStageZF_mono (le_max_right α β) hyβ⟩

/-- Every finite tuple of constructible parameters occurs in one common level. -/
theorem exists_LStage_for_tuple {n : Nat}
    (s : Tuple ZFSet.{u} n) (hs : ∀ i, s i ∈ L) :
    ∃ α : Ordinal.{u}, ∀ i, s i ∈ LStageZF α := by
  induction n with
  | zero =>
      exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
      have hsInit : ∀ i : Fin n, s i.castSucc ∈ L :=
        fun i => hs i.castSucc
      rcases ih (fun i => s i.castSucc) hsInit with ⟨α, hα⟩
      rcases hs (Fin.last n) with ⟨β, hβ⟩
      refine ⟨max α β, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact LStageZF_mono (le_max_right α β) hβ
      · exact LStageZF_mono (le_max_left α β) (hα j)

/-- The constructible universe is closed under unordered pairing. -/
theorem pair_mem_L {x y : ZFSet.{u}} (hx : x ∈ L) (hy : y ∈ L) :
    ({x, y} : ZFSet.{u}) ∈ L := by
  rcases exists_common_LStage hx hy with ⟨α, hxα, hyα⟩
  refine ⟨Order.succ α, ?_⟩
  rw [LStageZF_succ]
  exact pair_mem_DefZF hxα hyα

/-- The constructible universe is closed under singleton formation. -/
theorem singleton_mem_L {x : ZFSet.{u}} (hx : x ∈ L) :
    ({x} : ZFSet.{u}) ∈ L := by
  simpa using pair_mem_L hx hx

/-- The Kuratowski ordered pair of two constructible sets is constructible. -/
theorem orderedPair_mem_L {x y : ZFSet.{u}} (hx : x ∈ L) (hy : y ∈ L) :
    ZFSet.pair x y ∈ L := by
  change ({{x}, {x, y}} : ZFSet.{u}) ∈ L
  exact pair_mem_L (singleton_mem_L hx) (pair_mem_L hx hy)

/-- The constructible universe is closed under internal union. -/
theorem sUnion_mem_L {x : ZFSet.{u}} (hx : x ∈ L) :
    ZFSet.sUnion x ∈ L := by
  rcases hx with ⟨α, hxα⟩
  refine ⟨Order.succ α, ?_⟩
  rw [LStageZF_succ]
  exact sUnion_mem_DefZF (LStageZF_isTransitive α) hxα

/-- The constructible universe is closed under binary union. -/
theorem union_mem_L {x y : ZFSet.{u}} (hx : x ∈ L) (hy : y ∈ L) :
    x ∪ y ∈ L := by
  rw [← ZFSet.sUnion_pair]
  exact sUnion_mem_L (pair_mem_L hx hy)

/-- The constructible universe is closed under binary intersection. -/
theorem inter_mem_L {x y : ZFSet.{u}} (hx : x ∈ L) (hy : y ∈ L) :
    x ∩ y ∈ L := by
  rcases exists_common_LStage hx hy with ⟨α, hxα, hyα⟩
  refine ⟨Order.succ α, ?_⟩
  rw [LStageZF_succ]
  exact inter_mem_DefZF (LStageZF_isTransitive α) hxα hyα

/-- The constructible universe is closed under set difference. -/
theorem sdiff_mem_L {x y : ZFSet.{u}} (hx : x ∈ L) (hy : y ∈ L) :
    x \ y ∈ L := by
  rcases exists_common_LStage hx hy with ⟨α, hxα, hyα⟩
  refine ⟨Order.succ α, ?_⟩
  rw [LStageZF_succ]
  exact sdiff_mem_DefZF (LStageZF_isTransitive α) hxα hyα

/-- The constructible universe is transitive as an external class. -/
theorem mem_L_of_mem {x y : ZFSet.{u}} (hxy : x ∈ y) (hy : y ∈ L) : x ∈ L := by
  rcases hy with ⟨α, hyα⟩
  exact ⟨α, (LStageZF_isTransitive α).mem_trans hxy hyα⟩

theorem IsConstructible.of_mem {x y : ZFSet.{u}}
    (hy : IsConstructible y) (hxy : x ∈ y) : IsConstructible x :=
  mem_L_of_mem hxy hy

end ZFC

end Constructible
