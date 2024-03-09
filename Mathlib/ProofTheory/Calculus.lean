/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.ProofTheory.System

/-!
# Sequent calculus and variants

This file defines the Gentzen's sequent calculus, as well as Tait's calculus.

## Main Definitions
* `Gentzen` Gentzen's sequent calculus
* `Tait`    Tait's calculus

## References
- [Buss, *An Introduction to Proof Theory*][buss]

-/

namespace ProofTheory

/-- Class `OneSided` for one-sided derivations -/
class OneSided (F : Type*) where
  /-- A one-sided derivation -/
  Derivation : List F → Type*

/-- Class `TwoSided` for two-sided derivations -/
class TwoSided (F : Type*) where
  /-- A two-sided derivation -/
  Derivation : List F → List F → Type*

/-- Prefix notation for `OneSided.Derivation`  -/
prefix: 45 " ⊢¹ " => OneSided.Derivation

/-- Infix notation for `TwoSided.Derivation`  -/
infix: 45 " ⊢² " => TwoSided.Derivation

/-- Abbreviation for a one-sided derivable formula -/
abbrev OneSided.Derivable {F : Type*} [OneSided F] (Δ : List F) : Prop := Nonempty (⊢¹ Δ)

/-- Abbreviation for a two-sided derivable formula -/
abbrev TwoSided.Derivable {F : Type*} [TwoSided F] (Γ Δ : List F) : Prop := Nonempty (Γ ⊢² Δ)

/-- Prefix notation for `OneSided.Derivable` -/
prefix: 45 " ⊢¹! " => OneSided.Derivable

/-- Infix notation for `TwoSided.Derivable` -/
infix: 45 " ⊢²! " => TwoSided.Derivable

/-- One-sided proof system having deduction rule of Tait-calculus -/
class Tait (F : Type*) [LogicalConnective F] extends OneSided F where
  /-- `⊤` introduction rule -/
  verum (Δ : List F)         : ⊢¹ ⊤ :: Δ
  /-- `⋏` introduction rule -/
  and {p q : F} {Δ : List F} : ⊢¹ p :: Δ → ⊢¹ q :: Δ → ⊢¹ p ⋏ q :: Δ
  /-- `⋎` introduction rule -/
  or {p q : F} {Δ : List F}  : ⊢¹ p :: q :: Δ → ⊢¹ p ⋎ q :: Δ
  /-- Weakening rule -/
  wk {Δ Δ' : List F}         : ⊢¹ Δ → Δ ⊆ Δ' → ⊢¹ Δ'
  /-- Excluded middle -/
  em {p} {Δ : List F}        : p ∈ Δ → ~p ∈ Δ → ⊢¹ Δ

/-- One-sided proof system having cut rule -/
class Tait.Cut (F : Type*) [LogicalConnective F] [Tait F] where
  /-- cut rule -/
  cut {Δ : List F} {p} : ⊢¹ p :: Δ → ⊢¹ ~p :: Δ → ⊢¹ Δ

/-- Two-sided proof system having deduction rule of Gentzen style sequent calculus -/
class Gentzen (F : Type*) [LogicalConnective F] extends TwoSided F where
  /-- `⊤`-right rule -/
  verum (Γ Δ : List F)                : Γ ⊢² ⊤ :: Δ
  /-- `⊥`-left rule -/
  falsum (Γ Δ : List F)               : ⊥ :: Γ ⊢² Δ
  /-- `~`-left rule -/
  negLeft {p : F} {Γ Δ : List F}      : Γ ⊢² p :: Δ → ~p :: Γ ⊢² Δ
  /-- `~`-right rule -/
  negRight {p : F} {Γ Δ : List F}     : p :: Γ ⊢² Δ → Γ ⊢² ~p :: Δ
  /-- `⋏`-left rule -/
  andLeft {p q : F} {Γ Δ : List F}    : p :: q :: Γ ⊢² Δ → p ⋏ q :: Γ ⊢² Δ
  /-- `⋏`-right rule -/
  andRight {p q : F} {Γ Δ : List F}   : Γ ⊢² p :: Δ → Γ ⊢² q :: Δ → Γ ⊢² p ⋏ q :: Δ
  /-- `⋎`-left rule -/
  orLeft {p q : F} {Γ Δ : List F}     : p :: Γ ⊢² Δ → q :: Γ ⊢² Δ → p ⋎ q :: Γ ⊢² Δ
  /-- `⋎`-right rule -/
  orRight {p q : F} {Γ Δ : List F}    : Γ ⊢² p :: q :: Δ → Γ ⊢² p ⋎ q :: Δ
  /-- `⭢`-left rule -/
  implyLeft {p q : F} {Γ Δ : List F}  : Γ ⊢² p :: Δ → q :: Γ ⊢² Δ → (p ⭢ q) :: Γ ⊢² Δ
  /-- `⭢`-right rule -/
  implyRight {p q : F} {Γ Δ : List F} : p :: Γ ⊢² q :: Δ → Γ ⊢² (p ⭢ q) :: Δ
  /-- Weakening rule -/
  wk {Γ Γ' Δ Δ' : List F}             : Γ ⊢² Δ → Γ ⊆ Γ' → Δ ⊆ Δ' → Γ' ⊢² Δ'
  /-- Axiom for closed sequents -/
  close {p} {Γ Δ : List F}               : p ∈ Γ → p ∈ Δ → Γ ⊢² Δ

/-- Two-sided proof system having cut rule -/
class Gentzen.Cut (F : Type*) [LogicalConnective F] [Gentzen F] where
  /-- Cut rule -/
  cut {Γ Δ : List F} {p} : Γ ⊢² p :: Δ → p :: Γ ⊢² Δ → Γ ⊢² Δ

/-- Class `LawfulTwoSided` for a two-side proof system which is consistent with `Proof` -/
class LawfulTwoSided (F : Type*) [LogicalConnective F] [TwoSided F] [Proof F] where
  /-- To proof -/
  toProof₁ {Γ} {T : Set F} {p : F} : Γ ⊢² [p] → (∀ q ∈ Γ, T ⊢ q) → T ⊢ p

variable {F : Type*} [LogicalConnective F]

namespace OneSided

variable [OneSided F] {Γ Δ : List F}

/-- Cast for equivalent formulas -/
protected abbrev cast (d : ⊢¹ Δ) (e : Δ = Γ) : ⊢¹ Γ := cast (congrArg _ e) d

end OneSided

namespace Tait

variable [DeMorgan F] [Tait F]

variable {Γ Δ : List F}

instance : TwoSided F where
  Derivation := fun Γ Δ ↦ ⊢¹ Γ.map (~·) ++ Δ

/-- Conversion of a two-sided proof of the form `p :: Γ ⊢² Δ` to a one-sided proof -/
def ofConsLeft {p : F} {Γ Δ : List F} (b : p :: Γ ⊢² Δ) :
    ⊢¹ ~p :: (Γ.map (~·) ++ Δ) := wk b (by simp)

/-- Conversion of a two-sided proof of the form `Γ ⊢² p :: Δ` to a one-sided proof -/
def ofConsRight {p : F} {Γ Δ : List F} (b : Γ ⊢² p :: Δ) :
    ⊢¹ p :: (Γ.map (~·) ++ Δ) :=
  wk b (by
    simp only [List.append_subset, List.cons_subset, List.mem_cons, List.mem_append, List.mem_map,
      true_or, true_and]
    exact ⟨List.subset_cons_of_subset _ (List.subset_append_left _ _),
      List.subset_cons_of_subset _ (List.subset_append_right _ _)⟩)

/-- Conversion of a two-sided proof of the form `Γ ⊢² p :: q :: Δ` to a one-sided proof -/
def ofConsRight₂ {p q : F} {Γ Δ : List F} (b : Γ ⊢² p :: q :: Δ) :
    ⊢¹ p :: q :: (Γ.map (~·) ++ Δ) :=
  wk b (by
    simp only [List.append_subset, List.cons_subset, List.mem_cons, List.mem_append, List.mem_map,
      true_or, or_true, true_and]
    exact ⟨List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $
    List.subset_append_left _ _, List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $
    List.subset_append_right _ _⟩)

/-- Conversion of a two-sided proof of the form `p :: Γ ⊢² q :: Δ` to a one-sided proof -/
def ofConsLeftRight {p q : F} {Γ Δ : List F} (b : p :: Γ ⊢² q :: Δ) :
    ⊢¹ ~p :: q :: (Γ.map (~·) ++ Δ) :=
  wk b (by
    simp only [List.map_cons, List.cons_append, List.cons_subset, List.mem_cons, List.mem_append,
      List.mem_map, true_or, List.append_subset, or_true, true_and]
    exact ⟨List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $
      List.subset_append_left _ _, List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $
      List.subset_append_right _ _⟩)

/-- Conversion of an one-sided proof to two-sided proof of the form `p :: Γ ⊢² Δ` -/
def toConsLeft {p : F} {Γ Δ : List F} (b : ⊢¹ ~p :: (Γ.map (~·) ++ Δ)) : p :: Γ ⊢² Δ :=
  wk b (by simp)

/-- Conversion of an one-sided proof to two-sided proof of the form `Γ ⊢² p :: Δ` -/
def toConsRight {p : F} {Γ Δ : List F}
    (b : ⊢¹ p :: (Γ.map (~·) ++ Δ)) :
    Γ ⊢² p :: Δ :=
  wk b (by
    simp only [List.cons_subset, List.mem_append, List.mem_map, List.mem_cons, true_or, or_true,
      List.append_subset, List.subset_append_left, true_and]
    exact List.subset_append_of_subset_right _ (List.subset_cons _ _))

instance : Gentzen F where
  verum := fun _ _ ↦ toConsRight (verum _)
  falsum := fun _ _ ↦ toConsLeft (by simpa using verum _)
  negLeft := fun b ↦ toConsLeft (OneSided.cast (ofConsRight b) (by simp))
  negRight := fun b ↦ toConsRight (OneSided.cast (ofConsLeft b) (by simp))
  andLeft := fun b ↦ OneSided.cast (or b) (by simp)
  andRight := fun bp bq ↦
    toConsRight (OneSided.cast (and (ofConsRight bp) (ofConsRight bq)) (by simp))
  orLeft := fun bp bq ↦
    toConsLeft (OneSided.cast (and (ofConsLeft bp) (ofConsLeft bq)) (by simp))
  orRight := fun b ↦ toConsRight (OneSided.cast (or $ ofConsRight₂ b) (by simp))
  implyLeft := fun bp bq ↦
    toConsLeft (OneSided.cast (and (ofConsRight bp) (ofConsLeft bq)) (by simp[DeMorgan.imply]))
  implyRight := fun b ↦
    toConsRight (OneSided.cast (or $ ofConsLeftRight b) (by simp[DeMorgan.imply]))
  wk := fun b hΓ hΔ ↦ wk b (by
    simp only [List.append_subset]
    exact ⟨List.subset_append_of_subset_left _ $ List.map_subset _ hΓ,
      List.subset_append_of_subset_right _ $ hΔ⟩)
  close := fun {p} _ _ hΓ hΔ ↦ em (p := p)
    (List.mem_append.mpr $ .inr $ hΔ)
    (List.mem_append.mpr $ .inl $ List.mem_map_of_mem (~·) hΓ)

variable [Tait.Cut F]

instance : Gentzen.Cut F := ⟨fun d d' ↦ Cut.cut (ofConsRight d) (ofConsLeft d')⟩

/-- Equivalence for two-sided proof and one-sided proof -/
def equiv : Γ ⊢² Δ ≃ ⊢¹ Γ.map (~·) ++ Δ := Equiv.refl _

/-- A sequent is provable if its succedent is provable in Tait-calculus -/
def tauto (b : ⊢¹ Δ) : Γ ⊢² Δ := wk b (by simp)

end Tait

namespace Gentzen

variable [Gentzen F] [Gentzen.Cut F] {Γ Δ E : List F}

/-- Weaken on the left -/
def wkLeft {Γ Γ' Δ : List F} (d : Γ ⊢² Δ) (ss : Γ ⊆ Γ') : Γ' ⊢² Δ := wk d ss (by simp)

/-- Weaken on the right -/
def wkRight {Γ Δ Δ' : List F} (d : Γ ⊢² Δ) (ss : Δ ⊆ Δ') : Γ ⊢² Δ' := wk d (by simp) ss

/-- Deriving `⊤` (second version) -/
def verum' (h : ⊤ ∈ Δ) : Γ ⊢² Δ := wkRight (verum Γ Δ) (by simp[h])

/-- Employ negation from the left -/
def ofNegLeft {p} (b : ~p :: Γ ⊢² Δ) : Γ ⊢² p :: Δ :=
  let d : p :: Γ ⊢² p :: Δ :=
    Gentzen.wk
      (show [p] ⊢² [p] from close (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl))
      (by simp) (by simp)
  Cut.cut (negRight d) (wkRight b (by simp))

/-- Employ negation from the right -/
def ofNegRight {p} (b : Γ ⊢² ~p :: Δ) : p :: Γ ⊢² Δ :=
  let d : p :: Γ ⊢² p :: Δ :=
    Gentzen.wk
      (show [p] ⊢² [p] from close (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl))
      (by simp) (by simp)
  Cut.cut (wkLeft b (by simp)) (negLeft d)

/-- Define cut (alternative) -/
def Cut.cut' {Γ₁ Γ₂ Δ₁ Δ₂ : List F} {p : F} (d₁ : Γ₁ ⊢² p :: Δ₁) (d₂ : p :: Γ₂ ⊢² Δ₂) :
    Γ₁ ++ Γ₂ ⊢² Δ₁ ++ Δ₂ :=
  let d₁ : Γ₁ ++ Γ₂ ⊢² p :: (Δ₁ ++ Δ₂) := wk d₁ (by simp) (List.cons_subset_cons _ $ by simp)
  let d₂ : p :: (Γ₁ ++ Γ₂) ⊢² Δ₁ ++ Δ₂ := wk d₂ (List.cons_subset_cons _ $ by simp) (by simp)
  Cut.cut d₁ d₂

/-- `T ⊢' Γ` is two-sided proofs where antecedent belongs to the theory `T`.

`T ⊢' {p₁, ..., pₙ}` is equivalent to `T ⊢ p₁ ⋎ ... ⋎ pₙ` if `LawfulTwoSided F` holds. -/
structure Disjconseq (T : Set F) (Γ : List F) where
  /-- Antecedent for derivation -/
  antecedent : List F
  /-- Each antecedent formula is in `T` -/
  antecedent_subset : ∀ p ∈ antecedent, p ∈ T
  /-- Antecedent implies derivation -/
  derivation : antecedent ⊢² Γ

/-- Infix notation for `Disjconseq` -/
infix: 45 " ⊢' " => Disjconseq

variable {T : Set F}

/-- Equivalence with two-sided proof -/
def DisjconseqEquivDerivation : T ⊢' Γ ≃ (Δ : {Δ : List F // ∀ π ∈ Δ, π ∈ T}) × Δ ⊢² Γ where
  toFun := fun b ↦ ⟨⟨b.antecedent, b.antecedent_subset⟩, b.derivation⟩
  invFun := fun p ↦ ⟨p.1, p.1.prop, p.2⟩
  left_inv := fun b ↦ by simp
  right_inv := fun b ↦ by simp

/-- Strengthening still yields derivation -/
def Disjconseq.weakening {T U : Set F} {Γ : List F} (b : T ⊢' Γ) (h : T ⊆ U) : U ⊢' Γ where
  antecedent := b.antecedent
  antecedent_subset := fun p hp ↦ h (b.antecedent_subset p hp)
  derivation := b.derivation

/-- Conversion of a two-sided proofs where antecedent belongs to the theory to `Disjconseq` -/
def toDisjconseq {Γ Δ} (d : Γ ⊢² Δ) (ss : ∀ p ∈ Γ, p ∈ T) : T ⊢' Δ where
  antecedent := Γ
  antecedent_subset := ss
  derivation := d

namespace Disjconseq

/-- A sequent is provable if its succedent is provable in two-sided proof -/
def tauto {Δ} (d : [] ⊢² Δ) : T ⊢' Δ := toDisjconseq d (by simp)

/-- Weakening for sequents -/
def wk (b : T ⊢' Γ) (Γ' : List F) (ss : Γ ⊆ Γ') : T ⊢' Γ' where
  antecedent := b.antecedent
  antecedent_subset := b.antecedent_subset
  derivation := wkRight b.derivation ss

/-- Cut for sequents -/
def cut (p : F) (b : T ⊢' p :: Γ) (b' : T ⊢' ~p :: Γ) : T ⊢' Γ where
  antecedent := b.antecedent ++ b'.antecedent
  antecedent_subset := by
    simp only [List.mem_append]
    rintro p (hp | hp)
    · exact b.antecedent_subset _ hp
    · exact b'.antecedent_subset _ hp
  derivation :=
    let d : b.antecedent ++ b'.antecedent ⊢² p :: Γ := wkLeft b.derivation (by simp)
    let d' : b.antecedent ++ b'.antecedent ⊢² ~p :: Γ := wkLeft b'.derivation (by simp)
    Cut.cut d' (negLeft d)

/-- Cut for sequents (alternative) -/
def cut' (p : F) (b : T ⊢' p :: Γ) (b' : T ⊢' ~p :: Δ) : T ⊢' Γ ++ Δ where
  antecedent := b.antecedent ++ b'.antecedent
  antecedent_subset := by
    simp only [List.mem_append]
    rintro p (hp | hp)
    · exact b.antecedent_subset _ hp
    · exact b'.antecedent_subset _ hp
  derivation := by
    let d : b.antecedent ++ b'.antecedent ⊢² p :: Γ := wkLeft b.derivation (by simp)
    let d' : b.antecedent ++ b'.antecedent ⊢² ~p :: Δ := wkLeft b'.derivation (by simp)
    exact Gentzen.wk (Cut.cut' d' (negLeft d)) (by simp) (by simp)

/-- Verum for sequents -/
def verum (Γ : List F) : T ⊢' ⊤ :: Γ := ⟨[], by simp, Gentzen.verum _ _⟩

-- def verum' (h : ⊤ ∈ Γ) : T ⊢' Γ := wk (verum Γ) (by simp[h])

/-- `⋏` introduction -/
def and (p q : F) (bp : T ⊢' p :: Δ) (bq : T ⊢' q :: Δ) : T ⊢' p ⋏ q :: Δ where
  antecedent := bp.antecedent ++ bq.antecedent
  antecedent_subset := by
    simp only [List.mem_append]
    rintro p (hp | hp)
    · exact bp.antecedent_subset _ hp
    · exact bq.antecedent_subset _ hp
  derivation := Gentzen.andRight
      (Gentzen.wkLeft bp.derivation (List.subset_append_left _ _))
      (Gentzen.wkLeft bq.derivation (List.subset_append_right _ _))

/-- `⋎` introduction -/
def or (p q : F)  (b : T ⊢' p :: q :: Δ) : T ⊢' p ⋎ q :: Δ where
  antecedent := b.antecedent
  antecedent_subset := b.antecedent_subset
  derivation := Gentzen.orRight b.derivation

/-- Deduction theorem for `Disjconseq` -/
def deduction [DecidableEq F] {p} (b : insert p T ⊢' Δ) : T ⊢' ~p :: Δ where
  antecedent := b.antecedent.filter (· ≠ p)
  antecedent_subset := by
    simp[List.mem_filter]
    intro q hq ne
    simpa[ne] using b.antecedent_subset q hq
  derivation := negRight (wkLeft b.derivation $ by
    intro q hq
    by_cases e : q = p <;> simp[List.mem_filter, hq, e])

/-- Deduction theorem for `Disjconseq` -/
def deductionNeg [DecidableEq F] {p} (b : insert (~p) T ⊢' Δ) : T ⊢' p :: Δ where
  antecedent := b.antecedent.filter (· ≠ ~p)
  antecedent_subset := by
    simp[List.mem_filter]
    intro q hq ne
    simpa[ne] using b.antecedent_subset q hq
  derivation := ofNegLeft (wkLeft b.derivation $ by
    intro q hq
    by_cases e : q = ~p <;> simp[List.mem_filter, hq, e])

end Disjconseq

variable (F)

instance : Proof F where
  Prf := fun T p ↦ T ⊢' [p]
  axm := fun {p T} h ↦
    ⟨[p], by simpa,
      close (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl)⟩
  weakening' := fun ss b ↦ b.weakening ss

variable {F}

/-- Conversion of a two-sided proof whose antecedent is provable to a `Disjconseq` -/
def toProof : {Γ Δ : List F} → Γ ⊢² Δ → (∀ q ∈ Γ, T ⊢ q) → T ⊢' Δ
  | [],     _, d, _ => toDisjconseq d (by simp)
  | q :: Γ, Δ, d, h =>
    let bn : T ⊢' ~q :: Δ := toProof (negRight d) (fun q hq ↦ h q (by simp[hq]))
    let b : T ⊢' [q] := h q (by simp)
    b.cut' q bn

instance : LawfulTwoSided F := ⟨toProof⟩

/-- Cut a theory `U` -/
def proofCut {T U : Set F} {p} (dU : T ⊢* U) (dp : U ⊢ p) : T ⊢ p :=
  toProof dp.derivation (fun q hq ↦ dU $ dp.antecedent_subset q hq)

/-- Proof is equivalent to two-sided proof -/
def proofEquivDerivation {p : F} :
    T ⊢ p ≃ (Δ : {Δ : List F // ∀ π ∈ Δ, π ∈ T}) × Δ ⊢² [p] :=
  DisjconseqEquivDerivation

lemma provable_iff {p : F} :
    T ⊢! p ↔ ∃ Δ : List F, (∀ π ∈ Δ, π ∈ T) ∧ (Δ ⊢²! [p]) :=
  ⟨by rintro ⟨b⟩; rcases proofEquivDerivation b with ⟨Δ, d⟩; exact ⟨Δ, Δ.prop, ⟨d⟩⟩,
   by rintro ⟨Δ, h, ⟨d⟩⟩; exact ⟨proofEquivDerivation.symm ⟨⟨Δ, h⟩, d⟩⟩⟩

theorem compact :
    Proof.Consistent T ↔ ∀ T' : Finset F, ↑T' ⊆ T → Proof.Consistent (T' : Set F) :=
  ⟨fun c u hu ↦ c.of_subset hu,
   fun h ↦ ⟨by
    letI := Classical.typeDecidableEq F
    rintro ⟨Δ, hΔ, d⟩
    exact (Proof.unprovable_iff_not_provable.mp $
      Proof.consistent_iff_unprovable.mp $ h Δ.toFinset (by intro p; simpa using hΔ p))
      (provable_iff.mpr $ ⟨Δ, by simp, ⟨d⟩⟩)⟩⟩

theorem compact_inconsistent (h : ¬Proof.Consistent T) :
    ∃ s : Finset F, ↑s ⊆ T ∧ ¬Proof.Consistent (s : Set F) := by
  simpa using (not_iff_not.mpr compact).mp h

lemma consistent_iff_empty_sequent :
    Proof.Consistent T ↔ IsEmpty (T ⊢' []) :=
  ⟨by contrapose; simp[Proof.Consistent]; intro b; exact ⟨b.wk _ (by simp)⟩,
   by contrapose; simp[Proof.Consistent]
      rintro ⟨Δ, h, d⟩
      have : Δ ⊢² [] := Cut.cut d (falsum _ _)
      exact ⟨toDisjconseq this h⟩⟩

lemma provable_iff_inconsistent {p} :
    T ⊢! p ↔ ¬ Proof.Consistent (insert (~p) T) :=
  ⟨by rintro ⟨⟨Δ, h, d⟩⟩
      simp[consistent_iff_empty_sequent]
      exact ⟨⟨~p :: Δ, by simp; intro q hq; right; exact h q hq, negLeft d⟩⟩,
   by letI := Classical.typeDecidableEq F
      simp[consistent_iff_empty_sequent]
      intro b
      exact ⟨b.deductionNeg⟩⟩

lemma refutable_iff_inconsistent {p} :
    T ⊢! ~p ↔ ¬Proof.Consistent (insert p T) :=
  ⟨by rintro ⟨⟨Δ, h, d⟩⟩
      simp[consistent_iff_empty_sequent]
      exact ⟨⟨p :: Δ, by simp; intro q hq; right; exact h q hq, ofNegRight d⟩⟩,
   by letI := Classical.typeDecidableEq F
      simp[consistent_iff_empty_sequent]
      intro b
      exact ⟨b.deduction⟩⟩

lemma consistent_insert_iff_not_refutable {p} :
    Proof.Consistent (insert p T) ↔ T ⊬ ~p := by
  rw [Proof.unprovable_iff_not_provable, refutable_iff_inconsistent]; simp

lemma inconsistent_of_provable_and_refutable {p}
    (bp : T ⊢ p) (br : T ⊢ ~p) : ¬ Proof.Consistent T := fun A ↦ by
  have : T ⊢' [] := Disjconseq.cut _ bp br
  exact (consistent_iff_empty_sequent.mp A).false this

lemma inconsistent_of_provable_and_refutable' {p}
    (bp : T ⊢! p) (br : T ⊢! ~p) : ¬ Proof.Consistent T := by
  rcases bp with ⟨bp⟩; rcases br with ⟨br⟩
  exact inconsistent_of_provable_and_refutable bp br

@[simp] lemma consistent_theory_iff_consistent :
    Proof.Consistent (Proof.theory T) ↔ Proof.Consistent T :=
  ⟨fun h ↦ h.of_subset (by intro _; simp[Proof.theory]; exact fun h ↦ ⟨Proof.axm h⟩),
   fun consis ↦ ⟨fun b ↦ by
      have : ¬ Proof.Consistent T := Proof.inconsistent_of_proof
        (proofCut Proof.provableTheory_theory b)
      contradiction ⟩⟩

end Gentzen

namespace LawfulTwoSided

variable [Proof F] [TwoSided F] [LawfulTwoSided F]

/-- Nil proof -/
def toProofOfNil {p : F} (b : [] ⊢² [p]) (T : Set F) : T ⊢ p :=
  toProof₁ b (by intro q h; exact False.elim ((List.mem_nil_iff q).mp h))

lemma toProof₁! {Γ} {T : Set F} {p : F} (b : Γ ⊢² [p]) (H : ∀ q ∈ Γ, T ⊢! q) : T ⊢! p :=
  ⟨toProof₁ b (fun q hq ↦ (H q hq).toProof)⟩

end LawfulTwoSided

end ProofTheory
