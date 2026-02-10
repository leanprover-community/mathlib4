/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Corecursion

/-!

# Multiseries definitions

In this file we define the multiseries and its main properties: sortedness and approximation.

## Main definitions

* `Basis` is the list of functions used to construct monomials in multiseries.
* `Multiseries basis_hd basis_tl` is the type of multiseries in a basis `basis_hd :: basis_tl`.
* `MultiseriesExpansion basis` is an multiseries expansion of some function `f : ℝ → ℝ`.
  If `basis = []` then the mutliseries represents a constant function, otherwise it is
  a pair of a multiseries `ms : Multiseries basis_hd basis_tl` and a function `f : ℝ → ℝ`.
* `Multiseries.Sorted ms` means that at each level of `ms` as a nested tree all exponents are
  strictly decreasing.
* `MultiseriesExpansion.Approximates ms` means that the multiseries `ms` can be used to obtain
  an asymptotical approximations of its attached function.

## Implementation details

* `Multiseries basis_hd basis_tl` is defined as a `Seq (ℝ × MultiseriesExpansion basis_tl)`, so
  we need to port some `Seq` API to `Multiseries`.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Filter Asymptotics Topology Stream'

/-- List of functions used to construct monomials in multiseries. -/
abbrev Basis := List (ℝ → ℝ)

/-- Multiseries representing a given function `f : ℝ → ℝ`.
`MultiseriesExpansion []` is just `ℝ`: multiseries representing constant functions.
Otherwise it is a pair of a `Multiseries basis_hd basis_tl` and a function `ℝ → ℝ`. We call
the former an expansion of the latter. -/
def MultiseriesExpansion (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | .cons _ basis_tl => Seq (ℝ × MultiseriesExpansion basis_tl) × (ℝ → ℝ)

namespace MultiseriesExpansion

set_option linter.unusedVariables false in
/-- Multiseries in a basis `basis_hd :: basis_tl`. It is a generalisation of asymptotic expansions.
A multiseries in a basis `[b₁, ..., bₙ]` is a formal series made from monomials
`b₁ ^ e₁ * ... * bₙ ^ eₙ` where `e₁, ..., eₙ` are real numbers. We treat multivariate series in
a basis `[b₁, ..., bₙ]` as a univariate series in the variable `b₁` (`basis_hd`) with coefficients
being multiseries in the basis `[b₂, ..., bₙ]` (`basis_tl`). We represent such a series as a lazy
list (`Seq`) of pairs `(exp, coef)` where `exp` is the exponent of `b₁` and `coef` is the
coefficient (a multiseries in `basis_tl`). -/
@[nolint unusedArguments]
def Multiseries (basis_hd : ℝ → ℝ) (basis_tl : Basis) : Type :=
  Seq (ℝ × MultiseriesExpansion basis_tl)

namespace Multiseries

/-- Converts a `Multiseries basis_hd basis_tl` to a `Seq (ℝ × MultiseriesExpansion basis_tl)`. -/
def toSeq {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Seq (ℝ × MultiseriesExpansion basis_tl) :=
  ms

/-- The empty multiseries. -/
def nil {basis_hd basis_tl} : Multiseries basis_hd basis_tl := Seq.nil

/-- Prepend a monomial to a multiseries. -/
def cons {basis_hd basis_tl} (exp : ℝ) (coef : MultiseriesExpansion basis_tl)
    (tl : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd basis_tl :=
  Seq.cons (exp, coef) tl

/-- Recursion principle for `Multiseries basis_hd basis_tl`. It is equivalent to
`Stream'.Seq.recOn` but provides some convenience. -/
@[cases_eliminator]
def recOn {basis_hd basis_tl} {motive : Multiseries basis_hd basis_tl → Sort*}
    (ms : Multiseries basis_hd basis_tl) (nil : motive nil)
    (cons : ∀ exp coef (tl : Multiseries basis_hd basis_tl), motive (cons exp coef tl)) :
    motive ms := by
  cases ms using Stream'.Seq.recOn with
  | nil => apply nil
  | cons hd tl => apply cons

/-- Destruct a multiseries into a triple `(exp, coef, tl)`, where `exp` is leading exponent,
`coef` is leading coefficient, and `tl` is tail. -/
def destruct {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Option (ℝ × MultiseriesExpansion basis_tl × Multiseries basis_hd basis_tl) :=
  (Seq.destruct ms).map (fun ((exp, coef), tl) => (exp, coef, tl))

/-- The head of a multiseries, i.e. the first two elements of `destruct`. -/
def head {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Option (ℝ × MultiseriesExpansion basis_tl) :=
  Seq.head ms

/-- The tail of a multiseries, i.e. the last element of `destruct`. -/
def tail {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) : Multiseries basis_hd basis_tl :=
  Seq.tail ms

/-- Given two functions `f : ℝ → ℝ` and
`g : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl'`, apply them to exponents and
coefficients of a multiseries. -/
def map {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → ℝ)
    (g : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl')
    (ms : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd' basis_tl' :=
  Seq.map (fun (exp, coef) ↦ (f exp, g coef)) ms

/-- Corecursor for `Multiseries basis_hd basis_tl`. -/
def corec {β : Type*} {basis_hd} {basis_tl}
    (f : β → Option (ℝ × MultiseriesExpansion basis_tl × β)) (b : β) :
    Multiseries basis_hd basis_tl :=
  Seq.corec (fun a => (f a).map (fun (exp, coef, next) => ((exp, coef), next))) b

/-- An operation on multiseries called a "friend" if any `n`-prefix of its output depends only on
the `n`-prefix of the input. Such operations can be used in the tail of (non-primitive) corecursive
definitions. -/
def FriendlyOperation {basis_hd basis_tl}
    (op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl) : Prop :=
  Seq.FriendlyOperation op

/-- A family of friendly operations on multiseries indexed by a type `γ`. -/
class FriendlyOperationClass {basis_hd basis_tl} {γ : Type*}
    (op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl) : Prop
    extends Seq.FriendlyOperationClass op

theorem FriendlyOperationClass.mk' {basis_hd basis_tl} {γ : Type*}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h : ∀ c, FriendlyOperation (op c)) :
    FriendlyOperationClass op := by
  suffices Seq.FriendlyOperationClass op by constructor
  exact ⟨h⟩

private lemma destruct_eq_destruct_map {basis_hd basis_tl}
    (s : Stream'.Seq (ℝ × MultiseriesExpansion basis_tl)) :
    s.destruct = (Multiseries.destruct (basis_hd := basis_hd) s).map
      (fun (exp, coef, tl) => ((exp, coef), tl)) := by
  simp only [destruct, Option.map_map]
  exact Option.map_id_apply.symm

theorem FriendlyOperation.coind_comp_friend_left {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (motive : (Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl) → Prop)
    (h_base : motive op)
    (h_step : ∀ op, motive op → ∃ T : Option (ℝ × MultiseriesExpansion basis_tl) →
        Option (ℝ × MultiseriesExpansion basis_tl × Subtype FriendlyOperation × Subtype motive),
      ∀ s, (op s).destruct =
        (T s.head).map (fun (exp, coef, opf, op') => (exp, coef, opf.val <| op'.val (s.tail)))) :
    FriendlyOperation op := by
  apply Seq.FriendlyOperation.coind_comp_friend_left motive h_base
  intro op h_op
  specialize h_step op h_op
  obtain ⟨T, hT⟩ := h_step
  use fun hd? ↦ (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  specialize hT s
  rw [destruct_eq_destruct_map, hT]
  simp [head]
  rfl

theorem FriendlyOperation.coind_comp_friend_right {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (motive : (Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl) → Prop)
    (h_base : motive op)
    (h_step : ∀ op, motive op → ∃ T : Option (ℝ × MultiseriesExpansion basis_tl) →
        Option (ℝ × MultiseriesExpansion basis_tl × Subtype FriendlyOperation × Subtype motive),
      ∀ s, (op s).destruct =
        (T s.head).map (fun (exp, coef, opf, op') => (exp, coef, op'.val <| opf.val (s.tail)))) :
    FriendlyOperation op := by
  apply Seq.FriendlyOperation.coind_comp_friend_right motive h_base
  intro op h_op
  specialize h_step op h_op
  obtain ⟨T, hT⟩ := h_step
  use fun hd? ↦ (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  specialize hT s
  rw [destruct_eq_destruct_map, hT]
  simp [Seq.head]
  rfl

/-- Non-primitive corecursor for `Multiseries basis_hd basis_tl` allowing to use a friendly
operation in the tail of the corecursive definition. -/
noncomputable def gcorec {β γ : Type*} {basis_hd} {basis_tl}
    (F : β → Option (ℝ × MultiseriesExpansion basis_tl × γ × β))
    (op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl)
    [FriendlyOperationClass op]
    (b : β) :
    Multiseries basis_hd basis_tl :=
  Seq.gcorec (fun a => (F a).map (fun (exp, coef, c, next) => ((exp, coef), c, next))) op b


instance (basis_hd basis_tl) : Inhabited (Multiseries basis_hd basis_tl) where
  default := (default : Seq (ℝ × MultiseriesExpansion basis_tl))

instance {basis_hd basis_tl} :
    Membership (ℝ × MultiseriesExpansion basis_tl) (Multiseries basis_hd basis_tl) where
  mem ms x := x ∈ ms.toSeq

theorem eq_of_bisim {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x y : Multiseries basis_hd basis_tl}
    (motive : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = .nil ∧ y = .nil) ∨ ∃ exp coef,
      ∃ (x' y' : Multiseries basis_hd basis_tl),
      x = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') :
    x = y := Seq.eq_of_bisim' motive base (by grind [nil, cons])

theorem eq_of_bisim_strong {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {x y : Multiseries basis_hd basis_tl}
    (motive : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = y) ∨ ∃ exp coef,
      ∃ (x' y' : Multiseries basis_hd basis_tl),
      x = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') :
    x = y := Seq.eq_of_bisim_strong motive base (by grind [nil, cons])

theorem FriendlyOperationClass.FriendlyOperation {basis_hd basis_tl} {γ : Type*}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    [h : FriendlyOperationClass op]
    (c : γ) :
    FriendlyOperation (op c) :=
  h.friend c

theorem FriendlyOperation.destruct {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h : FriendlyOperation op) :
    ∃ T : Option (ℝ × MultiseriesExpansion basis_tl) →
      Option (ℝ × MultiseriesExpansion basis_tl × Subtype FriendlyOperation),
      ∀ ms, destruct (op ms) = (T ms.head).map
        (fun (exp, coef, op') ↦ (exp, coef, op'.val ms.tail)) := by
  have h' := Seq.FriendlyOperation.destruct h
  obtain ⟨T, hT⟩ := h'
  use fun hd? ↦ (T hd?).map (fun ((exp, coef), op') ↦ (exp, coef, op'))
  intro ms
  specialize hT ms
  unfold Multiseries.destruct
  simp [hT]
  simp [head, tail]
  cases T (Seq.head ms) <;> simp

theorem FriendlyOperation.head_eq_head {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h : FriendlyOperation op) {x y : Multiseries basis_hd basis_tl}
    (h_head : x.head = y.head) : (op x).head = (op y).head :=
  Seq.FriendlyOperation.op_head_eq h h_head

theorem FriendlyOperation.id {basis_hd basis_tl} :
    FriendlyOperation (id : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl) :=
  Seq.FriendlyOperation.id

theorem FriendlyOperation.comp {basis_hd basis_tl}
    {op₁ op₂ : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h₁ : FriendlyOperation op₁) (h₂ : FriendlyOperation op₂) :
    FriendlyOperation (op₁ ∘ op₂) :=
  Seq.FriendlyOperation.comp h₁ h₂

theorem FriendlyOperation.const {basis_hd basis_tl} {s : Multiseries basis_hd basis_tl} :
    FriendlyOperation (fun _ ↦ s) :=
  Seq.FriendlyOperation.const

theorem FriendlyOperation.ite {basis_hd basis_tl}
    {op₁ op₂ : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h₁ : FriendlyOperation op₁) (h₂ : FriendlyOperation op₂)
    {P : Option (ℝ × MultiseriesExpansion basis_tl) → Prop} [DecidablePred P] :
    FriendlyOperation (fun ms ↦ if P ms.head then op₁ ms else op₂ ms) :=
  Seq.FriendlyOperation.ite h₁ h₂

theorem FriendlyOperation.cons {basis_hd basis_tl} (exp : ℝ)
    (coef : MultiseriesExpansion basis_tl) :
    FriendlyOperation (cons (basis_hd := basis_hd) exp coef) :=
  Seq.FriendlyOperation.cons _

theorem FriendlyOperation.cons_tail {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    (h : FriendlyOperation op) :
    FriendlyOperation (fun ms ↦ (op (.cons exp coef ms)).tail) :=
  Seq.FriendlyOperation.cons_tail h

theorem FriendlyOperationClass.comp {basis_hd basis_tl} {γ γ' : Type*}
    {g : γ' → γ}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    [h : FriendlyOperationClass op] : FriendlyOperationClass (fun c ↦ op (g c)) := by
  have : Seq.FriendlyOperationClass (fun c ↦ op (g c)) := by
    apply Seq.FriendlyOperationClass.comp
  constructor

theorem eq_of_bisim_friend {γ : Type*} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    [FriendlyOperationClass op]
    {x y : Multiseries basis_hd basis_tl}
    (motive : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = y) ∨ ∃ exp coef,
      ∃ (c : γ) (x' y' : Multiseries basis_hd basis_tl),
      x = cons exp coef (op c x') ∧ y = cons exp coef (op c y') ∧ motive x' y') :
    x = y := by
  apply Seq.FriendlyOperationClass.eq_of_bisim (op := op) motive base
  peel step with x y ih h
  obtain h | ⟨exp, coef, c, x', y', rfl, rfl, h_next⟩ := h
  · simp [h]
  right
  use (exp, coef), x', y', c
  simpa [cons]

section simp

@[simp]
theorem cons_ne_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    cons exp coef tl ≠ .nil := by
  intro h
  simp only [cons, nil] at h
  apply Seq.cons_ne_nil h

@[simp]
theorem nil_ne_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    .nil ≠ cons exp coef tl := cons_ne_nil.symm

@[simp]
theorem cons_eq_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp1 exp2 : ℝ}
    {coef1 coef2 : MultiseriesExpansion basis_tl} {tl1 tl2 : Multiseries basis_hd basis_tl} :
    cons exp1 coef1 tl1 = cons exp2 coef2 tl2 ↔ exp1 = exp2 ∧ coef1 = coef2 ∧ tl1 = tl2 := by
  rw [cons, cons, Seq.cons_eq_cons]
  grind

theorem corec_nil {β : Type*} {basis_hd} {basis_tl}
    {f : β → Option (ℝ × MultiseriesExpansion basis_tl × β)} {b : β} (h : f b = none) :
    corec f b = (nil : Multiseries basis_hd basis_tl) := by
  simp only [corec, nil]
  rw [Seq.corec_nil]
  simpa

theorem corec_cons {β : Type*} {basis_hd} {basis_tl} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {next : β}
    {f : β → Option (ℝ × MultiseriesExpansion basis_tl × β)} {b : β}
    (h : f b = some (exp, coef, next)) :
    (corec f b : Multiseries basis_hd basis_tl) = cons exp coef (corec f next) := by
  simp only [corec, cons]
  rw [Seq.corec_cons]
  simpa

theorem gcorec_nil {β γ : Type*} {basis_hd} {basis_tl}
    {F : β → Option (ℝ × MultiseriesExpansion basis_tl × γ × β)}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    [FriendlyOperationClass op] {b : β}
    (h : F b = none) :
    gcorec F op b = nil := by
  unfold gcorec
  rw [Seq.gcorec_nil]
  · simp [nil]
  · simpa

theorem gcorec_some {β γ : Type*} {basis_hd} {basis_tl}
    {F : β → Option (ℝ × MultiseriesExpansion basis_tl × γ × β)}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    [FriendlyOperationClass op] {b : β}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {c : γ} {next : β}
    (h : F b = some (exp, coef, c, next)) :
    gcorec F op b = cons exp coef (op c (gcorec F op next)) := by
  unfold gcorec
  rw [Seq.gcorec_some]
  · simp [cons]
    rfl
  · simpa

@[simp]
theorem destruct_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    destruct (nil : Multiseries basis_hd basis_tl) = none := by
  simp [destruct, nil]

@[simp]
theorem destruct_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    destruct (cons exp coef tl) = some (exp, coef, tl) := by
  simp [destruct, cons]

theorem destruct_eq_none {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    (h : destruct ms = none) : ms = nil := by
  apply Stream'.Seq.destruct_eq_none
  simpa [destruct] using h

theorem destruct_eq_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : destruct ms = some (exp, coef, tl)) : ms = cons exp coef tl := by
  apply Stream'.Seq.destruct_eq_cons
  simp [destruct] at h
  grind

@[simp]
theorem head_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (nil : Multiseries basis_hd basis_tl).head = none := by
  simp [head, nil]

@[simp]
theorem head_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).head = some (exp, coef) := by
  simp [head, cons]

@[simp]
theorem tail_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (nil : Multiseries basis_hd basis_tl).tail = nil := by
  simp [tail, nil]

@[simp]
theorem tail_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).tail = tl := by
  simp [tail, cons]

@[simp]
theorem map_nil {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → ℝ)
    (g : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl') :
    (nil : Multiseries basis_hd basis_tl).map f g = (nil : Multiseries basis_hd' basis_tl') := by
  simp [map, nil]

@[simp]
theorem map_cons {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → ℝ)
    (g : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl') {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).map f g = cons (basis_hd := basis_hd')
      (f exp) (g coef) (map f g tl) := by
  simp [map, cons]

@[simp]
theorem map_id {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    ms.map (fun exp => exp) (fun coef => coef) = ms :=
  Stream'.Seq.map_id ms

@[simp← ]
theorem map_comp {b₁ b₂ b₃ bs₁ bs₂ bs₃}
    (f₁ : ℝ → ℝ) (g₁ : MultiseriesExpansion bs₁ → MultiseriesExpansion bs₂)
    (f₂ : ℝ → ℝ) (g₂ : MultiseriesExpansion bs₂ → MultiseriesExpansion bs₃)
    (ms : Multiseries b₁ bs₁) :
    (ms.map (f₂ ∘ f₁) (g₂ ∘ g₁) : Multiseries b₃ bs₃) =
    (ms.map f₁ g₁ : Multiseries b₂ bs₂).map f₂ g₂ := by
  simp [map, ← Stream'.Seq.map_comp]
  rfl

@[simp]
theorem notMem_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x : ℝ × MultiseriesExpansion basis_tl} :
    x ∉ (nil : Multiseries basis_hd basis_tl) :=
  Seq.notMem_nil _

@[simp]
theorem mem_cons_iff {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {x : ℝ × MultiseriesExpansion basis_tl} :
    x ∈ cons exp coef tl ↔ x = (exp, coef) ∨ x ∈ tl :=
  Seq.mem_cons_iff

@[simp]
theorem Pairwise_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {R} :
    Seq.Pairwise R (nil : Multiseries basis_hd basis_tl) := by
  simp [nil]

@[simp]
theorem Pairwise_cons_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {R exp coef} :
    Seq.Pairwise R (cons exp coef (nil : Multiseries basis_hd basis_tl)) := by
  simp [cons, nil]

end simp

end Multiseries

/-- Convert a real number to a multiseries in empty basis. -/
def ofReal (c : ℝ) : MultiseriesExpansion [] := c

/-- Convert a multiseries in empty basis to a real number. -/
def toReal (ms : MultiseriesExpansion []) : ℝ := ms

/-- Convert a multiseries in non-empty basis to a sequence of pairs `(exp, coef)`. -/
def seq {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    Multiseries basis_hd basis_tl :=
  ms.1

/-- Convert a multiseries to a function. -/
def toFun {basis : Basis} (ms : MultiseriesExpansion basis) : ℝ → ℝ :=
  match basis with
  | [] => fun _ ↦ ms.toReal
  | .cons _ _ =>  ms.2

/-- Constructs a multiseries from a `Multiseries basis_hd basis_tl` and a function. -/
def mk {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : ℝ → ℝ) :
    MultiseriesExpansion (basis_hd :: basis_tl) :=
  (s, f)

/-- Recursion principle for `MultiseriesExpansion (basis_hd :: basis_tl)`. -/
@[cases_eliminator]
def recOn {basis_hd basis_tl} {motive : MultiseriesExpansion (basis_hd :: basis_tl) → Sort*}
    (nil : ∀ f, motive (mk .nil f))
    (cons : ∀ exp coef tl f, motive (.mk (.cons exp coef tl) f))
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : motive ms := by
  let ⟨s, f⟩ := ms
  cases s with
  | nil => apply nil
  | cons hd tl => apply cons

instance (basis : Basis) : Inhabited (MultiseriesExpansion basis) :=
  match basis with
  | [] => ⟨(default : ℝ)⟩
  | List.cons basis_hd basis_tl => ⟨(default : Multiseries basis_hd basis_tl × (ℝ → ℝ))⟩

theorem eq_mk {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    ms = mk ms.seq ms.toFun := rfl

theorem mk_eq_mk_iff {basis_hd basis_tl} (s t : Multiseries basis_hd basis_tl) (f g : ℝ → ℝ) :
    mk (basis_hd := basis_hd) s f = mk (basis_hd := basis_hd) t g ↔ s = t ∧ f = g where
  mp h := by rwa [mk, mk, Prod.mk_inj] at h
  mpr h := by simp [h]

@[simp]
theorem ms_eq_mk_iff {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl))
    (s : Multiseries basis_hd basis_tl) (f : ℝ → ℝ) : ms = mk s f ↔ ms.seq = s ∧ ms.toFun = f := by
  conv => lhs; lhs; rw [eq_mk ms]
  rw [mk_eq_mk_iff]

@[simp]
theorem mk_eq_mk_iff_iff {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl))
    (s : Multiseries basis_hd basis_tl) (f : ℝ → ℝ) :
    mk s f = ms ↔ ms.seq = s ∧ ms.toFun = f := by
  rw [@Eq.comm _ (mk s f) ms, ms_eq_mk_iff]

theorem ms_eq_ms_iff_mk_eq_mk {basis_hd basis_tl}
    (ms₁ ms₂ : MultiseriesExpansion (basis_hd :: basis_tl)) :
    ms₁ = ms₂ ↔ ms₁.seq = ms₂.seq ∧ ms₁.toFun = ms₂.toFun where
  mp h := by simp [h]
  mpr h := by
    rw [eq_mk ms₁, eq_mk ms₂]
    simp [h]

@[simp]
theorem const_toFun (ms : MultiseriesExpansion []) : ms.toFun = fun _ ↦ ms.toReal := rfl

@[simp]
theorem mk_toFun {basis_hd basis_tl} {s : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} :
    (mk (basis_hd := basis_hd) s f).toFun = f := rfl

@[simp]
theorem mk_seq {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : ℝ → ℝ) :
    (mk (basis_hd := basis_hd) s f).seq = s := rfl

/-- Replace the function attached to a multiseries. -/
def replaceFun {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl))
    (f : ℝ → ℝ) : MultiseriesExpansion (basis_hd :: basis_tl) :=
  mk ms.seq f

@[simp]
theorem mk_replaceFun {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl)
    (f g : ℝ → ℝ) :
    (mk (basis_hd := basis_hd) s f).replaceFun g = mk (basis_hd := basis_hd) s g :=
  rfl

@[simp]
theorem replaceFun_toFun {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) (f : ℝ → ℝ) :
    (ms.replaceFun f).toFun = f := rfl

@[simp]
theorem replaceFun_seq {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) (f : ℝ → ℝ) :
    (ms.replaceFun f).seq = ms.seq := rfl

section leadingExp

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}
  {ms : MultiseriesExpansion (basis_hd :: basis_tl)}

namespace Multiseries

/-- The leading exponent of multiseries with non-empty basis. For `ms = []` it is `⊥`. -/
def leadingExp (s : Multiseries basis_hd basis_tl) : WithBot ℝ :=
  match s.head with
  | none => ⊥
  | some (exp, _) => exp

@[simp]
theorem leadingExp_nil : (nil : Multiseries basis_hd basis_tl).leadingExp = ⊥ :=
  rfl

@[simp]
theorem leadingExp_cons {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).leadingExp = exp :=
  rfl

/-- If `ms.leadingExp = ⊥` then `ms = []`. -/
@[simp]
theorem leadingExp_eq_bot (s : Multiseries basis_hd basis_tl) :
    s.leadingExp = ⊥ ↔ s = nil := by
  cases s <;> simp

end Multiseries

/-- The leading exponent of multiseries with non-empty basis. For `ms = []` it is `⊥`. -/
def leadingExp (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : WithBot ℝ :=
  ms.seq.leadingExp

@[simp]
theorem leadingExp_def (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    leadingExp ms = ms.seq.leadingExp := rfl

end leadingExp

section Sorted

/-- Auxilary instance for order on pairs `(exp, coef)` used below to define `Sorted` in terms
of `Stream'.Seq.Pairwise`. `(exp₁, coef₁) ≤ (exp₂, coef₂)` iff `exp₁ ≤ exp₂`. -/
scoped instance {basis} : Preorder (ℝ × MultiseriesExpansion basis) := Preorder.lift Prod.fst

private theorem lt_iff_lt {basis} {exp1 exp2 : ℝ} {coef1 coef2 : MultiseriesExpansion basis} :
    (exp1, coef1) < (exp2, coef2) ↔ exp1 < exp2 := by
  rfl

/-- Multiseries `ms` is `Sorted` when at each its level exponents are sorted. -/
inductive Sorted : {basis : Basis} → (MultiseriesExpansion basis) → Prop
| const (ms : MultiseriesExpansion []) : Sorted ms
| seq {hd} {tl} (ms : MultiseriesExpansion (hd :: tl))
    (h_coef : ∀ x ∈ ms.seq, x.2.Sorted)
    (h_Pairwise : Seq.Pairwise (· > ·) ms.seq) : ms.Sorted

/-- Multiseries `ms` is `Sorted` when at each its level exponents are sorted. -/
def Multiseries.Sorted {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) : Prop :=
  (mk s 0).Sorted (basis := basis_hd :: basis_tl)

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}

@[simp]
theorem Sorted_iff_Seq_Sorted {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    ms.Sorted ↔ Multiseries.Sorted ms.seq where
  mp h := by
    cases h with | seq _ h_coef h_Pairwise =>
    constructor
    · simpa using h_coef
    · simpa using h_Pairwise
  mpr h := by
    cases h with | seq _ h_coef h_Pairwise =>
    constructor
    · simpa using h_coef
    · simpa using h_Pairwise

namespace Multiseries

@[simp]
theorem Sorted.nil : Sorted (nil : Multiseries basis_hd basis_tl) := by
  unfold Sorted
  constructor <;> simp

/-- `[(exp, coef)]` is `Sorted` when `coef` is `Sorted`. -/
theorem Sorted.cons_nil {basis_hd basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    (h_coef : coef.Sorted) :
    Sorted (cons exp coef (.nil : Multiseries basis_hd basis_tl)) := by
  constructor
  · simpa
  · simp

theorem Sorted.cons {basis_hd basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl}
    (h_coef : coef.Sorted)
    (h_comp : leadingExp tl < exp)
    (h_tl : tl.Sorted) :
    Sorted (cons exp coef tl) := by
  cases h_tl with | seq _ h_tl_coef h_tl_tl =>
  constructor
  · simp at h_tl_coef ⊢
    grind
  · cases tl
    · exact Seq.Pairwise_cons_nil
    apply Seq.Pairwise.cons_cons_of_trans _ h_tl_tl
    simpa [lt_iff_lt] using h_comp

/-- The fact `Sorted (cons (exp, coef) tl)` implies that `coef` and `tl` are `Sorted`, and
leading exponent of `tl` is less than `exp`. -/
theorem Sorted_cons {basis_hd basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} (h : Sorted (cons exp coef tl)) :
    coef.Sorted ∧ leadingExp tl < exp ∧ tl.Sorted := by
  cases h with | seq _ h_coef h_Pairwise =>
  constructor
  · specialize h_coef (exp, coef) (by simp)
    simpa using h_coef
  cases tl with
  | nil =>
    simp
  | cons tl_exp tl_coef tl_tl =>
  obtain ⟨h_all, h_Pairwise⟩ := Seq.Pairwise.cons_elim h_Pairwise
  constructor
  · simp only [leadingExp_cons, WithBot.coe_lt_coe]
    apply h_all (tl_exp, tl_coef) (by simp [cons])
  constructor
  · intro x hx
    apply h_coef
    simp at hx ⊢
    grind
  · assumption

theorem Sorted.tail {ms : Multiseries basis_hd basis_tl} (h : ms.Sorted) :
    ms.tail.Sorted := by
  cases ms with
  | nil => simp
  | cons exp coef tl => simpa using (Sorted_cons h).right.right

/-- Coinduction principle for proving `Sorted`. For some predicate `motive` on multiseries,
if `motive ms` (base case) and the predicate "survives" destruction of its argument, then `ms` is
`Sorted`. Here "survive" means that if `x = cons (exp, coef) tl` than `motive x` must imply
`coef.Sorted`, `tl.leadingExp < exp` and `motive tl`. -/
theorem Sorted.coind {s : Multiseries basis_hd basis_tl}
    (motive : (ms : Multiseries basis_hd basis_tl) → Prop)
    (h_base : motive s)
    (h_step : ∀ exp coef tl, motive (.cons exp coef tl) →
        coef.Sorted ∧
        leadingExp tl < exp ∧
        motive tl) :
    s.Sorted := by
  constructor
  · apply Seq.all_coind
    · exact h_base
    · intro (exp, coef) tl h
      specialize h_step exp coef tl h
      grind
  · apply Seq.Pairwise.coind_trans
    · exact h_base
    · intro (exp, coef) tl h
      constructor
      · intro (tl_exp, tl_coef) h_tl
        simp only [gt_iff_lt]
        change tl_exp < exp
        replace h_step := (h_step exp coef tl h).right.left
        cases tl <;> simp [leadingExp, head] at h_tl h_step; grind
      · specialize h_step exp coef tl h
        grind

/-- A predicate that says that a function `op` preserves well-orderedness of multiseries. -/
abbrev PreservesSorted {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl) : Prop :=
  ∀ x, x.Sorted → (op x).Sorted

theorem PreservesSorted.comp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {op op' : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h_preserves : PreservesSorted op) (h_preserves' : PreservesSorted op') :
    PreservesSorted (op ∘ op') := by
  simp [PreservesSorted] at *
  grind

theorem Sorted.coind_friend {ms : Multiseries basis_hd basis_tl}
    (motive : (ms : Multiseries basis_hd basis_tl) → Prop)
    (h_base : motive ms)
    (h_step : ∀ exp coef tl, motive (.cons exp coef tl) →
        coef.Sorted ∧
        tl.leadingExp < exp ∧
        ∃ (op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl)
        (x : Multiseries basis_hd basis_tl), tl = op x ∧
        FriendlyOperation op ∧ PreservesSorted op ∧ motive x) :
    ms.Sorted := by
  let motive' (ms : Multiseries basis_hd basis_tl) : Prop :=
    ∃ (op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl)
      (x : Multiseries basis_hd basis_tl), ms = op x ∧ FriendlyOperation op ∧
      PreservesSorted op ∧ motive x
  apply Sorted.coind motive'
  · use id, ms
    simp [h_base, FriendlyOperation.id, PreservesSorted]
  intro exp coef tl ⟨op, x, h_eq, h_friend, h_preserves, hx⟩
  cases x with
  | nil =>
    have : Sorted (.cons exp coef tl) := by
      rw [h_eq]
      apply h_preserves
      apply Sorted.nil
    obtain ⟨h_coef_wo, h_comp, h_tl⟩ := Sorted_cons this
    exact ⟨h_coef_wo, h_comp, fun _ ↦ tl, .nil, rfl, FriendlyOperation.const,
      fun _ _ ↦ h_tl, hx⟩
  | cons x_exp x_coef x_tl =>
  obtain ⟨hx_coef, hx_comp, op', y, hx_tl, h_friend', h_preserves', hy⟩ :=
    h_step x_exp x_coef x_tl hx
  obtain ⟨x_tl', hx_tl_head, this⟩ : ∃ (x_tl' : Multiseries basis_hd basis_tl),
      x_tl.head = x_tl'.head ∧ Sorted (.cons x_exp x_coef x_tl') := by
    cases x_tl with
    | nil =>
      use .nil
      simp only [head_nil, true_and]
      apply Sorted.cons_nil hx_coef
    | cons x_tl_exp x_tl_coef x_tl_tl =>
      use .cons x_tl_exp x_tl_coef .nil
      simp only [head_cons, true_and]
      apply Sorted.cons hx_coef
      · simpa using hx_comp
      apply Sorted.cons_nil
      cases y with
      | nil =>
        have : Sorted (.cons x_tl_exp x_tl_coef x_tl_tl) := by
          rw [hx_tl]
          apply h_preserves'
          apply Sorted.nil
        obtain ⟨h_coef_wo, h_comp, h_tl⟩ := Sorted_cons this
        assumption
      | cons y_exp y_coef y_tl =>
        have : Sorted (basis_hd := basis_hd) (.cons y_exp y_coef .nil) := by
          apply Sorted.cons_nil
          grind
        apply h_preserves' at this
        obtain ⟨T, hT⟩ := FriendlyOperation.destruct h_friend'
        have h1 := hT (.cons y_exp y_coef .nil)
        have h2 := hT (.cons y_exp y_coef y_tl)
        simp only [tail_cons, head_cons] at h1 h2
        cases hT_head : T (some (y_exp, y_coef)) with
        | none =>
          simp [hT_head, ← hx_tl] at h2
        | some v =>
        obtain ⟨z_exp, z_coef, op'', h_friend''⟩ := v
        simp only [hT_head, Option.map_some, ← hx_tl, destruct_cons, Option.some.injEq,
          Prod.mk.injEq] at h1 h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        apply destruct_eq_cons at h1
        rw [h1] at this
        obtain ⟨h_coef_wo, h_comp, h_tl⟩ := Sorted_cons this
        assumption
  apply h_preserves at this
  obtain ⟨T, hT⟩ := FriendlyOperation.destruct h_friend
  have h1 := hT (.cons x_exp x_coef x_tl')
  have h2 := hT (.cons x_exp x_coef x_tl)
  simp only [tail_cons, head_cons] at h1 h2
  cases hT_head : T (some (x_exp, x_coef)) with
  | none => simp [← h_eq, hT_head] at h2
  | some v =>
  obtain ⟨exp', coef', op'', h_friend''⟩ := v
  simp only [hT_head, Option.map_some, ← h_eq, destruct_cons, Option.some.injEq,
    Prod.mk.injEq] at h1 h2
  obtain ⟨rfl, rfl, h_tl_eq⟩ := h2
  apply destruct_eq_cons at h1
  rw [h1] at this
  obtain ⟨h_coef_wo, h_comp, h_tl⟩ := Sorted_cons this
  refine ⟨h_coef_wo, ?_, ?_⟩
  · simpa [h_tl_eq, leadingExp, FriendlyOperation.head_eq_head h_friend'' hx_tl_head] using h_comp
  simp only [motive']
  use (fun z ↦ if (op' z).leadingExp < x_exp then
    (op (.cons x_exp x_coef (op' z))).tail else .nil), y
  constructorm* _ ∧ _
  · simp [← hx_tl, ← h_eq, hx_comp]
  · change FriendlyOperation ((fun z ↦ if z.leadingExp < (x_exp : WithBot ℝ) then
      (op (.cons x_exp x_coef z)).tail else .nil) ∘ op')
    apply FriendlyOperation.comp _ h_friend'
    simp only [leadingExp]
    let P (hd : Option (ℝ × MultiseriesExpansion basis_tl)) : Prop :=
      (match hd with | none => ⊥ | some (exp, _) => exp) < (x_exp : WithBot ℝ)
    apply FriendlyOperation.ite (P := P)
    · apply FriendlyOperation.cons_tail h_friend
    · apply FriendlyOperation.const
  · intro z hz
    dsimp
    split_ifs with h_if
    · apply Sorted.tail
      apply h_preserves
      apply Sorted.cons hx_coef h_if (h_preserves' z hz)
    · apply Sorted.nil
  · exact hy

theorem Sorted.coind_friend' {ms : Multiseries basis_hd basis_tl}
    {γ : Type*} (op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl)
    [FriendlyOperationClass op]
    (motive : (ms : Multiseries basis_hd basis_tl) → Prop)
    (C : γ → Prop)
    (h_op : ∀ c x, C c → x.Sorted → (op c x).Sorted)
    (h_base : motive ms)
    (h_step : ∀ exp coef tl, motive (.cons exp coef tl) →
        coef.Sorted ∧
        tl.leadingExp < exp ∧
        ∃ c x, tl = op c x ∧ C c ∧ motive x) :
    ms.Sorted := by
  apply Sorted.coind_friend motive h_base
  intro exp coef tl ih
  specialize h_step exp coef tl ih
  obtain ⟨h_coef_wo, h_comp, c, x, h_tl, h_C, hx⟩ := h_step
  refine ⟨h_coef_wo, h_comp, op c, x, h_tl, FriendlyOperationClass.FriendlyOperation _,
    by grind, hx⟩

end Multiseries

/-- `[]` is `Sorted`. -/
theorem Sorted.nil (f : ℝ → ℝ) : @Sorted (basis_hd :: basis_tl) (mk .nil f) := by
  simp

/-- `[(exp, coef)]` is `Sorted` when `coef` is `Sorted`. -/
theorem Sorted.cons_nil {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {f : ℝ → ℝ}
    (h_coef : coef.Sorted) :
    @Sorted (basis_hd :: basis_tl) (mk (.cons exp coef .nil) f) := by
  simp [Multiseries.Sorted.cons_nil h_coef]

/-- `cons (exp, coef) tl` is `Sorted` when `coef` and `tl` are `Sorted` and leading
exponent of `tl` is less than `exp`. -/
theorem Sorted.cons {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl}
    {f : ℝ → ℝ}
    (h_coef : coef.Sorted)
    (h_comp : tl.leadingExp < exp)
    (h_tl : tl.Sorted) :
    @Sorted (basis_hd :: basis_tl) (mk (.cons exp coef tl) f) := by
  simp [Multiseries.Sorted.cons h_coef h_comp h_tl]

/-- The fact `Sorted (cons (exp, coef) tl)` implies that `coef` and `tl` are `Sorted`, and
leading exponent of `tl` is less than `exp`. -/
theorem Sorted_cons {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ}
    (h : @Sorted (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) :
    coef.Sorted ∧ tl.leadingExp < exp ∧ tl.Sorted := by
  apply Multiseries.Sorted_cons (by simpa using h)

end Sorted

section Approximates

section Majorated

/-- `Majorated f g exp` for real functions `f` and `g` means that for any `exp' < exp`,
`f =o[atTop] g^exp'`. -/
def Majorated (f basis_hd : ℝ → ℝ) (exp : ℝ) : Prop :=
  ∀ exp', exp < exp' → f =o[atTop] (fun t ↦ (basis_hd t) ^ exp')

/-- One can change the argument of `Majorated` with the function that eventually equals to it. -/
theorem Majorated_of_EventuallyEq {f g basis_hd : ℝ → ℝ} {exp : ℝ} (h_eq : g =ᶠ[atTop] f)
    (h : Majorated f basis_hd exp) : Majorated g basis_hd exp := by
  simp only [Majorated] at *
  intro exp' h_exp
  specialize h exp' h_exp
  exact EventuallyEq.trans_isLittleO h_eq h

/-- For any function `f`, `f^exp` is Majorated with `f` with exponent `exp`. -/
theorem Majorated_self {f : ℝ → ℝ} {exp : ℝ}
    (h : Tendsto f atTop atTop) :
    Majorated (fun t ↦ (f t)^exp) f exp := by
  simp only [Majorated]
  intro exp' h_exp
  apply (isLittleO_iff_tendsto' _).mpr
  · have : (fun t ↦ f t ^ exp / f t ^ exp') =ᶠ[atTop] fun t ↦ (f t)^(exp - exp') := by
      apply (Tendsto.eventually_gt_atTop h 0).mono
      intro t h
      simp only [← Real.rpow_sub h]
    apply Tendsto.congr' this.symm
    conv =>
      arg 1
      rw [show (fun t ↦ f t ^ (exp - exp')) = ((fun t ↦ t^(-(exp' - exp))) ∘ f) by ext; simp]
    apply Tendsto.comp _ h
    apply tendsto_rpow_neg_atTop
    linarith
  · apply (Tendsto.eventually_gt_atTop h 0).mono
    intro t h1 h2
    absurd h2
    exact (Real.rpow_pos_of_pos h1 _).ne.symm

/-- If one can Majorate `f` with `exp1`, then it can be Majorated with any `exp2 > exp1`. -/
theorem Majorated_of_le {f basis_hd : ℝ → ℝ} {exp1 exp2 : ℝ}
    (h_lt : exp1 ≤ exp2) (h : Majorated f basis_hd exp1) :
    Majorated f basis_hd exp2 := by
  simp only [Majorated] at *
  intro exp' h_exp
  apply h _ (by linarith)

/-- If `f` is Majorated with negative exponent, then it tends to zero. -/
theorem Majorated_tendsto_zero_of_neg {f basis_hd : ℝ → ℝ} {exp : ℝ}
    (h_lt : exp < 0) (h : Majorated f basis_hd exp) :
    Tendsto f atTop (𝓝 0) := by
  simp only [Majorated] at h
  specialize h 0 (by linarith)
  simpa using h

/-- Constants can be Majorated with `exp = 0`. -/
theorem const_Majorated {basis_hd : ℝ → ℝ} (h_tendsto : Tendsto basis_hd atTop atTop)
    {c : ℝ} : Majorated (fun _ ↦ c) basis_hd 0 := by
  intro exp h_exp
  apply Asymptotics.isLittleO_const_left.mpr
  right
  apply Tendsto.comp tendsto_norm_atTop_atTop
  apply Tendsto.comp (tendsto_rpow_atTop h_exp)
  exact h_tendsto

/-- Zero can be Majorated with any exponent. -/
theorem zero_Majorated {basis_hd : ℝ → ℝ} {exp : ℝ} : Majorated (fun _ ↦ 0) basis_hd exp := by
  intro exp h_exp
  apply Asymptotics.isLittleO_zero

/-- `f * c` can be Majorated with the same exponent as `f` for any constant `c`. -/
theorem smul_Majorated {f basis_hd : ℝ → ℝ} {exp : ℝ} (h : Majorated f basis_hd exp)
    {c : ℝ} : Majorated (c • f) basis_hd exp := by
  intro exp h_exp
  apply IsLittleO.const_mul_left (h exp h_exp)

/-- Sum of two function, that can be Majorated with exponents `f_exp` and `g_exp`, can be
Majorated with exponent `f_exp ⊔ g_exp`. -/
theorem add_Majorated {f g basis_hd : ℝ → ℝ} {f_exp g_exp : ℝ} (hf : Majorated f basis_hd f_exp)
    (hg : Majorated g basis_hd g_exp) : Majorated (f + g) basis_hd (f_exp ⊔ g_exp) := by
  simp only [Majorated] at *
  intro exp h_exp
  simp only [sup_lt_iff] at h_exp
  apply IsLittleO.add
  · exact hf _ h_exp.left
  · exact hg _ h_exp.right

theorem add_Majorated' {f g basis_hd : ℝ → ℝ} {exp f_exp g_exp : ℝ}
    (hf : Majorated f basis_hd f_exp)
    (hg : Majorated g basis_hd g_exp) (hf_exp : f_exp ≤ exp) (hg_exp : g_exp ≤ exp) :
    Majorated (f + g) basis_hd exp := by
  apply Majorated_of_le _ (add_Majorated hf hg)
  simp [hf_exp, hg_exp]

/-- Product of two function, that can be Majorated with exponents `f_exp` and `g_exp`, can be
Majorated with exponent `f_exp + g_exp`. -/
theorem mul_Majorated {f g basis_hd : ℝ → ℝ} {f_exp g_exp : ℝ} (hf : Majorated f basis_hd f_exp)
    (hg : Majorated g basis_hd g_exp) (h_pos : ∀ᶠ t in atTop, 0 < basis_hd t) :
    Majorated (f * g) basis_hd (f_exp + g_exp) := by
  simp only [Majorated] at *
  intro exp h_exp
  let ε := (exp - f_exp - g_exp) / 2
  specialize hf (f_exp + ε) (by dsimp [ε]; linarith)
  specialize hg (g_exp + ε) (by dsimp [ε]; linarith)
  apply IsLittleO.trans_eventuallyEq
    (g₁ := fun t ↦ basis_hd t ^ (f_exp + ε) * basis_hd t ^ (g_exp + ε))
  · exact IsLittleO.mul hf hg
  · simp only [EventuallyEq]
    apply h_pos.mono
    intro t hx
    conv =>
      rhs
      rw [show exp = (f_exp + ε) + (g_exp + ε) by dsimp [ε]; ring_nf]
      rw [Real.rpow_add hx]

theorem mul_bounded_Majorated {f g basis_hd : ℝ → ℝ} {exp : ℝ} (hf : Majorated f basis_hd exp)
    (hg : g =O[atTop] (fun _ ↦ (1 : ℝ))) :
    Majorated (f * g) basis_hd exp := by
  intro exp h_exp
  convert IsLittleO.mul_isBigO (hf _ h_exp) hg using 1
  simp

end Majorated

mutual
  /-- Auxilliary monotone map, for which `Approximates` is the greatest fixed point. -/
  def Approximates.T (basis : Basis) : (MultiseriesExpansion basis → Prop) →o
      (MultiseriesExpansion basis → Prop) :=
    match (generalizing := true) basis with
    | [] => {
      toFun := fun P ms => True
      monotone' := monotone_const
    }
    | .cons basis_hd basis_tl => {
      toFun := fun P ms =>
        (ms.seq = .nil ∧ ms.toFun =ᶠ[atTop] 0) ∨
        (∃ (exp : ℝ) (coef : MultiseriesExpansion basis_tl) (tl : Multiseries basis_hd basis_tl),
          ms.seq = .cons exp coef tl ∧ coef.Approximates ∧
          Majorated ms.toFun basis_hd exp ∧
          P (mk tl (ms.toFun - basis_hd ^ exp * coef.toFun)))
      monotone' P Q hPQ ms hP := by
        change ∀ ms, P ms → Q ms at hPQ
        generalize Approximates = A at *
        grind
    }

  /-- Coinductive predicate stating that `ms` approximates `f` on `basis`. This means that
  * If `basis = []`, i.e. ms is just a real number, then `f =ᶠ[atTop] ms`.
  * If `basis ≠ []`, and `ms = nil`, then `f =ᶠ[atTop] 0`.
  * If `basis = basis_hd :: basis_tl`, and `ms = cons (exp, coef) tl`, then
    `f` is Majorated with exponent `exp` by `basis_hd`,
    `coef` approximates some function `fC`, and
    `tl` approximates `f - fC * basis_hd ^ exp`
  -/
  def Approximates {basis} (ms : MultiseriesExpansion basis) : Prop :=
    (Approximates.T basis).gfp ms
end

variable {f basis_hd : ℝ → ℝ} {basis_tl : Basis}

private theorem Approximates.step {basis} {ms : MultiseriesExpansion basis} :
    ms.Approximates ↔ Approximates.T basis Approximates ms := by
  conv_lhs => unfold Approximates; rw [← OrderHom.isFixedPt_gfp]
  conv_rhs => arg 2; eta_expand; unfold Approximates; change OrderHom.gfp _

@[simp]
theorem Approximates.const {c : MultiseriesExpansion []} : Approximates c := by
  rw [Approximates.step]
  simp [T]

/-- `[]` approximates zero function. -/
theorem Approximates.nil (h : f =ᶠ[atTop] 0) :
    @Approximates (basis_hd :: basis_tl) (mk .nil f) := by
  rw [Approximates.step]
  simpa [T]

/-- `cons (exp, coef) tl` approximates `f` when `f` can be Majorated with exponent `exp`, and
there exists some function `fC` such that `coef` approximates `fC` and `tl` approximates
`f - fC * basis_hd ^ exp`. -/
theorem Approximates.cons {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl}
    (h_coef : coef.Approximates)
    (h_maj : Majorated f basis_hd exp)
    (h_tl : (mk (basis_hd := basis_hd) tl (f - basis_hd ^ exp * coef.toFun)).Approximates) :
    @Approximates (basis_hd :: basis_tl) (mk (.cons exp coef tl) f) := by
  rw [Approximates.step]
  simp [T]
  grind

theorem Approximates.coind {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    (motive : MultiseriesExpansion (basis_hd :: basis_tl) → Prop)
    (h_base : motive ms)
    (h_step : ∀ ms, motive ms →
      (ms.seq = .nil ∧ ms.toFun =ᶠ[atTop] 0) ∨
      (∃ exp coef tl, ms.seq = .cons exp coef tl ∧
        coef.Approximates ∧
        Majorated ms.toFun basis_hd exp ∧
        motive (mk (basis_hd := basis_hd) tl (ms.toFun - basis_hd ^ exp * coef.toFun)))) :
    ms.Approximates := by
  have : motive ≤ T _ motive := by
    intro ms h
    simp [T]
    grind
  have := OrderHom.le_gfp _ this
  unfold Approximates
  aesop

/-- If `[]` approximates `f`, then `f = 0` eventually. -/
theorem Approximates_nil (h : @Approximates (basis_hd :: basis_tl) (mk .nil f)) :
    f =ᶠ[atTop] 0 := by
  rw [Approximates.step] at h
  simpa [Approximates.T] using h

@[simp]
theorem Approximates_nil_iff {f : ℝ → ℝ} :
    (mk (basis_hd := basis_hd) (basis_tl := basis_tl) .nil f).Approximates ↔ f =ᶠ[atTop] 0 where
  mp h := Approximates_nil h
  mpr h := Approximates.nil h

/-- If `cons (exp, coef) tl` approximates `f`, then `f` can be Majorated with exponent `exp`, and
there exists function `fC` such that `coef` approximates `fC` and `tl` approximates
`f - fC * basis_hd ^ exp`. -/
theorem Approximates_cons {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : Approximates (basis := basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) :
    coef.Approximates ∧
    Majorated f basis_hd exp ∧
    (mk (basis_hd := basis_hd) tl (f - basis_hd ^ exp * coef.toFun)).Approximates := by
  rw [Approximates.step] at h
  simpa [Approximates.T] using h

theorem replaceFun_Sorted {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    {f : ℝ → ℝ} (h_wo : ms.Sorted) :
    (ms.replaceFun f).Sorted := by
  simpa using h_wo

/-- One can replace `f` in `Approximates` with the funcion that eventually equals `f`. -/
theorem replaceFun_Approximates {ms : MultiseriesExpansion (basis_hd :: basis_tl)} {f : ℝ → ℝ}
    (h_equiv : ms.toFun =ᶠ[atTop] f) (h_approx : ms.Approximates) :
    (ms.replaceFun f).Approximates := by
  let motive (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : Prop :=
      ∃ (ms' : MultiseriesExpansion (basis_hd :: basis_tl)) (f' : ℝ → ℝ),
      ms = ms'.replaceFun f' ∧ ms'.Approximates ∧ ms'.toFun =ᶠ[atTop] f'
  apply Approximates.coind motive
  · simp only [motive]
    use ms, f
  rintro _ ⟨ms, f, rfl, h_approx, h_eq⟩
  cases ms with
  | nil g =>
    simp only [Approximates_nil_iff, mk_toFun, mk_replaceFun, mk_seq, true_and,
      Multiseries.nil_ne_cons, false_and, exists_const, or_false] at h_approx h_eq ⊢
    grw [← h_eq, h_approx]
  | cons exp coef tl g =>
    right
    obtain ⟨h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
    use exp, coef, tl
    simp only [mk_replaceFun, mk_seq, h_coef, mk_toFun, true_and]
    simp only [mk_toFun] at h_eq
    constructor
    · exact Majorated_of_EventuallyEq h_eq.symm h_maj
    refine ⟨mk tl (g - basis_hd ^ exp * coef.toFun), _, rfl, h_tl, ?_⟩
    simp only [mk_toFun]
    grw [h_eq]

instance (basis_hd : ℝ → ℝ) (basis_tl : Basis) :
    Setoid (MultiseriesExpansion (basis_hd :: basis_tl)) where
  r x y := x.seq = y.seq ∧ x.toFun =ᶠ[atTop] y.toFun
  iseqv := by
    constructor
    · simp
    · grind [EventuallyEq.symm]
    · grind [EventuallyEq.trans]

@[simp]
theorem equiv_def {x y : MultiseriesExpansion (basis_hd :: basis_tl)} :
    x ≈ y ↔ x.seq = y.seq ∧ x.toFun =ᶠ[atTop] y.toFun := by
  rfl

end Approximates

end MultiseriesExpansion

end Tactic.ComputeAsymptotics
