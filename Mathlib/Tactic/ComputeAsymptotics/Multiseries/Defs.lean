/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.Seq.Basic
public import Mathlib.Data.Real.Basic

/-!

# Multiseries definitions

In this file, we define the multiseries and its main properties: sortedness and approximation.
A multiseries in a basis `[b₁, ..., bₙ]` represents a multivariate series:
it is a formal series made from monomials `b₁ ^ e₁ * ... * bₙ ^ eₙ` where `e₁, ..., eₙ` are real
numbers. We treat multivariate series in a basis `[b₁, ..., bₙ]` as a univariate series in the
variable `b₁` (`basis_hd`) with coefficients being multiseries
in the basis `[b₂, ..., bₙ]` (`basis_tl`).

## Main definitions

* `Basis` is the list of functions used to construct monomials in multiseries.
* `Multiseries basis_hd basis_tl` is the type of multiseries in a basis `basis_hd :: basis_tl`.
* `MultiseriesExpansion basis` is a multiseries expansion of some function `f : ℝ → ℝ`.
  If `basis = []`, then the multiseries represents a constant function, otherwise it is
  a pair of a multiseries `ms : Multiseries basis_hd basis_tl` and a function `f : ℝ → ℝ`.

## Implementation details

* `Multiseries basis_hd basis_tl` is defined as a `Seq (ℝ × MultiseriesExpansion basis_tl)`, so
  we need to port some `Seq` API to `Multiseries`.

-/

@[expose] public section

namespace ComputeAsymptotics

open Stream'

/-- List of functions used to construct monomials in multiseries. -/
abbrev Basis := List (ℝ → ℝ)

/-- Multiseries representing a given function `f : ℝ → ℝ`.
`MultiseriesExpansion []` is just `ℝ`: multiseries representing constant functions.
Otherwise it is a pair of a `Multiseries basis_hd basis_tl` and a function `ℝ → ℝ`. We call
the former an expansion of the latter.

Note: most of the theory can be formulated in terms of `Multiseries`, but we need to explicitly
store the approximated function to be able to use the eventual zeroness oracle at the trimming step.
-/
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
coefficient (a multiseries in `basis_tl`).

`MultiseriesExpansion` is a `Multiseries` with an attached real function.
-/
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
    motive ms := Stream'.Seq.recOn _ nil fun _ _ ↦ cons _ _ _

/-- Destruct a multiseries into a triple `(exp, coef, tl)`, where `exp` is the leading exponent,
`coef` is the leading coefficient, and `tl` is the tail. -/
def destruct {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Option (ℝ × MultiseriesExpansion basis_tl × Multiseries basis_hd basis_tl) :=
  (Seq.destruct ms).map (fun ((exp, coef), tl) => (exp, coef, tl))

/-- The head of a multiseries, i.e. the first two entries of the tuple returned by `destruct`. -/
def head {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Option (ℝ × MultiseriesExpansion basis_tl) :=
  Seq.head ms

/-- The tail of a multiseries, i.e. the last entry of the tuple returned by `destruct`. -/
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

private lemma destruct_eq_destruct_map {basis_hd basis_tl}
    (s : Stream'.Seq (ℝ × MultiseriesExpansion basis_tl)) :
    s.destruct = (Multiseries.destruct (basis_hd := basis_hd) s).map
      (fun (exp, coef, tl) => ((exp, coef), tl)) := by
  simp only [destruct, Option.map_map]
  exact Option.map_id_apply.symm

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

/-- Convert a real number to a multiseries in an empty basis. -/
def ofReal (c : ℝ) : MultiseriesExpansion [] := c

/-- Convert a multiseries in an empty basis to a real number. -/
def toReal (ms : MultiseriesExpansion []) : ℝ := ms

/-- Convert a multiseries in a non-empty basis to a sequence of pairs `(exp, coef)`. -/
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

theorem ext_iff {basis_hd basis_tl}
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

end MultiseriesExpansion

end ComputeAsymptotics
