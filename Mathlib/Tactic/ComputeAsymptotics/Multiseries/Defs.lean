/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Corecursion

/-!
# Main definitions

* `PreMS basis` is the type of lazy formal multiseries, where `basis` is the list of basis
functions. It is defined recursively as `PreMS [] = ℝ` (constants), and
`PreMS (b₁ :: tl) = Seq (ℝ × PreMS tl)`. This is lazy possibly infinite list of pairs, where each
pair `(exp, coef)` represents the monomial `b₁ ^ exp * coef`. The type is isomorphic to the type
of trees of finite fixed depth with possibly infinite branching and `ℝ`-valued labels in vertexes.
* `WellOrdered ms` is the predicate meaning that at each level of `ms` as a nested tree all
exponents are Pairwise by TODO (убывание).
* `Approximates ms f` is the predicate meaning that the multiseries `ms` can be used to obtain
an asymptotical approximations of the real function `f`.
For details see the docs for `Approximates`.

# Definition used inside the theory
* `leadingExp ms` is the value of leading exponent of `ms`. Is `ms = []` then it is `⊥`.

-/

@[expose] public section

namespace ComputeAsymptotics

open Filter Asymptotics Topology Stream'

/-- List of functions used to construct monomials in multiseries. -/
abbrev Basis := List (ℝ → ℝ)

/-- TODO -/
def PreMS (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | .cons _ tl => Seq (ℝ × PreMS tl) × (ℝ → ℝ)

namespace PreMS

set_option linter.unusedVariables false in
def SeqMS (basis_hd : ℝ → ℝ) (basis_tl : Basis) : Type := Seq (ℝ × PreMS basis_tl)

namespace SeqMS

def toSeq {basis_hd basis_tl} (ms : SeqMS basis_hd basis_tl) : Seq (ℝ × PreMS basis_tl) :=
  ms

/-- The empty multiseries. -/
def nil {basis_hd basis_tl} : SeqMS basis_hd basis_tl := Seq.nil

/-- Prepend a monomial to a multiseries. -/
def cons {basis_hd basis_tl} (exp : ℝ) (coef : PreMS basis_tl)
    (tl : SeqMS basis_hd basis_tl) :
    SeqMS basis_hd basis_tl :=
  Seq.cons (exp, coef) tl

/-- Recursion principle for multiseries with non-empty basis. It is equivalent to
`Stream'.Seq.recOn` but provides some convenience. For example one can write
`cases' ms with exp coef tl` while cannot `cases' ms with (exp, coef) tl` (`cases` tactic does
not support argument deconstruction). -/
@[cases_eliminator]
def recOn {basis_hd basis_tl} {motive : SeqMS basis_hd basis_tl → Sort*}
    (ms : SeqMS basis_hd basis_tl) (nil : motive nil)
    (cons : ∀ exp coef (tl : SeqMS basis_hd basis_tl), motive (cons exp coef tl)) :
    motive ms := by
  cases ms using Stream'.Seq.recOn with
  | nil => apply nil
  | cons hd tl => apply cons

/-- Destruct a multiseries into a triple `(exp, coef, tl)`, where `exp` is leading exponent,
`coef` is leading coefficient, and `tl` is tail. -/
def destruct {basis_hd basis_tl} (ms : SeqMS basis_hd basis_tl) :
    Option (ℝ × PreMS basis_tl × SeqMS basis_hd basis_tl) :=
  (Seq.destruct ms).map (fun ((exp, coef), tl) => (exp, coef, tl))

/-- The head of a multiseries, i.e. the first two elements of `destruct`. -/
def head {basis_hd basis_tl} (ms : SeqMS basis_hd basis_tl) : Option (ℝ × PreMS basis_tl) :=
  Seq.head ms

/-- The tail of a multiseries, i.e. the last element of `destruct`. -/
def tail {basis_hd basis_tl} (ms : SeqMS basis_hd basis_tl) : SeqMS basis_hd basis_tl :=
  Seq.tail ms

/-- Given two functions `f : ℝ → ℝ` and `g : PreMS basis_tl → PreMS basis_tl'`, apply them to
exponents and coefficients of a multiseries. -/
def map {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → ℝ)
    (g : PreMS basis_tl → PreMS basis_tl')
    (ms : SeqMS basis_hd basis_tl) :
    SeqMS basis_hd' basis_tl' :=
  Seq.map (fun (exp, coef) ↦ (f exp, g coef)) ms

/-- Corecursor for `SeqMS basis_hd basis_tl`. -/
def corec {β : Type*} {basis_hd} {basis_tl} (f : β → Option (ℝ × PreMS basis_tl × β)) (b : β) :
    SeqMS basis_hd basis_tl :=
  Seq.corec (fun a => (f a).map (fun (exp, coef, next) => ((exp, coef), next))) b

/-- An operation on multiseries called a "friend" if any `n`-prefix of its output depends only on
the `n`-prefix of the input. Such operations can be used in the tail of (non-primitive) corecursive
definitions. -/
def FriendOperation {basis_hd basis_tl}
    (op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl) : Prop :=
  Stream'.Seq.FriendOperation op

/-- A family of friendly operations on multiseries indexed by a type `γ`. -/
class FriendOperationClass {basis_hd basis_tl} {γ : Type*}
    (op : γ → SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl) : Prop
    extends Stream'.Seq.FriendOperationClass op

theorem FriendOperationClass.mk' {basis_hd basis_tl} {γ : Type*}
    {op : γ → SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    (h : ∀ c, FriendOperation (op c)) :
    FriendOperationClass op := by
  suffices Stream'.Seq.FriendOperationClass op by constructor
  exact ⟨h⟩

private lemma destruct_eq_destruct_map {basis_hd basis_tl} (s : Stream'.Seq (ℝ × PreMS basis_tl)) :
    s.destruct = (SeqMS.destruct (basis_hd := basis_hd) s).map
      (fun (exp, coef, tl) => ((exp, coef), tl)) := by
  simp only [destruct, Option.map_map]
  exact Option.map_id_apply.symm

theorem FriendOperation.coind_comp_friend_left {basis_hd basis_tl}
    {op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    (motive : (SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl) → Prop)
    (h_base : motive op)
    (h_step : ∀ op, motive op → ∃ T : Option (ℝ × PreMS basis_tl) →
        Option (ℝ × PreMS basis_tl × Subtype FriendOperation × Subtype motive),
      ∀ s, (op s).destruct =
        (T s.head).map (fun (exp, coef, opf, op') => (exp, coef, opf.val <| op'.val (s.tail)))) :
    FriendOperation op := by
  apply Stream'.Seq.FriendOperation.coind_comp_friend_left motive h_base
  intro op h_op
  specialize h_step op h_op
  obtain ⟨T, hT⟩ := h_step
  use fun hd? ↦ (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  specialize hT s
  rw [destruct_eq_destruct_map, hT]
  simp [head]
  rfl

theorem FriendOperation.coind_comp_friend_right {basis_hd basis_tl}
    {op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    (motive : (SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl) → Prop)
    (h_base : motive op)
    (h_step : ∀ op, motive op → ∃ T : Option (ℝ × PreMS basis_tl) →
        Option (ℝ × PreMS basis_tl × Subtype FriendOperation × Subtype motive),
      ∀ s, (op s).destruct =
        (T s.head).map (fun (exp, coef, opf, op') => (exp, coef, op'.val <| opf.val (s.tail)))) :
    FriendOperation op := by
  apply Stream'.Seq.FriendOperation.coind_comp_friend_right motive h_base
  intro op h_op
  specialize h_step op h_op
  obtain ⟨T, hT⟩ := h_step
  use fun hd? ↦ (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  specialize hT s
  rw [destruct_eq_destruct_map, hT]
  simp [Seq.head]
  rfl

/-- Non-primitive corecursor for `SeqMS basis_hd basis_tl` allowing to use a friendly operation
in the tail of the corecursive definition. -/
noncomputable def gcorec {β γ : Type*} {basis_hd} {basis_tl}
    (F : β → Option (ℝ × PreMS basis_tl × γ × β))
    (op : γ → SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl)
    [FriendOperationClass op]
    (b : β) :
    SeqMS basis_hd basis_tl :=
  Stream'.Seq.gcorec (fun a => (F a).map (fun (exp, coef, c, next) => ((exp, coef), c, next))) op b


instance (basis_hd basis_tl) : Inhabited (SeqMS basis_hd basis_tl) where
  default := (default : Seq (ℝ × PreMS basis_tl))

instance {basis_hd basis_tl} : Membership (ℝ × PreMS basis_tl) (SeqMS basis_hd basis_tl) where
  mem ms x := x ∈ ms.toSeq

theorem eq_of_bisim {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x y : SeqMS basis_hd basis_tl}
    (motive : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = .nil ∧ y = .nil) ∨ ∃ exp coef,
      ∃ (x' y' : SeqMS basis_hd basis_tl),
      x = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') :
    x = y := Seq.eq_of_bisim' motive base (by grind [nil, cons])

theorem eq_of_bisim_strong {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {x y : SeqMS basis_hd basis_tl}
    (motive : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = y) ∨ ∃ exp coef,
      ∃ (x' y' : SeqMS basis_hd basis_tl),
      x = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') :
    x = y := Seq.eq_of_bisim_strong motive base (by grind [nil, cons])

theorem FriendOperationClass.FriendOperation {basis_hd basis_tl} {γ : Type*}
    {op : γ → SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    [h : FriendOperationClass op]
    (c : γ) :
    FriendOperation (op c) :=
  h.friend c

theorem FriendOperation.destruct {basis_hd basis_tl}
    {op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    (h : FriendOperation op) :
    ∃ T : Option (ℝ × PreMS basis_tl) → Option (ℝ × PreMS basis_tl × Subtype FriendOperation),
      ∀ ms, destruct (op ms) = (T ms.head).map
        (fun (exp, coef, op') ↦ (exp, coef, op'.val ms.tail)) := by
  have h' := Stream'.Seq.FriendOperation.destruct h
  obtain ⟨T, hT⟩ := h'
  use fun hd? ↦ (T hd?).map (fun ((exp, coef), op') ↦ (exp, coef, op'))
  intro ms
  specialize hT ms
  unfold SeqMS.destruct
  simp [hT]
  simp [head, tail]
  cases T (Seq.head ms) <;> simp

theorem FriendOperation.head_eq_head {basis_hd basis_tl}
    {op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    (h : FriendOperation op) {x y : SeqMS basis_hd basis_tl}
    (h_head : x.head = y.head) : (op x).head = (op y).head :=
  Stream'.Seq.FriendOperation.head_eq_head h h_head

-- theorem FriendOperation.head_eq_head_of_cons {basis_hd basis_tl}
--     {op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
--     (h : FriendOperation op) {exp : ℝ} {coef : PreMS basis_tl}
--     {x y : SeqMS basis_hd basis_tl} :
--     (op (cons exp coef x)).head = (op (cons exp coef y)).head :=
--   Stream'.Seq.FriendOperation.head_eq_head_of_cons h

theorem FriendOperation.id {basis_hd basis_tl} :
    FriendOperation (id : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl) :=
  Stream'.Seq.FriendOperation.id

theorem FriendOperation.comp {basis_hd basis_tl}
    {op₁ op₂ : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    (h₁ : FriendOperation op₁) (h₂ : FriendOperation op₂) :
    FriendOperation (op₁ ∘ op₂) :=
  Stream'.Seq.FriendOperation.comp h₁ h₂

theorem FriendOperation.const {basis_hd basis_tl} {s : SeqMS basis_hd basis_tl} :
    FriendOperation (fun _ ↦ s) :=
  Stream'.Seq.FriendOperation.const

theorem FriendOperation.ite {basis_hd basis_tl}
    {op₁ op₂ : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    (h₁ : FriendOperation op₁) (h₂ : FriendOperation op₂)
    {P : Option (ℝ × PreMS basis_tl) → Prop} [DecidablePred P] :
    FriendOperation (fun ms ↦ if P ms.head then op₁ ms else op₂ ms) :=
  Stream'.Seq.FriendOperation.ite h₁ h₂

theorem FriendOperation.cons {basis_hd basis_tl} (exp : ℝ) (coef : PreMS basis_tl) :
    FriendOperation (cons (basis_hd := basis_hd) exp coef) :=
  Stream'.Seq.FriendOperation.cons _

theorem FriendOperation.cons_tail {basis_hd basis_tl}
    {op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    {exp : ℝ} {coef : PreMS basis_tl}
    (h : FriendOperation op) :
    FriendOperation (fun ms ↦ (op (.cons exp coef ms)).tail) :=
  Stream'.Seq.FriendOperation.cons_tail h

theorem FriendOperationClass.comp {basis_hd basis_tl} {γ γ' : Type*}
    {g : γ' → γ}
    {op : γ → SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    [h : FriendOperationClass op] : FriendOperationClass (fun c ↦ op (g c)) := by
  have : Stream'.Seq.FriendOperationClass (fun c ↦ op (g c)) := by
    apply Stream'.Seq.FriendOperationClass.comp
  constructor

theorem eq_of_bisim_friend {γ : Type*} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {op : γ → SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    [FriendOperationClass op]
    {x y : SeqMS basis_hd basis_tl}
    (motive : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = y) ∨ ∃ exp coef,
      ∃ (c : γ) (x' y' : SeqMS basis_hd basis_tl),
      x = cons exp coef (op c x') ∧ y = cons exp coef (op c y') ∧ motive x' y') :
    x = y := by
  apply Stream'.Seq.FriendOperationClass.eq_of_bisim (op := op) motive base
  peel step with x y ih h
  obtain h | ⟨exp, coef, c, x', y', rfl, rfl, h_next⟩ := h
  · simp [h]
  right
  use (exp, coef), x', y', c
  simpa [cons]

section simp

@[simp]
theorem cons_ne_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl} :
    cons exp coef tl ≠ .nil := by
  intro h
  simp only [cons, nil] at h
  apply Seq.cons_ne_nil h

@[simp]
theorem nil_ne_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl} :
    .nil ≠ cons exp coef tl := cons_ne_nil.symm

@[simp]
theorem cons_eq_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp1 exp2 : ℝ}
    {coef1 coef2 : PreMS basis_tl} {tl1 tl2 : SeqMS basis_hd basis_tl} :
    cons exp1 coef1 tl1 = cons exp2 coef2 tl2 ↔ exp1 = exp2 ∧ coef1 = coef2 ∧ tl1 = tl2 := by
  rw [cons, cons, Seq.cons_eq_cons]
  grind

theorem corec_nil {β : Type*} {basis_hd} {basis_tl}
    {f : β → Option (ℝ × PreMS basis_tl × β)} {b : β} (h : f b = none) :
    corec f b = (nil : SeqMS basis_hd basis_tl) := by
  simp only [corec, nil]
  rw [Seq.corec_nil]
  simpa

theorem corec_cons {β : Type*} {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl} {next : β}
    {f : β → Option (ℝ × PreMS basis_tl × β)} {b : β}
    (h : f b = some (exp, coef, next)) :
    (corec f b : SeqMS basis_hd basis_tl) = cons exp coef (corec f next) := by
  simp only [corec, cons]
  rw [Seq.corec_cons]
  simpa

theorem gcorec_nil {β γ : Type*} {basis_hd} {basis_tl} {F : β → Option (ℝ × PreMS basis_tl × γ × β)}
    {op : γ → SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    [FriendOperationClass op] {b : β}
    (h : F b = none) :
    gcorec F op b = nil := by
  unfold gcorec
  rw [Stream'.Seq.gcorec_nil]
  · simp [nil]
  · simpa

theorem gcorec_some {β γ : Type*} {basis_hd} {basis_tl}
    {F : β → Option (ℝ × PreMS basis_tl × γ × β)}
    {op : γ → SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    [FriendOperationClass op] {b : β}
    {exp : ℝ} {coef : PreMS basis_tl} {c : γ} {next : β}
    (h : F b = some (exp, coef, c, next)) :
    gcorec F op b = cons exp coef (op c (gcorec F op next)) := by
  unfold gcorec
  rw [Stream'.Seq.gcorec_some]
  · simp [cons]
    rfl
  · simpa

@[simp]
theorem destruct_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    destruct (nil : SeqMS basis_hd basis_tl) = none := by
  simp [destruct, nil]

@[simp]
theorem destruct_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl} :
    destruct (cons exp coef tl) = some (exp, coef, tl) := by
  simp [destruct, cons]

theorem destruct_eq_none {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    (h : destruct ms = none) : ms = nil := by
  apply Stream'.Seq.destruct_eq_none
  simpa [destruct] using h

theorem destruct_eq_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (h : destruct ms = some (exp, coef, tl)) : ms = cons exp coef tl := by
  apply Stream'.Seq.destruct_eq_cons
  simp [destruct] at h
  grind

@[simp]
theorem head_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (nil : SeqMS basis_hd basis_tl).head = none := by
  simp [head, nil]

@[simp]
theorem head_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl} :
    (cons exp coef tl).head = some (exp, coef) := by
  simp [head, cons]

@[simp]
theorem tail_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (nil : SeqMS basis_hd basis_tl).tail = nil := by
  simp [tail, nil]

@[simp]
theorem tail_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl} :
    (cons exp coef tl).tail = tl := by
  simp [tail, cons]

@[simp]
theorem map_nil {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → ℝ)
    (g : PreMS basis_tl → PreMS basis_tl') :
    (nil : SeqMS basis_hd basis_tl).map f g = (nil : SeqMS basis_hd' basis_tl') := by
  simp [map, nil]

@[simp]
theorem map_cons {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → ℝ)
    (g : PreMS basis_tl → PreMS basis_tl') {exp : ℝ}
    {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl} :
    (cons exp coef tl).map f g = cons (basis_hd := basis_hd')
      (f exp) (g coef) (map f g tl) := by
  simp [map, cons]

@[simp]
theorem map_id {basis_hd basis_tl} (ms : SeqMS basis_hd basis_tl) :
    ms.map (fun exp => exp) (fun coef => coef) = ms :=
  Stream'.Seq.map_id ms

@[simp← ]
theorem map_comp {b₁ b₂ b₃ bs₁ bs₂ bs₃}
    (f₁ : ℝ → ℝ) (g₁ : PreMS bs₁ → PreMS bs₂)
    (f₂ : ℝ → ℝ) (g₂ : PreMS bs₂ → PreMS bs₃)
    (ms : SeqMS b₁ bs₁) :
    (ms.map (f₂ ∘ f₁) (g₂ ∘ g₁) : SeqMS b₃ bs₃) =
    (ms.map f₁ g₁ : SeqMS b₂ bs₂).map f₂ g₂ := by
  simp [map, ← Stream'.Seq.map_comp]
  rfl

@[simp]
theorem notMem_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x : ℝ × PreMS basis_tl} :
    x ∉ (nil : SeqMS basis_hd basis_tl) :=
  Seq.notMem_nil _

@[simp]
theorem mem_cons_iff {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl} {x : ℝ × PreMS basis_tl} :
    x ∈ cons exp coef tl ↔ x = (exp, coef) ∨ x ∈ tl :=
  Seq.mem_cons_iff

@[simp]
theorem Pairwise_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {R} :
    Seq.Pairwise R (nil : SeqMS basis_hd basis_tl) := by
  simp [nil]

@[simp]
theorem Pairwise_cons_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {R exp coef} :
    Seq.Pairwise R (cons exp coef (nil : SeqMS basis_hd basis_tl)) := by
  simp [cons, nil]

end simp

end SeqMS

def ofReal (c : ℝ) : PreMS [] := c

/-- Convert a multiseries in empty basis to a real number. -/
def toReal (ms : PreMS []) : ℝ := ms

/-- Convert a multiseries in non-empty basis to a sequence of pairs `(exp, coef)`. -/
def seq {basis_hd basis_tl} (ms : PreMS (basis_hd :: basis_tl)) :
    SeqMS basis_hd basis_tl :=
  ms.1

def toFun {basis : Basis} (ms : PreMS basis) : ℝ → ℝ :=
  match basis with
  | [] => fun _ ↦ ms.toReal
  | .cons _ _ =>  ms.2

def mk {basis_hd basis_tl} (s : SeqMS basis_hd basis_tl) (f : ℝ → ℝ) :
    PreMS (basis_hd :: basis_tl) :=
  (s, f)

@[cases_eliminator]
def recOn {basis_hd basis_tl} {motive : PreMS (basis_hd :: basis_tl) → Sort*}
    (nil : ∀ f, motive (mk .nil f))
    (cons : ∀ exp coef tl f, motive (.mk (.cons exp coef tl) f))
    (ms : PreMS (basis_hd :: basis_tl)) : motive ms := by
  let ⟨s, f⟩ := ms
  cases s with
  | nil => apply nil
  | cons hd tl => apply cons

instance (basis : Basis) : Inhabited (PreMS basis) :=
  match basis with
  | [] => ⟨(default : ℝ)⟩
  | List.cons basis_hd basis_tl => ⟨(default : SeqMS basis_hd basis_tl × (ℝ → ℝ))⟩

-- @[simp]
-- theorem ofReal_toReal (c : ℝ) : (ofReal c).toReal = c := rfl

-- @[simp]
-- theorem toReal_ofReal (c : PreMS []) : (ofReal c.toReal) = c := rfl

theorem eq_mk {basis_hd basis_tl} (ms : PreMS (basis_hd :: basis_tl)) :
    ms = mk ms.seq ms.toFun := rfl

@[simp]
theorem mk_eq_mk_iff {basis_hd basis_tl} (s t : SeqMS basis_hd basis_tl) (f g : ℝ → ℝ) :
    mk (basis_hd := basis_hd) s f = mk (basis_hd := basis_hd) t g ↔ s = t ∧ f = g where
  mp h := by rwa [mk, mk, Prod.mk_inj] at h
  mpr h := by simp [h]

@[simp]
theorem ms_eq_mk_iff {basis_hd basis_tl} (ms : PreMS (basis_hd :: basis_tl))
    (s : SeqMS basis_hd basis_tl) (f : ℝ → ℝ) :
    ms = mk s f ↔ ms.seq = s ∧ ms.toFun = f := by
  conv => lhs; lhs; rw [eq_mk ms]
  simp

@[simp]
theorem mk_eq_mk_iff_iff {basis_hd basis_tl} (ms : PreMS (basis_hd :: basis_tl))
    (s : SeqMS basis_hd basis_tl) (f : ℝ → ℝ) :
    mk s f = ms ↔ ms.seq = s ∧ ms.toFun = f := by
  rw [@Eq.comm _ (mk s f) ms]
  simp

theorem ms_eq_ms_iff_mk_eq_mk {basis_hd basis_tl} (ms₁ ms₂ : PreMS (basis_hd :: basis_tl)) :
    ms₁ = ms₂ ↔ ms₁.seq = ms₂.seq ∧ ms₁.toFun = ms₂.toFun where
  mp h := by simp [h]
  mpr h := by
    rw [eq_mk ms₁, eq_mk ms₂]
    simp [h]

@[simp]
theorem const_toFun (ms : PreMS []) : ms.toFun = fun _ ↦ ms.toReal := rfl

@[simp]
theorem mk_toFun {basis_hd basis_tl} {s : SeqMS basis_hd basis_tl} {f : ℝ → ℝ} :
    (mk (basis_hd := basis_hd) s f).toFun = f := rfl

@[simp]
theorem mk_seq {basis_hd basis_tl} (s : SeqMS basis_hd basis_tl) (f : ℝ → ℝ) :
    (mk (basis_hd := basis_hd) s f).seq = s := rfl

def replaceFun {basis_hd basis_tl} (ms : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ) :
    PreMS (basis_hd :: basis_tl) :=
  mk ms.seq f

@[simp]
theorem mk_replaceFun {basis_hd basis_tl} (s : SeqMS basis_hd basis_tl) (f g : ℝ → ℝ) :
    (mk (basis_hd := basis_hd) s f).replaceFun g = mk (basis_hd := basis_hd) s g :=
  rfl

@[simp]
theorem replaceFun_toFun {basis_hd basis_tl} (ms : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ) :
    (ms.replaceFun f).toFun = f := rfl

@[simp]
theorem replaceFun_seq {basis_hd basis_tl} (ms : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ) :
    (ms.replaceFun f).seq = ms.seq := rfl

section leadingExp

-- TODO: move
@[simp]
theorem bot_lt_zero : (⊥ : WithBot ℝ) < 0 := by
  rw [← sign_eq_neg_one_iff]
  rfl

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}

namespace SeqMS

/-- The leading exponent of multiseries with non-empty basis. For `ms = []` it is `⊥`. -/
def leadingExp (s : SeqMS basis_hd basis_tl) : WithBot ℝ :=
  match s.head with
  | none => ⊥
  | some (exp, _) => exp

@[simp]
theorem leadingExp_nil : (nil : SeqMS basis_hd basis_tl).leadingExp = ⊥ :=
  rfl

@[simp]
theorem leadingExp_cons {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl} :
    (cons exp coef tl).leadingExp = exp :=
  rfl

-- @[simp]
-- theorem leadingExp_cons' {hd : ℝ × PreMS basis_tl} {tl : SeqMS basis_hd basis_tl} :
--     leadingExp (.cons hd tl) = hd.1 :=
--   rfl

-- theorem leadingExp_of_head :
--     ms.leadingExp = ms.head.elim ⊥ (fun (exp, _) ↦ exp) := by
--   cases ms <;> simp

/-- If `ms.leadingExp = ⊥` then `ms = []`. -/
@[simp]
theorem leadingExp_eq_bot (s : SeqMS basis_hd basis_tl) :
    s.leadingExp = ⊥ ↔ s = nil := by
  cases s <;> simp

-- /-- If `ms.leadingExp` is real number `exp` then `ms = cons (exp, coef) tl` for some `coef` and
-- `tl`. -/
-- theorem leadingExp_eq_coe {exp : ℝ} (h : ms.leadingExp = ↑exp) :
--     ∃ coef tl, ms = cons exp coef tl := by
--   cases ms with
--   | nil => simp at h
--   | cons exp coef tl =>
--     simp only [leadingExp_cons, WithBot.coe_inj] at h
--     subst h
--     use coef, tl

end SeqMS

def leadingExp (ms : PreMS (basis_hd :: basis_tl)) : WithBot ℝ :=
  ms.seq.leadingExp

@[simp]
theorem leadingExp_def (ms : PreMS (basis_hd :: basis_tl)) :
    leadingExp ms = ms.seq.leadingExp := rfl

end leadingExp

section WellOrdered

/-- Auxilary instance for order on pairs `(exp, coef)` used below to define `WellOrdered` in terms
of `Stream'.Seq.Pairwise`. `(exp₁, coef₁) ≤ (exp₂, coef₂)` iff `exp₁ ≤ exp₂`. -/
scoped instance {basis} : Preorder (ℝ × PreMS basis) := Preorder.lift Prod.fst

private theorem lt_iff_lt {basis} {exp1 exp2 : ℝ} {coef1 coef2 : PreMS basis} :
    (exp1, coef1) < (exp2, coef2) ↔ exp1 < exp2 := by
  rfl

/-- Multiseries `ms` is `WellOrdered` when at each its level exponents are Pairwise by TODO. -/
inductive WellOrdered : {basis : Basis} → (PreMS basis) → Prop
| const (ms : PreMS []) : WellOrdered ms
| seq {hd} {tl} (ms : PreMS (hd :: tl))
    (h_coef : ∀ x ∈ ms.seq, x.2.WellOrdered)
    (h_Pairwise : Seq.Pairwise (· > ·) ms.seq) : ms.WellOrdered

-- TODO: can be done nicer?
def SeqMS.WellOrdered {basis_hd basis_tl} (s : SeqMS basis_hd basis_tl) : Prop :=
  (mk s 0).WellOrdered (basis := basis_hd :: basis_tl)

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}

@[simp]
theorem WellOrdered_iff_Seq_WellOrdered {ms : PreMS (basis_hd :: basis_tl)} :
    ms.WellOrdered ↔ SeqMS.WellOrdered ms.seq where
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

namespace SeqMS

@[simp]
theorem WellOrdered.nil : WellOrdered (nil : SeqMS basis_hd basis_tl) := by
  unfold WellOrdered
  constructor <;> simp

/-- `[(exp, coef)]` is `WellOrdered` when `coef` is `WellOrdered`. -/
theorem WellOrdered.cons_nil {basis_hd basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    (h_coef : coef.WellOrdered) :
    WellOrdered (cons exp coef (.nil : SeqMS basis_hd basis_tl)) := by
  constructor
  · simpa
  · simp

theorem WellOrdered.cons {basis_hd basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl}
    (h_coef : coef.WellOrdered)
    (h_comp : leadingExp tl < exp)
    (h_tl : tl.WellOrdered) :
    WellOrdered (cons exp coef tl) := by
  cases h_tl with | seq _ h_tl_coef h_tl_tl =>
  constructor
  · simp at h_tl_coef ⊢
    grind
  · cases tl
    · exact Seq.Pairwise_cons_nil
    apply Seq.Pairwise.cons_cons_of_trans _ h_tl_tl
    simpa [lt_iff_lt] using h_comp

/-- The fact `WellOrdered (cons (exp, coef) tl)` implies that `coef` and `tl` are `WellOrdered`, and
leading exponent of `tl` is less than `exp`. -/
theorem WellOrdered_cons {basis_hd basis_tl} {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (h : WellOrdered (cons exp coef tl)) :
    coef.WellOrdered ∧ leadingExp tl < exp ∧ tl.WellOrdered := by
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
  · simp
    apply h_all (tl_exp, tl_coef) (by simp [cons])
  constructor
  · intro x hx
    apply h_coef
    simp at hx ⊢
    grind
  · assumption

theorem WellOrdered.tail {ms : SeqMS basis_hd basis_tl} (h : ms.WellOrdered) :
    ms.tail.WellOrdered := by
  cases ms with
  | nil => simp
  | cons exp coef tl => simpa using (WellOrdered_cons h).right.right

/-- Coinduction principle for proving `WellOrdered`. For some predicate `motive` on multiseries,
if `motive ms` (base case) and the predicate "survives" destruction of its argument, then `ms` is
`WellOrdered`. Here "survive" means that if `x = cons (exp, coef) tl` than `motive x` must imply
`coef.wellOrdered`, `tl.leadingExp < exp` and `motive tl`. -/
theorem WellOrdered.coind {s : SeqMS basis_hd basis_tl}
    (motive : (ms : SeqMS basis_hd basis_tl) → Prop)
    (h_base : motive s)
    (h_step : ∀ exp coef tl, motive (.cons exp coef tl) →
        coef.WellOrdered ∧
        leadingExp tl < exp ∧
        motive tl) :
    s.WellOrdered := by
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

abbrev PreservesWellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl) : Prop :=
  ∀ x, x.WellOrdered → (op x).WellOrdered

theorem PreservesWellOrdered.comp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {op op' : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl}
    (h_preserves : PreservesWellOrdered op) (h_preserves' : PreservesWellOrdered op') :
    PreservesWellOrdered (op ∘ op') := by
  simp [PreservesWellOrdered] at *
  grind

theorem WellOrdered.coind_friend {ms : SeqMS basis_hd basis_tl}
    (motive : (ms : SeqMS basis_hd basis_tl) → Prop)
    (h_base : motive ms)
    (h_step : ∀ exp coef tl, motive (.cons exp coef tl) →
        coef.WellOrdered ∧
        tl.leadingExp < exp ∧
        ∃ (op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl)
        (x : SeqMS basis_hd basis_tl), tl = op x ∧
        FriendOperation op ∧ PreservesWellOrdered op ∧ motive x) :
    ms.WellOrdered := by
  let motive' (ms : SeqMS basis_hd basis_tl) : Prop :=
    ∃ (op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl)
      (x : SeqMS basis_hd basis_tl), ms = op x ∧ FriendOperation op ∧
      PreservesWellOrdered op ∧ motive x
  apply WellOrdered.coind motive'
  · use id, ms
    simp [h_base, FriendOperation.id, PreservesWellOrdered]
  intro exp coef tl ⟨op, x, h_eq, h_friend, h_preserves, hx⟩
  cases x with
  | nil =>
    have : WellOrdered (.cons exp coef tl) := by
      rw [h_eq]
      apply h_preserves
      apply WellOrdered.nil
    obtain ⟨h_coef_wo, h_comp, h_tl⟩ := WellOrdered_cons this
    exact ⟨h_coef_wo, h_comp, fun _ ↦ tl, .nil, rfl, FriendOperation.const,
      fun _ _ ↦ h_tl, hx⟩
  | cons x_exp x_coef x_tl =>
  obtain ⟨hx_coef, hx_comp, op', y, hx_tl, h_friend', h_preserves', hy⟩ :=
    h_step x_exp x_coef x_tl hx
  obtain ⟨x_tl', hx_tl_head, this⟩ : ∃ (x_tl' : SeqMS basis_hd basis_tl),
      x_tl.head = x_tl'.head ∧ WellOrdered (.cons x_exp x_coef x_tl') := by
    cases x_tl with
    | nil =>
      use .nil
      simp only [head_nil, true_and]
      apply WellOrdered.cons_nil hx_coef
    | cons x_tl_exp x_tl_coef x_tl_tl =>
      use .cons x_tl_exp x_tl_coef .nil
      simp only [head_cons, true_and]
      apply WellOrdered.cons hx_coef
      · simpa using hx_comp
      apply WellOrdered.cons_nil
      cases y with
      | nil =>
        have : WellOrdered (.cons x_tl_exp x_tl_coef x_tl_tl) := by
          rw [hx_tl]
          apply h_preserves'
          apply WellOrdered.nil
        obtain ⟨h_coef_wo, h_comp, h_tl⟩ := WellOrdered_cons this
        assumption
      | cons y_exp y_coef y_tl =>
        have : WellOrdered (basis_hd := basis_hd) (.cons y_exp y_coef .nil) := by
          apply WellOrdered.cons_nil
          grind
        apply h_preserves' at this
        obtain ⟨T, hT⟩ := FriendOperation.destruct h_friend'
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
        obtain ⟨h_coef_wo, h_comp, h_tl⟩ := WellOrdered_cons this
        assumption
  apply h_preserves at this
  obtain ⟨T, hT⟩ := FriendOperation.destruct h_friend
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
  obtain ⟨h_coef_wo, h_comp, h_tl⟩ := WellOrdered_cons this
  refine ⟨h_coef_wo, ?_, ?_⟩
  · simpa [h_tl_eq, leadingExp, FriendOperation.head_eq_head h_friend'' hx_tl_head] using h_comp
  simp only [motive']
  use (fun z ↦ if (op' z).leadingExp < x_exp then
    (op (.cons x_exp x_coef (op' z))).tail else .nil), y
  constructorm* _ ∧ _
  · simp [← hx_tl, ← h_eq, hx_comp]
  · change FriendOperation ((fun z ↦ if z.leadingExp < (x_exp : WithBot ℝ) then
      (op (.cons x_exp x_coef z)).tail else .nil) ∘ op')
    apply FriendOperation.comp _ h_friend'
    simp only [leadingExp]
    let P (hd : Option (ℝ × PreMS basis_tl)) : Prop :=
      (match hd with | none => ⊥ | some (exp, _) => exp) < (x_exp : WithBot ℝ)
    apply FriendOperation.ite (P := P)
    · apply FriendOperation.cons_tail h_friend
    · apply FriendOperation.const
  · intro z hz
    dsimp
    split_ifs with h_if
    · apply WellOrdered.tail
      apply h_preserves
      apply WellOrdered.cons hx_coef h_if (h_preserves' z hz)
    · apply WellOrdered.nil
  · exact hy

theorem WellOrdered.coind_friend' {ms : SeqMS basis_hd basis_tl}
    {γ : Type*} (op : γ → SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl)
    [FriendOperationClass op]
    (motive : (ms : SeqMS basis_hd basis_tl) → Prop)
    (C : γ → Prop)
    (h_op : ∀ c x, C c → x.WellOrdered → (op c x).WellOrdered)
    (h_base : motive ms)
    (h_step : ∀ exp coef tl, motive (.cons exp coef tl) →
        coef.WellOrdered ∧
        tl.leadingExp < exp ∧
        ∃ c x, tl = op c x ∧ C c ∧ motive x) :
    ms.WellOrdered := by
  apply WellOrdered.coind_friend motive h_base
  intro exp coef tl ih
  specialize h_step exp coef tl ih
  obtain ⟨h_coef_wo, h_comp, c, x, h_tl, h_C, hx⟩ := h_step
  refine ⟨h_coef_wo, h_comp, op c, x, h_tl, FriendOperationClass.FriendOperation _, by grind, hx⟩

end SeqMS

/-- `[]` is `WellOrdered`. -/
@[simp]
theorem WellOrdered.nil (f : ℝ → ℝ) : @WellOrdered (basis_hd :: basis_tl) (mk .nil f) := by
  simp

/-- `[(exp, coef)]` is `WellOrdered` when `coef` is `WellOrdered`. -/
theorem WellOrdered.cons_nil {exp : ℝ} {coef : PreMS basis_tl} {f : ℝ → ℝ} (h_coef : coef.WellOrdered) :
    @WellOrdered (basis_hd :: basis_tl) (mk (.cons exp coef .nil) f) := by
  simp [SeqMS.WellOrdered.cons_nil h_coef]

/-- `cons (exp, coef) tl` is `WellOrdered` when `coef` and `tl` are `WellOrdered` and leading
exponent of `tl` is less than `exp`. -/
theorem WellOrdered.cons {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl} {f : ℝ → ℝ}
    (h_coef : coef.WellOrdered)
    (h_comp : tl.leadingExp < exp)
    (h_tl : tl.WellOrdered) :
    @WellOrdered (basis_hd :: basis_tl) (mk (.cons exp coef tl) f) := by
  simp [SeqMS.WellOrdered.cons h_coef h_comp h_tl]

/-- The fact `WellOrdered (cons (exp, coef) tl)` implies that `coef` and `tl` are `WellOrdered`, and
leading exponent of `tl` is less than `exp`. -/
theorem WellOrdered_cons {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl} {f : ℝ → ℝ}
    (h : @WellOrdered (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) :
    coef.WellOrdered ∧ tl.leadingExp < exp ∧ tl.WellOrdered := by
  apply SeqMS.WellOrdered_cons (by simpa using h)

end WellOrdered

section Approximates

section Majorated

/-- `majorated f g exp` for real functions `f` and `g` means that for any `exp' < exp`,
`f =o[atTop] g^exp'`. -/
def majorated (f basis_hd : ℝ → ℝ) (exp : ℝ) : Prop :=
  ∀ exp', exp < exp' → f =o[atTop] (fun t ↦ (basis_hd t) ^ exp')

/-- One can change the argument of `majorated` with the function that eventually equals to it. -/
theorem majorated_of_EventuallyEq {f g basis_hd : ℝ → ℝ} {exp : ℝ} (h_eq : g =ᶠ[atTop] f)
    (h : majorated f basis_hd exp) : majorated g basis_hd exp := by
  simp only [majorated] at *
  intro exp' h_exp
  specialize h exp' h_exp
  exact EventuallyEq.trans_isLittleO h_eq h

-- TODO: upstream?
/-- For any function `f`, `f^exp` is majorated with `f` with exponent `exp`. -/
theorem majorated_self {f : ℝ → ℝ} {exp : ℝ}
    (h : Tendsto f atTop atTop) :
    majorated (fun t ↦ (f t)^exp) f exp := by
  simp only [majorated]
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

/-- If one can majorate `f` with `exp1`, then it can be majorated with any `exp2 > exp1`. -/
theorem majorated_of_le {f basis_hd : ℝ → ℝ} {exp1 exp2 : ℝ}
    (h_lt : exp1 ≤ exp2) (h : majorated f basis_hd exp1) :
    majorated f basis_hd exp2 := by
  simp only [majorated] at *
  intro exp' h_exp
  apply h _ (by linarith)

/-- If `f` is majorated with negative exponent, then it tends to zero. -/
theorem majorated_tendsto_zero_of_neg {f basis_hd : ℝ → ℝ} {exp : ℝ}
    (h_lt : exp < 0) (h : majorated f basis_hd exp) :
    Tendsto f atTop (𝓝 0) := by
  simp only [majorated] at h
  specialize h 0 (by linarith)
  simpa using h

/-- Constants can be majorated with `exp = 0`. -/
theorem const_majorated {basis_hd : ℝ → ℝ} (h_tendsto : Tendsto basis_hd atTop atTop)
    {c : ℝ} : majorated (fun _ ↦ c) basis_hd 0 := by
  intro exp h_exp
  apply Asymptotics.isLittleO_const_left.mpr
  right
  apply Tendsto.comp tendsto_norm_atTop_atTop
  apply Tendsto.comp (tendsto_rpow_atTop h_exp)
  exact h_tendsto

/-- Zero can be majorated with any exponent. -/
theorem zero_majorated {basis_hd : ℝ → ℝ} {exp : ℝ} : majorated (fun _ ↦ 0) basis_hd exp := by
  intro exp h_exp
  apply Asymptotics.isLittleO_zero

/-- `f * c` can be majorated with the same exponent as `f` for any constant `c`. -/
theorem smul_majorated {f basis_hd : ℝ → ℝ} {exp : ℝ} (h : majorated f basis_hd exp)
    {c : ℝ} : majorated (c • f) basis_hd exp := by
  intro exp h_exp
  apply IsLittleO.const_mul_left (h exp h_exp)

-- /-- `f * c` can be majorated with the same exponent as `f` for any constant `c`. -/
-- theorem mul_const_majorated {f basis_hd : ℝ → ℝ} {exp : ℝ} (h : majorated f basis_hd exp)
--     {c : ℝ} : majorated (fun t ↦ (f t) * c) basis_hd exp := by
--   intro exp h_exp
--   simp_rw [mul_comm]
--   apply IsLittleO.const_mul_left (h exp h_exp)

/-- Sum of two function, that can be majorated with exponents `f_exp` and `g_exp`, can be
majorated with exponent `f_exp ⊔ g_exp`. -/
theorem add_majorated {f g basis_hd : ℝ → ℝ} {f_exp g_exp : ℝ} (hf : majorated f basis_hd f_exp)
    (hg : majorated g basis_hd g_exp) : majorated (f + g) basis_hd (f_exp ⊔ g_exp) := by
  simp only [majorated] at *
  intro exp h_exp
  simp only [sup_lt_iff] at h_exp
  apply IsLittleO.add
  · exact hf _ h_exp.left
  · exact hg _ h_exp.right

theorem add_majorated' {f g basis_hd : ℝ → ℝ} {exp f_exp g_exp : ℝ}
    (hf : majorated f basis_hd f_exp)
    (hg : majorated g basis_hd g_exp) (hf_exp : f_exp ≤ exp) (hg_exp : g_exp ≤ exp) :
    majorated (f + g) basis_hd exp := by
  apply majorated_of_le _ (add_majorated hf hg)
  simp [hf_exp, hg_exp]

/-- Product of two function, that can be majorated with exponents `f_exp` and `g_exp`, can be
majorated with exponent `f_exp + g_exp`. -/
theorem mul_majorated {f g basis_hd : ℝ → ℝ} {f_exp g_exp : ℝ} (hf : majorated f basis_hd f_exp)
    (hg : majorated g basis_hd g_exp) (h_pos : ∀ᶠ t in atTop, 0 < basis_hd t) :
    majorated (f * g) basis_hd (f_exp + g_exp) := by
  simp only [majorated] at *
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

end Majorated

mutual
  /-- Auxilliary monotone map, for which `Approximates` is the greatest fixed point. -/
  def Approximates.T (basis : Basis) : (PreMS basis → Prop) →o
      (PreMS basis → Prop) :=
    match (generalizing := true) basis with
    | [] => {
      toFun := fun P ms => True
      monotone' := monotone_const
    }
    | .cons basis_hd basis_tl => {
      toFun := fun P ms =>
        (ms.seq = .nil ∧ ms.toFun =ᶠ[atTop] 0) ∨
        (∃ (exp : ℝ) (coef : PreMS basis_tl) (tl : SeqMS basis_hd basis_tl),
          ms.seq = .cons exp coef tl ∧ coef.Approximates ∧
          majorated ms.toFun basis_hd exp ∧
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
    `f` is majorated with exponent `exp` by `basis_hd`,
    `coef` approximates some function `fC`, and
    `tl` approximates `f - fC * basis_hd ^ exp`
  -/
  def Approximates {basis} (ms : PreMS basis) : Prop :=
    (Approximates.T basis).gfp ms
end

variable {f basis_hd : ℝ → ℝ} {basis_tl : Basis}

private theorem Approximates.step {basis} {ms : PreMS basis} :
    ms.Approximates ↔ (Approximates.T basis Approximates ms) := by
  conv_lhs => unfold Approximates; rw [← OrderHom.isFixedPt_gfp]
  conv_rhs => arg 2; eta_expand; unfold Approximates; change OrderHom.gfp _

@[simp]
theorem Approximates.const {c : PreMS []} : Approximates c := by
  rw [Approximates.step]
  simp [T]

/-- `[]` approximates zero function. -/
theorem Approximates.nil (h : f =ᶠ[atTop] 0) :
    @Approximates (basis_hd :: basis_tl) (mk .nil f) := by
  rw [Approximates.step]
  simpa [T]

/-- `cons (exp, coef) tl` approximates `f` when `f` can be majorated with exponent `exp`, and
there exists some function `fC` such that `coef` approximates `fC` and `tl` approximates
`f - fC * basis_hd ^ exp`. -/
theorem Approximates.cons {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (h_coef : coef.Approximates)
    (h_maj : majorated f basis_hd exp)
    (h_tl : (mk (basis_hd := basis_hd) tl (f - basis_hd ^ exp * coef.toFun)).Approximates) :
    @Approximates (basis_hd :: basis_tl) (mk (.cons exp coef tl) f) := by
  rw [Approximates.step]
  simp [T]
  grind

theorem Approximates.coind {ms : PreMS (basis_hd :: basis_tl)}
    (motive : PreMS (basis_hd :: basis_tl) → Prop)
    (h_base : motive ms)
    (h_step : ∀ ms, motive ms →
      (ms.seq = .nil ∧ ms.toFun =ᶠ[atTop] 0) ∨
      (∃ exp coef tl, ms.seq = .cons exp coef tl ∧
        coef.Approximates ∧
        majorated ms.toFun basis_hd exp ∧
        motive (mk (basis_hd := basis_hd) tl (ms.toFun - basis_hd ^ exp * coef.toFun)))) :
    ms.Approximates := by
  have : motive ≤ T _ motive := by
    intro ms h
    simp [T]
    grind
  have := OrderHom.le_gfp _ this
  unfold Approximates
  aesop

-- @[simp]
-- theorem Approximates_const_iff {ms : PreMS []} {f : ℝ → ℝ} :
--     ms.Approximates f ↔ f =ᶠ[atTop] (fun _ ↦ ms) where
--   mp h := by
--     rw [Approximates.step] at h
--     simpa [Approximates.T] using h
--   mpr h := Approximates.const h

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

/-- If `cons (exp, coef) tl` approximates `f`, then `f` can be majorated with exponent `exp`, and
there exists function `fC` such that `coef` approximates `fC` and `tl` approximates
`f - fC * basis_hd ^ exp`. -/
theorem Approximates_cons {exp : ℝ}
    {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (h : Approximates (basis := basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) :
    coef.Approximates ∧
    majorated f basis_hd exp ∧
    (mk (basis_hd := basis_hd) tl (f - basis_hd ^ exp * coef.toFun)).Approximates := by
  rw [Approximates.step] at h
  simpa [Approximates.T] using h

theorem replaceFun_WellOrdered {ms : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ}
    (h_wo : ms.WellOrdered) :
    (ms.replaceFun f).WellOrdered := by
  simpa using h_wo

/-- One can replace `f` in `Approximates` with the funcion that eventually equals `f`. -/
theorem replaceFun_Approximates {ms : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ}
    (h_equiv : ms.toFun =ᶠ[atTop] f) (h_approx : ms.Approximates) :
    (ms.replaceFun f).Approximates := by
  let motive (ms : PreMS (basis_hd :: basis_tl)) : Prop :=
      ∃ (ms' : PreMS (basis_hd :: basis_tl)) (f' : ℝ → ℝ),
      ms = ms'.replaceFun f' ∧ ms'.Approximates ∧ ms'.toFun =ᶠ[atTop] f'
  apply Approximates.coind motive
  · simp only [motive]
    use ms, f
  rintro _ ⟨ms, f, rfl, h_approx, h_eq⟩
  cases ms with
  | nil g =>
    simp at h_approx h_eq ⊢
    grw [← h_eq, h_approx]
  | cons exp coef tl g =>
    right
    obtain ⟨h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
    use exp, coef, tl
    simp [h_coef]
    simp at h_eq
    constructor
    · exact majorated_of_EventuallyEq h_eq.symm h_maj
    refine ⟨mk tl (g - basis_hd ^ exp * coef.toFun), _, rfl, h_tl, ?_⟩
    simp
    grw [h_eq]

instance (basis_hd : ℝ → ℝ) (basis_tl : Basis) : Setoid (PreMS (basis_hd :: basis_tl)) where
  r x y := x.seq = y.seq ∧ x.toFun =ᶠ[atTop] y.toFun
  iseqv := by
    constructor
    · simp
    · grind [EventuallyEq.symm]
    · grind [EventuallyEq.trans]

@[simp]
theorem equiv_def {x y : PreMS (basis_hd :: basis_tl)} :
    x ≈ y ↔ x.seq = y.seq ∧ x.toFun =ᶠ[atTop] y.toFun := by
  rfl

end Approximates

end PreMS

end ComputeAsymptotics
