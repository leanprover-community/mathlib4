/-
Copyright (c) 2024 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Finite.Sum
import Mathlib.ModelTheory.Satisfiability

/-!

# Functional Formulas in a First Order Theory

This file provides an interface for using definable functions of a first order theory, and
proving that properties of these functions definable by first-order formulas.

## Main definitions

* `FirstOrder.Language.Theory.FunctionalFormula` - For a Theory `T`, a `FunctionalFormula T α β`
  is a formula `φ : L.Formula (α ⊕ β)` such that in all models `M`, the set of elements of
  `(α ⊕ β) → M` satisfying `φ` is the graph of a function. We quotient by semantic equivalence.
* `FirstOrder.Language.Theory.FunctionalFormula.Realize` -The semantics of
  `T.FunctionalFormula α β` as a relation on `α → M` and `β → M`.
* `FirstOrder.Language.Theory.FunctionalFormula.realize` - The semantics of a
  `T.FunctionalFormula α β` as a function `(α → M) → (β → M)`

There are also examples of how properties of definable functions can be expressed with first
order formulas, for example `FunctionalFormula.equal` and `FunctionalFormula.injOn`,

* `FirstOrder.Language.Theory.FunctionalFormulaLang` - Given a `Language`, `L` and a `Theory`,
  `T` we can extend `L` to a language whose function symbols are the definable functions in the
  `Theory`, `T`
* `FirstOrder.Language.Theory.FunctionalFormulaLangtoBoundedFormula` -  Every`BoundedFormula` in
  `FunctionalFormulaLang T` is equivalent to a `BoundedFormula` in `T`

## Tags

definable function

## TODO

Define an interface for translating functional formulas across extensions of languages and
theories.

-/

universe u v w x y z

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) {α : Type w} {β : Type x} {γ : Type y}
variable [Finite β] {M : Type z} [L.Structure M] [T.Model M] [Nonempty M]

/-- The equivalence relation on `FunctionFormula`. Two `FunctionalFormula` are equivalent
if they have the same semantics in all models. -/
def FunctionalFormulaSetoid (α : Type w) (β : Type x) [Finite β] :
    Setoid {φ : L.Formula (α ⊕ β) // T ⊨ᵇ Formula.iExsUnique β φ } where
  r := fun x y => T ⊨ᵇ x.1.iff y.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · simp [ModelsBoundedFormula]
    · rintro ⟨x, _⟩ ⟨y, _⟩
      simp +contextual [ModelsBoundedFormula, Formula.iff, BoundedFormula.realize_iff]
    · rintro ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩
      simp +contextual [ModelsBoundedFormula, Formula.iff, BoundedFormula.realize_iff]

/-- For a Theory `T`, a `FunctionalFormula T α β` is a formula `φ : L.Formula (α ⊕ β)` such that
in all Models `M`, the set of elements of `(α ⊕ β) → M` satisfying `φ` is the graph of a function.
We quotient by semantic equivalence.  -/
structure FunctionalFormula (α : Type w) (β : Type x) [Finite β] : Type _ where
  ofQuotient ::
  /-- The map to the Quotient of a set of formulas -/
  toQuotient : Quotient (FunctionalFormulaSetoid T α β)

namespace FunctionalFormula

variable {T}

/-- The constructor for a `FunctionalFormula`. To make a `FunctionalFormula`, we need a formula,
and a proof that it is the graph of a function in all models, stated using `ExistsUnique` -/
def mk (φ : L.Formula (α ⊕ β)) (h : T ⊨ᵇ Formula.iExsUnique β φ) : FunctionalFormula T α β :=
  ofQuotient (Quotient.mk _ ⟨φ, h⟩)

/-- The semantics of a `T.FunctionalFormula α β` as a relation on `α → M` and `β → M`. See
also `realize` for the semantics as a function.  -/
def Realize (f : FunctionalFormula T α β) (x : α → M) (y : β → M) : Prop :=
  Quotient.lift (fun φ => φ.1.Realize (Sum.elim x y)) (by
    intro a b hab
    simpa using hab.realize_formula M (v := Sum.elim x y)) f.toQuotient

/-- A `Formula` corresponding to a `FunctionalFormula`. This is non-unique, so we used the
axiom of choice to select one.  -/
noncomputable def toFormula (f : FunctionalFormula T α β) : L.Formula (α ⊕ β) := f.1.out.1

@[simp]
theorem realize_toFormula (f : FunctionalFormula T α β) (x : α ⊕ β → M) :
    f.toFormula.Realize x ↔ f.Realize (x ∘ Sum.inl) (x ∘ Sum.inr) := by
  rcases f with ⟨f⟩
  induction f using Quotient.inductionOn with
  | h f =>
    simp only [toFormula, Realize, Sum.elim_comp_inl_inr]
    conv_rhs => rw [← Quotient.out_eq (Quotient.mk _ f), Quotient.lift_mk]

theorem toFormula_spec (f : FunctionalFormula T α β) : T ⊨ᵇ Formula.iExsUnique β f.toFormula :=
  f.1.out.2

@[simp]
theorem realize_mk (φ : L.Formula (α ⊕ β)) (h : T ⊨ᵇ Formula.iExsUnique β φ) (x : α → M)
    (y : β → M) : (mk φ h).Realize x y ↔ φ.Realize (Sum.elim x y) := by
  simp [Realize, mk]

private theorem exists_fun_eq_iff (f : T.FunctionalFormula α β) : ∃ f' : (α → M) → (β → M),
    ∀ x, ∀ y, f' x = y ↔ f.Realize x y := by
  rcases f with ⟨φ, h⟩
  have := fun x : α → M => h.realize_formula M (v := x)
  simp only [Formula.realize_iExsUnique, ExistsUnique, id_eq, Classical.skolem] at this
  rcases this with ⟨f, hf⟩
  use f
  intro x y
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact (hf x).1
  · rintro h
    exact ((hf x).2 y h).symm

/-- The semantics of a `T.FunctionalFormula α β` as a function `(α → M) → (β → M)` -/
noncomputable def realize (f : T.FunctionalFormula α β) : (α → M) → (β → M) :=
  Classical.choose (f.exists_fun_eq_iff)

theorem realize_iff_realize_eq {f : T.FunctionalFormula α β} {x : α → M} {y : β → M} :
    f.Realize x y ↔ f.realize x = y :=
  (Classical.choose_spec (f.exists_fun_eq_iff) x y).symm

@[ext]
theorem ext {f g : T.FunctionalFormula α β}
    (h : ∀ (M : Theory.ModelType.{_, _, max u v w x} T) (x : α → M), f.realize x = g.realize x) :
    f = g := by
  rcases f with ⟨f⟩; rcases g with ⟨g⟩
  induction f, g using Quotient.inductionOn₂ with
  | h f g =>
      simp only [ModelsBoundedFormula, FunctionalFormulaSetoid, ofQuotient.injEq, Quotient.eq,
        BoundedFormula.realize_iff, Fin.forall_fin_zero_pi]
      intro M v
      have := h M (v ∘ Sum.inl)
      rw [← eq_iff_eq_cancel_left] at this
      have := @this (v ∘ Sum.inr)
      simp only [@eq_comm _ (v ∘ Sum.inr), ← realize_iff_realize_eq, Realize, Sum.elim_comp_inl_inr,
        Quotient.lift_mk] at this
      exact this

/-- The `FunctionalFormula` corresponding to a `Term` in a language. -/
def ofTerm (t : L.Term α) : T.FunctionalFormula α Unit :=
  mk (Term.equal (t.relabel Sum.inl) (var (Sum.inr ())))
  (by
    simp only [ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, id_eq,
      Formula.realize_equal, Term.realize_relabel, Sum.elim_comp_inl, Term.realize_var,
      Sum.elim_inr, forall_const]
    intro M x
    use fun _ => t.realize x
    simp +contextual [funext_iff, eq_comm])

@[simp]
theorem realize_ofTerm (t : L.Term α) (x : α → M) :
    (ofTerm (T := T) t).realize x = fun _ => t.realize x := by
  rw [← realize_iff_realize_eq]
  simp [ofTerm, Formula.Realize, Term.realize_relabel, Term.realize_var, Term.equal,
    Function.comp_def]

variable (T)
/-- `comap T f` is the `FunctionalFormula` corresponding to a relabelling of variables by `f` -/
noncomputable def comap (f : β → α) : T.FunctionalFormula α β :=
  mk (Formula.iAlls β <|
    (Formula.iInf
      (fun b => Term.equal (var (Sum.inr b)) (var (Sum.inl (f b))))).relabel Sum.inl) <| by
  simp only [models_formula_iff, Formula.realize_iExsUnique, Formula.realize_iAlls,
    Formula.realize_relabel, Sum.elim_comp_inl, Formula.realize_iInf, Finset.mem_univ,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl, forall_const]
  intro M x
  use fun y => x (f y)
  simp [Formula.Realize, Term.equal, funext_iff]

variable {T}
@[simp]
theorem realize_comap (f : β → α) (x : α → M) : (comap T f).realize x = x ∘ f := by
  rw [← realize_iff_realize_eq]; simp [comap]

variable (T)
/-- The identity functional as a `FunctionalFormula` -/
protected noncomputable def id : T.FunctionalFormula β β :=
  comap T id

@[simp]
theorem realize_id (x : β → M) :
    (FunctionalFormula.id T).realize (T := T) (M := M) x = x := by
  simp [FunctionalFormula.id]

variable {T}
/-- Composing two functional formulas -/
noncomputable def comp [Finite γ] (f : T.FunctionalFormula β γ) (g : T.FunctionalFormula α β) :
    T.FunctionalFormula α γ :=
  mk (Formula.iExs β
    (f.toFormula.relabel (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)) ⊓
     g.toFormula.relabel (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr))) <| by
  simp only [ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, id_eq, Formula.realize_iExs,
    Formula.realize_inf, Formula.realize_relabel, forall_const]
  intro M x
  use f.realize (g.realize x)
  simp only [Function.comp_def, Formula.realize_iExs, id_eq, Formula.realize_relabel,
    forall_exists_index]
  refine ⟨?_, ?_⟩
  · use g.realize x
    simp [realize_iff_realize_eq, Function.comp_def]
  · intro y z
    simp only [realize_toFormula, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      realize_iff_realize_eq, funext_iff, and_imp]
    intro h1 h2 g
    simp only [← h1, ← h2]

@[simp]
theorem realize_comp [Finite γ] (f : T.FunctionalFormula β γ) (g : T.FunctionalFormula α β)
    (x : α → M) : (f.comp g).realize x = f.realize (g.realize x) := by
  rw [← realize_iff_realize_eq]
  simp only [comp, Function.comp_def, realize_mk, Formula.realize_iExs, id_eq, Formula.realize_inf,
    Formula.realize_relabel, realize_toFormula, Sum.elim_inl, Sum.elim_inr]
  use g.realize x
  simp [Function.comp_def, realize_iff_realize_eq]

/-- Change the variables of the domain of a `FunctionalFormula` -/
noncomputable def relabelLeft (f : α → γ) (g : T.FunctionalFormula α β) : T.FunctionalFormula γ β :=
  mk (g.toFormula.relabel (Sum.map f id)) <| by
    simp only [Sum.map, Function.comp_def, CompTriple.comp_eq, models_formula_iff,
      Formula.realize_iExsUnique, id_eq, Formula.realize_relabel, realize_toFormula, Sum.elim_inl,
      Sum.elim_inr, realize_iff_realize_eq, funext_iff]
    intro M v
    simpa only [Function.comp_def, Formula.realize_iExsUnique, id_eq, realize_toFormula,
      Sum.elim_inl, Sum.elim_inr, realize_iff_realize_eq, funext_iff] using
      g.toFormula_spec.realize_formula (v := v ∘ f)

@[simp]
theorem realize_relabelLeft (f : α → γ) (g : T.FunctionalFormula α β) (x : γ → M) :
    (relabelLeft f g).realize x = g.realize (x ∘ f) := by
  simp only [relabelLeft, Sum.map, Function.comp_def, CompTriple.comp_eq, ← realize_iff_realize_eq,
    realize_mk, Formula.realize_relabel, realize_toFormula, Sum.elim_inl, Sum.elim_inr]
  rw [realize_iff_realize_eq]
  simp [funext_iff, Function.comp_def]

/-- Change the variables of the codomain of a `FunctionalFormula` -/
noncomputable def relabelRight [Finite γ] (f : γ → β) (g : T.FunctionalFormula α β) :
    T.FunctionalFormula α γ :=
  (comap T f).comp g

@[simp]
theorem realize_relabelRight [Finite γ] (f : γ → β) (g : T.FunctionalFormula α β) (x : α → M) :
    (relabelRight f g).realize x = g.realize x ∘ f := by
  simp [relabelRight, Function.comp_def]

/-- Create a `FunctionalFormula` with relization of type `(α → M) → ((Σ b : β, γ b) → M)` given a
`FunctionalFormula` with realization of type `(α → M) → (γ b → M)` for each `b : β` -/
noncomputable def toSigma {γ : β → Type y} [∀ b, Finite (γ b)]
    (f : (b : β) → T.FunctionalFormula α (γ b)) :
    T.FunctionalFormula α (Sigma γ) :=
  mk (Formula.iInf
    (fun b => (f b).toFormula.relabel (Sum.elim Sum.inl (fun g => Sum.inr ⟨_, g⟩)))) <| by
  simp only [models_formula_iff, Formula.realize_iExsUnique, id_eq, Formula.realize_iInf,
    Finset.mem_univ, Formula.realize_relabel, Function.comp_def, realize_toFormula, Sum.elim_inl,
    Sum.elim_inr, forall_const]
  intro M x
  use (fun i : Σ b, γ b => (f i.1).realize x i.2)
  simp +contextual [realize_iff_realize_eq]

@[simp]
theorem realize_toSigma {γ : β → Type y} [∀ b, Finite (γ b)]
    (f : (b : β) → T.FunctionalFormula α (γ b)) (x : α → M) :
    (toSigma f).realize x = fun i => (f i.1).realize x i.2 := by
  simp only [toSigma, realize_mk, Formula.realize_iInf, Finset.mem_univ, Formula.realize_relabel,
    Function.comp_def, realize_toFormula, Sum.elim_inl, Sum.elim_inr, forall_const,
    ← realize_iff_realize_eq]
  simp only [realize_iff_realize_eq, implies_true]

/-- Create a `FunctionalFormula` whose realization has type `(α → M) → (β ⊕ γ → M)` given a
`FunctionalFormula` with realization of type `(α → M) → (β → M)` and a
`FunctionalFormula` with realization of type `(α → M) → (γ → M)` -/
noncomputable def toSum [Finite γ] (f : T.FunctionalFormula α β) (g : T.FunctionalFormula α γ) :
    T.FunctionalFormula α (β ⊕ γ) :=
  mk (f.toFormula.relabel (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) ⊓
     (g.toFormula.relabel (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)))) <| by
    simp only [Function.comp_def, models_formula_iff, Formula.realize_iExsUnique,
      Formula.realize_inf, Formula.realize_relabel, realize_toFormula, Sum.elim_inl, Sum.elim_inr]
    intro M x
    use Sum.elim (f.realize x) (g.realize x)
    simp +contextual [realize_iff_realize_eq, funext_iff]

@[simp]
theorem realize_toSum [Finite γ] (f : T.FunctionalFormula α β) (g : T.FunctionalFormula α γ)
    (x : α → M) : (toSum f g).realize x = Sum.elim (f.realize x) (g.realize x) := by
  simp only [toSum, Function.comp_def, ← realize_iff_realize_eq, realize_mk, Formula.realize_inf,
    Formula.realize_relabel, realize_toFormula, Sum.elim_inl, Sum.elim_inr]
  simp only [realize_iff_realize_eq, and_self]

/-- Given `f : T.FunctionalFormula α β` and `φ : L.Formula β`, `rel φ f` is the `L.Formula α`
whose semantics on `x : α → M` is `φ.Realize (f.realize x)` -/
noncomputable def rel (φ : L.Formula β) (f : T.FunctionalFormula α β) : L.Formula α :=
  Formula.iAlls β (f.toFormula.imp (φ.relabel Sum.inr))

@[simp]
theorem realize_rel (φ : L.Formula β) (f : T.FunctionalFormula α β) (x : α → M) :
    (rel φ f).Realize x ↔ φ.Realize (f.realize x) := by
  simp [rel, realize_iff_realize_eq]

/-- Given `f : T.FunctionalFormula α β`, `g : T.FunctionalFormula α γ` and
`φ : L.Formula (β ⊕ γ)`, `rel2 φ f g` is the `L.Formula α`
whose semantics on `x : α → M` is `φ.Realize (Sum.elim (f.realize x) (g.realize x))` -/
noncomputable def rel2 [Finite γ] (φ : L.Formula (β ⊕ γ))
    (f : T.FunctionalFormula α β) (g : T.FunctionalFormula α γ) :
    L.Formula α :=
  Formula.iAlls (β ⊕ γ) ((toSum f g).toFormula.imp (φ.relabel Sum.inr))

@[simp]
theorem realize_rel2 [Finite γ] (φ : L.Formula (β ⊕ γ))
    (f : T.FunctionalFormula α β) (g : T.FunctionalFormula α γ) (x : α → M) :
    (rel2 φ f g).Realize x ↔ φ.Realize (Sum.elim (f.realize x) (g.realize x)) := by
  simp [rel2, realize_iff_realize_eq]

/-- Given `f g : T.Functional α β`, `equal f g` is the `L.Formula α` whose semantics on `x : α → M`
is `f.realize x = g.realize x` -/
noncomputable def equal (f g : T.FunctionalFormula α β) : L.Formula α :=
  rel2 (Formula.iInf
    (fun b => Term.equal (var (Sum.inl b)) (var (Sum.inr b))))
    f g

@[simp]
theorem realize_equal (f g : T.FunctionalFormula α β) (x : α → M) :
    (equal f g).Realize x ↔ f.realize x = g.realize x := by
  simp [equal, funext_iff]

/-- Given `f : T.FunctionFormula (α ⊕ γ) β` and `s : L.Formula (α ⊕ γ)`, `injOn f S` is the
formula whose semantics on `x : α → M` are that `f` partially applied at `x` is injective
on the predicate `S` partially applied at `x` -/
noncomputable def injOn [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β)
    (s : L.Formula (α ⊕ γ)) : L.Formula α :=
  Formula.iAlls (γ ⊕ γ) (
    (s.relabel (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl))).imp <|
    (s.relabel (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr))).imp <|
    (equal (f.relabelLeft (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)))
          (f.relabelLeft (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)))).imp <|
    equal (comap T (Sum.inr ∘ Sum.inl)) (comap T (Sum.inr ∘ Sum.inr)))

@[simp]
theorem realize_injOn [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) (s : L.Formula (α ⊕ γ))
    (x : α → M) : (injOn f s).Realize x ↔
      Set.InjOn (fun y : γ → M => f.realize (Sum.elim x y)) { y | s.Realize (Sum.elim x y) } := by
  simp only [injOn, Function.comp_def, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_relabel, Sum.elim_inr, realize_equal, realize_relabelLeft, funext_iff,
    Sum.forall_sum, Set.InjOn, Set.mem_setOf_eq]
  simp +singlePass [← Sum.elim_comp_inl_inr]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  tauto

/-- Given `f : T.FunctionFormula (α ⊕ γ) β`, `injective f` is the formula whose semantics on
`x : α → M` are that `f` partially applied at `x` is injective -/
noncomputable def injective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) : L.Formula α :=
  injOn f ⊤

@[simp]
theorem realize_injective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) (x : α → M) :
    (injective f).Realize x ↔ Function.Injective
      (fun y : γ → M => f.realize (Sum.elim x y)) := by
  simp [injective, Set.InjOn, Function.Injective]

/-- Given `f : T.FunctionFormula (α ⊕ γ) β` and `s : L.Formula (α ⊕ γ)`, and
`t : L.Formula (α ⊕ β)`, `surjOn f s t` is the formula whose semantics on `x : α → M` are that
`t` is contained in the image of `f` on the set `s`, when `f`, `s` and `t` are partially applied at
`x` -/
noncomputable def surjOn [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β)
    (s : L.Formula (α ⊕ γ)) (t : L.Formula (α ⊕ β)) : L.Formula α :=
  Formula.iAlls β (t.imp <| Formula.iExs γ <|
    s.relabel (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) ⊓
    (f.toFormula.relabel
    (Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr))))

@[simp]
theorem realize_surjOn [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) (s : L.Formula (α ⊕ γ))
    (t : L.Formula (α ⊕ β)) (x : α → M) : (surjOn f s t).Realize x ↔
      Set.SurjOn (fun y : γ → M => f.realize (Sum.elim x y))
        { y | s.Realize (Sum.elim x y) } {b | t.Realize (Sum.elim x b)} := by
  simp only [surjOn, Function.comp_def, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_relabel, Sum.elim_inr, Formula.realize_iExs, Formula.realize_inf,
    realize_toFormula, Sum.elim_inl, realize_iff_realize_eq, funext_iff, Set.SurjOn, Set.subset_def,
    Set.mem_setOf_eq, Set.mem_image]
  simp +singlePass [← Sum.elim_comp_inl_inr]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]

/-- Given `f : T.FunctionFormula (α ⊕ γ) β`, `surjective f` is the formula whose semantics on
`x : α → M` are that `f` partially applied at `x` is surjective -/
noncomputable def surjective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) : L.Formula α :=
  surjOn f ⊤ ⊤

@[simp]
theorem realize_surjective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) (x : α → M) :
    (surjective f).Realize x ↔ Function.Surjective (fun y : γ → M => f.realize (Sum.elim x y)) := by
  simp [surjective, Set.SurjOn, Function.Surjective, Set.eq_univ_iff_forall]

/-- Given `f : T.FunctionFormula (α ⊕ γ) β` and `s : L.Formula (α ⊕ γ)`, and
`t : L.Formula (α ⊕ β)`, `mapsTo f s t` is the formula whose semantics on `x : α → M` are that
the image of `f` on the set `s` is contained in `t`, when `f`, `s` and `t` are partially applied at
`x` -/
noncomputable def mapsTo [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β)
    (s : L.Formula (α ⊕ γ)) (t : L.Formula (α ⊕ β)) : L.Formula α :=
  Formula.iAlls γ (s.imp <| Formula.iAlls β (f.toFormula.imp
    (t.relabel (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr))))

@[simp]
theorem realize_mapsTo [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) (S : L.Formula (α ⊕ γ))
    (T : L.Formula (α ⊕ β)) (x : α → M) : (mapsTo f S T).Realize x ↔
      Set.MapsTo (fun y : γ → M => f.realize (Sum.elim x y))
        { y | S.Realize (Sum.elim x y) } {b | T.Realize (Sum.elim x b)} := by
  simp +contextual only [mapsTo, Function.comp_def, Formula.realize_iAlls, Formula.realize_imp,
    realize_toFormula, Sum.elim_inl, Sum.elim_inr, realize_iff_realize_eq, Formula.realize_relabel,
    forall_eq', Set.MapsTo, Set.mem_setOf_eq]
  simp +singlePass [← Sum.elim_comp_inl_inr]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]

end FunctionalFormula

open FunctionalFormula

/-- Given a `Language`, `L` and a `Theory`,  `T` we can extend `L` to a language whose function
symbols are the definable functions in the `Theory` `T` -/
def FunctionalFormulaLang : Language where
  Functions := fun n => FunctionalFormula.{u, v, 0, 0} T (Fin n) Unit
  Relations := L.Relations

namespace FunctionalFormulaLang

/-- The canonical language map from `L` to `FunctionalFormulaLang T` -/
def of : L →ᴸ FunctionalFormulaLang T where
  onFunction := fun _ f => ofTerm (func f var)
  onRelation := fun _ R => R

/-- The natural theory on `FunctionalFormulaLang T`, which includes all sentences in `T`,
as well as sentences demanding that all the function symbols we have added have the expected
semantics. -/
def theory : (FunctionalFormulaLang T).Theory :=
  (of T).onTheory T ∪
    ⋃ (n : ℕ), Set.range (fun f : FunctionalFormula T (Fin n) Unit =>
      Formula.iAlls (Fin n ⊕ Unit) <|
        ((Term.equal (func f (fun i => var (Sum.inl i))) (var (Sum.inr ()))).iff
        ((of T).onFormula f.toFormula)).relabel Sum.inr)

@[simps]
noncomputable instance : (FunctionalFormulaLang T).Structure M where
  funMap := fun f x => f.realize x ()
  RelMap := fun R => Structure.RelMap (L := L) R

instance : (of T).IsExpansionOn M where
    map_onFunction := by intros; simp [of]
    map_onRelation := by intros; simp [of]

noncomputable instance : (FunctionalFormulaLang.theory T).Model M where
  realize_of_mem := fun φ hφ => by
    simp only [theory, Set.mem_union, LHom.mem_onTheory, Set.mem_iUnion, Set.mem_range] at hφ
    rcases hφ with ⟨φ₀, hφ₀, rfl⟩ | ⟨i, hi, rfl⟩
    · simp only [LHom.realize_onSentence]
      exact realize_sentence_of_mem T hφ₀
    · simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
        Function.comp_def, Sum.elim_inr, Formula.realize_iff, Formula.realize_equal,
        Term.realize_func, Term.realize_var, instStructure_funMap, LHom.realize_onFormula,
        realize_toFormula, realize_iff_realize_eq, funext_iff]
      intro i
      refine ⟨?_, ?_⟩
      · rintro h ⟨⟩; exact h
      · intro h; exact h _

/-- Every Model of `T` is also a mode of `FunctionalFormulaLang.theory T` and vice versa.
This could be done with instances in both directions, but this would create instance diamonds.

Instead we provie instances in one direction and we provide this equivalence and then whenever it
is necessary to prove something of the form
`∀ (M : Theory.ModelType (FunctionalFormulaLang.theory T))`, we can start with
`rw [Equiv.forall_congr_left (modelTypeEquiv T).symm]` and we will then have to prove
a similar formula `∀ (M : Theory.ModelType T)`, which will also be a model of
`FunctionalFormulaLang.theory T`. This is used in the proof of
`FunctionalFormulaLang.modelsBoundedFormula_iff` -/
noncomputable def modelTypeEquiv : Theory.ModelType.{_, _, w} T ≃
    Theory.ModelType (FunctionalFormulaLang.theory T) :=
  letI i1 : ∀ (M :  ModelType.{max u v, v, w} (theory.{u, v} T)), L.Structure M := fun M =>
    { funMap := fun f x => Structure.funMap (L := FunctionalFormulaLang T)
        (ofTerm (func f var)) x
      RelMap := fun R => Structure.RelMap (L := FunctionalFormulaLang T) R }
  letI i2 : ∀ (M : ModelType.{max u v, v, w} (theory.{u, v} T)), T.Model M := fun M =>
    { realize_of_mem := by
        intro φ hφ
        simpa using (models_sentence_of_mem (T := FunctionalFormulaLang.theory T)
          (φ := (of T).onSentence φ) (Set.mem_union_left _ ⟨φ, hφ, rfl⟩)).realize_sentence M  }
  { toFun := fun M => ⟨M⟩
    invFun := fun M => ⟨M⟩
    left_inv := by
      intro M
      refine ModelType.casesOn M (fun M {S} _ _ => ?_)
      cases S
      simp only [instStructure_funMap, ModelType.mk.injEq, realize_ofTerm, Term.realize_func,
        Term.realize_var, heq_eq_eq, true_and]
      ext
      · simp [Structure.funMap]
      · simp [Structure.RelMap]
    right_inv := by
      intro M
      let _ := i1 M; let _ := i2 M
      induction M using ModelType.casesOn with
      | @mk M S _ _ =>
        simp only [eq_mp_eq_cast, instStructure, ModelType.mk.injEq, heq_eq_eq, true_and]
        ext n f x
        · have := models_sentence_of_mem (T := FunctionalFormulaLang.theory T)
            (Set.mem_union_right _ (Set.mem_iUnion.2 ⟨n, Set.mem_range.2 ⟨f, rfl⟩⟩))
          have := this.realize_formula M (v := Empty.elim)
          simp only [Formula.realize_iAlls, Formula.realize_relabel, Function.comp_def,
            Sum.elim_inr, Formula.realize_iff, Formula.realize_equal, Term.realize_func,
            Term.realize_var, LHom.realize_onFormula, realize_toFormula, realize_iff_realize_eq,
            funext_iff] at this
          have := (this (Sum.elim x (fun _ => S.funMap f x))).1 (by simp) ()
          simpa
        · simp [Structure.RelMap] }

variable {T}
/-- Proving `FunctionalFormulaLang.theory T ⊨ᵇ φ` by proving it over all models of `T`
(which are automatically models of `FunctionalFormulaLang.theory T`) instead of over
all models `M` of `FunctionalFormulaLang.theory T` (which do not have an instance of `M ⊨ T` defined
in mathlib).

It is never a good idea to unfold the definition of `ModelsBoundedFormula` to prove
`FunctionalFormulaLang.theory T ⊨ᵇ φ`, and this theorem should always be used instead. -/
theorem modelsBoundedFormula_iff {n : ℕ} {φ : T.FunctionalFormulaLang.BoundedFormula α n} :
    (FunctionalFormulaLang.theory T ⊨ᵇ φ) ↔ (∀ (M : Theory.ModelType.{_, _, max u v w} T)
      (x : α → M) (y : Fin n → M), φ.Realize x y) := by
  rw [ModelsBoundedFormula, Equiv.forall_congr_left (modelTypeEquiv T).symm]
  simp [modelTypeEquiv]

/-- Every `Term` in `FunctionalFormulaLang T` is a definable function in `T` -/
noncomputable def ofTerm : (FunctionalFormulaLang T).Term α → T.FunctionalFormula α Unit
  | Term.var x => FunctionalFormula.ofTerm (var x)
  | Term.func f x => f.comp ((toSigma (fun i => ofTerm (x i))).relabelRight (fun i => ⟨i, ()⟩))

@[simp]
theorem realize_ofTerm : ∀ (t : (FunctionalFormulaLang T).Term α) (x : α → M) (u : Unit),
    (ofTerm t).realize x u = t.realize x
  | Term.var v, x, u => by simp [ofTerm, FunctionalFormula.realize_ofTerm]
  | Term.func f x, y, u => by simp [ofTerm, Function.comp_def, realize_ofTerm]

/-- Every`BoundedFormula` in `FunctionalFormulaLang T` is equivalent to a `BoundedFormula` in `T`.
-/
noncomputable def toBoundedFormulaAux : ∀ {n : ℕ}
    (φ : (FunctionalFormulaLang T).BoundedFormula α n),
    { φ' : L.BoundedFormula α n // FunctionalFormulaLang.theory T ⊨ᵇ
        ((of T).onBoundedFormula φ').iff φ }
  | _, BoundedFormula.falsum => ⟨BoundedFormula.falsum, by
    simp [ModelsBoundedFormula, BoundedFormula.Realize]⟩
  | _, @BoundedFormula.equal _ _ n t₁ t₂ =>
    ⟨BoundedFormula.relabel id ((ofTerm t₁).equal (ofTerm t₂)), by
      simp [modelsBoundedFormula_iff, Formula.boundedFormula_realize_eq_realize, funext_iff,
          BoundedFormula.Realize]⟩
  | _, @BoundedFormula.rel _ _ m n R x =>
      let φ := (BoundedFormula.rel (L := L) (n := n) (α := Empty) (R : L.Relations n)
        (fun i => (var (Sum.inr i)))).toFormula
      ⟨BoundedFormula.relabel id <| rel φ ((toSigma (ofTerm ∘ x)).relabelRight (
          Sum.elim Empty.elim (fun i => ⟨i, ()⟩))), by
        simp [φ, Formula.boundedFormula_realize_eq_realize, funext_iff,
          BoundedFormula.Realize, modelsBoundedFormula_iff]⟩
  | _, BoundedFormula.imp φ₁ φ₂ =>
      let ψ₁ := toBoundedFormulaAux φ₁
      let ψ₂ := toBoundedFormulaAux φ₂
      ⟨ψ₁.1.imp ψ₂.1, by
          have h1 := modelsBoundedFormula_iff.1 ψ₁.2
          have h2 := modelsBoundedFormula_iff.1 ψ₂.2
          simp only [BoundedFormula.realize_iff, LHom.realize_onBoundedFormula] at h1 h2
          simp [modelsBoundedFormula_iff, BoundedFormula.Realize, h1, h2]⟩
  | _, BoundedFormula.all φ =>
      let ψ := toBoundedFormulaAux φ
      ⟨ψ.1.all, by
        have h := modelsBoundedFormula_iff.1 ψ.2
        simp only [BoundedFormula.realize_iff, LHom.realize_onBoundedFormula] at h
        simp [modelsBoundedFormula_iff, BoundedFormula.Realize, h]⟩

/-- Every`BoundedFormula` in `FunctionalFormulaLang T` is equivalent to a `BoundedFormula` in `T`.
-/
noncomputable def toBoundedFormula {n : ℕ} (φ : (FunctionalFormulaLang T).BoundedFormula α n) :
    L.BoundedFormula α n :=
  (toBoundedFormulaAux φ).1

@[simp]
theorem realize_toBoundedFormula {n : ℕ} (φ : (FunctionalFormulaLang T).BoundedFormula α n)
    (x : α → M) (y : Fin n → M) : (toBoundedFormula φ).Realize x y ↔ φ.Realize x y := by
  have := ((toBoundedFormulaAux φ).2).realize_boundedFormula M (xs := y) (v := x)
  simpa

/-- Every `Formula` in `FunctionalFormulaLang T` is equivalent to a `Formula` in `T`. -/
noncomputable def toFormula (φ : (FunctionalFormulaLang T).Formula α) : L.Formula α :=
  toBoundedFormula φ

@[simp]
theorem realize_toFormula (φ : (FunctionalFormulaLang T).Formula α) (x : α → M) :
    (toFormula φ).Realize x ↔ φ.Realize x := by
  simp [toFormula, Formula.Realize]

/-- Every `Sentence` in `FunctionalFormulaLang T` is equivalent to a `Sentence` in `T`. -/
noncomputable def toSentence (φ : (FunctionalFormulaLang T).Sentence) : L.Sentence :=
  toFormula φ

@[simp]
theorem realize_toSentence (φ : (FunctionalFormulaLang T).Sentence) :
    M ⊨ toSentence φ ↔ M ⊨ φ := by
  simp [toSentence, Sentence.Realize]

end FunctionalFormulaLang

end Theory

end Language

end FirstOrder
