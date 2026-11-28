/-
Copyright (c) 2024 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.ModelTheory.Equivalence

/-!
# Definable functions in a first-order theory

A formula in variables `α ⊕ β` defines a function if every model of the theory has exactly
one output tuple `β → M` for each input tuple `α → M`. The type
`FirstOrder.Language.Theory.FunctionalFormula` consists of the semantic equivalence classes
of such formulas. The output index type `β` is finite.

* `FunctionalFormula.Realize` interprets the graph in a model. `FunctionalFormula.realize`
  evaluates the corresponding function.
* `FunctionalFormula.comp` composes definable functions. The formulas `FunctionalFormula.injOn`,
  `FunctionalFormula.surjOn` and `FunctionalFormula.mapsTo` express properties of their values.
* `FunctionalFormulaLang` adjoins a symbol for each definable function with one output.
  `FunctionalFormulaLang.toBoundedFormula` translates formulas back to the original language.

## TODO

Translate functional formulas along extensions of languages and theories.
-/

@[expose] public section

universe u v w x y z

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) {α : Type w} {β : Type x} {γ : Type y}
variable [Finite β] {M : Type z} [L.Structure M] [T.Model M] [Nonempty M]

variable {T} in
/-- Equivalent graphs remain equivalent after quantifying a unique tuple of outputs. -/
protected theorem Iff.iExsUnique {φ ψ : L.Formula (α ⊕ β)} (h : φ ⇔[T] ψ) :
    φ.iExsUnique β ⇔[T] ψ.iExsUnique β := by
  intro M v xs
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_iExsUnique,
    BoundedFormula.realize_iExsUnique]
  exact existsUnique_congr fun _ => h.realize_iff

/-- A functional formula is an equivalence class of formulas whose graph gives a unique
tuple of outputs for each input in every model of the theory. -/
def FunctionalFormula (α : Type w) (β : Type x) [Finite β] :=
  {q : Quotient (T.iffSetoid (α := α ⊕ β) (n := 0)) //
    q.liftOn (fun φ => T ⊨ᵇ Formula.iExsUnique β φ) (by
      intro φ ψ h
      apply propext
      simp only [models_formula_iff]
      exact forall_congr' fun _ => forall_congr' fun _ => (Iff.iExsUnique h).realize_iff)}

namespace FunctionalFormula

variable {T}

/-- Construct a functional formula from a graph and its unique-output property. -/
def mk (φ : L.Formula (α ⊕ β)) (h : T ⊨ᵇ Formula.iExsUnique β φ) : T.FunctionalFormula α β :=
  ⟨Quotient.mk _ φ, h⟩

/-- The graph of a functional formula in a model of the theory. -/
def Realize (f : T.FunctionalFormula α β) (x : α → M) (y : β → M) : Prop :=
  f.val.liftOn (fun φ => Formula.Realize φ (Sum.elim x y)) fun _ _ h => propext (Iff.realize_iff h)

/-- A representative formula for a definable function. -/
noncomputable def toFormula (f : T.FunctionalFormula α β) : L.Formula (α ⊕ β) := f.val.out

@[simp]
theorem realize_toFormula (f : T.FunctionalFormula α β) (x : α ⊕ β → M) :
    f.toFormula.Realize x ↔ f.Realize (x ∘ Sum.inl) (x ∘ Sum.inr) := by
  unfold Realize toFormula
  simp only [Sum.elim_comp_inl_inr]
  conv_rhs => rw [← f.val.out_eq]
  rfl

theorem toFormula_spec (f : T.FunctionalFormula α β) : T ⊨ᵇ Formula.iExsUnique β f.toFormula := by
  have h := f.property
  rw [← f.val.out_eq] at h
  exact h

@[simp]
theorem realize_mk (φ : L.Formula (α ⊕ β)) (h : T ⊨ᵇ Formula.iExsUnique β φ) (x : α → M)
    (y : β → M) : (mk φ h).Realize x y ↔ φ.Realize (Sum.elim x y) :=
  Iff.rfl

theorem existsUnique_realize (f : T.FunctionalFormula α β) (x : α → M) :
    ∃! y : β → M, f.Realize x y := by
  have h := f.toFormula_spec.realize_formula M (v := x)
  simpa only [Formula.realize_iExsUnique, realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr]
    using h

/-- The function defined by a functional formula in a model of the theory. -/
noncomputable def realize (f : T.FunctionalFormula α β) (x : α → M) : β → M :=
  (existsUnique_realize f x).exists.choose

theorem realize_iff_realize_eq {f : T.FunctionalFormula α β} {x : α → M} {y : β → M} :
    f.Realize x y ↔ f.realize x = y := by
  have hy := (existsUnique_realize f x).exists.choose_spec
  exact ⟨fun h => (existsUnique_realize f x).unique hy h, fun h => h ▸ hy⟩

@[ext]
theorem ext {f g : T.FunctionalFormula α β}
    (h : ∀ (M : Theory.ModelType.{_, _, max u v w x} T) (x : α → M), f.realize x = g.realize x) :
    f = g := by
  apply Subtype.ext
  rw [← f.val.out_eq, ← g.val.out_eq]
  apply Quotient.sound
  change T ⊨ᵇ f.toFormula.iff g.toFormula
  rw [models_formula_iff]
  intro M v
  rw [Formula.realize_iff, realize_toFormula, realize_toFormula,
    realize_iff_realize_eq, realize_iff_realize_eq, h]

/-- The function with one output coordinate given by the term `t`. -/
def ofTerm (t : L.Term α) : T.FunctionalFormula α Unit :=
  mk (Term.equal (t.relabel Sum.inl) (var (Sum.inr ())))
  (by
    simp only [ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, Formula.realize_equal,
      Term.realize_relabel, Sum.elim_comp_inl, Term.realize_var, Sum.elim_inr, forall_const]
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
/-- The function on tuples obtained by precomposing with `f`. -/
noncomputable def comap (f : β → α) : T.FunctionalFormula α β :=
  mk (Formula.iAlls β <|
    (Formula.iInf
      (fun b => Term.equal (var (Sum.inr b)) (var (Sum.inl (f b))))).relabel Sum.inl) <| by
  simp only [models_formula_iff, Formula.realize_iExsUnique, Formula.realize_iAlls,
    Formula.realize_relabel, Sum.elim_comp_inl, Formula.realize_iInf, Formula.realize_equal,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, forall_const]
  intro M x
  use fun y => x (f y)
  simp [funext_iff]

variable {T} in
@[simp]
theorem realize_comap (f : β → α) (x : α → M) : (comap T f).realize x = x ∘ f := by
  rw [← realize_iff_realize_eq]; simp [comap]

/-- The identity on tuples indexed by `β`. -/
protected noncomputable def id : T.FunctionalFormula β β :=
  comap T id

@[simp]
theorem realize_id (x : β → M) :
    (FunctionalFormula.id T).realize (T := T) (M := M) x = x := by
  simp [FunctionalFormula.id]

variable {T}
/-- Compose two definable functions. -/
noncomputable def comp [Finite γ] (f : T.FunctionalFormula β γ) (g : T.FunctionalFormula α β) :
    T.FunctionalFormula α γ :=
  mk (Formula.iExs β
    (f.toFormula.relabel (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)) ⊓
     g.toFormula.relabel (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr))) <| by
  simp only [ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, Formula.realize_iExs,
    Formula.realize_inf, Formula.realize_relabel, forall_const]
  intro M x
  use f.realize (g.realize x)
  simp only [Function.comp_def, forall_exists_index]
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
  simp only [comp, Function.comp_def, realize_mk, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_relabel, realize_toFormula, Sum.elim_inl, Sum.elim_inr]
  use g.realize x
  simp [realize_iff_realize_eq]

/-- Relabel the input coordinates of a definable function. -/
noncomputable def relabelLeft (f : α → γ) (g : T.FunctionalFormula α β) : T.FunctionalFormula γ β :=
  mk (g.toFormula.relabel (Sum.map f id)) <| by
    simp only [Sum.map, Function.comp_def, models_formula_iff, Formula.realize_iExsUnique,
      Formula.realize_relabel, realize_toFormula, Sum.elim_inl, Sum.elim_inr,
      realize_iff_realize_eq, funext_iff]
    intro M v
    simpa only [Function.comp_def, Formula.realize_iExsUnique, id_eq, realize_toFormula,
      Sum.elim_inl, Sum.elim_inr, realize_iff_realize_eq, funext_iff] using
      g.toFormula_spec.realize_formula (v := v ∘ f)

@[simp]
theorem realize_relabelLeft (f : α → γ) (g : T.FunctionalFormula α β) (x : γ → M) :
    (relabelLeft f g).realize x = g.realize (x ∘ f) := by
  simp only [relabelLeft, Sum.map, Function.comp_def, ← realize_iff_realize_eq, realize_mk,
    Formula.realize_relabel, realize_toFormula, Sum.elim_inl, Sum.elim_inr]
  rw [realize_iff_realize_eq]
  simp

/-- Relabel the output coordinates of a definable function. -/
noncomputable def relabelRight [Finite γ] (f : γ → β) (g : T.FunctionalFormula α β) :
    T.FunctionalFormula α γ :=
  (comap T f).comp g

@[simp]
theorem realize_relabelRight [Finite γ] (f : γ → β) (g : T.FunctionalFormula α β) (x : α → M) :
    (relabelRight f g).realize x = g.realize x ∘ f := by
  simp [relabelRight, Function.comp_def]

/-- Combine the output tuples of a finite family of definable functions into a single tuple. -/
noncomputable def toSigma {γ : β → Type y} [∀ b, Finite (γ b)]
    (f : (b : β) → T.FunctionalFormula α (γ b)) :
    T.FunctionalFormula α (Sigma γ) :=
  mk (Formula.iInf
    (fun b => (f b).toFormula.relabel (Sum.elim Sum.inl (fun g => Sum.inr ⟨_, g⟩)))) <| by
  simp only [models_formula_iff, Formula.realize_iExsUnique, Formula.realize_iInf,
    Formula.realize_relabel, Function.comp_def, realize_toFormula, Sum.elim_inl, Sum.elim_inr]
  intro M x
  use (fun i : Σ b, γ b => (f i.1).realize x i.2)
  simp +contextual [realize_iff_realize_eq]

@[simp]
theorem realize_toSigma {γ : β → Type y} [∀ b, Finite (γ b)]
    (f : (b : β) → T.FunctionalFormula α (γ b)) (x : α → M) :
    (toSigma f).realize x = fun i => (f i.1).realize x i.2 := by
  simp only [toSigma, ← realize_iff_realize_eq, realize_mk, Formula.realize_iInf,
    Formula.realize_relabel, Function.comp_def, realize_toFormula, Sum.elim_inl, Sum.elim_inr]
  simp only [realize_iff_realize_eq, implies_true]

/-- Pair the outputs of two definable functions with the same inputs. -/
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

/-- Pull back the predicate `φ` along the definable function `f`. -/
noncomputable def rel (φ : L.Formula β) (f : T.FunctionalFormula α β) : L.Formula α :=
  Formula.iAlls β (f.toFormula.imp (φ.relabel Sum.inr))

@[simp]
theorem realize_rel (φ : L.Formula β) (f : T.FunctionalFormula α β) (x : α → M) :
    (rel φ f).Realize x ↔ φ.Realize (f.realize x) := by
  simp [rel, realize_iff_realize_eq]

/-- Apply a predicate to the pair of outputs of `f` and `g`. -/
noncomputable def rel2 [Finite γ] (φ : L.Formula (β ⊕ γ))
    (f : T.FunctionalFormula α β) (g : T.FunctionalFormula α γ) :
    L.Formula α :=
  Formula.iAlls (β ⊕ γ) ((toSum f g).toFormula.imp (φ.relabel Sum.inr))

@[simp]
theorem realize_rel2 [Finite γ] (φ : L.Formula (β ⊕ γ))
    (f : T.FunctionalFormula α β) (g : T.FunctionalFormula α γ) (x : α → M) :
    (rel2 φ f g).Realize x ↔ φ.Realize (Sum.elim (f.realize x) (g.realize x)) := by
  simp [rel2, realize_iff_realize_eq]

/-- The predicate that two definable functions have the same output. -/
noncomputable def equal (f g : T.FunctionalFormula α β) : L.Formula α :=
  rel2 (Formula.iInf
    (fun b => Term.equal (var (Sum.inl b)) (var (Sum.inr b))))
    f g

@[simp]
theorem realize_equal (f g : T.FunctionalFormula α β) (x : α → M) :
    (equal f g).Realize x ↔ f.realize x = g.realize x := by
  simp [equal, funext_iff]

/-- After fixing the parameters `α`, the function is injective on the set defined by `s`. -/
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
    Formula.realize_relabel, realize_equal, realize_relabelLeft, funext_iff, Sum.forall_sum,
    Set.InjOn, Set.mem_ofPred_eq]
  simp +singlePass [← Sum.elim_comp_inl_inr]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  tauto

/-- After fixing the parameters `α`, the resulting function is injective. -/
noncomputable def injective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) : L.Formula α :=
  injOn f ⊤

@[simp]
theorem realize_injective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) (x : α → M) :
    (injective f).Realize x ↔ Function.Injective
      (fun y : γ → M => f.realize (Sum.elim x y)) := by
  simp [injective, Set.InjOn, Function.Injective]

/-- After fixing the parameters `α`, the image of the set defined by `s` contains the set
defined by `t`. -/
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
    Set.mem_ofPred_eq, Set.mem_image]
  simp +singlePass [← Sum.elim_comp_inl_inr]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]

/-- After fixing the parameters `α`, the resulting function is surjective. -/
noncomputable def surjective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) : L.Formula α :=
  surjOn f ⊤ ⊤

@[simp]
theorem realize_surjective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) (x : α → M) :
    (surjective f).Realize x ↔ Function.Surjective (fun y : γ → M => f.realize (Sum.elim x y)) := by
  simp [surjective, Set.SurjOn, Function.Surjective, Set.eq_univ_iff_forall]

/-- After fixing the parameters `α`, the function maps the set defined by `s` into the set
defined by `t`. -/
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
    forall_eq', Set.MapsTo, Set.mem_ofPred_eq]
  simp +singlePass [← Sum.elim_comp_inl_inr]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]

end FunctionalFormula

open FunctionalFormula

/-- The language whose function symbols are the definable functions of `T` and whose relation
symbols are those of the original language. -/
def FunctionalFormulaLang : Language where
  Functions := fun n => FunctionalFormula.{u, v, 0, 0} T (Fin n) (Fin 1)
  Relations := L.Relations

namespace FunctionalFormulaLang

/-- The canonical language map from `L` to `FunctionalFormulaLang T`. -/
noncomputable def of : L →ᴸ FunctionalFormulaLang T where
  onFunction := fun _ f => (ofTerm (func f var)).relabelRight (fun _ : Fin 1 => ())
  onRelation := fun _ R => R

/-- The image of `T` together with axioms identifying each new function symbol with its
defining graph. -/
noncomputable def theory : (FunctionalFormulaLang T).Theory :=
  (of T).onTheory T ∪
    ⋃ (n : ℕ), Set.range (fun f : FunctionalFormula T (Fin n) (Fin 1) =>
      Formula.iAlls (Fin n ⊕ Fin 1) <|
        ((Term.equal (func f (fun i => var (Sum.inl i))) (var (Sum.inr 0))).iff
        ((of T).onFormula f.toFormula)).relabel Sum.inr)

@[simps]
noncomputable instance : (FunctionalFormulaLang T).Structure M where
  funMap := fun f x => f.realize x 0
  RelMap := fun R => Structure.RelMap (L := L) R

instance : (of T).IsExpansionOn M where
  map_onFunction := by
    intro n f x
    change ((FunctionalFormula.ofTerm (func f var)).relabelRight
      (fun _ : Fin 1 => ())).realize x 0 = _
    simp [FunctionalFormula.realize_ofTerm, FunctionalFormula.realize_relabelRight]
  map_onRelation := by intros; rfl

noncomputable instance : (FunctionalFormulaLang.theory T).Model M where
  realize_of_mem := fun φ hφ => by
    simp only [theory, Set.mem_union, LHom.mem_onTheory, Set.mem_iUnion, Set.mem_range] at hφ
    rcases hφ with ⟨φ₀, hφ₀, rfl⟩ | ⟨i, hi, rfl⟩
    · simp only [LHom.realize_onSentence]
      exact realize_sentence_of_mem T hφ₀
    · simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
      Function.comp_def, Sum.elim_inr, Formula.realize_iff, Formula.realize_equal,
      Term.realize_var, LHom.realize_onFormula, realize_toFormula,
      realize_iff_realize_eq, funext_iff]
      intro i
      refine ⟨?_, ?_⟩
      · intro h j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        exact h
      · intro h; exact h _

/-- Expanding a model of `T` by its definable functions is inverse to taking its reduct along
`FunctionalFormulaLang.of`. Both operations preserve the carrier. -/
noncomputable def modelTypeEquiv : Theory.ModelType.{_, _, w} T ≃
    Theory.ModelType (FunctionalFormulaLang.theory T) :=
  letI i1 : ∀ (M : ModelType.{max u v, v, w} (theory T)), L.Structure M :=
    fun M => (of T).reduct M
  letI i2 : ∀ (M : ModelType.{max u v, v, w} (theory.{u, v} T)), T.Model M := fun M =>
    { realize_of_mem := by
        intro φ hφ
        simpa using (models_sentence_of_mem (T := FunctionalFormulaLang.theory T)
          (φ := (of T).onSentence φ) (Set.mem_union_left _ ⟨φ, hφ, rfl⟩)).realize_sentence
          M }
  { toFun := fun M => ⟨M⟩
    invFun := fun M => ⟨M⟩
    left_inv := by
      intro M
      refine ModelType.casesOn M (fun M {_} _ _ => ?_)
      simp only [ModelType.mk.injEq, heq_eq_eq, true_and]
      ext n f x
      · exact (of T).map_onFunction (M := M) f x
      · rfl
    right_inv := by
      intro M
      let _ := i1 M
      let _ := i2 M
      induction M using ModelType.casesOn with
      | @mk M S _ _ =>
        simp only [ModelType.mk.injEq, heq_eq_eq, true_and]
        ext n f x
        · have := models_sentence_of_mem (T := FunctionalFormulaLang.theory T)
            (Set.mem_union_right _ (Set.mem_iUnion.2 ⟨n, Set.mem_range.2 ⟨f, rfl⟩⟩))
          have := this.realize_formula M (v := Empty.elim)
          simp only [Formula.realize_iAlls, Formula.realize_relabel, Function.comp_def,
            Sum.elim_inr, Formula.realize_iff, Formula.realize_equal, Term.realize_func,
            Term.realize_var, LHom.realize_onFormula] at this
          change T.FunctionalFormula (Fin n) (Fin 1) at f
          have hg := (this (Sum.elim x (fun _ => S.funMap f x))).1 (by simp)
          have hr : f.Realize x (fun _ => S.funMap f x) :=
            (FunctionalFormula.realize_toFormula f _).1 hg
          exact congrFun (realize_iff_realize_eq.1 hr) 0
        · rfl }

variable {T}

/-- A bounded formula holds in the expanded theory iff it holds in the canonical expansion of
every model of `T`. -/
theorem modelsBoundedFormula_iff {n : ℕ} {φ : T.FunctionalFormulaLang.BoundedFormula α n} :
    (FunctionalFormulaLang.theory T ⊨ᵇ φ) ↔ (∀ (M : Theory.ModelType.{_, _, max u v w} T)
      (x : α → M) (y : Fin n → M), φ.Realize x y) := by
  rw [ModelsBoundedFormula, Equiv.forall_congr_left (modelTypeEquiv T).symm]
  rfl

/-- Interpret a term of the expanded language as a definable function of `T`. -/
noncomputable def ofTerm : (FunctionalFormulaLang T).Term α → T.FunctionalFormula α Unit
  | Term.var x => FunctionalFormula.ofTerm (var x)
  | Term.func f x => (f.relabelRight (fun _ : Unit => (0 : Fin 1))).comp
      ((toSigma (fun i => ofTerm (x i))).relabelRight (fun i => ⟨i, ()⟩))

@[simp]
theorem realize_ofTerm : ∀ (t : (FunctionalFormulaLang T).Term α) (x : α → M) (u : Unit),
    (ofTerm t).realize x u = t.realize x
  | Term.var v, x, u => by simp [ofTerm, FunctionalFormula.realize_ofTerm]
  | Term.func f x, y, u => by
    change T.FunctionalFormula (Fin _) (Fin 1) at f
    cases u
    change (comp _ _).realize y () = f.realize _ 0
    simp [FunctionalFormula.realize_comp, FunctionalFormula.realize_relabelRight,
      FunctionalFormula.realize_toSigma, Function.comp_def, realize_ofTerm]

/-- Translate a bounded formula of the expanded language to an equivalent bounded formula of
the original language. -/
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
        simp only [BoundedFormula.toFormula, modelsBoundedFormula_iff, BoundedFormula.realize_iff,
          LHom.realize_onBoundedFormula, BoundedFormula.realize_relabel, Nat.add_zero,
          Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
          Formula.boundedFormula_realize_eq_realize, realize_rel, realize_relabelRight,
          realize_toSigma, Function.comp_apply, realize_ofTerm, BoundedFormula.Realize, RelMap_def,
          φ]
        intro M a v
        change L.Relations n at R
        rw [Formula.realize_rel]
        rfl⟩
  | _, BoundedFormula.imp φ₁ φ₂ =>
      let ψ₁ := toBoundedFormulaAux φ₁
      let ψ₂ := toBoundedFormulaAux φ₂
      ⟨ψ₁.val.imp ψ₂.val, by
          have h1 := modelsBoundedFormula_iff.1 ψ₁.property
          have h2 := modelsBoundedFormula_iff.1 ψ₂.property
          simp only [BoundedFormula.realize_iff, LHom.realize_onBoundedFormula] at h1 h2
          simp [modelsBoundedFormula_iff, BoundedFormula.Realize, h1, h2]⟩
  | _, BoundedFormula.all φ =>
      let ψ := toBoundedFormulaAux φ
      ⟨ψ.val.all, by
        have h := modelsBoundedFormula_iff.1 ψ.property
        simp only [BoundedFormula.realize_iff, LHom.realize_onBoundedFormula] at h
        simp [modelsBoundedFormula_iff, BoundedFormula.Realize, h]⟩

/-- Translate a bounded formula of the expanded language to an equivalent bounded formula of
the original language. -/
noncomputable def toBoundedFormula {n : ℕ} (φ : (FunctionalFormulaLang T).BoundedFormula α n) :
    L.BoundedFormula α n :=
  (toBoundedFormulaAux φ).val

@[simp]
theorem realize_toBoundedFormula {n : ℕ} (φ : (FunctionalFormulaLang T).BoundedFormula α n)
    (x : α → M) (y : Fin n → M) : (toBoundedFormula φ).Realize x y ↔ φ.Realize x y := by
  have := ((toBoundedFormulaAux φ).property).realize_boundedFormula M (xs := y) (v := x)
  simpa

/-- Translate a formula of the expanded language to a formula of the original language. -/
noncomputable def toFormula (φ : (FunctionalFormulaLang T).Formula α) : L.Formula α :=
  toBoundedFormula φ

@[simp]
theorem realize_toFormula (φ : (FunctionalFormulaLang T).Formula α) (x : α → M) :
    (toFormula φ).Realize x ↔ φ.Realize x := by
  simp [toFormula, Formula.Realize]

/-- Translate a sentence of the expanded language to a sentence of the original language. -/
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
