/-
Copyright (c) 2024 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed

universe u v w x y z

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) {α : Type w} {β : Type x} {γ : Type y}
variable [Finite β] {M : Type z} [L.Structure M] [T.Model M] [Nonempty M]

def FunctionalFormula (α : Type w) (β : Type x) [Finite β] : Type _ :=
  { φ : L.Formula (α ⊕ β) // T ⊨ᵇ Formula.iExsUnique id φ }

namespace FunctionalFormula

variable {T}

theorem exists_fun_eq_iff (f : T.FunctionalFormula α β) : ∃ f' : (α → M) → (β → M),
    ∀ x, ∀ y, f' x = y ↔ f.1.Realize (Sum.elim x y) := by
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

noncomputable def realize (f : T.FunctionalFormula α β) : (α → M) → (β → M) :=
  Classical.choose (f.exists_fun_eq_iff)

theorem realize_spec {f : T.FunctionalFormula α β} {x : α → M} {y : β → M} :
    f.realize x = y ↔ f.1.Realize (Sum.elim x y) :=
  Classical.choose_spec (f.exists_fun_eq_iff) x y

theorem realize_spec' {f : T.FunctionalFormula α β} {x : α ⊕ β → M} :
    f.1.Realize x ↔ f.realize (x ∘ Sum.inl) = x ∘ Sum.inr := by
  rw [realize_spec]; simp

theorem realize_spec2 {f : T.FunctionalFormula α β} {x : α ⊕ β → M} {y : Fin 0 → M} :
    BoundedFormula.Realize f.1 x y ↔ f.realize (x ∘ Sum.inl) = x ∘ Sum.inr := by
  rw [← realize_spec', Formula.Realize, iff_iff_eq]
  congr; ext x; exact Fin.elim0 x

def ofTerm (t : L.Term α) : T.FunctionalFormula α Unit :=
  ⟨Term.equal (t.relabel Sum.inl) (var (Sum.inr ())), by
    simp only [ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, id_eq,
      Formula.realize_equal, Term.realize_relabel, Sum.elim_comp_inl, Term.realize_var,
      Sum.elim_inr, forall_const]
    intro M x
    use fun _ => t.realize x
    simp +contextual [funext_iff, eq_comm]⟩

@[simp]
theorem realize_ofTerm (t : L.Term α) (x : α → M) :
    (ofTerm (T := T) t).realize x = fun _ => t.realize x := by
  rw [realize_spec]
  simp [ofTerm, Formula.Realize, Term.realize_relabel, Term.realize_var, Term.equal,
    Function.comp_def]

variable (T)
noncomputable def comap (f : β → α) : T.FunctionalFormula α β :=
  let e := Fintype.ofFinite β
  ⟨Formula.iAlls (γ := β) Sum.inl
    (Formula.iInf (Finset.univ : Finset β)
      (fun b => Term.equal (var (Sum.inr b)) (var (Sum.inl (f b))))), by
  simp only [models_formula_iff, Formula.realize_iExsUnique, id_eq, Formula.realize_iAlls,
    Sum.elim_inl, forall_const, Formula.realize_iInf]
  intro M x
  use fun y => x (f y)
  simp [Formula.Realize, Term.equal, funext_iff]⟩

variable {T}
@[simp]
theorem realize_comap (f : β → α) (x : α → M) : (comap T f).realize x = x ∘ f := by
  rw [realize_spec]; simp [comap]

variable (T)
protected noncomputable def id : T.FunctionalFormula β β :=
  comap T id

@[simp]
theorem realize_id (x : β → M) :
    (FunctionalFormula.id T).realize (T := T) (M := M) x = x := by
  simp [FunctionalFormula.id]

variable {T}
noncomputable def comp [Finite γ] (f : T.FunctionalFormula β γ) (g : T.FunctionalFormula α β) :
    T.FunctionalFormula α γ :=
  ⟨Formula.iExs (α := (α ⊕ γ) ⊕ β) (γ := β) id
    (f.1.relabel (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)) ⊓
     g.1.relabel (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)), by
  simp only [ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, id_eq, Formula.realize_iExs,
    Formula.realize_inf, Formula.realize_relabel, forall_const]
  intro M x
  use f.realize (g.realize x)
  simp only [Function.comp_def, Formula.realize_iExs, id_eq, Formula.realize_relabel,
    forall_exists_index]
  refine ⟨?_, ?_⟩
  · use g.realize x
    simp [realize_spec', Function.comp_def]
  · intro y z
    simp only [realize_spec', Function.comp_def, Sum.elim_inl, Sum.elim_inr, funext_iff, and_imp]
    intro h1 h2 g
    simp only [← h1, ← h2]⟩

@[simp]
theorem realize_comp [Finite γ] (f : T.FunctionalFormula β γ) (g : T.FunctionalFormula α β)
    (x : α → M) : (f.comp g).realize x = f.realize (g.realize x) := by
  rw [realize_spec]
  simp only [comp, Function.comp_def, Formula.realize_iExs, id_eq, Formula.realize_inf,
    Formula.realize_relabel]
  use g.realize x
  simp [Function.comp_def, realize_spec']

def relabelLeft (f : α → γ) (g : T.FunctionalFormula α β) : T.FunctionalFormula γ β :=
  ⟨g.1.relabel (Sum.map f id), by
    simp only [Sum.map, Function.comp_def, CompTriple.comp_eq, models_formula_iff,
      Formula.realize_iExsUnique, id_eq, Formula.realize_relabel, realize_spec', Sum.elim_inl,
      Sum.elim_inr, funext_iff]
    intro M v
    simpa only [Function.comp_def, Formula.realize_iExsUnique, id_eq, realize_spec', Sum.elim_inl,
      Sum.elim_inr, funext_iff] using g.2.realize_formula M (v := v ∘ f)⟩

@[simp]
theorem realize_relabelLeft (f : α → γ) (g : T.FunctionalFormula α β) (x : γ → M) :
    (relabelLeft f g).realize x = g.realize (x ∘ f) := by
  simp only [relabelLeft, Sum.map, Function.comp_def, CompTriple.comp_eq, realize_spec,
    Formula.realize_relabel]
  rw [realize_spec']
  simp [funext_iff, Function.comp_def]

noncomputable def relabelRight [Finite γ] (f : γ → β) (g : T.FunctionalFormula α β) :
    T.FunctionalFormula α γ :=
  (comap T f).comp g

@[simp]
theorem realize_relabelRight [Finite γ] (f : γ → β) (g : T.FunctionalFormula α β) (x : α → M) :
    (relabelRight f g).realize x = g.realize x ∘ f := by
  simp only [relabelRight, realize_comp, realize_comap, Function.comp_def]

noncomputable def toSigma {γ : β → Type y} [∀ b, Finite (γ b)]
    (f : ∀ b, T.FunctionalFormula α (γ b)) :
    T.FunctionalFormula α (Σ b, γ b) :=
  let e := Fintype.ofFinite β
  ⟨Formula.iInf (Finset.univ : Finset β)
    (fun b => (f b).1.relabel (Sum.elim Sum.inl (fun g => Sum.inr ⟨_, g⟩))), by
  simp only [models_formula_iff, Formula.realize_iExsUnique, id_eq, forall_const]
  intro M x
  use (fun i : Σ b, γ b => (f i.1).realize x i.2)
  simp only [Formula.realize_iInf, Finset.mem_univ, Formula.realize_relabel, Function.comp_def,
    realize_spec', Sum.elim_inl, Sum.elim_inr, imp_self, implies_true, funext_iff, forall_const,
    true_and]
  intro y h z
  cases z
  rw [h]⟩

@[simp]
theorem realize_toSigma {γ : β → Type y} [∀ b, Finite (γ b)]
    (f : ∀ b, T.FunctionalFormula α (γ b)) (x : α → M) :
    (toSigma f).realize x = fun i => (f i.1).realize x i.2 := by
  rw [realize_spec]
  simp only [toSigma, Formula.realize_iInf, Finset.mem_univ, Formula.realize_relabel,
    Function.comp_def, realize_spec', Sum.elim_inl, Sum.elim_inr, imp_self, implies_true]

noncomputable def rel {γ : β → Type y} [∀ b, Finite (γ b)] (φ : L.Formula (Sigma γ))
    (f : ∀ b, T.FunctionalFormula α (γ b)) : L.Formula α :=
  Formula.iAlls id ((toSigma f).1.imp (φ.relabel Sum.inr))

@[simp]
theorem realize_rel {γ : β → Type y} [∀ b, Finite (γ b)] (φ : L.Formula (Sigma γ))
    (f : ∀ b, T.FunctionalFormula α (γ b)) (x : α → M) :
    (rel φ f).Realize x ↔ φ.Realize (fun b => (f b.1).realize x b.2) := by
  simp [rel, realize_spec']

noncomputable def equal (f g : T.FunctionalFormula α β) : L.Formula α :=
  let _ := Fintype.ofFinite β
  rel (Formula.iInf (Finset.univ : Finset β)
    (fun b => Term.equal (var ⟨true, b⟩) (var ⟨false, b⟩)))
    (fun b : Bool => if b then f else g)

@[simp]
theorem realize_equal (f g : T.FunctionalFormula α β) (x : α → M) :
    (equal f g).Realize x ↔ f.realize x = g.realize x := by
  simp [equal, funext_iff]

end FunctionalFormula

open FunctionalFormula

def FunctionalFormulaLang : Language where
  Functions := fun n => FunctionalFormula.{u, v, 0, 0} T (Fin n) Unit
  Relations := L.Relations

namespace FunctionalFormulaLang

def of : L →ᴸ FunctionalFormulaLang T where
  onFunction := fun _ f => ofTerm (func f var)
  onRelation := fun _ R => R

def theory : (FunctionalFormulaLang T).Theory :=
  (of T).onTheory T ∪
    ⋃ (n : ℕ), Set.range (fun f : FunctionalFormula T (Fin n) Unit =>
      Formula.iAlls (γ := Fin n ⊕ Unit) Sum.inr <|
        (Term.equal (func f (fun i => var (Sum.inl i))) (var (Sum.inr ()))).iff
        ((of T).onFormula f.1))

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
    · simp only [Sentence.Realize, Formula.realize_iAlls, Sum.elim_inr, Formula.realize_iff,
        Formula.realize_equal, Term.realize_func, Term.realize_var, instStructure_funMap,
        LHom.realize_onFormula, realize_spec', Function.comp_def, funext_iff]
      intro i
      refine ⟨?_, ?_⟩
      · rintro h ⟨⟩; exact h
      · intro h; exact h _

variable {T}
noncomputable def ofTerm : (FunctionalFormulaLang T).Term α → T.FunctionalFormula α Unit
  | Term.var x => FunctionalFormula.ofTerm (var x)
  | Term.func f x => f.comp ((toSigma (fun i => ofTerm (x i))).relabelRight (fun i => ⟨i, ()⟩))

@[simp]
theorem realize_ofTerm : ∀ (t : (FunctionalFormulaLang T).Term α) (x : α → M) (u : Unit),
    (ofTerm t).realize x u = t.realize x
  | Term.var v, x, u => by simp [ofTerm, FunctionalFormula.realize_ofTerm]
  | Term.func f x, y, u => by simp [ofTerm, Function.comp_def, realize_ofTerm]

noncomputable def toBoundedFormulaAux : ∀ {n : ℕ}
    (φ : (FunctionalFormulaLang T).BoundedFormula α n),
    { φ' : L.BoundedFormula α n // ∀ (M : Theory.ModelType.{_, _, max u v} T)
        (x : α → M) (y : Fin n → M), φ'.Realize x y = φ.Realize x y }
  | _, BoundedFormula.falsum => ⟨BoundedFormula.falsum, by
    simp [ModelsBoundedFormula, BoundedFormula.Realize]⟩
  | _, @BoundedFormula.equal _ _ n t₁ t₂ =>
    ⟨BoundedFormula.relabel id ((ofTerm t₁).equal (ofTerm t₂)), by
      simp [ModelsBoundedFormula, Formula.boundedFormula_realize_eq_realize, funext_iff,
          BoundedFormula.Realize]⟩
  | _, @BoundedFormula.rel _ _ m n R x =>
      let φ := (BoundedFormula.rel (L := L) (n := n) (α := Empty) (R : L.Relations n)
        (fun i => (var (Sum.inr i)))).toFormula
      let φ' := BoundedFormula.relabel id
        (rel (β := Fin n) (φ.relabel (Sum.elim Empty.elim (fun i => ⟨i, ()⟩))) (ofTerm ∘ x))
      ⟨φ', by
        simp [φ, φ', Formula.boundedFormula_realize_eq_realize, funext_iff,
          BoundedFormula.Realize]⟩
  | _, BoundedFormula.imp φ₁ φ₂ =>
      let ψ₁ := toBoundedFormulaAux φ₁
      let ψ₂ := toBoundedFormulaAux φ₂
      ⟨ψ₁.1.imp ψ₂.1, fun M x y => by simp only [BoundedFormula.Realize, ψ₁.2, ψ₂.2]⟩
  | _, BoundedFormula.all φ =>
      let ψ := toBoundedFormulaAux φ
      ⟨ψ.1.all, fun M x y => by simp only [BoundedFormula.Realize, ψ.2]⟩

noncomputable def toBoundedFormula {n : ℕ} (φ : (FunctionalFormulaLang T).BoundedFormula α n) :
    L.BoundedFormula α n :=
  (toBoundedFormulaAux φ).1

theorem realize_toBoundedFormula {n : ℕ} (φ : (FunctionalFormulaLang T).BoundedFormula α n)
    (x : α → M) (y : Fin n → M) : (toBoundedFormula φ).Realize x y = φ.Realize x y := by


end FunctionalFormulaLang

end Theory

end Language

end FirstOrder
