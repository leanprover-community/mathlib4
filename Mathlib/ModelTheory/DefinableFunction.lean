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

structure FunctionalFormula (α : Type w) (β : Type x) [Finite β] : Type _ where
  ofQuotient :: toQuotient : Quotient (FunctionalFormulaSetoid T α β)

namespace FunctionalFormula

variable {T}

def mk (φ : L.Formula (α ⊕ β)) (h : T ⊨ᵇ Formula.iExsUnique β φ) : FunctionalFormula T α β :=
  ofQuotient (Quotient.mk _ ⟨φ, h⟩)

def Realize (f : FunctionalFormula T α β) (x : α → M) (y : β → M) : Prop :=
  Quotient.lift (fun φ => φ.1.Realize (Sum.elim x y)) (by
    intro a b hab
    simpa using hab.realize_formula M (v := Sum.elim x y)) f.toQuotient

noncomputable def toFormula : FunctionalFormula T α β → L.Formula (α ⊕ β) := fun f => f.1.out.1

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

theorem exists_fun_eq_iff (f : T.FunctionalFormula α β) : ∃ f' : (α → M) → (β → M),
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
noncomputable def comap (f : β → α) : T.FunctionalFormula α β :=
  let e := Fintype.ofFinite β
  mk (Formula.iAlls β <|
    (Formula.iInf (Finset.univ : Finset β)
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
protected noncomputable def id : T.FunctionalFormula β β :=
  comap T id

@[simp]
theorem realize_id (x : β → M) :
    (FunctionalFormula.id T).realize (T := T) (M := M) x = x := by
  simp [FunctionalFormula.id]

variable {T}
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

noncomputable def relabelRight [Finite γ] (f : γ → β) (g : T.FunctionalFormula α β) :
    T.FunctionalFormula α γ :=
  (comap T f).comp g

@[simp]
theorem realize_relabelRight [Finite γ] (f : γ → β) (g : T.FunctionalFormula α β) (x : α → M) :
    (relabelRight f g).realize x = g.realize x ∘ f := by
  simp only [relabelRight, realize_comp, realize_comap, Function.comp_def]

noncomputable def toSigma {γ : β → Type y} [∀ b, Finite (γ b)]
    (f : ∀ b, T.FunctionalFormula α (γ b)) :
    T.FunctionalFormula α (Sigma γ) :=
  let e := Fintype.ofFinite β
  mk (Formula.iInf (Finset.univ : Finset β)
    (fun b => (f b).toFormula.relabel (Sum.elim Sum.inl (fun g => Sum.inr ⟨_, g⟩)))) <| by
  simp only [models_formula_iff, Formula.realize_iExsUnique, id_eq, Formula.realize_iInf,
    Finset.mem_univ, Formula.realize_relabel, Function.comp_def, realize_toFormula, Sum.elim_inl,
    Sum.elim_inr, forall_const]
  intro M x
  use (fun i : Σ b, γ b => (f i.1).realize x i.2)
  simp only [realize_iff_realize_eq, implies_true, funext_iff, eq_comm, true_and]
  intro y h z
  cases z
  rw [h]

@[simp]
theorem realize_toSigma {γ : β → Type y} [∀ b, Finite (γ b)]
    (f : ∀ b, T.FunctionalFormula α (γ b)) (x : α → M) :
    (toSigma f).realize x = fun i => (f i.1).realize x i.2 := by
  simp only [toSigma, realize_mk, Formula.realize_iInf, Finset.mem_univ, Formula.realize_relabel,
    Function.comp_def, realize_toFormula, Sum.elim_inl, Sum.elim_inr, forall_const,
    ← realize_iff_realize_eq]
  simp only [realize_iff_realize_eq, implies_true]

noncomputable def rel {γ : β → Type y} [∀ b, Finite (γ b)] (φ : L.Formula (Sigma γ))
    (f : ∀ b, T.FunctionalFormula α (γ b)) : L.Formula α :=
  Formula.iAlls (Sigma γ) ((toSigma f).toFormula.imp (φ.relabel Sum.inr))

@[simp]
theorem realize_rel {γ : β → Type y} [∀ b, Finite (γ b)] (φ : L.Formula (Sigma γ))
    (f : ∀ b, T.FunctionalFormula α (γ b)) (x : α → M) :
    (rel φ f).Realize x ↔ φ.Realize (fun b => (f b.1).realize x b.2) := by
  simp [rel, realize_iff_realize_eq]

noncomputable def equal (f g : T.FunctionalFormula α β) : L.Formula α :=
  let _ := Fintype.ofFinite β
  rel (Formula.iInf (Finset.univ : Finset β)
    (fun b => Term.equal (var ⟨true, b⟩) (var ⟨false, b⟩)))
    (fun b : Bool => if b then f else g)

@[simp]
theorem realize_equal (f g : T.FunctionalFormula α β) (x : α → M) :
    (equal f g).Realize x ↔ f.realize x = g.realize x := by
  simp [equal, funext_iff]

noncomputable def injective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) : L.Formula α :=
  Formula.iAlls (γ ⊕ γ)
    ((equal (f.relabelLeft (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)))
           (f.relabelLeft (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)))).imp
     (equal (comap T (Sum.inr ∘ Sum.inl)) (comap T (Sum.inr ∘ (Sum.inr)))))

@[simp]
theorem realize_injective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) (x : α → M) :
    (injective f).Realize x ↔ Function.Injective
      (fun y : γ → M => f.realize (Sum.elim x y)) := by
  simp only [injective, Function.comp_def, Formula.realize_iAlls, id_eq, Formula.realize_imp,
    realize_equal, realize_relabelLeft, funext_iff, realize_comap, Sum.elim_inr, Sum.forall_sum,
    Function.Injective]
  simp +singlePass [← Sum.elim_comp_inl_inr]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]

noncomputable def surjective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) : L.Formula α :=
  Formula.iAlls β (Formula.iExs γ (f.toFormula.relabel
    (Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr))))

@[simp]
theorem realize_surjective [Finite γ] (f : T.FunctionalFormula (α ⊕ γ) β) (x : α → M) :
    (surjective f).Realize x ↔ Function.Surjective (fun y : γ → M => f.realize (Sum.elim x y)) := by
  simp only [surjective, Function.comp_def, Formula.realize_iAlls, id_eq, Formula.realize_iExs,
    Formula.realize_relabel, realize_toFormula, Sum.elim_inl, Sum.elim_inr, realize_iff_realize_eq,
    funext_iff, Function.Surjective]
  simp +singlePass [← Sum.elim_comp_inl_inr]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]

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

noncomputable def modelTypeEquiv : Theory.ModelType.{_, _, w} T ≃
    Theory.ModelType (FunctionalFormulaLang.theory T) where
  toFun := fun M => ⟨M⟩
  invFun := fun M =>
    let i1 : L.Structure M :=
      { funMap := fun f x => Structure.funMap (L := FunctionalFormulaLang T)
          (ofTerm (func f var)) x
        RelMap := fun R => Structure.RelMap (L := FunctionalFormulaLang T) R }
    let i2 : T.Model M :=
      { realize_of_mem := by
          intro φ hφ
          simpa using (models_sentence_of_mem (T := FunctionalFormulaLang.theory T)
            (φ := (of T).onSentence φ) (Set.mem_union_left _ ⟨φ, hφ, rfl⟩)).realize_sentence M  }
    ⟨M⟩
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
    refine ModelType.casesOn M (fun M {S} _ _ => ?_)
    simp only [eq_mp_eq_cast, instStructure, ModelType.mk.injEq, heq_eq_eq, true_and]
    let i1 : L.Structure M :=
      { funMap := fun f x => Structure.funMap (L := FunctionalFormulaLang T)
          (ofTerm (func f var)) x
        RelMap := fun R => Structure.RelMap (L := FunctionalFormulaLang T) R }
    let i2 : T.Model M :=
      { realize_of_mem := by
          intro φ hφ
          simpa using (models_sentence_of_mem (T := FunctionalFormulaLang.theory T)
            (φ := (of T).onSentence φ) (Set.mem_union_left _ ⟨φ, hφ, rfl⟩)).realize_sentence M  }
    ext n f x
    · have := models_sentence_of_mem (T := FunctionalFormulaLang.theory T)
        (Set.mem_union_right _ (Set.mem_iUnion.2 ⟨n, Set.mem_range.2 ⟨f, rfl⟩⟩))
      have := this.realize_formula M (v := Empty.elim)
      simp only [Formula.realize_iAlls, Formula.realize_relabel, Function.comp_def, Sum.elim_inr,
        Formula.realize_iff, Formula.realize_equal, Term.realize_func, Term.realize_var,
        LHom.realize_onFormula, realize_toFormula, realize_iff_realize_eq, funext_iff] at this
      have := (this (Sum.elim x (fun _ => S.funMap f x))).1 (by simp) ()
      simpa
    · simp [Structure.RelMap]

variable {T}
theorem modelsBoundedFormula_iff {n : ℕ} {φ : T.FunctionalFormulaLang.BoundedFormula α n} :
    ((FunctionalFormulaLang.theory T) ⊨ᵇ φ) ↔ (∀ (N : Theory.ModelType.{_, _, max u v w} T)
      (x : α → N) (y : Fin n → N), φ.Realize x y) := by
  rw [ModelsBoundedFormula, Equiv.forall_congr_left (modelTypeEquiv T).symm]
  simp [modelTypeEquiv]

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
    { φ' : L.BoundedFormula α n // (FunctionalFormulaLang.theory T) ⊨ᵇ
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
      let φ' := BoundedFormula.relabel id
        (rel (β := Fin n) (φ.relabel (Sum.elim Empty.elim (fun i => ⟨i, ()⟩))) (ofTerm ∘ x))
      ⟨φ', by
        simp [φ, φ', Formula.boundedFormula_realize_eq_realize, funext_iff,
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

noncomputable def toBoundedFormula {n : ℕ} (φ : (FunctionalFormulaLang T).BoundedFormula α n) :
    L.BoundedFormula α n :=
  (toBoundedFormulaAux φ).1

theorem realize_toBoundedFormula {n : ℕ} (φ : (FunctionalFormulaLang T).BoundedFormula α n)
    (x : α → M) (y : Fin n → M) : (toBoundedFormula φ).Realize x y ↔ φ.Realize x y := by
  have := ((toBoundedFormulaAux φ).2).realize_boundedFormula M (xs := y) (v := x)
  simpa

end FunctionalFormulaLang

end Theory

end Language

end FirstOrder
