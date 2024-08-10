/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.ModelTheory.Syntax.Basic


/-!
# Basics on First-Order Syntax
This file defines first-order terms, formulas, sentences, and theories in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions


## Implementation Notes


## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language}
variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variable {α : Type u'} {β : Type v'} {γ : Type*}
variable {n : ℕ}

open FirstOrder

open Structure Fin Finset

namespace Term

/-- The `Finset` of variables used in a given term. -/
@[simp]
def varFinset [DecidableEq α] : L.Term α → Finset α
  | var i => {i}
  | func _f ts => univ.biUnion fun i => (ts i).varFinset

-- Porting note: universes in different order
/-- The `Finset` of variables from the left side of a sum used in a given term. -/
@[simp]
def varFinsetLeft [DecidableEq α] : L.Term (α ⊕ β) → Finset α
  | var (Sum.inl i) => {i}
  | var (Sum.inr _i) => ∅
  | func _f ts => univ.biUnion fun i => (ts i).varFinsetLeft

-- Porting note: universes in different order
@[simp]
def relabel (g : α → β) : L.Term α → L.Term β
  | var i => var (g i)
  | func f ts => func f fun {i} => (ts i).relabel g

theorem relabel_id (t : L.Term α) : t.relabel id = t := by
  induction' t with _ _ _ _ ih
  · rfl
  · simp [ih]

@[simp]
theorem relabel_id_eq_id : (Term.relabel id : L.Term α → L.Term α) = id :=
  funext relabel_id

@[simp]
theorem relabel_relabel (f : α → β) (g : β → γ) (t : L.Term α) :
    (t.relabel f).relabel g = t.relabel (g ∘ f) := by
  induction' t with _ _ _ _ ih
  · rfl
  · simp [ih]

@[simp]
theorem relabel_comp_relabel (f : α → β) (g : β → γ) :
    (Term.relabel g ∘ Term.relabel f : L.Term α → L.Term γ) = Term.relabel (g ∘ f) :=
  funext (relabel_relabel f g)

/-- Relabels a term's variables along a bijection. -/
@[simps]
def relabelEquiv (g : α ≃ β) : L.Term α ≃ L.Term β :=
  ⟨relabel g, relabel g.symm, fun t => by simp, fun t => by simp⟩

-- Porting note: universes in different order
/-- Restricts a term to use only a set of the given variables. -/
def restrictVar [DecidableEq α] : ∀ (t : L.Term α) (_f : t.varFinset → β), L.Term β
  | var a, f => var (f ⟨a, mem_singleton_self a⟩)
  | func F ts, f =>
    func F fun i => (ts i).restrictVar (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => varFinset (ts i)) (mem_univ i)))

-- Porting note: universes in different order
/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
def restrictVarLeft [DecidableEq α] {γ : Type*} :
    ∀ (t : L.Term (α ⊕ γ)) (_f : t.varFinsetLeft → β), L.Term (β ⊕ γ)
  | var (Sum.inl a), f => var (Sum.inl (f ⟨a, mem_singleton_self a⟩))
  | var (Sum.inr a), _f => var (Sum.inr a)
  | func F ts, f =>
    func F fun i =>
      (ts i).restrictVarLeft (f ∘ Set.inclusion (subset_biUnion_of_mem
        (fun i => varFinsetLeft (ts i)) (mem_univ i)))

-- Porting note: universes in different order
/-- Sends a term with constants to a term with extra variables. -/
@[simp]
def constantsToVars : L[[γ]].Term α → L.Term (γ ⊕ α)
  | var a => var (Sum.inr a)
  | @func _ _ 0 f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => var (Sum.inl c)
  | @func _ _ (_n + 1) f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => isEmptyElim c

-- Porting note: universes in different order
/-- Sends a term with extra variables to a term with constants. -/
@[simp]
def varsToConstants : L.Term (γ ⊕ α) → L[[γ]].Term α
  | var (Sum.inr a) => var a
  | var (Sum.inl c) => Constants.term (Sum.inr c)
  | func f ts => func (Sum.inl f) fun i => (ts i).varsToConstants

/-- A bijection between terms with constants and terms with extra variables. -/
@[simps]
def constantsVarsEquiv : L[[γ]].Term α ≃ L.Term (γ ⊕ α) :=
  ⟨constantsToVars, varsToConstants, by
    intro t
    induction' t with _ n f _ ih
    · rfl
    · cases n
      · cases f
        · simp [constantsToVars, varsToConstants, ih]
        · simp [constantsToVars, varsToConstants, Constants.term, eq_iff_true_of_subsingleton]
      · cases' f with f f
        · simp [constantsToVars, varsToConstants, ih]
        · exact isEmptyElim f, by
    intro t
    induction' t with x n f _ ih
    · cases x <;> rfl
    · cases n <;> · simp [varsToConstants, constantsToVars, ih]⟩

/-- A bijection between terms with constants and terms with extra variables. -/
def constantsVarsEquivLeft : L[[γ]].Term (α ⊕ β) ≃ L.Term ((γ ⊕ α) ⊕ β) :=
  constantsVarsEquiv.trans (relabelEquiv (Equiv.sumAssoc _ _ _)).symm

@[simp]
theorem constantsVarsEquivLeft_apply (t : L[[γ]].Term (α ⊕ β)) :
    constantsVarsEquivLeft t = (constantsToVars t).relabel (Equiv.sumAssoc _ _ _).symm :=
  rfl

@[simp]
theorem constantsVarsEquivLeft_symm_apply (t : L.Term ((γ ⊕ α) ⊕ β)) :
    constantsVarsEquivLeft.symm t = varsToConstants (t.relabel (Equiv.sumAssoc _ _ _)) :=
  rfl

/-- Raises all of the `Fin`-indexed variables of a term greater than or equal to `m` by `n'`. -/
def liftAt {n : ℕ} (n' m : ℕ) : L.Term (α ⊕ (Fin n)) → L.Term (α ⊕ (Fin (n + n'))) :=
  relabel (Sum.map id fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n')

-- Porting note: universes in different order
/-- Substitutes the variables in a given term with terms. -/
@[simp]
def subst : L.Term α → (α → L.Term β) → L.Term β
  | var a, tf => tf a
  | func f ts, tf => func f fun i => (ts i).subst tf

end Term

/-- Applies a relation to terms as a bounded formula. -/
def Relations.formula (R : L.Relations n) (ts : Fin n → L.Term α) : L.Formula α :=
  R.boundedFormula fun i => (ts i).relabel Sum.inl

/-- Applies a unary relation to a term as a formula. -/
def Relations.formula₁ (r : L.Relations 1) (t : L.Term α) : L.Formula α :=
  r.formula ![t]

/-- Applies a binary relation to two terms as a formula. -/
def Relations.formula₂ (r : L.Relations 2) (t₁ t₂ : L.Term α) : L.Formula α :=
  r.formula ![t₁, t₂]

/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.Term α) : L.Formula α :=
  (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)

namespace BoundedFormula

-- Porting note: universes in different order
/-- The `Finset` of variables used in a given formula. -/
@[simp]
def freeVarFinset [DecidableEq α] : ∀ {n}, L.BoundedFormula α n → Finset α
  | _n, falsum => ∅
  | _n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | _n, rel _R ts => univ.biUnion fun i => (ts i).varFinsetLeft
  | _n, imp f₁ f₂ => f₁.freeVarFinset ∪ f₂.freeVarFinset
  | _n, all f => f.freeVarFinset

-- Porting note: universes in different order
/-- Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`. -/
@[simp]
def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BoundedFormula α m → L.BoundedFormula α n
  | _m, _n, _h, falsum => falsum
  | _m, _n, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _m, _n, h, rel R ts => rel R (Term.relabel (Sum.map id (Fin.castLE h)) ∘ ts)
  | _m, _n, h, imp f₁ f₂ => (f₁.castLE h).imp (f₂.castLE h)
  | _m, _n, h, all f => (f.castLE (add_le_add_right h 1)).all

@[simp]
theorem castLE_rfl {n} (h : n ≤ n) (φ : L.BoundedFormula α n) : φ.castLE h = φ := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [Fin.castLE_of_eq]
  · simp [Fin.castLE_of_eq]
  · simp [Fin.castLE_of_eq, ih1, ih2]
  · simp [Fin.castLE_of_eq, ih3]

@[simp]
theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (φ : L.BoundedFormula α k) :
    (φ.castLE km).castLE mn = φ.castLE (km.trans mn) := by
  revert m n
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3 <;> intro m n km mn
  · rfl
  · simp
  · simp only [castLE, eq_self_iff_true, heq_iff_eq, true_and_iff]
    rw [← Function.comp.assoc, Term.relabel_comp_relabel]
    simp
  · simp [ih1, ih2]
  · simp only [castLE, ih3]

@[simp]
theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    (BoundedFormula.castLE mn ∘ BoundedFormula.castLE km :
        L.BoundedFormula α k → L.BoundedFormula α n) =
      BoundedFormula.castLE (km.trans mn) :=
  funext (castLE_castLE km mn)

-- Porting note: universes in different order
/-- Restricts a bounded formula to only use a particular set of free variables. -/
def restrictFreeVar [DecidableEq α] :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (_f : φ.freeVarFinset → β), L.BoundedFormula β n
  | _n, falsum, _f => falsum
  | _n, equal t₁ t₂, f =>
    equal (t₁.restrictVarLeft (f ∘ Set.inclusion subset_union_left))
      (t₂.restrictVarLeft (f ∘ Set.inclusion subset_union_right))
  | _n, rel R ts, f =>
    rel R fun i => (ts i).restrictVarLeft (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => Term.varFinsetLeft (ts i)) (mem_univ i)))
  | _n, imp φ₁ φ₂, f =>
    (φ₁.restrictFreeVar (f ∘ Set.inclusion subset_union_left)).imp
      (φ₂.restrictFreeVar (f ∘ Set.inclusion subset_union_right))
  | _n, all φ, f => (φ.restrictFreeVar f).all

-- Porting note: universes in different order
/-- Maps bounded formulas along a map of terms and a map of relations. -/
def mapTermRel {g : ℕ → ℕ} (ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin (g n))))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (h : ∀ n, L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula β (g n + 1)) :
    ∀ {n}, L.BoundedFormula α n → L'.BoundedFormula β (g n)
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => equal (ft _ t₁) (ft _ t₂)
  | _n, rel R ts => rel (fr _ R) fun i => ft _ (ts i)
  | _n, imp φ₁ φ₂ => (φ₁.mapTermRel ft fr h).imp (φ₂.mapTermRel ft fr h)
  | n, all φ => (h n (φ.mapTermRel ft fr h)).all

/-- Raises all of the `Fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def liftAt : ∀ {n : ℕ} (n' _m : ℕ), L.BoundedFormula α n → L.BoundedFormula α (n + n') :=
  fun {n} n' m φ =>
  φ.mapTermRel (fun k t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])

@[simp]
theorem mapTermRel_mapTermRel {L'' : Language}
    (ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin n)))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (ft' : ∀ n, L'.Term (β ⊕ Fin n) → L''.Term (γ ⊕ (Fin n)))
    (fr' : ∀ n, L'.Relations n → L''.Relations n) {n} (φ : L.BoundedFormula α n) :
    ((φ.mapTermRel ft fr fun _ => id).mapTermRel ft' fr' fun _ => id) =
      φ.mapTermRel (fun _ => ft' _ ∘ ft _) (fun _ => fr' _ ∘ fr _) fun _ => id := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [mapTermRel]
  · simp [mapTermRel]
  · simp [mapTermRel, ih1, ih2]
  · simp [mapTermRel, ih3]

@[simp]
theorem mapTermRel_id_id_id {n} (φ : L.BoundedFormula α n) :
    (φ.mapTermRel (fun _ => id) (fun _ => id) fun _ => id) = φ := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [mapTermRel]
  · simp [mapTermRel]
  · simp [mapTermRel, ih1, ih2]
  · simp [mapTermRel, ih3]

/-- An equivalence of bounded formulas given by an equivalence of terms and an equivalence of
relations. -/
@[simps]
def mapTermRelEquiv (ft : ∀ n, L.Term (α ⊕ (Fin n)) ≃ L'.Term (β ⊕ (Fin n)))
    (fr : ∀ n, L.Relations n ≃ L'.Relations n) {n} : L.BoundedFormula α n ≃ L'.BoundedFormula β n :=
  ⟨mapTermRel (fun n => ft n) (fun n => fr n) fun _ => id,
    mapTermRel (fun n => (ft n).symm) (fun n => (fr n).symm) fun _ => id, fun φ => by simp, fun φ =>
    by simp⟩

/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → β ⊕ (Fin n)) (k : ℕ) : α ⊕ (Fin k) → β ⊕ (Fin (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

@[simp]
theorem sum_elim_comp_relabelAux {m : ℕ} {g : α → β ⊕ (Fin n)} {v : β → M}
    {xs : Fin (n + m) → M} : Sum.elim v xs ∘ relabelAux g m =
    Sum.elim (Sum.elim v (xs ∘ castAdd m) ∘ g) (xs ∘ natAdd n) := by
  ext x
  cases' x with x x
  · simp only [BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inl, Sum.elim_inl]
    cases' g x with l r <;> simp
  · simp [BoundedFormula.relabelAux]

@[simp]
theorem relabelAux_sum_inl (k : ℕ) :
    relabelAux (Sum.inl : α → α ⊕ (Fin n)) k = Sum.map id (natAdd n) := by
  ext x
  cases x <;> · simp [relabelAux]

/-- Relabels a bounded formula's variables along a particular function. -/
def relabel (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α k) : L.BoundedFormula β (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))

/-- Relabels a bounded formula's free variables along a bijection. -/
def relabelEquiv (g : α ≃ β) {k} : L.BoundedFormula α k ≃ L.BoundedFormula β k :=
  mapTermRelEquiv (fun _n => Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
    fun _n => _root_.Equiv.refl _

@[simp]
theorem relabel_falsum (g : α → β ⊕ (Fin n)) {k} :
    (falsum : L.BoundedFormula α k).relabel g = falsum :=
  rfl

@[simp]
theorem relabel_bot (g : α → β ⊕ (Fin n)) {k} : (⊥ : L.BoundedFormula α k).relabel g = ⊥ :=
  rfl

@[simp]
theorem relabel_imp (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g) :=
  rfl

@[simp]
theorem relabel_not (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α k) :
    φ.not.relabel g = (φ.relabel g).not := by simp [BoundedFormula.not]

@[simp]
theorem relabel_all (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabel g = (φ.relabel g).all := by
  rw [relabel, mapTermRel, relabel]
  simp

@[simp]
theorem relabel_ex (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.ex.relabel g = (φ.relabel g).ex := by simp [BoundedFormula.ex]

@[simp]
theorem relabel_sum_inl (φ : L.BoundedFormula α n) :
    (φ.relabel Sum.inl : L.BoundedFormula α (0 + n)) = φ.castLE (ge_of_eq (zero_add n)) := by
  simp only [relabel, relabelAux_sum_inl]
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]
  · simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]; rfl
  · simp [mapTermRel, ih1, ih2]
  · simp [mapTermRel, ih3, castLE]

/-- Substitutes the variables in a given formula with terms. -/
def subst {n : ℕ} (φ : L.BoundedFormula α n) (f : α → L.Term β) : L.BoundedFormula β n :=
  φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)))
    (fun _ => id) fun _ => id

/-- A bijection sending formulas with constants to formulas with extra variables. -/
def constantsVarsEquiv : L[[γ]].BoundedFormula α n ≃ L.BoundedFormula (γ ⊕ α) n :=
  mapTermRelEquiv (fun _ => Term.constantsVarsEquivLeft) fun _ => Equiv.sumEmpty _ _

-- Porting note: universes in different order
/-- Turns the extra variables of a bounded formula into free variables. -/
@[simp]
def toFormula : ∀ {n : ℕ}, L.BoundedFormula α n → L.Formula (α ⊕ (Fin n))
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => t₁.equal t₂
  | _n, rel R ts => R.formula ts
  | _n, imp φ₁ φ₂ => φ₁.toFormula.imp φ₂.toFormula
  | _n, all φ =>
    (φ.toFormula.relabel
        (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))).all

end BoundedFormula

end Language

end FirstOrder
