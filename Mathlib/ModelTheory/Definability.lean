/-
Copyright (c) 2021 Aaron Anderson, Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Alex Meiburg
-/
import Mathlib.Data.SetLike.Basic
import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic.FunProp

/-!
# Definable Sets

This file defines what it means for a set over a first-order structure to be definable.

## Main Definitions

- `Set.Definable` is defined so that `A.Definable L s` indicates that the
  set `s` of a finite Cartesian power of `M` is definable with parameters in `A`.
- `Set.Definable₁` is defined so that `A.Definable₁ L s` indicates that
  `(s : Set M)` is definable with parameters in `A`.
- `Set.Definable₂` is defined so that `A.Definable₂ L s` indicates that
  `(s : Set (M × M))` is definable with parameters in `A`.
- A `FirstOrder.Language.DefinableSet` is defined so that `L.DefinableSet A α` is the Boolean
  algebra of subsets of `α → M` defined by formulas with parameters in `A`.
- A function `f` is `A.TermDefinable L` if it can be expressed as a term in the language,
  which is stronger than typical FO definability. `A.TermDefinable L`

## Main Results

- `L.DefinableSet A α` forms a `BooleanAlgebra`
- `Set.Definable.image_comp` shows that definability is closed under projections in finite
  dimensions.
- `Set.Definable_trans` shows that `Set.Definable` is transitive, in the sense that if `S` can be
  defined in `L` and all of `L`'s functions and relations can be defined in `L'`, then `S` is
  also definable in `L'`.

-/

universe u v w u₁

namespace Set

variable {M : Type w} (A : Set M) (L : FirstOrder.Language.{u, v}) [L.Structure M]

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {α : Type u₁} {β : Type*}

/-- A subset of a finite Cartesian product of a structure is definable over a set `A` when
  membership in the set is given by a first-order formula with parameters from `A`. -/
def Definable (s : Set (α → M)) : Prop :=
  ∃ φ : L[[A]].Formula α, s = setOf φ.Realize

variable {L} {A} {B : Set M} {s : Set (α → M)}

theorem Definable.map_expansion {L' : FirstOrder.Language} [L'.Structure M] (h : A.Definable L s)
    (φ : L →ᴸ L') [φ.IsExpansionOn M] : A.Definable L' s := by
  obtain ⟨ψ, rfl⟩ := h
  refine ⟨(φ.addConstants A).onFormula ψ, ?_⟩
  ext x
  simp only [mem_setOf_eq, LHom.realize_onFormula]

theorem definable_iff_exists_formula_sum :
    A.Definable L s ↔ ∃ φ : L.Formula (A ⊕ α), s = {v | φ.Realize (Sum.elim (↑) v)} := by
  rw [Definable, Equiv.exists_congr_left (BoundedFormula.constantsVarsEquiv)]
  refine exists_congr (fun φ => iff_iff_eq.2 (congr_arg (s = ·) ?_))
  ext
  simp only [BoundedFormula.constantsVarsEquiv, constantsOn,
    BoundedFormula.mapTermRelEquiv_symm_apply, mem_setOf_eq, Formula.Realize]
  refine BoundedFormula.realize_mapTermRel_id ?_ (fun _ _ _ => rfl)
  intros
  simp only [Term.constantsVarsEquivLeft_symm_apply, Term.realize_varsToConstants,
    coe_con, Term.realize_relabel]
  congr 1 with a
  rcases a with (_ | _) | _ <;> rfl

theorem empty_definable_iff :
    (∅ : Set M).Definable L s ↔ ∃ φ : L.Formula α, s = setOf φ.Realize := by
  rw [Definable, Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onFormula]
  simp

theorem definable_iff_empty_definable_with_params :
    A.Definable L s ↔ (∅ : Set M).Definable (L[[A]]) s :=
  empty_definable_iff.symm

theorem Definable.mono (hAs : A.Definable L s) (hAB : A ⊆ B) : B.Definable L s := by
  rw [definable_iff_empty_definable_with_params] at *
  exact hAs.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

@[simp]
theorem definable_empty : A.Definable L (∅ : Set (α → M)) :=
  ⟨⊥, by
    ext
    simp⟩

@[simp]
theorem definable_univ : A.Definable L (univ : Set (α → M)) :=
  ⟨⊤, by
    ext
    simp⟩

@[simp]
theorem Definable.inter {f g : Set (α → M)} (hf : A.Definable L f) (hg : A.Definable L g) :
    A.Definable L (f ∩ g) := by
  rcases hf with ⟨φ, rfl⟩
  rcases hg with ⟨θ, rfl⟩
  refine ⟨φ ⊓ θ, ?_⟩
  ext
  simp

@[simp]
theorem Definable.union {f g : Set (α → M)} (hf : A.Definable L f) (hg : A.Definable L g) :
    A.Definable L (f ∪ g) := by
  rcases hf with ⟨φ, hφ⟩
  rcases hg with ⟨θ, hθ⟩
  refine ⟨φ ⊔ θ, ?_⟩
  ext
  rw [hφ, hθ, mem_setOf_eq, Formula.realize_sup, mem_union, mem_setOf_eq, mem_setOf_eq]

theorem definable_finset_inf {ι : Type*} {f : ι → Set (α → M)} (hf : ∀ i, A.Definable L (f i))
    (s : Finset ι) : A.Definable L (s.inf f) := by
  classical
    refine Finset.induction definable_univ (fun i s _ h => ?_) s
    rw [Finset.inf_insert]
    exact (hf i).inter h

theorem definable_finset_sup {ι : Type*} {f : ι → Set (α → M)} (hf : ∀ i, A.Definable L (f i))
    (s : Finset ι) : A.Definable L (s.sup f) := by
  classical
    refine Finset.induction definable_empty (fun i s _ h => ?_) s
    rw [Finset.sup_insert]
    exact (hf i).union h

theorem definable_biInter_finset {ι : Type*} {f : ι → Set (α → M)}
    (hf : ∀ i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋂ i ∈ s, f i) := by
  rw [← Finset.inf_set_eq_iInter]
  exact definable_finset_inf hf s

@[deprecated (since := "2025-08-28")]
alias definable_finset_biInter := definable_biInter_finset

theorem definable_biUnion_finset {ι : Type*} {f : ι → Set (α → M)}
    (hf : ∀ i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋃ i ∈ s, f i) := by
  rw [← Finset.sup_set_eq_biUnion]
  exact definable_finset_sup hf s

@[deprecated (since := "2025-08-28")]
alias definable_finset_biUnion := definable_biUnion_finset

@[simp]
theorem Definable.compl {s : Set (α → M)} (hf : A.Definable L s) : A.Definable L sᶜ := by
  rcases hf with ⟨φ, hφ⟩
  refine ⟨φ.not, ?_⟩
  ext v
  rw [hφ, compl_setOf, mem_setOf, mem_setOf, Formula.realize_not]

@[simp]
theorem Definable.sdiff {s t : Set (α → M)} (hs : A.Definable L s) (ht : A.Definable L t) :
    A.Definable L (s \ t) :=
  hs.inter ht.compl

@[simp] lemma Definable.himp {s t : Set (α → M)} (hs : A.Definable L s) (ht : A.Definable L t) :
    A.Definable L (s ⇨ t) := by rw [himp_eq]; exact ht.union hs.compl

theorem Definable.preimage_comp (f : α → β) {s : Set (α → M)} (h : A.Definable L s) :
    A.Definable L ((fun g : β → M => g ∘ f) ⁻¹' s) := by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨φ.relabel f, ?_⟩
  ext
  simp only [Set.preimage_setOf_eq, mem_setOf_eq, Formula.realize_relabel]

theorem Definable.image_comp_equiv {s : Set (β → M)} (h : A.Definable L s) (f : α ≃ β) :
    A.Definable L ((fun g : β → M => g ∘ f) '' s) := by
  refine (congr rfl ?_).mp (h.preimage_comp f.symm)
  rw [image_eq_preimage_of_inverse]
  · intro i
    ext b
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  · intro i
    ext a
    simp

theorem definable_iff_finitely_definable :
    A.Definable L s ↔ ∃ (A0 : Finset M), (A0 : Set M) ⊆ A ∧
      (A0 : Set M).Definable L s := by
  classical
  constructor
  · simp only [definable_iff_exists_formula_sum]
    rintro ⟨φ, rfl⟩
    let A0 := (φ.freeVarFinset.toLeft).image Subtype.val
    refine ⟨A0, by simp [A0], (φ.restrictFreeVar <| fun x => Sum.casesOn x.1
        (fun x hx => Sum.inl ⟨x, by simp [A0, hx]⟩) (fun x _ => Sum.inr x) x.2), ?_⟩
    ext
    simp only [Formula.Realize, mem_setOf_eq, Finset.coe_sort_coe]
    exact iff_comm.1 <| BoundedFormula.realize_restrictFreeVar _ (by simp)
  · rintro ⟨A0, hA0, hd⟩
    exact Definable.mono hd hA0

/-- This lemma is only intended as a helper for `Definable.image_comp`. -/
theorem Definable.image_comp_sumInl_fin (m : ℕ) {s : Set (Sum α (Fin m) → M)}
    (h : A.Definable L s) : A.Definable L ((fun g : Sum α (Fin m) → M => g ∘ Sum.inl) '' s) := by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨(BoundedFormula.relabel id φ).exs, ?_⟩
  ext x
  simp only [Set.mem_image, mem_setOf_eq, BoundedFormula.realize_exs,
    BoundedFormula.realize_relabel, Function.comp_id, Fin.castAdd_zero, Fin.cast_refl]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact
      ⟨y ∘ Sum.inr, (congr (congr rfl (Sum.elim_comp_inl_inr y).symm) (funext finZeroElim)).mp hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨Sum.elim x y, (congr rfl (funext finZeroElim)).mp hy, Sum.elim_comp_inl _ _⟩

/-- Shows that definability is closed under finite projections. -/
theorem Definable.image_comp_embedding {s : Set (β → M)} (h : A.Definable L s) (f : α ↪ β)
    [Finite β] : A.Definable L ((fun g : β → M => g ∘ f) '' s) := by
  classical
    cases nonempty_fintype β
    refine
      (congr rfl (ext fun x => ?_)).mp
        (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
              (Equiv.sumCongr (Equiv.ofInjective f f.injective)
                (Fintype.equivFin (↥(range f)ᶜ)).symm)).image_comp_sumInl_fin
          _)
    simp only [mem_image, exists_exists_and_eq_and]
    refine exists_congr fun y => and_congr_right fun _ => Eq.congr_left (funext fun a => ?_)
    simp

/-- Shows that definability is closed under finite projections. -/
theorem Definable.image_comp {s : Set (β → M)} (h : A.Definable L s) (f : α → β) [Finite α]
    [Finite β] : A.Definable L ((fun g : β → M => g ∘ f) '' s) := by
  classical
    cases nonempty_fintype α
    cases nonempty_fintype β
    have h :=
      (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
                (Equiv.sumCongr (_root_.Equiv.refl _)
                  (Fintype.equivFin _).symm)).image_comp_sumInl_fin
            _).preimage_comp
        (rangeSplitting f)
    have h' :
      A.Definable L { x : α → M | ∀ a, x a = x (rangeSplitting f (rangeFactorization f a)) } := by
      have h' : ∀ a,
        A.Definable L { x : α → M | x a = x (rangeSplitting f (rangeFactorization f a)) } := by
          refine fun a => ⟨(var a).equal (var (rangeSplitting f (rangeFactorization f a))), ext ?_⟩
          simp
      refine (congr rfl (ext ?_)).mp (definable_biInter_finset h' Finset.univ)
      simp
    refine (congr rfl (ext fun x => ?_)).mp (h.inter h')
    simp only [mem_inter_iff, mem_preimage, mem_image, exists_exists_and_eq_and,
      mem_setOf_eq]
    constructor
    · rintro ⟨⟨y, ys, hy⟩, hx⟩
      refine ⟨y, ys, ?_⟩
      ext a
      rw [hx a, ← Function.comp_apply (f := x), ← hy]
      simp
    · rintro ⟨y, ys, rfl⟩
      refine ⟨⟨y, ys, ?_⟩, fun a => ?_⟩
      · ext
        simp [Set.apply_rangeSplitting f]
      · rw [Function.comp_apply, Function.comp_apply, apply_rangeSplitting f,
          rangeFactorization_coe]

variable (L A)

/-- A 1-dimensional version of `Definable`, for `Set M`. -/
def Definable₁ (s : Set M) : Prop :=
  A.Definable L { x : Fin 1 → M | x 0 ∈ s }

/-- A 2-dimensional version of `Definable`, for `Set (M × M)`. -/
def Definable₂ (s : Set (M × M)) : Prop :=
  A.Definable L { x : Fin 2 → M | (x 0, x 1) ∈ s }

variable (L' : Language) [inst' : L'.Structure M]

/-- Definability is transitive. Given a structure S on L and T on L', if:
  * a set S is Definable in some M-structure on L,
  * the realizations of all L.Functions have tupleGraph that's Definable on S,
  * the realizations of all L.Relations are Definable on S,
then S is Definable on T, as well. -/
theorem Definable.trans {S : Set (α → M)} (h₁ : A.Definable L S)
    (h₂ : ∀ {n} (g : L[[A]].Functions n), A.Definable L' (g.term.realize).tupleGraph)
    (h₃ : ∀ {n} (g : L[[A]].Relations n), A.Definable L' (RelMap g)) :
    A.Definable L' S :=
  h₁.elim fun φ₁ hφ₁ ↦
    ⟨_, hφ₁.trans <| (φ₁.subst_definitions_eq
      (fun g ↦ (h₂ g).choose_spec.symm) (fun g ↦ (h₃ g).choose_spec.symm)).symm⟩

end Set

namespace FirstOrder

namespace Language

open Set

variable (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M] (A : Set M) (α : Type u₁)

/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
def DefinableSet :=
  { s : Set (α → M) // A.Definable L s }

namespace DefinableSet

variable {L A α}
variable {s t : L.DefinableSet A α} {x : α → M}

instance instSetLike : SetLike (L.DefinableSet A α) (α → M) where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

instance instTop : Top (L.DefinableSet A α) :=
  ⟨⟨⊤, definable_univ⟩⟩

instance instBot : Bot (L.DefinableSet A α) :=
  ⟨⟨⊥, definable_empty⟩⟩

instance instSup : Max (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s ∪ t, s.2.union t.2⟩⟩

instance instInf : Min (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s ∩ t, s.2.inter t.2⟩⟩

instance instHasCompl : HasCompl (L.DefinableSet A α) :=
  ⟨fun s => ⟨sᶜ, s.2.compl⟩⟩

instance instSDiff : SDiff (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s \ t, s.2.sdiff t.2⟩⟩

-- Why does it complain that `s ⇨ t` is noncomputable?
noncomputable instance instHImp : HImp (L.DefinableSet A α) where
  himp s t := ⟨s ⇨ t, s.2.himp t.2⟩

instance instInhabited : Inhabited (L.DefinableSet A α) :=
  ⟨⊥⟩

theorem le_iff : s ≤ t ↔ (s : Set (α → M)) ≤ (t : Set (α → M)) :=
  Iff.rfl

@[simp]
theorem mem_top : x ∈ (⊤ : L.DefinableSet A α) :=
  mem_univ x

@[simp]
theorem notMem_bot {x : α → M} : x ∉ (⊥ : L.DefinableSet A α) :=
  notMem_empty x

@[deprecated (since := "2025-05-23")] alias not_mem_bot := notMem_bot

@[simp]
theorem mem_sup : x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t :=
  Iff.rfl

@[simp]
theorem mem_inf : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t :=
  Iff.rfl

@[simp]
theorem mem_compl : x ∈ sᶜ ↔ x ∉ s :=
  Iff.rfl

@[simp]
theorem mem_sdiff : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_top : ((⊤ : L.DefinableSet A α) : Set (α → M)) = univ :=
  rfl

@[simp, norm_cast]
theorem coe_bot : ((⊥ : L.DefinableSet A α) : Set (α → M)) = ∅ :=
  rfl

@[simp, norm_cast]
theorem coe_sup (s t : L.DefinableSet A α) :
    ((s ⊔ t : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M)) ∪ (t : Set (α → M)) :=
  rfl

@[simp, norm_cast]
theorem coe_inf (s t : L.DefinableSet A α) :
    ((s ⊓ t : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M)) ∩ (t : Set (α → M)) :=
  rfl

@[simp, norm_cast]
theorem coe_compl (s : L.DefinableSet A α) :
    ((sᶜ : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M))ᶜ :=
  rfl

@[simp, norm_cast]
theorem coe_sdiff (s t : L.DefinableSet A α) :
    ((s \ t : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M)) \ (t : Set (α → M)) :=
  rfl

@[simp, norm_cast]
lemma coe_himp (s t : L.DefinableSet A α) : ↑(s ⇨ t) = (s ⇨ t : Set (α → M)) := rfl

noncomputable instance instBooleanAlgebra : BooleanAlgebra (L.DefinableSet A α) :=
  Function.Injective.booleanAlgebra (α := L.DefinableSet A α) _ Subtype.coe_injective
    coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff coe_himp

end DefinableSet

end Language

end FirstOrder

namespace Set

variable {M : Type w} (A : Set M) (L : FirstOrder.Language.{u, v}) {L' : FirstOrder.Language}
variable [L.Structure M] [L'.Structure M]

variable {α : Type u₁} {β : Type*}

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

/-- A function from a Cartesian power of a structure to that structure is term-definable over
  a set `A` when the value of the function is given by a term with constants `A`. -/
@[fun_prop]
def TermDefinable (f : (α → M) → M) : Prop :=
  ∃ φ : L[[A]].Term α, f = φ.realize

/-- Every TermDefinable function has a tupleGraph that is definable. -/
theorem TermDefinable.Definable {f : (α → M) → M} (h : A.TermDefinable L f) :
    A.Definable L f.tupleGraph := by
  obtain ⟨φ,rfl⟩ := h
  use (φ.relabel Sum.inl).equal (Term.var (Sum.inr ()))
  ext v
  simp [Function.tupleGraph]

variable {L} {A B} {f : (α → M) → M}

@[fun_prop]
theorem TermDefinable.map_expansion (h : A.TermDefinable L f)
    (φ : L →ᴸ L') [φ.IsExpansionOn M] : A.TermDefinable L' f := by
  obtain ⟨ψ, rfl⟩ := h
  use (φ.addConstants A).onTerm ψ
  simp

theorem empty_termDefinable_iff :
    (∅ : Set M).TermDefinable L f ↔ ∃ φ : L.Term α, f = φ.realize := by
  rw [TermDefinable, Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onTerm]
  simp

theorem termDefinable_iff_empty_termDefinable_with_params :
    A.TermDefinable L f ↔ (∅ : Set M).TermDefinable (L[[A]]) f :=
  empty_termDefinable_iff.symm

@[fun_prop]
theorem TermDefinable.mono {f : (α → M) → M} (h : A.TermDefinable L f) (hAB : A ⊆ B) :
    B.TermDefinable L f := by
  rw [termDefinable_iff_empty_termDefinable_with_params] at *
  exact h.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

/-- TermDefinable is transitive. If f is TermDefinable in a structure S on L, and all of the
  functions' realizations on S are TermDefinable on a structure T on L', then f is
  TermDefinable on T in L'. -/
@[fun_prop]
theorem TermDefinable.trans {f : (β → M) → M} (h₁ : A.TermDefinable L f)
    (h₂ : ∀ {n} (g : L[[A]].Functions n), A.TermDefinable L' g.term.realize) :
    A.TermDefinable L' f := by
  obtain ⟨x,rfl⟩ := h₁
  use x.substFunc (fun {n} (g : L[[A]].Functions n) ↦ Classical.choose (h₂ g))
  have hc : ∀ {n} (g : L[[A]].Functions n), _ := fun {n} g ↦ congrFun (Classical.choose_spec (h₂ g))
  funext v
  induction x
  next x₀ =>
    simp
  next n f ts ih =>
    simp [← ih, ← hc]

variable (L)

/-- A function from a structure to itself is term-definable over a set `A` when the value of the
  function is given by a term with constants `A`. Like `TermDefinable` but specialized for unary
  functions in order to write `M → M` instead of `(Unit → M) → M`. -/
@[fun_prop]
def TermDefinable₁ (f : M → M) : Prop :=
  ∃ φ : L[[A]].Term Unit, f = φ.realize ∘ Function.const _

/-- `TermDefinable₁` is equivalent to `TermDefinable` on the `Unit` index type. -/
theorem TermDefinable₁_iff_TermDefinable (f : M → M) : A.TermDefinable₁ L f ↔
    A.TermDefinable L (fun v ↦ f (v ())) := by
  dsimp [TermDefinable, TermDefinable₁]
  constructor <;> intro h <;> obtain ⟨φ,hφ⟩ := h <;> use φ
  · subst hφ
    funext v
    rw [Function.comp_apply, ← eq_const_of_subsingleton]
  · funext v
    rw [Function.comp_apply, ← congrFun hφ (Function.const Unit v), Function.const]

@[fun_prop]
theorem TermDefinable.TermDefinable₁ {f : M → M} (h : A.TermDefinable L (fun v ↦ f (v ()))) :
     A.TermDefinable₁ L f :=
  (A.TermDefinable₁_iff_TermDefinable L f).mpr h

/-- A `TermDefinable₁` function has a graph that's `Definable₂`. -/
theorem TermDefinable₁.Definable₂ {f : M → M} (h : A.TermDefinable₁ L f) :
    A.Definable₂ L f.graph := by
  rw [TermDefinable₁_iff_TermDefinable] at h
  obtain ⟨t,h⟩ := TermDefinable.Definable A L h
  use t.relabel (Sum.elim (fun _ ↦ 0) (fun _ ↦ 1))
  funext v
  convert congrFun h (Sum.elim (fun _ ↦ v 0) (fun _ ↦ v 1))
  rw [setOf, Formula.realize_relabel, Sum.comp_elim]
  rfl

/-- `id` is `TermDefinable₁` -/
@[fun_prop]
theorem TermDefinable₁_id : A.TermDefinable₁ L (id : M → M) :=
  ⟨Term.var (), rfl⟩

/-- `const` is `TermDefinable₁`, if the constant value is a language constant. -/
@[fun_prop]
theorem TermDefinable₁_const (C : L[[A]].Constants) : A.TermDefinable₁ L (Function.const M C) :=
  ⟨C.term, by simp only [Term.realize_constants]; rfl⟩

/-- `TermDefinable₁` functions are closed under composition. -/
@[fun_prop]
theorem TermDefinable₁_comp {f g : M → M} (hf : A.TermDefinable₁ L f) (hg : A.TermDefinable₁ L g) :
    A.TermDefinable₁ L (f ∘ g) := by
  obtain ⟨fφ,rfl⟩ := hf
  obtain ⟨gφ,rfl⟩ := hg
  use fφ.subst (fun (_:Unit) ↦ gφ)
  funext m
  simp [Function.const_def]

/-- A `TermDefinable` function postcomposed with `TermDefinable₁` is `TermDefinable`. -/
@[fun_prop]
theorem TermDefinable₁_comp_TermDefinable {f : M → M} {g : (α → M) → M}
    (hf : A.TermDefinable₁ L f) (hg : A.TermDefinable L g) :
    A.TermDefinable L (f ∘ g) := by
  obtain ⟨fφ,rfl⟩ := hf
  obtain ⟨gφ,rfl⟩ := hg
  use fφ.subst (fun (_:Unit) ↦ gφ)
  funext m
  simp [Function.const_def]

/-- A kary `TermDefinable` function composed with k `TermDefinable` functions is `TermDefinable`. -/
theorem TermDefinable_comp_TermDefinable {f : (α → M) → M} {g : α → (β → M) → M}
    (hf : A.TermDefinable L f) (hg : ∀ a, A.TermDefinable L (g a)) :
    A.TermDefinable L (fun b ↦ f (g · b)) := by
  obtain ⟨fφ,rfl⟩ := hf
  -- obtain ⟨gφ,rfl⟩ := hg
  use fφ.subst (fun a ↦ (hg a).choose)
  funext m
  conv =>
    enter [1, 1, a]
    rw [(hg a).choose_spec]
  simp

end Set
