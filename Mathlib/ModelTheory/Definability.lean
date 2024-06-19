/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.ModelTheory.Semantics

#align_import model_theory.definability from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Definable Sets
This file defines what it means for a set over a first-order structure to be definable.

## Main Definitions
* `Set.Definable` is defined so that `A.Definable L s` indicates that the
set `s` of a finite cartesian power of `M` is definable with parameters in `A`.
* `Set.Definable₁` is defined so that `A.Definable₁ L s` indicates that
`(s : Set M)` is definable with parameters in `A`.
* `Set.Definable₂` is defined so that `A.Definable₂ L s` indicates that
`(s : Set (M × M))` is definable with parameters in `A`.
* A `FirstOrder.Language.DefinableSet` is defined so that `L.DefinableSet A α` is the boolean
  algebra of subsets of `α → M` defined by formulas with parameters in `A`.

## Main Results
* `L.DefinableSet A α` forms a `BooleanAlgebra`
* `Set.Definable.image_comp` shows that definability is closed under projections in finite
  dimensions.

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
#align set.definable Set.Definable

variable {L} {A} {B : Set M} {s : Set (α → M)}

theorem Definable.map_expansion {L' : FirstOrder.Language} [L'.Structure M] (h : A.Definable L s)
    (φ : L →ᴸ L') [φ.IsExpansionOn M] : A.Definable L' s := by
  obtain ⟨ψ, rfl⟩ := h
  refine ⟨(φ.addConstants A).onFormula ψ, ?_⟩
  ext x
  simp only [mem_setOf_eq, LHom.realize_onFormula]
#align set.definable.map_expansion Set.Definable.map_expansion

theorem definable_iff_exists_formula_sum :
    A.Definable L s ↔ ∃ φ : L.Formula (A ⊕ α), s = {v | φ.Realize (Sum.elim (↑) v)} := by
  rw [Definable, Equiv.exists_congr_left (BoundedFormula.constantsVarsEquiv)]
  refine exists_congr (fun φ => iff_iff_eq.2 (congr_arg (s = ·) ?_))
  ext
  simp only [Formula.Realize, BoundedFormula.constantsVarsEquiv, constantsOn, mk₂_Relations,
    BoundedFormula.mapTermRelEquiv_symm_apply, mem_setOf_eq]
  refine BoundedFormula.realize_mapTermRel_id ?_ (fun _ _ _ => rfl)
  intros
  simp only [Term.constantsVarsEquivLeft_symm_apply, Term.realize_varsToConstants,
    coe_con, Term.realize_relabel]
  congr
  ext a
  rcases a with (_ | _) | _ <;> rfl

theorem empty_definable_iff :
    (∅ : Set M).Definable L s ↔ ∃ φ : L.Formula α, s = setOf φ.Realize := by
  rw [Definable, Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onFormula]
  simp [-constantsOn]
#align set.empty_definable_iff Set.empty_definable_iff

theorem definable_iff_empty_definable_with_params :
    A.Definable L s ↔ (∅ : Set M).Definable (L[[A]]) s :=
  empty_definable_iff.symm
#align set.definable_iff_empty_definable_with_params Set.definable_iff_empty_definable_with_params

theorem Definable.mono (hAs : A.Definable L s) (hAB : A ⊆ B) : B.Definable L s := by
  rw [definable_iff_empty_definable_with_params] at *
  exact hAs.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))
#align set.definable.mono Set.Definable.mono

@[simp]
theorem definable_empty : A.Definable L (∅ : Set (α → M)) :=
  ⟨⊥, by
    ext
    simp⟩
#align set.definable_empty Set.definable_empty

@[simp]
theorem definable_univ : A.Definable L (univ : Set (α → M)) :=
  ⟨⊤, by
    ext
    simp⟩
#align set.definable_univ Set.definable_univ

@[simp]
theorem Definable.inter {f g : Set (α → M)} (hf : A.Definable L f) (hg : A.Definable L g) :
    A.Definable L (f ∩ g) := by
  rcases hf with ⟨φ, rfl⟩
  rcases hg with ⟨θ, rfl⟩
  refine ⟨φ ⊓ θ, ?_⟩
  ext
  simp
#align set.definable.inter Set.Definable.inter

@[simp]
theorem Definable.union {f g : Set (α → M)} (hf : A.Definable L f) (hg : A.Definable L g) :
    A.Definable L (f ∪ g) := by
  rcases hf with ⟨φ, hφ⟩
  rcases hg with ⟨θ, hθ⟩
  refine ⟨φ ⊔ θ, ?_⟩
  ext
  rw [hφ, hθ, mem_setOf_eq, Formula.realize_sup, mem_union, mem_setOf_eq, mem_setOf_eq]
#align set.definable.union Set.Definable.union

theorem definable_finset_inf {ι : Type*} {f : ι → Set (α → M)} (hf : ∀ i, A.Definable L (f i))
    (s : Finset ι) : A.Definable L (s.inf f) := by
  classical
    refine Finset.induction definable_univ (fun i s _ h => ?_) s
    rw [Finset.inf_insert]
    exact (hf i).inter h
#align set.definable_finset_inf Set.definable_finset_inf

theorem definable_finset_sup {ι : Type*} {f : ι → Set (α → M)} (hf : ∀ i, A.Definable L (f i))
    (s : Finset ι) : A.Definable L (s.sup f) := by
  classical
    refine Finset.induction definable_empty (fun i s _ h => ?_) s
    rw [Finset.sup_insert]
    exact (hf i).union h
#align set.definable_finset_sup Set.definable_finset_sup

theorem definable_finset_biInter {ι : Type*} {f : ι → Set (α → M)}
    (hf : ∀ i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋂ i ∈ s, f i) := by
  rw [← Finset.inf_set_eq_iInter]
  exact definable_finset_inf hf s
#align set.definable_finset_bInter Set.definable_finset_biInter

theorem definable_finset_biUnion {ι : Type*} {f : ι → Set (α → M)}
    (hf : ∀ i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋃ i ∈ s, f i) := by
  rw [← Finset.sup_set_eq_biUnion]
  exact definable_finset_sup hf s
#align set.definable_finset_bUnion Set.definable_finset_biUnion

@[simp]
theorem Definable.compl {s : Set (α → M)} (hf : A.Definable L s) : A.Definable L sᶜ := by
  rcases hf with ⟨φ, hφ⟩
  refine ⟨φ.not, ?_⟩
  ext v
  rw [hφ, compl_setOf, mem_setOf, mem_setOf, Formula.realize_not]
#align set.definable.compl Set.Definable.compl

@[simp]
theorem Definable.sdiff {s t : Set (α → M)} (hs : A.Definable L s) (ht : A.Definable L t) :
    A.Definable L (s \ t) :=
  hs.inter ht.compl
#align set.definable.sdiff Set.Definable.sdiff

theorem Definable.preimage_comp (f : α → β) {s : Set (α → M)} (h : A.Definable L s) :
    A.Definable L ((fun g : β → M => g ∘ f) ⁻¹' s) := by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨φ.relabel f, ?_⟩
  ext
  simp only [Set.preimage_setOf_eq, mem_setOf_eq, Formula.realize_relabel]
#align set.definable.preimage_comp Set.Definable.preimage_comp

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
#align set.definable.image_comp_equiv Set.Definable.image_comp_equiv

theorem definable_iff_finitely_definable :
    A.Definable L s ↔ ∃ (A0 : Finset M), (A0 : Set M) ⊆ A ∧
      (A0 : Set M).Definable L s := by
  letI := Classical.decEq M
  letI := Classical.decEq α
  constructor
  · simp only [definable_iff_exists_formula_sum]
    rintro ⟨φ, rfl⟩
    let A0 := (φ.freeVarFinset.preimage Sum.inl
      (Function.Injective.injOn Sum.inl_injective _)).image Subtype.val
    have hA0 : (A0 : Set M) ⊆ A := by simp [A0]
    refine ⟨A0, hA0, (φ.restrictFreeVar
      (Set.inclusion (Set.Subset.refl _))).relabel ?_, ?_⟩
    · rintro ⟨a | a, ha⟩
      · exact Sum.inl (Sum.inl ⟨a, by simpa [A0] using ha⟩)
      · exact Sum.inl (Sum.inr a)
    · ext v
      simp only [Formula.Realize, BoundedFormula.realize_relabel,
        Set.mem_setOf_eq]
      apply Iff.symm
      convert BoundedFormula.realize_restrictFreeVar _
      ext a
      rcases a with ⟨_ | _, _⟩ <;> simp
  · rintro ⟨A0, hA0, hd⟩
    exact Definable.mono hd hA0

/-- This lemma is only intended as a helper for `Definable.image_comp`. -/
theorem Definable.image_comp_sum_inl_fin (m : ℕ) {s : Set (Sum α (Fin m) → M)}
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
#align set.definable.image_comp_sum_inl_fin Set.Definable.image_comp_sum_inl_fin

/-- Shows that definability is closed under finite projections. -/
theorem Definable.image_comp_embedding {s : Set (β → M)} (h : A.Definable L s) (f : α ↪ β)
    [Finite β] : A.Definable L ((fun g : β → M => g ∘ f) '' s) := by
  classical
    cases nonempty_fintype β
    refine
      (congr rfl (ext fun x => ?_)).mp
        (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
              (Equiv.sumCongr (Equiv.ofInjective f f.injective)
                (Fintype.equivFin (↥(range f)ᶜ)).symm)).image_comp_sum_inl_fin
          _)
    simp only [mem_preimage, mem_image, exists_exists_and_eq_and]
    refine exists_congr fun y => and_congr_right fun _ => Eq.congr_left (funext fun a => ?_)
    simp
#align set.definable.image_comp_embedding Set.Definable.image_comp_embedding

/-- Shows that definability is closed under finite projections. -/
theorem Definable.image_comp {s : Set (β → M)} (h : A.Definable L s) (f : α → β) [Finite α]
    [Finite β] : A.Definable L ((fun g : β → M => g ∘ f) '' s) := by
  classical
    cases nonempty_fintype α
    cases nonempty_fintype β
    have h :=
      (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
                (Equiv.sumCongr (_root_.Equiv.refl _)
                  (Fintype.equivFin _).symm)).image_comp_sum_inl_fin
            _).preimage_comp
        (rangeSplitting f)
    have h' :
      A.Definable L { x : α → M | ∀ a, x a = x (rangeSplitting f (rangeFactorization f a)) } := by
      have h' : ∀ a,
        A.Definable L { x : α → M | x a = x (rangeSplitting f (rangeFactorization f a)) } := by
          refine fun a => ⟨(var a).equal (var (rangeSplitting f (rangeFactorization f a))), ext ?_⟩
          simp
      refine (congr rfl (ext ?_)).mp (definable_finset_biInter h' Finset.univ)
      simp
    refine (congr rfl (ext fun x => ?_)).mp (h.inter h')
    simp only [Equiv.coe_trans, mem_inter_iff, mem_preimage, mem_image, exists_exists_and_eq_and,
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
#align set.definable.image_comp Set.Definable.image_comp

variable (L A)

/-- A 1-dimensional version of `Definable`, for `Set M`. -/
def Definable₁ (s : Set M) : Prop :=
  A.Definable L { x : Fin 1 → M | x 0 ∈ s }
#align set.definable₁ Set.Definable₁

/-- A 2-dimensional version of `Definable`, for `Set (M × M)`. -/
def Definable₂ (s : Set (M × M)) : Prop :=
  A.Definable L { x : Fin 2 → M | (x 0, x 1) ∈ s }
#align set.definable₂ Set.Definable₂

end Set

namespace FirstOrder

namespace Language

open Set

variable (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M] (A : Set M) (α : Type u₁)

/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
def DefinableSet :=
  { s : Set (α → M) // A.Definable L s }
#align first_order.language.definable_set FirstOrder.Language.DefinableSet

namespace DefinableSet

variable {L A α} {s t : L.DefinableSet A α} {x : α → M}

instance instSetLike : SetLike (L.DefinableSet A α) (α → M) where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective
#align first_order.language.definable_set.pi.set_like FirstOrder.Language.DefinableSet.instSetLike

instance instTop : Top (L.DefinableSet A α) :=
  ⟨⟨⊤, definable_univ⟩⟩
#align first_order.language.definable_set.has_top FirstOrder.Language.DefinableSet.instTop

instance instBot : Bot (L.DefinableSet A α) :=
  ⟨⟨⊥, definable_empty⟩⟩
#align first_order.language.definable_set.has_bot FirstOrder.Language.DefinableSet.instBot

instance instSup : Sup (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s ∪ t, s.2.union t.2⟩⟩
#align first_order.language.definable_set.has_sup FirstOrder.Language.DefinableSet.instSup

instance instInf : Inf (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s ∩ t, s.2.inter t.2⟩⟩
#align first_order.language.definable_set.has_inf FirstOrder.Language.DefinableSet.instInf

instance instHasCompl : HasCompl (L.DefinableSet A α) :=
  ⟨fun s => ⟨sᶜ, s.2.compl⟩⟩
#align first_order.language.definable_set.has_compl FirstOrder.Language.DefinableSet.instHasCompl

instance instSDiff : SDiff (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s \ t, s.2.sdiff t.2⟩⟩
#align first_order.language.definable_set.has_sdiff FirstOrder.Language.DefinableSet.instSDiff

instance instInhabited : Inhabited (L.DefinableSet A α) :=
  ⟨⊥⟩
#align first_order.language.definable_set.inhabited FirstOrder.Language.DefinableSet.instInhabited

theorem le_iff : s ≤ t ↔ (s : Set (α → M)) ≤ (t : Set (α → M)) :=
  Iff.rfl
#align first_order.language.definable_set.le_iff FirstOrder.Language.DefinableSet.le_iff

@[simp]
theorem mem_top : x ∈ (⊤ : L.DefinableSet A α) :=
  mem_univ x
#align first_order.language.definable_set.mem_top FirstOrder.Language.DefinableSet.mem_top

@[simp]
theorem not_mem_bot {x : α → M} : ¬x ∈ (⊥ : L.DefinableSet A α) :=
  not_mem_empty x
#align first_order.language.definable_set.not_mem_bot FirstOrder.Language.DefinableSet.not_mem_bot

@[simp]
theorem mem_sup : x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t :=
  Iff.rfl
#align first_order.language.definable_set.mem_sup FirstOrder.Language.DefinableSet.mem_sup

@[simp]
theorem mem_inf : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t :=
  Iff.rfl
#align first_order.language.definable_set.mem_inf FirstOrder.Language.DefinableSet.mem_inf

@[simp]
theorem mem_compl : x ∈ sᶜ ↔ ¬x ∈ s :=
  Iff.rfl
#align first_order.language.definable_set.mem_compl FirstOrder.Language.DefinableSet.mem_compl

@[simp]
theorem mem_sdiff : x ∈ s \ t ↔ x ∈ s ∧ ¬x ∈ t :=
  Iff.rfl
#align first_order.language.definable_set.mem_sdiff FirstOrder.Language.DefinableSet.mem_sdiff

@[simp, norm_cast]
theorem coe_top : ((⊤ : L.DefinableSet A α) : Set (α → M)) = univ :=
  rfl
#align first_order.language.definable_set.coe_top FirstOrder.Language.DefinableSet.coe_top

@[simp, norm_cast]
theorem coe_bot : ((⊥ : L.DefinableSet A α) : Set (α → M)) = ∅ :=
  rfl
#align first_order.language.definable_set.coe_bot FirstOrder.Language.DefinableSet.coe_bot

@[simp, norm_cast]
theorem coe_sup (s t : L.DefinableSet A α) :
    ((s ⊔ t : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M)) ∪ (t : Set (α → M)) :=
  rfl
#align first_order.language.definable_set.coe_sup FirstOrder.Language.DefinableSet.coe_sup

@[simp, norm_cast]
theorem coe_inf (s t : L.DefinableSet A α) :
    ((s ⊓ t : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M)) ∩ (t : Set (α → M)) :=
  rfl
#align first_order.language.definable_set.coe_inf FirstOrder.Language.DefinableSet.coe_inf

@[simp, norm_cast]
theorem coe_compl (s : L.DefinableSet A α) :
    ((sᶜ : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M))ᶜ :=
  rfl
#align first_order.language.definable_set.coe_compl FirstOrder.Language.DefinableSet.coe_compl

@[simp, norm_cast]
theorem coe_sdiff (s t : L.DefinableSet A α) :
    ((s \ t : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M)) \ (t : Set (α → M)) :=
  rfl
#align first_order.language.definable_set.coe_sdiff FirstOrder.Language.DefinableSet.coe_sdiff

instance instBooleanAlgebra : BooleanAlgebra (L.DefinableSet A α) :=
  Function.Injective.booleanAlgebra (α := L.DefinableSet A α) _ Subtype.coe_injective
    coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff
#align first_order.language.definable_set.boolean_algebra FirstOrder.Language.DefinableSet.instBooleanAlgebra

end DefinableSet

end Language

end FirstOrder
