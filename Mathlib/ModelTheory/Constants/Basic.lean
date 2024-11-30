/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.ModelTheory.LanguageMap

/-!
# Adding constants to a language

## Main Definitions

- `FirstOrder.Language.withConstants` is defined so that if `M` is an `L.Structure` and
  `A : Set M`, `L.withConstants A`, denoted `L[[A]]`, is a language which adds constant symbols for
  elements of `A` to `L`.

-/

universe u v u' v' w w'

namespace FirstOrder

namespace Language

open Structure

variable (L : Language.{u, v}) (L' : Language.{u', v'}) {M : Type w} [L.Structure M]

section ConstantsOn

variable (α : Type u')

/-- The type of functions for a language consisting only of constant symbols. -/
@[simp]
def constantsOnFunc : ℕ → Type u'
  | 0 => α
  | (_ + 1) => PEmpty

/-- A language with constants indexed by a type. -/
@[simps]
def constantsOn : Language.{u', 0} := ⟨constantsOnFunc α, fun _ => Empty⟩

variable {α}

theorem constantsOn_constants : (constantsOn α).Constants = α :=
  rfl

instance isAlgebraic_constantsOn : IsAlgebraic (constantsOn α) := by
  unfold constantsOn
  infer_instance

instance isEmpty_functions_constantsOn_succ {n : ℕ} : IsEmpty ((constantsOn α).Functions (n + 1)) :=
  inferInstanceAs (IsEmpty PEmpty)

instance isRelational_constantsOn [_ie : IsEmpty α] : IsRelational (constantsOn α) :=
  fun n => Nat.casesOn n _ie inferInstance

/-- Gives a `constantsOn α` structure to a type by assigning each constant a value. -/
def constantsOn.structure (f : α → M) : (constantsOn α).Structure M where
  funMap := fun {n} c _ =>
    match n, c with
    | 0, c => f c

variable {β : Type v'}

/-- A map between index types induces a map between constant languages. -/
def LHom.constantsOnMap (f : α → β) : constantsOn α →ᴸ constantsOn β where
  onFunction := fun {n} c =>
    match n, c with
    | 0, c => f c

theorem constantsOnMap_isExpansionOn {f : α → β} {fα : α → M} {fβ : β → M} (h : fβ ∘ f = fα) :
    @LHom.IsExpansionOn _ _ (LHom.constantsOnMap f) M (constantsOn.structure fα)
      (constantsOn.structure fβ) := by
  letI := constantsOn.structure fα
  letI := constantsOn.structure fβ
  exact
    ⟨fun {n} => Nat.casesOn n (fun F _x => (congr_fun h F : _)) fun n F => isEmptyElim F, fun R =>
      isEmptyElim R⟩

end ConstantsOn

section WithConstants

section

variable (α : Type w')

/-- Extends a language with a constant for each element of a parameter set in `M`. -/
def withConstants : Language.{max u w', v} :=
  L.sum (constantsOn α)

@[inherit_doc FirstOrder.Language.withConstants]
scoped[FirstOrder] notation:95 L "[[" α "]]" => Language.withConstants L α

/-- The language map adding constants. -/
@[simps!] -- Porting note: add `!` to `simps`
def lhomWithConstants : L →ᴸ L[[α]] :=
  LHom.sumInl

theorem lhomWithConstants_injective : (L.lhomWithConstants α).Injective :=
  LHom.sumInl_injective

variable {α}

/-- The constant symbol indexed by a particular element. -/
protected def con (a : α) : L[[α]].Constants :=
  Sum.inr a

variable {L} (α)

/-- Adds constants to a language map. -/
def LHom.addConstants {L' : Language} (φ : L →ᴸ L') : L[[α]] →ᴸ L'[[α]] :=
  φ.sumMap (LHom.id _)

instance paramsStructure (A : Set α) : (constantsOn A).Structure α :=
  constantsOn.structure (↑)

variable (L)

/-- The language map removing an empty constant set. -/
@[simps]
def LEquiv.addEmptyConstants [ie : IsEmpty α] : L ≃ᴸ L[[α]] where
  toLHom := lhomWithConstants L α
  invLHom := LHom.sumElim (LHom.id L) (LHom.ofIsEmpty (constantsOn α) L)
  left_inv := by rw [lhomWithConstants, LHom.sumElim_comp_inl]
  right_inv := by
    simp only [LHom.comp_sumElim, lhomWithConstants, LHom.comp_id]
    exact _root_.trans (congr rfl (Subsingleton.elim _ _)) LHom.sumElim_inl_inr

variable {α} {β : Type*}

@[simp]
theorem withConstants_funMap_sum_inl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {f : L.Functions n} {x : Fin n → M} : @funMap (L[[α]]) M _ n (Sum.inl f) x = funMap f x :=
  (lhomWithConstants L α).map_onFunction f x

@[simp]
theorem withConstants_relMap_sum_inl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {R : L.Relations n} {x : Fin n → M} : @RelMap (L[[α]]) M _ n (Sum.inl R) x = RelMap R x :=
  (lhomWithConstants L α).map_onRelation R x

/-- The language map extending the constant set. -/
def lhomWithConstantsMap (f : α → β) : L[[α]] →ᴸ L[[β]] :=
  LHom.sumMap (LHom.id L) (LHom.constantsOnMap f)

@[simp]
theorem LHom.map_constants_comp_sumInl {f : α → β} :
    (L.lhomWithConstantsMap f).comp LHom.sumInl = L.lhomWithConstants β := by ext <;> rfl

end

open FirstOrder

instance constantsOnSelfStructure : (constantsOn M).Structure M :=
  constantsOn.structure id

instance withConstantsSelfStructure : L[[M]].Structure M :=
  Language.sumStructure _ _ M

instance withConstants_self_expansion : (lhomWithConstants L M).IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

variable (α : Type*) [(constantsOn α).Structure M]

instance withConstantsStructure : L[[α]].Structure M :=
  Language.sumStructure _ _ _

instance withConstants_expansion : (L.lhomWithConstants α).IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

instance addEmptyConstants_is_expansion_on' :
    (LEquiv.addEmptyConstants L (∅ : Set M)).toLHom.IsExpansionOn M :=
  L.withConstants_expansion _

instance addEmptyConstants_symm_isExpansionOn :
    (LEquiv.addEmptyConstants L (∅ : Set M)).symm.toLHom.IsExpansionOn M :=
  LHom.sumElim_isExpansionOn _ _ _

instance addConstants_expansion {L' : Language} [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    (φ.addConstants α).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ M

@[simp]
theorem withConstants_funMap_sum_inr {a : α} {x : Fin 0 → M} :
    @funMap (L[[α]]) M _ 0 (Sum.inr a : L[[α]].Functions 0) x = L.con a := by
  rw [Unique.eq_default x]
  exact (LHom.sumInr : constantsOn α →ᴸ L.sum _).map_onFunction _ _

variable {α} (A : Set M)

@[simp]
theorem coe_con {a : A} : (L.con a : M) = a :=
  rfl

variable {A} {B : Set M} (h : A ⊆ B)

instance constantsOnMap_inclusion_isExpansionOn :
    (LHom.constantsOnMap (Set.inclusion h)).IsExpansionOn M :=
  constantsOnMap_isExpansionOn rfl

instance map_constants_inclusion_isExpansionOn :
    (L.lhomWithConstantsMap (Set.inclusion h)).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ _

end WithConstants

end Language

end FirstOrder
