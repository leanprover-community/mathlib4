/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.ModelTheory.Basic

/-!
# Language Maps

Maps between first-order languages in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions

- A `FirstOrder.Language.LHom`, denoted `L →ᴸ L'`, is a map between languages, sending the symbols
  of one to symbols of the same kind and arity in the other.
- A `FirstOrder.Language.LEquiv`, denoted `L ≃ᴸ L'`, is an invertible language homomorphism.
- `FirstOrder.Language.withConstants` is defined so that if `M` is an `L.Structure` and
  `A : Set M`, `L.withConstants A`, denoted `L[[A]]`, is a language which adds constant symbols for
  elements of `A` to `L`.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]

-/

universe u v u' v' w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

variable (L : Language.{u, v}) (L' : Language.{u', v'}) {M : Type w} [L.Structure M]

/-- A language homomorphism maps the symbols of one language to symbols of another. -/
structure LHom where
  /-- The mapping of functions -/
  onFunction : ∀ ⦃n⦄, L.Functions n → L'.Functions n := by
    exact fun {n} => isEmptyElim
  /-- The mapping of relations -/
  onRelation : ∀ ⦃n⦄, L.Relations n → L'.Relations n :=by
    exact fun {n} => isEmptyElim

@[inherit_doc FirstOrder.Language.LHom]
infixl:10 " →ᴸ " => LHom

-- \^L
variable {L L'}

namespace LHom

variable (ϕ : L →ᴸ L')

/-- Pulls a structure back along a language map. -/
def reduct (M : Type*) [L'.Structure M] : L.Structure M where
  funMap f xs := funMap (ϕ.onFunction f) xs
  RelMap r xs := RelMap (ϕ.onRelation r) xs

/-- The identity language homomorphism. -/
@[simps]
protected def id (L : Language) : L →ᴸ L :=
  ⟨fun _n => id, fun _n => id⟩

instance : Inhabited (L →ᴸ L) :=
  ⟨LHom.id L⟩

/-- The inclusion of the left factor into the sum of two languages. -/
@[simps]
protected def sumInl : L →ᴸ L.sum L' :=
  ⟨fun _n => Sum.inl, fun _n => Sum.inl⟩

/-- The inclusion of the right factor into the sum of two languages. -/
@[simps]
protected def sumInr : L' →ᴸ L.sum L' :=
  ⟨fun _n => Sum.inr, fun _n => Sum.inr⟩

variable (L L')

/-- The inclusion of an empty language into any other language. -/
@[simps]
protected def ofIsEmpty [L.IsAlgebraic] [L.IsRelational] : L →ᴸ L' where

variable {L L'} {L'' : Language}

@[ext]
protected theorem funext {F G : L →ᴸ L'} (h_fun : F.onFunction = G.onFunction)
    (h_rel : F.onRelation = G.onRelation) : F = G := by
  obtain ⟨Ff, Fr⟩ := F
  obtain ⟨Gf, Gr⟩ := G
  simp only [mk.injEq]
  exact And.intro h_fun h_rel

instance [L.IsAlgebraic] [L.IsRelational] : Unique (L →ᴸ L') :=
  ⟨⟨LHom.ofIsEmpty L L'⟩, fun _ => LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- The composition of two language homomorphisms. -/
@[simps]
def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
  ⟨fun _n F => g.1 (f.1 F), fun _ R => g.2 (f.2 R)⟩

-- added ᴸ to avoid clash with function composition
@[inherit_doc]
local infixl:60 " ∘ᴸ " => LHom.comp

@[simp]
theorem id_comp (F : L →ᴸ L') : LHom.id L' ∘ᴸ F = F := by
  cases F
  rfl

@[simp]
theorem comp_id (F : L →ᴸ L') : F ∘ᴸ LHom.id L = F := by
  cases F
  rfl

theorem comp_assoc {L3 : Language} (F : L'' →ᴸ L3) (G : L' →ᴸ L'') (H : L →ᴸ L') :
    F ∘ᴸ G ∘ᴸ H = F ∘ᴸ (G ∘ᴸ H) :=
  rfl

section SumElim

variable (ψ : L'' →ᴸ L')

/-- A language map defined on two factors of a sum. -/
@[simps]
protected def sumElim : L.sum L'' →ᴸ L' where
  onFunction _n := Sum.elim (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.elim (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

theorem sumElim_comp_inl (ψ : L'' →ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInl = ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

theorem sumElim_comp_inr (ψ : L'' →ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInr = ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

theorem sumElim_inl_inr : LHom.sumInl.sumElim LHom.sumInr = LHom.id (L.sum L') :=
  LHom.funext (funext fun _ => Sum.elim_inl_inr) (funext fun _ => Sum.elim_inl_inr)

theorem comp_sumElim {L3 : Language} (θ : L' →ᴸ L3) :
    θ ∘ᴸ ϕ.sumElim ψ = (θ ∘ᴸ ϕ).sumElim (θ ∘ᴸ ψ) :=
  LHom.funext (funext fun _n => Sum.comp_elim _ _ _) (funext fun _n => Sum.comp_elim _ _ _)

end SumElim

section SumMap

variable {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂)

/-- The map between two sum-languages induced by maps on the two factors. -/
@[simps]
def sumMap : L.sum L₁ →ᴸ L'.sum L₂ where
  onFunction _n := Sum.map (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.map (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

@[simp]
theorem sumMap_comp_inl : ϕ.sumMap ψ ∘ᴸ LHom.sumInl = LHom.sumInl ∘ᴸ ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

@[simp]
theorem sumMap_comp_inr : ϕ.sumMap ψ ∘ᴸ LHom.sumInr = LHom.sumInr ∘ᴸ ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

end SumMap

/-- A language homomorphism is injective when all the maps between symbol types are. -/
protected structure Injective : Prop where
  onFunction {n} : Function.Injective fun f : L.Functions n => onFunction ϕ f
  onRelation {n} : Function.Injective fun R : L.Relations n => onRelation ϕ R

/-- Pulls an `L`-structure along a language map `ϕ : L →ᴸ L'`, and then expands it
  to an `L'`-structure arbitrarily. -/
noncomputable def defaultExpansion (ϕ : L →ᴸ L')
    [∀ (n) (f : L'.Functions n), Decidable (f ∈ Set.range fun f : L.Functions n => onFunction ϕ f)]
    [∀ (n) (r : L'.Relations n), Decidable (r ∈ Set.range fun r : L.Relations n => onRelation ϕ r)]
    (M : Type*) [Inhabited M] [L.Structure M] : L'.Structure M where
  funMap {n} f xs :=
    if h' : f ∈ Set.range fun f : L.Functions n => onFunction ϕ f then funMap h'.choose xs
    else default
  RelMap {n} r xs :=
    if h' : r ∈ Set.range fun r : L.Relations n => onRelation ϕ r then RelMap h'.choose xs
    else default

/-- A language homomorphism is an expansion on a structure if it commutes with the interpretation of
all symbols on that structure. -/
class IsExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] : Prop where
  map_onFunction :
    ∀ {n} (f : L.Functions n) (x : Fin n → M), funMap (ϕ.onFunction f) x = funMap f x := by
      exact fun {n} => isEmptyElim
  map_onRelation :
    ∀ {n} (R : L.Relations n) (x : Fin n → M), RelMap (ϕ.onRelation R) x = RelMap R x := by
      exact fun {n} => isEmptyElim

@[simp]
theorem map_onFunction {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (f : L.Functions n) (x : Fin n → M) : funMap (ϕ.onFunction f) x = funMap f x :=
  IsExpansionOn.map_onFunction f x

@[simp]
theorem map_onRelation {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (R : L.Relations n) (x : Fin n → M) : RelMap (ϕ.onRelation R) x = RelMap R x :=
  IsExpansionOn.map_onRelation R x

instance id_isExpansionOn (M : Type*) [L.Structure M] : IsExpansionOn (LHom.id L) M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

instance ofIsEmpty_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] [L.IsAlgebraic]
    [L.IsRelational] : IsExpansionOn (LHom.ofIsEmpty L L') M where

instance sumElim_isExpansionOn {L'' : Language} (ψ : L'' →ᴸ L') (M : Type*) [L.Structure M]
    [L'.Structure M] [L''.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sumElim ψ).IsExpansionOn M :=
  ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

instance sumMap_isExpansionOn {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂) (M : Type*) [L.Structure M]
    [L'.Structure M] [L₁.Structure M] [L₂.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sumMap ψ).IsExpansionOn M :=
  ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

instance sumInl_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] :
    (LHom.sumInl : L →ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

instance sumInr_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] :
    (LHom.sumInr : L' →ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

@[simp]
theorem funMap_sumInl [(L.sum L').Structure M] [(LHom.sumInl : L →ᴸ L.sum L').IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n → M} : @funMap (L.sum L') M _ n (Sum.inl f) x = funMap f x :=
  (LHom.sumInl : L →ᴸ L.sum L').map_onFunction f x

@[simp]
theorem funMap_sumInr [(L'.sum L).Structure M] [(LHom.sumInr : L →ᴸ L'.sum L).IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n → M} : @funMap (L'.sum L) M _ n (Sum.inr f) x = funMap f x :=
  (LHom.sumInr : L →ᴸ L'.sum L).map_onFunction f x

theorem sumInl_injective : (LHom.sumInl : L →ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inl_injective h, fun h => Sum.inl_injective h⟩

theorem sumInr_injective : (LHom.sumInr : L' →ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inr_injective h, fun h => Sum.inr_injective h⟩

instance (priority := 100) isExpansionOn_reduct (ϕ : L →ᴸ L') (M : Type*) [L'.Structure M] :
    @IsExpansionOn L L' ϕ M (ϕ.reduct M) _ :=
  letI := ϕ.reduct M
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

theorem Injective.isExpansionOn_default {ϕ : L →ᴸ L'}
    [∀ (n) (f : L'.Functions n), Decidable (f ∈ Set.range fun f : L.Functions n => ϕ.onFunction f)]
    [∀ (n) (r : L'.Relations n), Decidable (r ∈ Set.range fun r : L.Relations n => ϕ.onRelation r)]
    (h : ϕ.Injective) (M : Type*) [Inhabited M] [L.Structure M] :
    @IsExpansionOn L L' ϕ M _ (ϕ.defaultExpansion M) := by
  letI := ϕ.defaultExpansion M
  refine ⟨fun {n} f xs => ?_, fun {n} r xs => ?_⟩
  · have hf : ϕ.onFunction f ∈ Set.range fun f : L.Functions n => ϕ.onFunction f := ⟨f, rfl⟩
    refine (dif_pos hf).trans ?_
    rw [h.onFunction hf.choose_spec]
  · have hr : ϕ.onRelation r ∈ Set.range fun r : L.Relations n => ϕ.onRelation r := ⟨r, rfl⟩
    refine (dif_pos hr).trans ?_
    rw [h.onRelation hr.choose_spec]

end LHom

/-- A language equivalence maps the symbols of one language to symbols of another bijectively. -/
structure LEquiv (L L' : Language) where
  /-- The forward language homomorphism -/
  toLHom : L →ᴸ L'
  /-- The inverse language homomorphism -/
  invLHom : L' →ᴸ L
  left_inv : invLHom.comp toLHom = LHom.id L
  right_inv : toLHom.comp invLHom = LHom.id L'

@[inherit_doc] infixl:10 " ≃ᴸ " => LEquiv

-- \^L
namespace LEquiv

variable (L) in
/-- The identity equivalence from a first-order language to itself. -/
@[simps]
protected def refl : L ≃ᴸ L :=
  ⟨LHom.id L, LHom.id L, LHom.comp_id _, LHom.comp_id _⟩

instance : Inhabited (L ≃ᴸ L) :=
  ⟨LEquiv.refl L⟩

variable {L'' : Language} (e' : L' ≃ᴸ L'') (e : L ≃ᴸ L')

/-- The inverse of an equivalence of first-order languages. -/
@[simps]
protected def symm : L' ≃ᴸ L :=
  ⟨e.invLHom, e.toLHom, e.right_inv, e.left_inv⟩

/-- The composition of equivalences of first-order languages. -/
@[simps, trans]
protected def trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') : L ≃ᴸ L'' :=
  ⟨e'.toLHom.comp e.toLHom, e.invLHom.comp e'.invLHom, by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e'.invLHom, e'.left_inv, LHom.id_comp, e.left_inv], by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e.toLHom, e.right_inv, LHom.id_comp, e'.right_inv]⟩

end LEquiv

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

theorem card_constantsOn : (constantsOn α).card = #α := by
  simp [card_eq_card_functions_add_card_relations, sum_nat_eq_add_sum_succ]

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
    ⟨fun {n} => Nat.casesOn n (fun F _x => (congr_fun h F :)) fun n F => isEmptyElim F, fun R =>
      isEmptyElim R⟩

end ConstantsOn

section WithConstants

variable (L)

section

variable (α : Type w')

/-- Extends a language with a constant for each element of a parameter set in `M`. -/
def withConstants : Language.{max u w', v} :=
  L.sum (constantsOn α)

@[inherit_doc FirstOrder.Language.withConstants]
scoped[FirstOrder] notation:95 L "[[" α "]]" => Language.withConstants L α

@[simp]
theorem card_withConstants :
    L[[α]].card = Cardinal.lift.{w'} L.card + Cardinal.lift.{max u v} #α := by
  rw [withConstants, card_sum, card_constantsOn]

/-- The language map adding constants. -/
@[simps!]
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
theorem withConstants_funMap_sumInl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {f : L.Functions n} {x : Fin n → M} : @funMap (L[[α]]) M _ n (Sum.inl f) x = funMap f x :=
  (lhomWithConstants L α).map_onFunction f x

@[simp]
theorem withConstants_relMap_sumInl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {R : L.Relations n} {x : Fin n → M} : @RelMap (L[[α]]) M _ n (Sum.inl R) x = RelMap R x :=
  (lhomWithConstants L α).map_onRelation R x

@[deprecated (since := "2025-02-21")] alias
withConstants_funMap_sum_inl := withConstants_funMap_sumInl
@[deprecated (since := "2025-02-21")] alias
withConstants_relMap_sum_inl := withConstants_relMap_sumInl

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
theorem withConstants_funMap_sumInr {a : α} {x : Fin 0 → M} :
    @funMap (L[[α]]) M _ 0 (Sum.inr a : L[[α]].Functions 0) x = L.con a := by
  rw [Unique.eq_default x]
  exact (LHom.sumInr : constantsOn α →ᴸ L.sum _).map_onFunction _ _

@[deprecated (since := "2025-02-21")] alias
withConstants_funMap_sum_inr := withConstants_funMap_sumInr

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
