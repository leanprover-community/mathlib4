/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.ModelTheory.Basic

#align_import model_theory.language_map from "leanprover-community/mathlib"@"b3951c65c6e797ff162ae8b69eab0063bcfb3d73"

/-!
# Language Maps
Maps between first-order languages in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions
* A `FirstOrder.Language.LHom`, denoted `L →ᴸ L'`, is a map between languages, sending the symbols
  of one to symbols of the same kind and arity in the other.
* A `FirstOrder.Language.LEquiv`, denoted `L ≃ᴸ L'`, is an invertible language homomorphism.
* `FirstOrder.Language.withConstants` is defined so that if `M` is an `L.Structure` and
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

set_option linter.uppercaseLean3 false

namespace Language

open Structure Cardinal

open Cardinal

variable (L : Language.{u, v}) (L' : Language.{u', v'}) {M : Type w} [L.Structure M]

/-- A language homomorphism maps the symbols of one language to symbols of another. -/
structure LHom where
  onFunction : ∀ ⦃n⦄, L.Functions n → L'.Functions n
  onRelation : ∀ ⦃n⦄, L.Relations n → L'.Relations n
#align first_order.language.Lhom FirstOrder.Language.LHom

@[inherit_doc FirstOrder.Language.LHom]
infixl:10 " →ᴸ " => LHom

-- \^L
variable {L L'}

namespace LHom

/-- Defines a map between languages defined with `Language.mk₂`. -/
protected def mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (φ₀ : c → L'.Constants)
    (φ₁ : f₁ → L'.Functions 1) (φ₂ : f₂ → L'.Functions 2) (φ₁' : r₁ → L'.Relations 1)
    (φ₂' : r₂ → L'.Relations 2) : Language.mk₂ c f₁ f₂ r₁ r₂ →ᴸ L' :=
  ⟨fun n =>
    Nat.casesOn n φ₀ fun n => Nat.casesOn n φ₁ fun n => Nat.casesOn n φ₂ fun _ => PEmpty.elim,
    fun n =>
    Nat.casesOn n PEmpty.elim fun n =>
      Nat.casesOn n φ₁' fun n => Nat.casesOn n φ₂' fun _ => PEmpty.elim⟩
#align first_order.language.Lhom.mk₂ FirstOrder.Language.LHom.mk₂

variable (ϕ : L →ᴸ L')

/-- Pulls a structure back along a language map. -/
def reduct (M : Type*) [L'.Structure M] : L.Structure M where
  funMap f xs := funMap (ϕ.onFunction f) xs
  RelMap r xs := RelMap (ϕ.onRelation r) xs
#align first_order.language.Lhom.reduct FirstOrder.Language.LHom.reduct

/-- The identity language homomorphism. -/
@[simps]
protected def id (L : Language) : L →ᴸ L :=
  ⟨fun _n => id, fun _n => id⟩
#align first_order.language.Lhom.id FirstOrder.Language.LHom.id

instance : Inhabited (L →ᴸ L) :=
  ⟨LHom.id L⟩

/-- The inclusion of the left factor into the sum of two languages. -/
@[simps]
protected def sumInl : L →ᴸ L.sum L' :=
  ⟨fun _n => Sum.inl, fun _n => Sum.inl⟩
#align first_order.language.Lhom.sum_inl FirstOrder.Language.LHom.sumInl

/-- The inclusion of the right factor into the sum of two languages. -/
@[simps]
protected def sumInr : L' →ᴸ L.sum L' :=
  ⟨fun _n => Sum.inr, fun _n => Sum.inr⟩
#align first_order.language.Lhom.sum_inr FirstOrder.Language.LHom.sumInr

variable (L L')

/-- The inclusion of an empty language into any other language. -/
@[simps]
protected def ofIsEmpty [L.IsAlgebraic] [L.IsRelational] : L →ᴸ L' :=
  ⟨fun n => (IsRelational.empty_functions n).elim, fun n => (IsAlgebraic.empty_relations n).elim⟩
#align first_order.language.Lhom.of_is_empty FirstOrder.Language.LHom.ofIsEmpty

variable {L L'} {L'' : Language}

@[ext]
protected theorem funext {F G : L →ᴸ L'} (h_fun : F.onFunction = G.onFunction)
    (h_rel : F.onRelation = G.onRelation) : F = G := by
  cases' F with Ff Fr
  cases' G with Gf Gr
  simp only [mk.injEq]
  exact And.intro h_fun h_rel
#align first_order.language.Lhom.funext FirstOrder.Language.LHom.funext

instance [L.IsAlgebraic] [L.IsRelational] : Unique (L →ᴸ L') :=
  ⟨⟨LHom.ofIsEmpty L L'⟩, fun _ => LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

theorem mk₂_funext {c f₁ f₂ : Type u} {r₁ r₂ : Type v} {F G : Language.mk₂ c f₁ f₂ r₁ r₂ →ᴸ L'}
    (h0 : ∀ c : (Language.mk₂ c f₁ f₂ r₁ r₂).Constants, F.onFunction c = G.onFunction c)
    (h1 : ∀ f : (Language.mk₂ c f₁ f₂ r₁ r₂).Functions 1, F.onFunction f = G.onFunction f)
    (h2 : ∀ f : (Language.mk₂ c f₁ f₂ r₁ r₂).Functions 2, F.onFunction f = G.onFunction f)
    (h1' : ∀ r : (Language.mk₂ c f₁ f₂ r₁ r₂).Relations 1, F.onRelation r = G.onRelation r)
    (h2' : ∀ r : (Language.mk₂ c f₁ f₂ r₁ r₂).Relations 2, F.onRelation r = G.onRelation r) :
    F = G :=
  LHom.funext
    (funext fun n =>
      Nat.casesOn n (funext h0) fun n =>
        Nat.casesOn n (funext h1) fun n =>
          Nat.casesOn n (funext h2) fun _n => funext fun f => PEmpty.elim f)
    (funext fun n =>
      Nat.casesOn n (funext fun r => PEmpty.elim r) fun n =>
        Nat.casesOn n (funext h1') fun n =>
          Nat.casesOn n (funext h2') fun _n => funext fun r => PEmpty.elim r)
#align first_order.language.Lhom.mk₂_funext FirstOrder.Language.LHom.mk₂_funext

/-- The composition of two language homomorphisms. -/
@[simps]
def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
  ⟨fun _n F => g.1 (f.1 F), fun _ R => g.2 (f.2 R)⟩
#align first_order.language.Lhom.comp FirstOrder.Language.LHom.comp

-- Porting note: added ᴸ to avoid clash with function composition
@[inherit_doc]
local infixl:60 " ∘ᴸ " => LHom.comp

@[simp]
theorem id_comp (F : L →ᴸ L') : LHom.id L' ∘ᴸ F = F := by
  cases F
  rfl
#align first_order.language.Lhom.id_comp FirstOrder.Language.LHom.id_comp

@[simp]
theorem comp_id (F : L →ᴸ L') : F ∘ᴸ LHom.id L = F := by
  cases F
  rfl
#align first_order.language.Lhom.comp_id FirstOrder.Language.LHom.comp_id

theorem comp_assoc {L3 : Language} (F : L'' →ᴸ L3) (G : L' →ᴸ L'') (H : L →ᴸ L') :
    F ∘ᴸ G ∘ᴸ H = F ∘ᴸ (G ∘ᴸ H) :=
  rfl
#align first_order.language.Lhom.comp_assoc FirstOrder.Language.LHom.comp_assoc

section SumElim

variable (ψ : L'' →ᴸ L')

/-- A language map defined on two factors of a sum. -/
@[simps]
protected def sumElim : L.sum L'' →ᴸ L' where
  onFunction _n := Sum.elim (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.elim (fun f => ϕ.onRelation f) fun f => ψ.onRelation f
#align first_order.language.Lhom.sum_elim FirstOrder.Language.LHom.sumElim

theorem sumElim_comp_inl (ψ : L'' →ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInl = ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)
#align first_order.language.Lhom.sum_elim_comp_inl FirstOrder.Language.LHom.sumElim_comp_inl

theorem sumElim_comp_inr (ψ : L'' →ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInr = ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)
#align first_order.language.Lhom.sum_elim_comp_inr FirstOrder.Language.LHom.sumElim_comp_inr

theorem sumElim_inl_inr : LHom.sumInl.sumElim LHom.sumInr = LHom.id (L.sum L') :=
  LHom.funext (funext fun _ => Sum.elim_inl_inr) (funext fun _ => Sum.elim_inl_inr)
#align first_order.language.Lhom.sum_elim_inl_inr FirstOrder.Language.LHom.sumElim_inl_inr

theorem comp_sumElim {L3 : Language} (θ : L' →ᴸ L3) :
    θ ∘ᴸ ϕ.sumElim ψ = (θ ∘ᴸ ϕ).sumElim (θ ∘ᴸ ψ) :=
  LHom.funext (funext fun _n => Sum.comp_elim _ _ _) (funext fun _n => Sum.comp_elim _ _ _)
#align first_order.language.Lhom.comp_sum_elim FirstOrder.Language.LHom.comp_sumElim

end SumElim

section SumMap

variable {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂)

/-- The map between two sum-languages induced by maps on the two factors. -/
@[simps]
def sumMap : L.sum L₁ →ᴸ L'.sum L₂ where
  onFunction _n := Sum.map (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.map (fun f => ϕ.onRelation f) fun f => ψ.onRelation f
#align first_order.language.Lhom.sum_map FirstOrder.Language.LHom.sumMap

@[simp]
theorem sumMap_comp_inl : ϕ.sumMap ψ ∘ᴸ LHom.sumInl = LHom.sumInl ∘ᴸ ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)
#align first_order.language.Lhom.sum_map_comp_inl FirstOrder.Language.LHom.sumMap_comp_inl

@[simp]
theorem sumMap_comp_inr : ϕ.sumMap ψ ∘ᴸ LHom.sumInr = LHom.sumInr ∘ᴸ ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)
#align first_order.language.Lhom.sum_map_comp_inr FirstOrder.Language.LHom.sumMap_comp_inr

end SumMap

/-- A language homomorphism is injective when all the maps between symbol types are. -/
protected structure Injective : Prop where
  onFunction {n} : Function.Injective fun f : L.Functions n => onFunction ϕ f
  onRelation {n} : Function.Injective fun R : L.Relations n => onRelation ϕ R
#align first_order.language.Lhom.injective FirstOrder.Language.LHom.Injective

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
#align first_order.language.Lhom.default_expansion FirstOrder.Language.LHom.defaultExpansion

/-- A language homomorphism is an expansion on a structure if it commutes with the interpretation of
all symbols on that structure. -/
class IsExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] : Prop where
  map_onFunction : ∀ {n} (f : L.Functions n) (x : Fin n → M), funMap (ϕ.onFunction f) x = funMap f x
  map_onRelation : ∀ {n} (R : L.Relations n) (x : Fin n → M),
    RelMap (ϕ.onRelation R) x = RelMap R x
#align first_order.language.Lhom.is_expansion_on FirstOrder.Language.LHom.IsExpansionOn

@[simp]
theorem map_onFunction {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (f : L.Functions n) (x : Fin n → M) : funMap (ϕ.onFunction f) x = funMap f x :=
  IsExpansionOn.map_onFunction f x
#align first_order.language.Lhom.map_on_function FirstOrder.Language.LHom.map_onFunction

@[simp]
theorem map_onRelation {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (R : L.Relations n) (x : Fin n → M) : RelMap (ϕ.onRelation R) x = RelMap R x :=
  IsExpansionOn.map_onRelation R x
#align first_order.language.Lhom.map_on_relation FirstOrder.Language.LHom.map_onRelation

instance id_isExpansionOn (M : Type*) [L.Structure M] : IsExpansionOn (LHom.id L) M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩
#align first_order.language.Lhom.id_is_expansion_on FirstOrder.Language.LHom.id_isExpansionOn

instance ofIsEmpty_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] [L.IsAlgebraic]
    [L.IsRelational] : IsExpansionOn (LHom.ofIsEmpty L L') M :=
  ⟨fun {n} => (IsRelational.empty_functions n).elim,
   fun {n} => (IsAlgebraic.empty_relations n).elim⟩
#align first_order.language.Lhom.of_is_empty_is_expansion_on FirstOrder.Language.LHom.ofIsEmpty_isExpansionOn

instance sumElim_isExpansionOn {L'' : Language} (ψ : L'' →ᴸ L') (M : Type*) [L.Structure M]
    [L'.Structure M] [L''.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sumElim ψ).IsExpansionOn M :=
  ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩
#align first_order.language.Lhom.sum_elim_is_expansion_on FirstOrder.Language.LHom.sumElim_isExpansionOn

instance sumMap_isExpansionOn {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂) (M : Type*) [L.Structure M]
    [L'.Structure M] [L₁.Structure M] [L₂.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sumMap ψ).IsExpansionOn M :=
  ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩
#align first_order.language.Lhom.sum_map_is_expansion_on FirstOrder.Language.LHom.sumMap_isExpansionOn

instance sumInl_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] :
    (LHom.sumInl : L →ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩
#align first_order.language.Lhom.sum_inl_is_expansion_on FirstOrder.Language.LHom.sumInl_isExpansionOn

instance sumInr_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] :
    (LHom.sumInr : L' →ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩
#align first_order.language.Lhom.sum_inr_is_expansion_on FirstOrder.Language.LHom.sumInr_isExpansionOn

@[simp]
theorem funMap_sumInl [(L.sum L').Structure M] [(LHom.sumInl : L →ᴸ L.sum L').IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n → M} : @funMap (L.sum L') M _ n (Sum.inl f) x = funMap f x :=
  (LHom.sumInl : L →ᴸ L.sum L').map_onFunction f x
#align first_order.language.Lhom.fun_map_sum_inl FirstOrder.Language.LHom.funMap_sumInl

@[simp]
theorem funMap_sumInr [(L'.sum L).Structure M] [(LHom.sumInr : L →ᴸ L'.sum L).IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n → M} : @funMap (L'.sum L) M _ n (Sum.inr f) x = funMap f x :=
  (LHom.sumInr : L →ᴸ L'.sum L).map_onFunction f x
#align first_order.language.Lhom.fun_map_sum_inr FirstOrder.Language.LHom.funMap_sumInr

theorem sumInl_injective : (LHom.sumInl : L →ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inl_injective h, fun h => Sum.inl_injective h⟩
#align first_order.language.Lhom.sum_inl_injective FirstOrder.Language.LHom.sumInl_injective

theorem sumInr_injective : (LHom.sumInr : L' →ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inr_injective h, fun h => Sum.inr_injective h⟩
#align first_order.language.Lhom.sum_inr_injective FirstOrder.Language.LHom.sumInr_injective

instance (priority := 100) isExpansionOn_reduct (ϕ : L →ᴸ L') (M : Type*) [L'.Structure M] :
    @IsExpansionOn L L' ϕ M (ϕ.reduct M) _ :=
  letI := ϕ.reduct M
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩
#align first_order.language.Lhom.is_expansion_on_reduct FirstOrder.Language.LHom.isExpansionOn_reduct

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
#align first_order.language.Lhom.injective.is_expansion_on_default FirstOrder.Language.LHom.Injective.isExpansionOn_default

end LHom

/-- A language equivalence maps the symbols of one language to symbols of another bijectively. -/
structure LEquiv (L L' : Language) where
  toLHom : L →ᴸ L'
  invLHom : L' →ᴸ L
  left_inv : invLHom.comp toLHom = LHom.id L
  right_inv : toLHom.comp invLHom = LHom.id L'
#align first_order.lanugage.Lequiv FirstOrder.Language.LEquiv

infixl:10 " ≃ᴸ " => LEquiv

-- \^L
namespace LEquiv

variable (L)

/-- The identity equivalence from a first-order language to itself. -/
@[simps]
protected def refl : L ≃ᴸ L :=
  ⟨LHom.id L, LHom.id L, LHom.comp_id _, LHom.comp_id _⟩
#align first_order.lanugage.Lequiv.refl FirstOrder.Language.LEquiv.refl

variable {L}

instance : Inhabited (L ≃ᴸ L) :=
  ⟨LEquiv.refl L⟩

variable {L'' : Language} (e' : L' ≃ᴸ L'') (e : L ≃ᴸ L')

/-- The inverse of an equivalence of first-order languages. -/
@[simps]
protected def symm : L' ≃ᴸ L :=
  ⟨e.invLHom, e.toLHom, e.right_inv, e.left_inv⟩
#align first_order.lanugage.Lequiv.symm FirstOrder.Language.LEquiv.symm

/-- The composition of equivalences of first-order languages. -/
@[simps, trans]
protected def trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') : L ≃ᴸ L'' :=
  ⟨e'.toLHom.comp e.toLHom, e.invLHom.comp e'.invLHom, by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e'.invLHom, e'.left_inv, LHom.id_comp, e.left_inv], by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e.toLHom, e.right_inv, LHom.id_comp, e'.right_inv]⟩
#align first_order.lanugage.Lequiv.trans FirstOrder.Language.LEquiv.trans

end LEquiv

section ConstantsOn

variable (α : Type u')

/-- A language with constants indexed by a type. -/
@[simp]
def constantsOn : Language.{u', 0} :=
  Language.mk₂ α PEmpty PEmpty PEmpty PEmpty
#align first_order.language.constants_on FirstOrder.Language.constantsOn

variable {α}

theorem constantsOn_constants : (constantsOn α).Constants = α :=
  rfl
#align first_order.language.constants_on_constants FirstOrder.Language.constantsOn_constants

instance isAlgebraic_constantsOn : IsAlgebraic (constantsOn α) :=
  Language.isAlgebraic_mk₂
#align first_order.language.is_algebraic_constants_on FirstOrder.Language.isAlgebraic_constantsOn

instance isRelational_constantsOn [_ie : IsEmpty α] : IsRelational (constantsOn α) :=
  Language.isRelational_mk₂
#align first_order.language.is_relational_constants_on FirstOrder.Language.isRelational_constantsOn

instance isEmpty_functions_constantsOn_succ {n : ℕ} : IsEmpty ((constantsOn α).Functions (n + 1)) :=
  Nat.casesOn n (inferInstanceAs (IsEmpty PEmpty))
    fun n => Nat.casesOn n (inferInstanceAs (IsEmpty PEmpty))
    fun _ => (inferInstanceAs (IsEmpty PEmpty))
#align first_order.language.is_empty_functions_constants_on_succ FirstOrder.Language.isEmpty_functions_constantsOn_succ

theorem card_constantsOn : (constantsOn α).card = #α := by simp
#align first_order.language.card_constants_on FirstOrder.Language.card_constantsOn

/-- Gives a `constantsOn α` structure to a type by assigning each constant a value. -/
def constantsOn.structure (f : α → M) : (constantsOn α).Structure M :=
  Structure.mk₂ f PEmpty.elim PEmpty.elim PEmpty.elim PEmpty.elim
#align first_order.language.constants_on.Structure FirstOrder.Language.constantsOn.structure

variable {β : Type v'}

/-- A map between index types induces a map between constant languages. -/
def LHom.constantsOnMap (f : α → β) : constantsOn α →ᴸ constantsOn β :=
  LHom.mk₂ f PEmpty.elim PEmpty.elim PEmpty.elim PEmpty.elim
#align first_order.language.Lhom.constants_on_map FirstOrder.Language.LHom.constantsOnMap

theorem constantsOnMap_isExpansionOn {f : α → β} {fα : α → M} {fβ : β → M} (h : fβ ∘ f = fα) :
    @LHom.IsExpansionOn _ _ (LHom.constantsOnMap f) M (constantsOn.structure fα)
      (constantsOn.structure fβ) := by
  letI := constantsOn.structure fα
  letI := constantsOn.structure fβ
  exact
    ⟨fun {n} => Nat.casesOn n (fun F _x => (congr_fun h F : _)) fun n F => isEmptyElim F, fun R =>
      isEmptyElim R⟩
#align first_order.language.constants_on_map_is_expansion_on FirstOrder.Language.constantsOnMap_isExpansionOn

end ConstantsOn

section WithConstants

variable (L)

section

variable (α : Type w')

/-- Extends a language with a constant for each element of a parameter set in `M`. -/
def withConstants : Language.{max u w', v} :=
  L.sum (constantsOn α)
#align first_order.language.with_constants FirstOrder.Language.withConstants

@[inherit_doc FirstOrder.Language.withConstants]
scoped[FirstOrder] notation:95 L "[[" α "]]" => Language.withConstants L α

@[simp]
theorem card_withConstants :
    L[[α]].card = Cardinal.lift.{w'} L.card + Cardinal.lift.{max u v} #α := by
  rw [withConstants, card_sum, card_constantsOn]
#align first_order.language.card_with_constants FirstOrder.Language.card_withConstants

/-- The language map adding constants.  -/
@[simps!] -- Porting note: add `!` to `simps`
def lhomWithConstants : L →ᴸ L[[α]] :=
  LHom.sumInl
#align first_order.language.Lhom_with_constants FirstOrder.Language.lhomWithConstants

theorem lhomWithConstants_injective : (L.lhomWithConstants α).Injective :=
  LHom.sumInl_injective
#align first_order.language.Lhom_with_constants_injective FirstOrder.Language.lhomWithConstants_injective

variable {α}

/-- The constant symbol indexed by a particular element. -/
protected def con (a : α) : L[[α]].Constants :=
  Sum.inr a
#align first_order.language.con FirstOrder.Language.con

variable {L} (α)

/-- Adds constants to a language map.  -/
def LHom.addConstants {L' : Language} (φ : L →ᴸ L') : L[[α]] →ᴸ L'[[α]] :=
  φ.sumMap (LHom.id _)
#align first_order.language.Lhom.add_constants FirstOrder.Language.LHom.addConstants

instance paramsStructure (A : Set α) : (constantsOn A).Structure α :=
  constantsOn.structure (↑)
#align first_order.language.params_Structure FirstOrder.Language.paramsStructure

variable (L)

/-- The language map removing an empty constant set.  -/
@[simps]
def LEquiv.addEmptyConstants [ie : IsEmpty α] : L ≃ᴸ L[[α]] where
  toLHom := lhomWithConstants L α
  invLHom := LHom.sumElim (LHom.id L) (LHom.ofIsEmpty (constantsOn α) L)
  left_inv := by rw [lhomWithConstants, LHom.sumElim_comp_inl]
  right_inv := by
    simp only [LHom.comp_sumElim, lhomWithConstants, LHom.comp_id]
    exact _root_.trans (congr rfl (Subsingleton.elim _ _)) LHom.sumElim_inl_inr
#align first_order.lanugage.Lequiv.add_empty_constants FirstOrder.Language.LEquiv.addEmptyConstants

variable {α} {β : Type*}

@[simp]
theorem withConstants_funMap_sum_inl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {f : L.Functions n} {x : Fin n → M} : @funMap (L[[α]]) M _ n (Sum.inl f) x = funMap f x :=
  (lhomWithConstants L α).map_onFunction f x
#align first_order.language.with_constants_fun_map_sum_inl FirstOrder.Language.withConstants_funMap_sum_inl

@[simp]
theorem withConstants_relMap_sum_inl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {R : L.Relations n} {x : Fin n → M} : @RelMap (L[[α]]) M _ n (Sum.inl R) x = RelMap R x :=
  (lhomWithConstants L α).map_onRelation R x
#align first_order.language.with_constants_rel_map_sum_inl FirstOrder.Language.withConstants_relMap_sum_inl

/-- The language map extending the constant set.  -/
def lhomWithConstantsMap (f : α → β) : L[[α]] →ᴸ L[[β]] :=
  LHom.sumMap (LHom.id L) (LHom.constantsOnMap f)
#align first_order.language.Lhom_with_constants_map FirstOrder.Language.lhomWithConstantsMap

@[simp]
theorem LHom.map_constants_comp_sumInl {f : α → β} :
    (L.lhomWithConstantsMap f).comp LHom.sumInl = L.lhomWithConstants β := by ext <;> rfl
#align first_order.language.Lhom.map_constants_comp_sum_inl FirstOrder.Language.LHom.map_constants_comp_sumInl

end

open FirstOrder

instance constantsOnSelfStructure : (constantsOn M).Structure M :=
  constantsOn.structure id
#align first_order.language.constants_on_self_Structure FirstOrder.Language.constantsOnSelfStructure

instance withConstantsSelfStructure : L[[M]].Structure M :=
  Language.sumStructure _ _ M
#align first_order.language.with_constants_self_Structure FirstOrder.Language.withConstantsSelfStructure

instance withConstants_self_expansion : (lhomWithConstants L M).IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩
#align first_order.language.with_constants_self_expansion FirstOrder.Language.withConstants_self_expansion

variable (α : Type*) [(constantsOn α).Structure M]

instance withConstantsStructure : L[[α]].Structure M :=
  Language.sumStructure _ _ _
#align first_order.language.with_constants_Structure FirstOrder.Language.withConstantsStructure

instance withConstants_expansion : (L.lhomWithConstants α).IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩
#align first_order.language.with_constants_expansion FirstOrder.Language.withConstants_expansion

instance addEmptyConstants_is_expansion_on' :
    (LEquiv.addEmptyConstants L (∅ : Set M)).toLHom.IsExpansionOn M :=
  L.withConstants_expansion _
#align first_order.language.add_empty_constants_is_expansion_on' FirstOrder.Language.addEmptyConstants_is_expansion_on'

instance addEmptyConstants_symm_isExpansionOn :
    (LEquiv.addEmptyConstants L (∅ : Set M)).symm.toLHom.IsExpansionOn M :=
  LHom.sumElim_isExpansionOn _ _ _
#align first_order.language.add_empty_constants_symm_is_expansion_on FirstOrder.Language.addEmptyConstants_symm_isExpansionOn

instance addConstants_expansion {L' : Language} [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    (φ.addConstants α).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ M
#align first_order.language.add_constants_expansion FirstOrder.Language.addConstants_expansion

@[simp]
theorem withConstants_funMap_sum_inr {a : α} {x : Fin 0 → M} :
    @funMap (L[[α]]) M _ 0 (Sum.inr a : L[[α]].Functions 0) x = L.con a := by
  rw [Unique.eq_default x]
  exact (LHom.sumInr : constantsOn α →ᴸ L.sum _).map_onFunction _ _
#align first_order.language.with_constants_fun_map_sum_inr FirstOrder.Language.withConstants_funMap_sum_inr

variable {α} (A : Set M)

@[simp]
theorem coe_con {a : A} : (L.con a : M) = a :=
  rfl
#align first_order.language.coe_con FirstOrder.Language.coe_con

variable {A} {B : Set M} (h : A ⊆ B)

instance constantsOnMap_inclusion_isExpansionOn :
    (LHom.constantsOnMap (Set.inclusion h)).IsExpansionOn M :=
  constantsOnMap_isExpansionOn rfl
#align first_order.language.constants_on_map_inclusion_is_expansion_on FirstOrder.Language.constantsOnMap_inclusion_isExpansionOn

instance map_constants_inclusion_isExpansionOn :
    (L.lhomWithConstantsMap (Set.inclusion h)).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ _
#align first_order.language.map_constants_inclusion_is_expansion_on FirstOrder.Language.map_constants_inclusion_isExpansionOn

end WithConstants

end Language

end FirstOrder
