/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.SetTheory.Cardinal.Basic

#align_import model_theory.basic from "leanprover-community/mathlib"@"369525b73f229ccd76a6ec0e0e0bf2be57599768"

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions
* A `FirstOrder.Language` defines a language as a pair of functions from the natural numbers to
  `Type l`. One sends `n` to the type of `n`-ary functions, and the other sends `n` to the type of
  `n`-ary relations.
* A `FirstOrder.Language.Structure` interprets the symbols of a given `FirstOrder.Language` in the
  context of a given type.
* A `FirstOrder.Language.Hom`, denoted `M →[L] N`, is a map from the `L`-structure `M` to the
  `L`-structure `N` that commutes with the interpretations of functions, and which preserves the
  interpretations of relations (although only in the forward direction).
* A `FirstOrder.Language.Embedding`, denoted `M ↪[L] N`, is an embedding from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
* A `FirstOrder.Language.Equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/

set_option autoImplicit true


universe u v u' v' w w'

open Cardinal

open Cardinal

namespace FirstOrder

/-! ### Languages and Structures -/


-- intended to be used with explicit universe parameters
/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
@[nolint checkUnivs]
structure Language where
  /-- For every arity, a `Type*` of functions of that arity -/
  Functions : ℕ → Type u
  /-- For every arity, a `Type*` of relations of that arity -/
  Relations : ℕ → Type v
#align first_order.language FirstOrder.Language

/-- Used to define `FirstOrder.Language₂`. -/
--@[simp]
def Sequence₂ (a₀ a₁ a₂ : Type u) : ℕ → Type u
  | 0 => a₀
  | 1 => a₁
  | 2 => a₂
  | _ => PEmpty
#align first_order.sequence₂ FirstOrder.Sequence₂

namespace Sequence₂

variable (a₀ a₁ a₂ : Type u)

instance inhabited₀ [h : Inhabited a₀] : Inhabited (Sequence₂ a₀ a₁ a₂ 0) :=
  h
#align first_order.sequence₂.inhabited₀ FirstOrder.Sequence₂.inhabited₀

instance inhabited₁ [h : Inhabited a₁] : Inhabited (Sequence₂ a₀ a₁ a₂ 1) :=
  h
#align first_order.sequence₂.inhabited₁ FirstOrder.Sequence₂.inhabited₁

instance inhabited₂ [h : Inhabited a₂] : Inhabited (Sequence₂ a₀ a₁ a₂ 2) :=
  h
#align first_order.sequence₂.inhabited₂ FirstOrder.Sequence₂.inhabited₂

instance {n : ℕ} : IsEmpty (Sequence₂ a₀ a₁ a₂ (n + 3)) := inferInstanceAs (IsEmpty PEmpty)

@[simp]
theorem lift_mk {i : ℕ} :
    Cardinal.lift.{v,u} #(Sequence₂ a₀ a₁ a₂ i)
      = #(Sequence₂ (ULift.{v,u} a₀) (ULift.{v,u} a₁) (ULift.{v,u} a₂) i) := by
  rcases i with (_ | _ | _ | i) <;>
    simp only [Sequence₂, mk_uLift, Nat.succ_ne_zero, IsEmpty.forall_iff, Nat.succ.injEq,
      add_eq_zero, OfNat.ofNat_ne_zero, and_false, one_ne_zero, mk_eq_zero, lift_zero]
#align first_order.sequence₂.lift_mk FirstOrder.Sequence₂.lift_mk

@[simp]
theorem sum_card : Cardinal.sum (fun i => #(Sequence₂ a₀ a₁ a₂ i)) = #a₀ + #a₁ + #a₂ := by
  rw [sum_nat_eq_add_sum_succ, sum_nat_eq_add_sum_succ, sum_nat_eq_add_sum_succ]
  simp [add_assoc, Sequence₂]
#align first_order.sequence₂.sum_card FirstOrder.Sequence₂.sum_card

end Sequence₂

namespace Language

/-- A constructor for languages with only constants, unary and binary functions, and
unary and binary relations. -/
@[simps]
protected def mk₂ (c f₁ f₂ : Type u) (r₁ r₂ : Type v) : Language :=
  ⟨Sequence₂ c f₁ f₂, Sequence₂ PEmpty r₁ r₂⟩
#align first_order.language.mk₂ FirstOrder.Language.mk₂

/-- The empty language has no symbols. -/
protected def empty : Language :=
  ⟨fun _ => Empty, fun _ => Empty⟩
#align first_order.language.empty FirstOrder.Language.empty

instance : Inhabited Language :=
  ⟨Language.empty⟩

/-- The sum of two languages consists of the disjoint union of their symbols. -/
protected def sum (L : Language.{u, v}) (L' : Language.{u', v'}) : Language :=
  ⟨fun n => Sum (L.Functions n) (L'.Functions n), fun n => Sum (L.Relations n) (L'.Relations n)⟩
#align first_order.language.sum FirstOrder.Language.sum

variable (L : Language.{u, v})

/-- The type of constants in a given language. -/
-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
protected def Constants :=
  L.Functions 0
#align first_order.language.constants FirstOrder.Language.Constants

@[simp]
theorem constants_mk₂ (c f₁ f₂ : Type u) (r₁ r₂ : Type v) :
    (Language.mk₂ c f₁ f₂ r₁ r₂).Constants = c :=
  rfl
#align first_order.language.constants_mk₂ FirstOrder.Language.constants_mk₂

/-- The type of symbols in a given language. -/
-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
def Symbols :=
  Sum (Σl, L.Functions l) (Σl, L.Relations l)
#align first_order.language.symbols FirstOrder.Language.Symbols

/-- The cardinality of a language is the cardinality of its type of symbols. -/
def card : Cardinal :=
  #L.Symbols
#align first_order.language.card FirstOrder.Language.card

/-- A language is relational when it has no function symbols. -/
class IsRelational : Prop where
  /-- There are no function symbols in the language. -/
  empty_functions : ∀ n, IsEmpty (L.Functions n)
#align first_order.language.is_relational FirstOrder.Language.IsRelational

/-- A language is algebraic when it has no relation symbols. -/
class IsAlgebraic : Prop where
  /-- There are no relation symbols in the language. -/
  empty_relations : ∀ n, IsEmpty (L.Relations n)
#align first_order.language.is_algebraic FirstOrder.Language.IsAlgebraic

variable {L} {L' : Language.{u', v'}}

theorem card_eq_card_functions_add_card_relations :
    L.card =
      (Cardinal.sum fun l => Cardinal.lift.{v} #(L.Functions l)) +
        Cardinal.sum fun l => Cardinal.lift.{u} #(L.Relations l) := by
  simp [card, Symbols]
#align first_order.language.card_eq_card_functions_add_card_relations FirstOrder.Language.card_eq_card_functions_add_card_relations

instance [L.IsRelational] {n : ℕ} : IsEmpty (L.Functions n) :=
  IsRelational.empty_functions n

instance [L.IsAlgebraic] {n : ℕ} : IsEmpty (L.Relations n) :=
  IsAlgebraic.empty_relations n

instance isRelational_of_empty_functions {symb : ℕ → Type*} :
    IsRelational ⟨fun _ => Empty, symb⟩ :=
  ⟨fun _ => instIsEmptyEmpty⟩
#align first_order.language.is_relational_of_empty_functions FirstOrder.Language.isRelational_of_empty_functions

instance isAlgebraic_of_empty_relations {symb : ℕ → Type*} : IsAlgebraic ⟨symb, fun _ => Empty⟩ :=
  ⟨fun _ => instIsEmptyEmpty⟩
#align first_order.language.is_algebraic_of_empty_relations FirstOrder.Language.isAlgebraic_of_empty_relations

instance isRelational_empty : IsRelational Language.empty :=
  Language.isRelational_of_empty_functions
#align first_order.language.is_relational_empty FirstOrder.Language.isRelational_empty

instance isAlgebraic_empty : IsAlgebraic Language.empty :=
  Language.isAlgebraic_of_empty_relations
#align first_order.language.is_algebraic_empty FirstOrder.Language.isAlgebraic_empty

instance isRelational_sum [L.IsRelational] [L'.IsRelational] : IsRelational (L.sum L') :=
  ⟨fun _ => instIsEmptySum⟩
#align first_order.language.is_relational_sum FirstOrder.Language.isRelational_sum

instance isAlgebraic_sum [L.IsAlgebraic] [L'.IsAlgebraic] : IsAlgebraic (L.sum L') :=
  ⟨fun _ => instIsEmptySum⟩
#align first_order.language.is_algebraic_sum FirstOrder.Language.isAlgebraic_sum

instance isRelational_mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h0 : IsEmpty c] [h1 : IsEmpty f₁]
    [h2 : IsEmpty f₂] : IsRelational (Language.mk₂ c f₁ f₂ r₁ r₂) :=
  ⟨fun n =>
    Nat.casesOn n h0 fun n => Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun _ =>
      inferInstanceAs (IsEmpty PEmpty)⟩
#align first_order.language.is_relational_mk₂ FirstOrder.Language.isRelational_mk₂

instance isAlgebraic_mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h1 : IsEmpty r₁] [h2 : IsEmpty r₂] :
    IsAlgebraic (Language.mk₂ c f₁ f₂ r₁ r₂) :=
  ⟨fun n =>
    Nat.casesOn n (inferInstanceAs (IsEmpty PEmpty)) fun n =>
      Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun _ => inferInstanceAs (IsEmpty PEmpty)⟩
#align first_order.language.is_algebraic_mk₂ FirstOrder.Language.isAlgebraic_mk₂

instance subsingleton_mk₂_functions {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h0 : Subsingleton c]
    [h1 : Subsingleton f₁] [h2 : Subsingleton f₂] {n : ℕ} :
    Subsingleton ((Language.mk₂ c f₁ f₂ r₁ r₂).Functions n) :=
  Nat.casesOn n h0 fun n =>
    Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun _ => ⟨fun x => PEmpty.elim x⟩
#align first_order.language.subsingleton_mk₂_functions FirstOrder.Language.subsingleton_mk₂_functions

instance subsingleton_mk₂_relations {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h1 : Subsingleton r₁]
    [h2 : Subsingleton r₂] {n : ℕ} : Subsingleton ((Language.mk₂ c f₁ f₂ r₁ r₂).Relations n) :=
  Nat.casesOn n ⟨fun x => PEmpty.elim x⟩ fun n =>
    Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun _ => ⟨fun x => PEmpty.elim x⟩
#align first_order.language.subsingleton_mk₂_relations FirstOrder.Language.subsingleton_mk₂_relations

@[simp]
theorem empty_card : Language.empty.card = 0 := by simp [card_eq_card_functions_add_card_relations]
#align first_order.language.empty_card FirstOrder.Language.empty_card

instance isEmpty_empty : IsEmpty Language.empty.Symbols := by
  simp only [Language.Symbols, isEmpty_sum, isEmpty_sigma]
  exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩
#align first_order.language.is_empty_empty FirstOrder.Language.isEmpty_empty

instance Countable.countable_functions [h : Countable L.Symbols] : Countable (Σl, L.Functions l) :=
  @Function.Injective.countable _ _ h _ Sum.inl_injective
#align first_order.language.countable.countable_functions FirstOrder.Language.Countable.countable_functions

@[simp]
theorem card_functions_sum (i : ℕ) :
    #((L.sum L').Functions i)
      = (Cardinal.lift.{u'} #(L.Functions i) + Cardinal.lift.{u} #(L'.Functions i) : Cardinal) := by
  simp [Language.sum]
#align first_order.language.card_functions_sum FirstOrder.Language.card_functions_sum

@[simp]
theorem card_relations_sum (i : ℕ) :
    #((L.sum L').Relations i) =
      Cardinal.lift.{v'} #(L.Relations i) + Cardinal.lift.{v} #(L'.Relations i) := by
  simp [Language.sum]
#align first_order.language.card_relations_sum FirstOrder.Language.card_relations_sum

@[simp]
theorem card_sum :
    (L.sum L').card = Cardinal.lift.{max u' v'} L.card + Cardinal.lift.{max u v} L'.card := by
  simp only [card_eq_card_functions_add_card_relations, card_functions_sum, card_relations_sum,
    sum_add_distrib', lift_add, lift_sum, lift_lift]
  simp only [add_assoc, add_comm (Cardinal.sum fun i => (#(L'.Functions i)).lift)]
#align first_order.language.card_sum FirstOrder.Language.card_sum

@[simp]
theorem card_mk₂ (c f₁ f₂ : Type u) (r₁ r₂ : Type v) :
    (Language.mk₂ c f₁ f₂ r₁ r₂).card =
      Cardinal.lift.{v} #c + Cardinal.lift.{v} #f₁ + Cardinal.lift.{v} #f₂ +
          Cardinal.lift.{u} #r₁ + Cardinal.lift.{u} #r₂ := by
  simp [card_eq_card_functions_add_card_relations, add_assoc]
#align first_order.language.card_mk₂ FirstOrder.Language.card_mk₂

variable (L) (M : Type w)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(Fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
@[ext]
class Structure where
  /-- Interpretation of the function symbols -/
  funMap : ∀ {n}, L.Functions n → (Fin n → M) → M
  /-- Interpretation of the relation symbols -/
  RelMap : ∀ {n}, L.Relations n → (Fin n → M) → Prop
set_option linter.uppercaseLean3 false in
#align first_order.language.Structure FirstOrder.Language.Structure
set_option linter.uppercaseLean3 false in
#align first_order.language.Structure.fun_map FirstOrder.Language.Structure.funMap
set_option linter.uppercaseLean3 false in
#align first_order.language.Structure.rel_map FirstOrder.Language.Structure.RelMap

variable (N : Type w') [L.Structure M] [L.Structure N]

open Structure

/-- Used for defining `FirstOrder.Language.Theory.ModelType.instInhabited`. -/
def Inhabited.trivialStructure {α : Type*} [Inhabited α] : L.Structure α :=
  ⟨default, default⟩
#align first_order.language.inhabited.trivial_structure FirstOrder.Language.Inhabited.trivialStructure

/-! ### Maps -/


/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
structure Hom where
  /-- The underlying function of a homomorphism of structures -/
  toFun : M → N
  /-- The homomorphism commutes with the interpretations of the function symbols -/
  -- Porting note:
  -- The autoparam here used to be `obviously`. We would like to replace it with `aesop`
  -- but that isn't currently sufficient.
  -- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases
  -- If that can be improved, we should change this to `by aesop` and remove the proofs below.
  map_fun' : ∀ {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    intros; trivial
  /-- The homomorphism sends related elements to related elements -/
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r x → RelMap r (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
#align first_order.language.hom FirstOrder.Language.Hom

@[inherit_doc]
scoped[FirstOrder] notation:25 A " →[" L "] " B => FirstOrder.Language.Hom L A B

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
structure Embedding extends M ↪ N where
  map_fun' : ∀ {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
#align first_order.language.embedding FirstOrder.Language.Embedding

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ↪[" L "] " B => FirstOrder.Language.Embedding L A B

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
structure Equiv extends M ≃ N where
  map_fun' : ∀ {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
#align first_order.language.equiv FirstOrder.Language.Equiv

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ≃[" L "] " B => FirstOrder.Language.Equiv L A B

-- Porting note: was [L.Structure P] and [L.Structure Q]
-- The former reported an error.
variable {L M N} {P : Type*} [Structure L P] {Q : Type*} [Structure L Q]

-- Porting note (#11445): new definition
/-- Interpretation of a constant symbol -/
@[coe]
def constantMap (c : L.Constants) : M := funMap c default

instance : CoeTC L.Constants M :=
  ⟨constantMap⟩

theorem funMap_eq_coe_constants {c : L.Constants} {x : Fin 0 → M} : funMap c x = c :=
  congr rfl (funext finZeroElim)
#align first_order.language.fun_map_eq_coe_constants FirstOrder.Language.funMap_eq_coe_constants

/-- Given a language with a nonempty type of constants, any structure will be nonempty. This cannot
  be a global instance, because `L` becomes a metavariable. -/
theorem nonempty_of_nonempty_constants [h : Nonempty L.Constants] : Nonempty M :=
  h.map (↑)
#align first_order.language.nonempty_of_nonempty_constants FirstOrder.Language.nonempty_of_nonempty_constants

/-- The function map for `FirstOrder.Language.Structure₂`. -/
def funMap₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (c' : c → M) (f₁' : f₁ → M → M)
    (f₂' : f₂ → M → M → M) : ∀ {n}, (Language.mk₂ c f₁ f₂ r₁ r₂).Functions n → (Fin n → M) → M
  | 0, f, _ => c' f
  | 1, f, x => f₁' f (x 0)
  | 2, f, x => f₂' f (x 0) (x 1)
  | _ + 3, f, _ => PEmpty.elim f
#align first_order.language.fun_map₂ FirstOrder.Language.funMap₂

/-- The relation map for `FirstOrder.Language.Structure₂`. -/
def RelMap₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (r₁' : r₁ → Set M) (r₂' : r₂ → M → M → Prop) :
    ∀ {n}, (Language.mk₂ c f₁ f₂ r₁ r₂).Relations n → (Fin n → M) → Prop
  | 0, r, _ => PEmpty.elim r
  | 1, r, x => x 0 ∈ r₁' r
  | 2, r, x => r₂' r (x 0) (x 1)
  | _ + 3, r, _ => PEmpty.elim r
#align first_order.language.rel_map₂ FirstOrder.Language.RelMap₂

/-- A structure constructor to match `FirstOrder.Language₂`. -/
protected def Structure.mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (c' : c → M) (f₁' : f₁ → M → M)
    (f₂' : f₂ → M → M → M) (r₁' : r₁ → Set M) (r₂' : r₂ → M → M → Prop) :
    (Language.mk₂ c f₁ f₂ r₁ r₂).Structure M :=
  ⟨funMap₂ c' f₁' f₂', RelMap₂ r₁' r₂'⟩
set_option linter.uppercaseLean3 false in
#align first_order.language.Structure.mk₂ FirstOrder.Language.Structure.mk₂

namespace Structure

variable {c f₁ f₂ : Type u} {r₁ r₂ : Type v}
variable {c' : c → M} {f₁' : f₁ → M → M} {f₂' : f₂ → M → M → M}
variable {r₁' : r₁ → Set M} {r₂' : r₂ → M → M → Prop}

@[simp]
theorem funMap_apply₀ (c₀ : c) {x : Fin 0 → M} :
    @Structure.funMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 0 c₀ x = c' c₀ :=
  rfl
set_option linter.uppercaseLean3 false in
#align first_order.language.Structure.fun_map_apply₀ FirstOrder.Language.Structure.funMap_apply₀

@[simp]
theorem funMap_apply₁ (f : f₁) (x : M) :
    @Structure.funMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 1 f ![x] = f₁' f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align first_order.language.Structure.fun_map_apply₁ FirstOrder.Language.Structure.funMap_apply₁

@[simp]
theorem funMap_apply₂ (f : f₂) (x y : M) :
    @Structure.funMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 2 f ![x, y] = f₂' f x y :=
  rfl
set_option linter.uppercaseLean3 false in
#align first_order.language.Structure.fun_map_apply₂ FirstOrder.Language.Structure.funMap_apply₂

@[simp]
theorem relMap_apply₁ (r : r₁) (x : M) :
    @Structure.RelMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 1 r ![x] = (x ∈ r₁' r) :=
  rfl
set_option linter.uppercaseLean3 false in
#align first_order.language.Structure.rel_map_apply₁ FirstOrder.Language.Structure.relMap_apply₁

@[simp]
theorem relMap_apply₂ (r : r₂) (x y : M) :
    @Structure.RelMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 2 r ![x, y] = r₂' r x y :=
  rfl
set_option linter.uppercaseLean3 false in
#align first_order.language.Structure.rel_map_apply₂ FirstOrder.Language.Structure.relMap_apply₂

end Structure

/-- `HomClass L F M N` states that `F` is a type of `L`-homomorphisms. You should extend this
  typeclass when you extend `FirstOrder.Language.Hom`. -/
class HomClass (L : outParam Language) (F M N : Type*)
  [FunLike F M N] [L.Structure M] [L.Structure N] : Prop where
  map_fun : ∀ (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : ∀ (φ : F) {n} (r : L.Relations n) (x), RelMap r x → RelMap r (φ ∘ x)
#align first_order.language.hom_class FirstOrder.Language.HomClass

/-- `StrongHomClass L F M N` states that `F` is a type of `L`-homomorphisms which preserve
  relations in both directions. -/
class StrongHomClass (L : outParam Language) (F M N : Type*)
  [FunLike F M N] [L.Structure M] [L.Structure N] : Prop where
  map_fun : ∀ (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : ∀ (φ : F) {n} (r : L.Relations n) (x), RelMap r (φ ∘ x) ↔ RelMap r x
#align first_order.language.strong_hom_class FirstOrder.Language.StrongHomClass

-- Porting note: using implicit brackets for `Structure` arguments
instance (priority := 100) StrongHomClass.homClass [L.Structure M]
    [L.Structure N] [FunLike F M N] [StrongHomClass L F M N] : HomClass L F M N where
  map_fun := StrongHomClass.map_fun
  map_rel φ _ R x := (StrongHomClass.map_rel φ R x).2
#align first_order.language.strong_hom_class.hom_class FirstOrder.Language.StrongHomClass.homClass

/-- Not an instance to avoid a loop. -/
theorem HomClass.strongHomClassOfIsAlgebraic [L.IsAlgebraic] {F M N} [L.Structure M] [L.Structure N]
    [FunLike F M N] [HomClass L F M N] : StrongHomClass L F M N where
  map_fun := HomClass.map_fun
  map_rel _ n R _ := (IsAlgebraic.empty_relations n).elim R
#align first_order.language.hom_class.strong_hom_class_of_is_algebraic FirstOrder.Language.HomClass.strongHomClassOfIsAlgebraic

theorem HomClass.map_constants {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [HomClass L F M N] (φ : F) (c : L.Constants) : φ c = c :=
  (HomClass.map_fun φ c default).trans (congr rfl (funext default))
#align first_order.language.hom_class.map_constants FirstOrder.Language.HomClass.map_constants

attribute [inherit_doc FirstOrder.Language.Hom.map_fun'] FirstOrder.Language.Embedding.map_fun'
  FirstOrder.Language.HomClass.map_fun FirstOrder.Language.StrongHomClass.map_fun
  FirstOrder.Language.Equiv.map_fun'

attribute [inherit_doc FirstOrder.Language.Hom.map_rel'] FirstOrder.Language.Embedding.map_rel'
  FirstOrder.Language.HomClass.map_rel FirstOrder.Language.StrongHomClass.map_rel
  FirstOrder.Language.Equiv.map_rel'

namespace Hom

instance instFunLike : FunLike (M →[L] N) M N where
  coe := Hom.toFun
  coe_injective' f g h := by cases f; cases g; cases h; rfl
#align first_order.language.hom.fun_like FirstOrder.Language.Hom.instFunLike

instance homClass : HomClass L (M →[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'
#align first_order.language.hom.hom_class FirstOrder.Language.Hom.homClass

instance [L.IsAlgebraic] : StrongHomClass L (M →[L] N) M N :=
  HomClass.strongHomClassOfIsAlgebraic

instance hasCoeToFun : CoeFun (M →[L] N) fun _ => M → N :=
  DFunLike.hasCoeToFun
#align first_order.language.hom.has_coe_to_fun FirstOrder.Language.Hom.hasCoeToFun

@[simp]
theorem toFun_eq_coe {f : M →[L] N} : f.toFun = (f : M → N) :=
  rfl
#align first_order.language.hom.to_fun_eq_coe FirstOrder.Language.Hom.toFun_eq_coe

@[ext]
theorem ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
#align first_order.language.hom.ext FirstOrder.Language.Hom.ext

theorem ext_iff {f g : M →[L] N} : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff
#align first_order.language.hom.ext_iff FirstOrder.Language.Hom.ext_iff

@[simp]
theorem map_fun (φ : M →[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x
#align first_order.language.hom.map_fun FirstOrder.Language.Hom.map_fun

@[simp]
theorem map_constants (φ : M →[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c
#align first_order.language.hom.map_constants FirstOrder.Language.Hom.map_constants

@[simp]
theorem map_rel (φ : M →[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r x → RelMap r (φ ∘ x) :=
  HomClass.map_rel φ r x
#align first_order.language.hom.map_rel FirstOrder.Language.Hom.map_rel

variable (L) (M)

/-- The identity map from a structure to itself. -/
@[refl]
def id : M →[L] M where
  toFun m := m
#align first_order.language.hom.id FirstOrder.Language.Hom.id

variable {L} {M}

instance : Inhabited (M →[L] M) :=
  ⟨id L M⟩

@[simp]
theorem id_apply (x : M) : id L M x = x :=
  rfl
#align first_order.language.hom.id_apply FirstOrder.Language.Hom.id_apply

/-- Composition of first-order homomorphisms. -/
@[trans]
def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P where
  toFun := hnp ∘ hmn
  -- Porting note: should be done by autoparam?
  map_fun' _ _ := by simp; rfl
  -- Porting note: should be done by autoparam?
  map_rel' _ _ h := map_rel _ _ _ (map_rel _ _ _ h)
#align first_order.language.hom.comp FirstOrder.Language.Hom.comp

@[simp]
theorem comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl
#align first_order.language.hom.comp_apply FirstOrder.Language.Hom.comp_apply

/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align first_order.language.hom.comp_assoc FirstOrder.Language.Hom.comp_assoc

@[simp]
theorem comp_id (f : M →[L] N) : f.comp (id L M) = f :=
  rfl

@[simp]
theorem id_comp (f : M →[L] N) : (id L N).comp f = f :=
  rfl

end Hom

/-- Any element of a `HomClass` can be realized as a first_order homomorphism. -/
def HomClass.toHom {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [HomClass L F M N] : F → M →[L] N := fun φ =>
  ⟨φ, HomClass.map_fun φ, HomClass.map_rel φ⟩
#align first_order.language.hom_class.to_hom FirstOrder.Language.HomClass.toHom

namespace Embedding

instance funLike : FunLike (M ↪[L] N) M N where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    ext x
    exact Function.funext_iff.1 h x

instance embeddingLike : EmbeddingLike (M ↪[L] N) M N where
  injective' f := f.toEmbedding.injective
#align first_order.language.embedding.embedding_like FirstOrder.Language.Embedding.embeddingLike

instance strongHomClass : StrongHomClass L (M ↪[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'
#align first_order.language.embedding.strong_hom_class FirstOrder.Language.Embedding.strongHomClass

#noalign first_order.language.embedding.has_coe_to_fun -- Porting note: replaced by funLike instance

@[simp]
theorem map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x
#align first_order.language.embedding.map_fun FirstOrder.Language.Embedding.map_fun

@[simp]
theorem map_constants (φ : M ↪[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c
#align first_order.language.embedding.map_constants FirstOrder.Language.Embedding.map_constants

@[simp]
theorem map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x
#align first_order.language.embedding.map_rel FirstOrder.Language.Embedding.map_rel

/-- A first-order embedding is also a first-order homomorphism. -/
def toHom : (M ↪[L] N) → M →[L] N :=
  HomClass.toHom
#align first_order.language.embedding.to_hom FirstOrder.Language.Embedding.toHom

@[simp]
theorem coe_toHom {f : M ↪[L] N} : (f.toHom : M → N) = f :=
  rfl
#align first_order.language.embedding.coe_to_hom FirstOrder.Language.Embedding.coe_toHom

theorem coe_injective : @Function.Injective (M ↪[L] N) (M → N) (↑)
  | f, g, h => by
    cases f
    cases g
    congr
    ext x
    exact Function.funext_iff.1 h x
#align first_order.language.embedding.coe_injective FirstOrder.Language.Embedding.coe_injective

@[ext]
theorem ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)
#align first_order.language.embedding.ext FirstOrder.Language.Embedding.ext

theorem ext_iff {f g : M ↪[L] N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h _ => h ▸ rfl, fun h => ext h⟩
#align first_order.language.embedding.ext_iff FirstOrder.Language.Embedding.ext_iff

theorem toHom_injective : @Function.Injective (M ↪[L] N) (M →[L] N) (·.toHom) := by
  intro f f' h
  ext
  exact congr_fun (congr_arg (↑) h) _

@[simp]
theorem toHom_inj {f g : M ↪[L] N} : f.toHom = g.toHom ↔ f = g :=
  ⟨fun h ↦ toHom_injective h, fun h ↦ congr_arg (·.toHom) h⟩

theorem injective (f : M ↪[L] N) : Function.Injective f :=
  f.toEmbedding.injective
#align first_order.language.embedding.injective FirstOrder.Language.Embedding.injective

/-- In an algebraic language, any injective homomorphism is an embedding. -/
@[simps!]
def ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) : M ↪[L] N :=
  { f with
    inj' := hf
    map_rel' := fun {_} r x => StrongHomClass.map_rel f r x }
#align first_order.language.embedding.of_injective FirstOrder.Language.Embedding.ofInjective

@[simp]
theorem coeFn_ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) :
    (ofInjective hf : M → N) = f :=
  rfl
#align first_order.language.embedding.coe_fn_of_injective FirstOrder.Language.Embedding.coeFn_ofInjective

@[simp]
theorem ofInjective_toHom [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) :
    (ofInjective hf).toHom = f := by
  ext; simp
#align first_order.language.embedding.of_injective_to_hom FirstOrder.Language.Embedding.ofInjective_toHom

variable (L) (M)

/-- The identity embedding from a structure to itself. -/
@[refl]
def refl : M ↪[L] M where toEmbedding := Function.Embedding.refl M
#align first_order.language.embedding.refl FirstOrder.Language.Embedding.refl

variable {L} {M}

instance : Inhabited (M ↪[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (x : M) : refl L M x = x :=
  rfl
#align first_order.language.embedding.refl_apply FirstOrder.Language.Embedding.refl_apply

/-- Composition of first-order embeddings. -/
@[trans]
def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P where
  toFun := hnp ∘ hmn
  inj' := hnp.injective.comp hmn.injective
  -- Porting note: should be done by autoparam?
  map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
  -- Porting note: should be done by autoparam?
  map_rel' := by intros; rw [Function.comp.assoc, map_rel, map_rel]
#align first_order.language.embedding.comp FirstOrder.Language.Embedding.comp

@[simp]
theorem comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl
#align first_order.language.embedding.comp_apply FirstOrder.Language.Embedding.comp_apply

/-- Composition of first-order embeddings is associative. -/
theorem comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align first_order.language.embedding.comp_assoc FirstOrder.Language.Embedding.comp_assoc

theorem comp_injective (h : N ↪[L] P) :
    Function.Injective (h.comp : (M ↪[L] N) →  (M ↪[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]
theorem comp_inj (h : N ↪[L] P) (f g : M ↪[L] N) : h.comp f = h.comp g ↔ f = g :=
  ⟨fun eq ↦ h.comp_injective eq, congr_arg h.comp⟩

theorem toHom_comp_injective (h : N ↪[L] P) :
    Function.Injective (h.toHom.comp : (M →[L] N) →  (M →[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]
theorem toHom_comp_inj (h : N ↪[L] P) (f g : M →[L] N) : h.toHom.comp f = h.toHom.comp g ↔ f = g :=
  ⟨fun eq ↦ h.toHom_comp_injective eq, congr_arg h.toHom.comp⟩

@[simp]
theorem comp_toHom (hnp : N ↪[L] P) (hmn : M ↪[L] N) :
    (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom :=
  rfl
#align first_order.language.embedding.comp_to_hom FirstOrder.Language.Embedding.comp_toHom

@[simp]
theorem comp_refl (f : M ↪[L] N) : f.comp (refl L M) = f := DFunLike.coe_injective rfl

@[simp]
theorem refl_comp (f : M ↪[L] N) : (refl L N).comp f = f := DFunLike.coe_injective rfl

@[simp]
theorem refl_toHom : (refl L M).toHom = Hom.id L M :=
  rfl

end Embedding

/-- Any element of an injective `StrongHomClass` can be realized as a first_order embedding. -/
def StrongHomClass.toEmbedding {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [EmbeddingLike F M N] [StrongHomClass L F M N] : F → M ↪[L] N := fun φ =>
  ⟨⟨φ, EmbeddingLike.injective φ⟩, StrongHomClass.map_fun φ, StrongHomClass.map_rel φ⟩
#align first_order.language.strong_hom_class.to_embedding FirstOrder.Language.StrongHomClass.toEmbedding

namespace Equiv

instance : EquivLike (M ≃[L] N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    simp only [mk.injEq]
    ext x
    exact Function.funext_iff.1 h₁ x

instance : StrongHomClass L (M ≃[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm]
def symm (f : M ≃[L] N) : N ≃[L] M :=
  { f.toEquiv.symm with
    map_fun' := fun n f' {x} => by
      simp only [Equiv.toFun_as_coe]
      rw [Equiv.symm_apply_eq]
      refine Eq.trans ?_ (f.map_fun' f' (f.toEquiv.symm ∘ x)).symm
      rw [← Function.comp.assoc, Equiv.toFun_as_coe, Equiv.self_comp_symm, Function.id_comp]
    map_rel' := fun n r {x} => by
      simp only [Equiv.toFun_as_coe]
      refine (f.map_rel' r (f.toEquiv.symm ∘ x)).symm.trans ?_
      rw [← Function.comp.assoc, Equiv.toFun_as_coe, Equiv.self_comp_symm, Function.id_comp] }
#align first_order.language.equiv.symm FirstOrder.Language.Equiv.symm

instance hasCoeToFun : CoeFun (M ≃[L] N) fun _ => M → N :=
  DFunLike.hasCoeToFun
#align first_order.language.equiv.has_coe_to_fun FirstOrder.Language.Equiv.hasCoeToFun

@[simp]
theorem symm_symm (f : M ≃[L] N) :
    f.symm.symm = f :=
  rfl

@[simp]
theorem apply_symm_apply (f : M ≃[L] N) (a : N) : f (f.symm a) = a :=
  f.toEquiv.apply_symm_apply a
#align first_order.language.equiv.apply_symm_apply FirstOrder.Language.Equiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (f : M ≃[L] N) (a : M) : f.symm (f a) = a :=
  f.toEquiv.symm_apply_apply a
#align first_order.language.equiv.symm_apply_apply FirstOrder.Language.Equiv.symm_apply_apply

@[simp]
theorem map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x
#align first_order.language.equiv.map_fun FirstOrder.Language.Equiv.map_fun

@[simp]
theorem map_constants (φ : M ≃[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c
#align first_order.language.equiv.map_constants FirstOrder.Language.Equiv.map_constants

@[simp]
theorem map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x
#align first_order.language.equiv.map_rel FirstOrder.Language.Equiv.map_rel

/-- A first-order equivalence is also a first-order embedding. -/
def toEmbedding : (M ≃[L] N) → M ↪[L] N :=
  StrongHomClass.toEmbedding
#align first_order.language.equiv.to_embedding FirstOrder.Language.Equiv.toEmbedding

/-- A first-order equivalence is also a first-order homomorphism. -/
def toHom : (M ≃[L] N) → M →[L] N :=
  HomClass.toHom
#align first_order.language.equiv.to_hom FirstOrder.Language.Equiv.toHom

@[simp]
theorem toEmbedding_toHom (f : M ≃[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl
#align first_order.language.equiv.to_embedding_to_hom FirstOrder.Language.Equiv.toEmbedding_toHom

@[simp]
theorem coe_toHom {f : M ≃[L] N} : (f.toHom : M → N) = (f : M → N) :=
  rfl
#align first_order.language.equiv.coe_to_hom FirstOrder.Language.Equiv.coe_toHom

@[simp]
theorem coe_toEmbedding (f : M ≃[L] N) : (f.toEmbedding : M → N) = (f : M → N) :=
  rfl
#align first_order.language.equiv.coe_to_embedding FirstOrder.Language.Equiv.coe_toEmbedding

theorem injective_toEmbedding : Function.Injective (toEmbedding : (M ≃[L] N) → M ↪[L] N) := by
  intro _ _ h; apply DFunLike.coe_injective; exact congr_arg (DFunLike.coe ∘ Embedding.toHom) h

theorem coe_injective : @Function.Injective (M ≃[L] N) (M → N) (↑) :=
  DFunLike.coe_injective
#align first_order.language.equiv.coe_injective FirstOrder.Language.Equiv.coe_injective

@[ext]
theorem ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)
#align first_order.language.equiv.ext FirstOrder.Language.Equiv.ext

theorem ext_iff {f g : M ≃[L] N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h _ => h ▸ rfl, fun h => ext h⟩
#align first_order.language.equiv.ext_iff FirstOrder.Language.Equiv.ext_iff

theorem bijective (f : M ≃[L] N) : Function.Bijective f :=
  EquivLike.bijective f
#align first_order.language.equiv.bijective FirstOrder.Language.Equiv.bijective

theorem injective (f : M ≃[L] N) : Function.Injective f :=
  EquivLike.injective f
#align first_order.language.equiv.injective FirstOrder.Language.Equiv.injective

theorem surjective (f : M ≃[L] N) : Function.Surjective f :=
  EquivLike.surjective f
#align first_order.language.equiv.surjective FirstOrder.Language.Equiv.surjective

variable (L) (M)

/-- The identity equivalence from a structure to itself. -/
@[refl]
def refl : M ≃[L] M where toEquiv := _root_.Equiv.refl M
#align first_order.language.equiv.refl FirstOrder.Language.Equiv.refl

variable {L} {M}

instance : Inhabited (M ≃[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (x : M) : refl L M x = x := by simp [refl]; rfl
#align first_order.language.equiv.refl_apply FirstOrder.Language.Equiv.refl_apply

/-- Composition of first-order equivalences. -/
@[trans]
def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
  { hmn.toEquiv.trans hnp.toEquiv with
    toFun := hnp ∘ hmn
    -- Porting note: should be done by autoparam?
    map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
    -- Porting note: should be done by autoparam?
    map_rel' := by intros; rw [Function.comp.assoc, map_rel, map_rel] }
#align first_order.language.equiv.comp FirstOrder.Language.Equiv.comp

@[simp]
theorem comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl
#align first_order.language.equiv.comp_apply FirstOrder.Language.Equiv.comp_apply

@[simp]
theorem comp_refl (g : M ≃[L] N) : g.comp (refl L M) = g :=
  rfl

@[simp]
theorem refl_comp (g : M ≃[L] N) : (refl L N).comp g = g :=
  rfl

@[simp]
theorem refl_toEmbedding : (refl L M).toEmbedding = Embedding.refl L M :=
  rfl

@[simp]
theorem refl_toHom : (refl L M).toHom = Hom.id L M :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align first_order.language.equiv.comp_assoc FirstOrder.Language.Equiv.comp_assoc

theorem injective_comp (h : N ≃[L] P) :
    Function.Injective (h.comp : (M ≃[L] N) →  (M ≃[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (congr_fun (congr_arg DFunLike.coe hfg) x)

@[simp]
theorem comp_toHom (hnp : N ≃[L] P) (hmn : M ≃[L] N) :
    (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom :=
  rfl

@[simp]
theorem comp_toEmbedding (hnp : N ≃[L] P) (hmn : M ≃[L] N) :
    (hnp.comp hmn).toEmbedding = hnp.toEmbedding.comp hmn.toEmbedding :=
  rfl

@[simp]
theorem self_comp_symm (f : M ≃[L] N) : f.comp f.symm = refl L N := by
  ext; rw [comp_apply, apply_symm_apply, refl_apply]

@[simp]
theorem symm_comp_self (f : M ≃[L] N) : f.symm.comp f = refl L M := by
  ext; rw [comp_apply, symm_apply_apply, refl_apply]

@[simp]
theorem symm_comp_self_toEmbedding (f : M ≃[L] N) :
    f.symm.toEmbedding.comp f.toEmbedding = Embedding.refl L M := by
  rw [← comp_toEmbedding, symm_comp_self, refl_toEmbedding]

@[simp]
theorem self_comp_symm_toEmbedding (f : M ≃[L] N) :
    f.toEmbedding.comp f.symm.toEmbedding = Embedding.refl L N := by
  rw [← comp_toEmbedding, self_comp_symm, refl_toEmbedding]

@[simp]
theorem symm_comp_self_toHom (f : M ≃[L] N) :
    f.symm.toHom.comp f.toHom = Hom.id L M := by
  rw [← comp_toHom, symm_comp_self, refl_toHom]

@[simp]
theorem self_comp_symm_toHom (f : M ≃[L] N) :
    f.toHom.comp f.symm.toHom = Hom.id L N := by
  rw [← comp_toHom, self_comp_symm, refl_toHom]

@[simp]
theorem comp_symm (f : M ≃[L] N) (g : N ≃[L] P) : (g.comp f).symm = f.symm.comp g.symm :=
  rfl

theorem comp_right_injective (h : M ≃[L] N) :
    Function.Injective (fun f ↦ f.comp h : (N ≃[L] P) → (M ≃[L] P)) := by
  intro f g hfg
  convert (congr_arg (fun r : (M ≃[L] P) ↦ r.comp h.symm) hfg) <;>
    rw [comp_assoc, self_comp_symm, comp_refl]

@[simp]
theorem comp_right_inj (h : M ≃[L] N) (f g : N ≃[L] P) : f.comp h = g.comp h ↔ f = g :=
  ⟨fun eq ↦ h.comp_right_injective eq, congr_arg (fun (r : N ≃[L] P) ↦ r.comp h)⟩

end Equiv

/-- Any element of a bijective `StrongHomClass` can be realized as a first_order isomorphism. -/
def StrongHomClass.toEquiv {F M N} [L.Structure M] [L.Structure N] [EquivLike F M N]
    [StrongHomClass L F M N] : F → M ≃[L] N := fun φ =>
  ⟨⟨φ, EquivLike.inv φ, EquivLike.left_inv φ, EquivLike.right_inv φ⟩, StrongHomClass.map_fun φ,
    StrongHomClass.map_rel φ⟩
#align first_order.language.strong_hom_class.to_equiv FirstOrder.Language.StrongHomClass.toEquiv

section SumStructure

variable (L₁ L₂ : Language) (S : Type*) [L₁.Structure S] [L₂.Structure S]

instance sumStructure : (L₁.sum L₂).Structure S where
  funMap := Sum.elim funMap funMap
  RelMap := Sum.elim RelMap RelMap
set_option linter.uppercaseLean3 false in
#align first_order.language.sum_Structure FirstOrder.Language.sumStructure

variable {L₁ L₂ S}

@[simp]
theorem funMap_sum_inl {n : ℕ} (f : L₁.Functions n) :
    @funMap (L₁.sum L₂) S _ n (Sum.inl f) = funMap f :=
  rfl
#align first_order.language.fun_map_sum_inl FirstOrder.Language.funMap_sum_inl

@[simp]
theorem funMap_sum_inr {n : ℕ} (f : L₂.Functions n) :
    @funMap (L₁.sum L₂) S _ n (Sum.inr f) = funMap f :=
  rfl
#align first_order.language.fun_map_sum_inr FirstOrder.Language.funMap_sum_inr

@[simp]
theorem relMap_sum_inl {n : ℕ} (R : L₁.Relations n) :
    @RelMap (L₁.sum L₂) S _ n (Sum.inl R) = RelMap R :=
  rfl
#align first_order.language.rel_map_sum_inl FirstOrder.Language.relMap_sum_inl

@[simp]
theorem relMap_sum_inr {n : ℕ} (R : L₂.Relations n) :
    @RelMap (L₁.sum L₂) S _ n (Sum.inr R) = RelMap R :=
  rfl
#align first_order.language.rel_map_sum_inr FirstOrder.Language.relMap_sum_inr

end SumStructure

section Empty

section

variable [Language.empty.Structure M] [Language.empty.Structure N]

@[simp]
theorem empty.nonempty_embedding_iff :
    Nonempty (M ↪[Language.empty] N) ↔ Cardinal.lift.{w'} #M ≤ Cardinal.lift.{w} #N :=
  _root_.trans ⟨Nonempty.map fun f => f.toEmbedding, Nonempty.map fun f => { toEmbedding := f }⟩
    Cardinal.lift_mk_le'.symm
#align first_order.language.empty.nonempty_embedding_iff FirstOrder.Language.empty.nonempty_embedding_iff

@[simp]
theorem empty.nonempty_equiv_iff :
    Nonempty (M ≃[Language.empty] N) ↔ Cardinal.lift.{w'} #M = Cardinal.lift.{w} #N :=
  _root_.trans ⟨Nonempty.map fun f => f.toEquiv, Nonempty.map fun f => { toEquiv := f }⟩
    Cardinal.lift_mk_eq'.symm
#align first_order.language.empty.nonempty_equiv_iff FirstOrder.Language.empty.nonempty_equiv_iff

end

instance emptyStructure : Language.empty.Structure M :=
  ⟨Empty.elim, Empty.elim⟩
set_option linter.uppercaseLean3 false in
#align first_order.language.empty_Structure FirstOrder.Language.emptyStructure

instance : Unique (Language.empty.Structure M) :=
  ⟨⟨Language.emptyStructure⟩, fun a => by
    ext _ f <;> exact Empty.elim f⟩

instance (priority := 100) strongHomClassEmpty {F M N} [FunLike F M N] :
    StrongHomClass Language.empty F M N :=
  ⟨fun _ _ f => Empty.elim f, fun _ _ r => Empty.elim r⟩
#align first_order.language.strong_hom_class_empty FirstOrder.Language.strongHomClassEmpty

/-- Makes a `Language.empty.Hom` out of any function. -/
@[simps]
def _root_.Function.emptyHom (f : M → N) : M →[Language.empty] N where toFun := f
#align function.empty_hom Function.emptyHom

/-- Makes a `Language.empty.Embedding` out of any function. -/
--@[simps] Porting note: commented out and lemmas added manually
def _root_.Embedding.empty (f : M ↪ N) : M ↪[Language.empty] N where toEmbedding := f
#align embedding.empty Embedding.empty

@[simp]
theorem toFun_embedding_empty (f : M ↪ N) : (Embedding.empty f : M → N) = f :=
  rfl

@[simp]
theorem toEmbedding_embedding_empty (f : M ↪ N) : (Embedding.empty f).toEmbedding = f :=
  rfl

/-- Makes a `Language.empty.Equiv` out of any function. -/
--@[simps] Porting note: commented out and lemmas added manually
def _root_.Equiv.empty (f : M ≃ N) : M ≃[Language.empty] N where toEquiv := f
#align equiv.empty Equiv.empty

@[simp]
theorem toFun_equiv_empty (f : M ≃ N) : (Equiv.empty f : M → N) = f :=
  rfl

@[simp]
theorem toEquiv_equiv_empty (f : M ≃ N) : (Equiv.empty f).toEquiv = f :=
  rfl

end Empty

end Language

end FirstOrder

namespace Equiv

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

open FirstOrder

variable {L : Language} {M : Type*} {N : Type*} [L.Structure M]

/-- A structure induced by a bijection. -/
@[simps!]
def inducedStructure (e : M ≃ N) : L.Structure N :=
  ⟨fun f x => e (funMap f (e.symm ∘ x)), fun r x => RelMap r (e.symm ∘ x)⟩
set_option linter.uppercaseLean3 false in
#align equiv.induced_Structure Equiv.inducedStructure

/-- A bijection as a first-order isomorphism with the induced structure on the codomain. -/
--@[simps!] Porting note: commented out and lemmas added manually
def inducedStructureEquiv (e : M ≃ N) : @Language.Equiv L M N _ (inducedStructure e) := by
  letI : L.Structure N := inducedStructure e
  exact
  { e with
    map_fun' := @fun n f x => by simp [← Function.comp.assoc e.symm e x]
    map_rel' := @fun n r x => by simp [← Function.comp.assoc e.symm e x] }
set_option linter.uppercaseLean3 false in
#align equiv.induced_Structure_equiv Equiv.inducedStructureEquiv

@[simp]
theorem toEquiv_inducedStructureEquiv (e : M ≃ N) :
    @Language.Equiv.toEquiv L M N _ (inducedStructure e) (inducedStructureEquiv e) = e :=
  rfl

@[simp]
theorem toFun_inducedStructureEquiv (e : M ≃ N) :
    DFunLike.coe (@inducedStructureEquiv L M N _ e) = e :=
  rfl

@[simp]
theorem toFun_inducedStructureEquiv_Symm (e : M ≃ N) :
    (by
    letI : L.Structure N := inducedStructure e
    exact DFunLike.coe (@inducedStructureEquiv L M N _ e).symm) = (e.symm : N → M) :=
  rfl

end Equiv
