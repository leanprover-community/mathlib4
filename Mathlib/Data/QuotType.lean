/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Logic.Relator
public import Mathlib.Logic.Unique
public meta import Qq.MetaM

/-!
# Typeclass for quotient types

This typeclass is primarily for use by type synonyms of `Quot` and `Quotient`.

Using `QuotType` API for type synonyms of `Quot` and `Quotient` will avoid defeq abuse caused by
directly using `Quot` and `Quotient` APIs.

## Main definitions

* `QuotType Q α r` : the type `Q` is canonically isomorphic to `Quot α r`.
                     used for deriving `QuotType` instances from the output type.
* `QuotTypeOut`    : used for deriving `QuotType` instances from the input type.
* `mkQ`            : the quotient map inferred from the output type

## Notations

* `⟦a⟧`            : the quotient map inferred from the output type
* `mkQ'` `⟦a⟧'`    : the quotient map inferred from the input type
                       via typeclass `QuotTypeOut`
-/

@[expose] public section

/--
The class `QuotType Q α r` expresses the type `Q` is canonically isomorphic to `Quot α r`.

Using `QuotType` API for type synonyms of `Quot` and `Quotient` will avoid defeq abuse of the types
caused by directly using `Quot` and `Quotient` APIs.
-/
class QuotType (Q : Sort*) (α : outParam Sort*) (r : outParam (α → α → Prop)) where
  /-- The quotient map. Inferred from the output type. -/
  mkQ : α → Q := by exact Quot.mk _
  /-- The map from the given quotient type to `Quot r`. -/
  toQuot : Q → Quot r := by exact (·)
  toQuot_mkQ : ∀ a, toQuot (mkQ a) = Quot.mk r a := by exact fun _ ↦ rfl
  mkQ_surjective : Function.Surjective mkQ := by exact Quot.exists_rep
  /--
  The analogue of `Quot.sound`: If `a` and `b` are related by the relation,
  then they have equal equivalence classes.
  -/
  sound {a b : α} : r a b → mkQ a = mkQ b := by exact Quot.sound

export QuotType (mkQ)

/--
`QuotTypeOut` is used for deriving `QuotType` instances from the input type.

The instances of `QuotTypeOut` may be defined for types that have specific uses.

```
instance : QuotTypeOut ZFSet PSet PSet.Equiv where
```

They are also usually defined as scoped or local instances.

```
scoped instance {α} [s : Setoid α] : QuotTypeOut (Quotient s) α (· ≈ ·) where
```
-/
class QuotTypeOut (Q : outParam Sort*) (α : Sort*) (r : outParam (α → α → Prop))
    [QuotType Q α r] : Prop where

namespace QuotType

attribute [simp] toQuot_mkQ

open Lean Elab Term Meta Qq

@[inherit_doc mkQ]
elab "⟦" a:term "⟧" : term <= Q => do
  synthesizeSyntheticMVars
  let Q ← instantiateMVars Q
  if Q.isMVar then
    tryPostpone
    throwError "The output type must be known."
  let v ← match ← inferType Q with | .sort v => pure v | _ => mkFreshLevelMVar
  have Q : Q(Sort v) := Q
  let α ← mkFreshExprMVarQ q(Sort $(← mkFreshLevelMVar))
  let r ← mkFreshExprMVarQ q($α → $α → Prop)
  let .some inst ← trySynthInstanceQ q(QuotType $Q $α $r) |
    tryPostpone
    throwError "Cannot find `QuotType` instance for type `{Q}`."
  pure q(@mkQ $Q $α $r $inst $(← Qq.elabTermEnsuringTypeQ a q($α)))

open PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `mkQ` -/
@[delab app.QuotType.mkQ]
meta def delabMkQ : Delab := do
  guard <| (← getExpr).isAppOfArity' ``mkQ 5
  let a ← withNaryArg 4 delab
  `(⟦$a⟧)

@[inherit_doc mkQ]
macro "⟦" a:term " : " α:term "⟧" : term => `(⟦($a : $α)⟧)

/-- The quotient map. Inferred from the input type via typeclass `QuotTypeOut`. -/
syntax (name := mkQ') "mkQ'" : term

@[term_elab QuotType.mkQ', inherit_doc QuotType.mkQ']
meta def mkQ'Impl : TermElab := fun stx typ? => do
  let .some expectedType := typ? |
    let α ← mkFreshTypeMVar
    let β ← mkFreshTypeMVar
    postponeElabTerm stx (some (← mkArrow α β))
  synthesizeSyntheticMVars
  let expectedType ← instantiateMVars expectedType
  let expectedType ← whnf expectedType
  let .forallE _ α _ _ := expectedType |
    if expectedType.isMVar then tryPostpone
    throwError "Expected type is not a function."
  if α.isMVar then
    tryPostpone
    throwError "The input type must be known."
  let Q ← mkFreshExprMVarQ q(Sort $(← mkFreshLevelMVar))
  let u ← match ← inferType α with | .sort u => pure u | _ => mkFreshLevelMVar
  have α : Q(Sort u) := α
  let r ← mkFreshExprMVarQ q($α → $α → Prop)
  let inst ← mkFreshExprMVarQ q(QuotType $Q $α $r)
  let .some _ ← trySynthInstanceQ q(@QuotTypeOut $Q $α $r $inst) |
    tryPostpone
    throwError "Cannot find `QuotTypeOut` instance for type `{α}`."
  pure q(@mkQ $Q $α $r $inst)

/-- The quotient map. Inferred from the input type. -/
macro "⟦" t:term "⟧'" : term => `(mkQ' $t)

/-- The quotient map. Inferred from the input type. -/
macro "⟦" t:term " : " α:term "⟧'" : term => `(⟦($t : $α)⟧')

end QuotType

namespace Quot

instance instQuotType {α} (r : α → α → Prop) : QuotType (Quot r) α r where

end Quot

namespace Quotient

instance instQuotType {α} (s : Setoid α) : QuotType (Quotient s) α (· ≈ ·) where
  mkQ := Quotient.mk _

@[nolint defLemma docBlame]
scoped instance instHasQuot {α} [s : Setoid α] : QuotTypeOut (Quotient s) α (· ≈ ·) where

end Quotient

namespace QuotType

section

variable {Q : Sort*} {α : Sort*} {r : α → α → Prop} [QuotType Q α r]

/--
The analogue of `Quot.lift`: if `f : α → β` respects the relation `r`,
then it lifts to a function on `Q` such that `liftQ f h ⟦a⟧ = f a`.
-/
protected def liftQ {β : Sort*} (f : α → β) (h : ∀ (a b : α), r a b → f a = f b) : Q → β :=
  fun q ↦ Quot.lift f h (toQuot q)

/--
The analogue of `Quot.liftOn`: if `f : α → β` respects the relation `r`,
then it lifts to a function on `Q` such that `liftOnQ ⟦a⟧ f h = f a`.
-/
protected abbrev liftOnQ {β : Sort*} (q : Q) (f : α → β) (c : (a b : α) → r a b → f a = f b) : β :=
  QuotType.liftQ f c q

@[simp]
theorem liftQ_mkQ {β : Sort*} (f : α → β) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) :
    QuotType.liftQ f h (⟦a⟧ : Q) = f a := by
  rw [QuotType.liftQ, toQuot_mkQ]

theorem liftOnQ_mkQ {β : Sort*} (a : α) (f : α → β) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    QuotType.liftOnQ (⟦a⟧ : Q) f h = f a :=
  liftQ_mkQ f h a

theorem exists_rep (q : Q) : ∃ a, ⟦a⟧ = q :=
  QuotType.mkQ_surjective q

@[elab_as_elim]
theorem ind {motive : Q → Prop}
    (h : (a : α) → motive ⟦a⟧) (q : Q) : motive q :=
  (exists_rep q).rec fun a ha ↦ ha ▸ h a

@[elab_as_elim]
protected theorem inductionOn {motive : Q → Prop}
    (q : Q) (h : (a : α) → motive ⟦a⟧) : motive q :=
  ind h q

section
variable {motive : Q → Sort*} (f : (a : α) → motive ⟦a⟧)

/-- Auxiliary definition for `QuotType.recQ`. -/
@[reducible, macro_inline]
protected def indep (a : α) : PSigma motive :=
  ⟨⟦a⟧, f a⟩

protected theorem indepCoherent
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b) :
    (a b : α) → r a b → QuotType.indep f a = QuotType.indep f b :=
  fun a b e ↦ PSigma.eta (sound e) (h a b e)

protected theorem liftQIndepPr1
    (h : ∀ (a b : α) (p : r a b), Eq.ndrec (f a) (sound p) = f b) (q : Q) :
    (QuotType.liftQ (QuotType.indep f) (QuotType.indepCoherent f h) q).1 = q := by
  induction q using QuotType.ind
  rw [liftQ_mkQ]

end

/-- The analogue of `Quot.rec` for `QuotType`. -/
@[inline, elab_as_elim]
def recQ {motive : Q → Sort*}
    (f : (a : α) → motive ⟦a⟧)
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    (q : Q) :
    motive q :=
  Eq.ndrecOn (QuotType.liftQIndepPr1 f h q)
    ((QuotType.liftQ (QuotType.indep f) (QuotType.indepCoherent f h) q).2)

@[simp]
theorem recQ_mkQ {motive : Q → Sort*}
    (f : (a : α) → motive ⟦a⟧)
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    (a : α) :
    QuotType.recQ (motive := motive) f h ⟦a⟧ = f a := by
  rw [QuotType.recQ, ← heq_iff_eq, eqRec_heq_iff_heq, liftQ_mkQ]

/-- The analogue of `Quot.recOn` for `QuotType`. -/
@[elab_as_elim]
abbrev recOnQ {motive : Q → Sort*}
    (q : Q)
    (f : (a : α) → motive ⟦a⟧)
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b) :
    motive q :=
  QuotType.recQ f h q

/-- The analogue of `Quot.recOnSubsingleton` for `QuotType`. -/
@[elab_as_elim]
abbrev recOnSubsingletonQ {motive : Q → Sort*}
    [_h : ∀ a, Subsingleton (motive ⟦a⟧)]
    (q : Q)
    (f : (a : α) → motive ⟦a⟧) :
    motive q :=
  QuotType.recOnQ q f (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- The analogue of `Quot.hrecOn` for `QuotType`. -/
@[elab_as_elim]
abbrev hrecOnQ {motive : Q → Sort*}
    (q : Q)
    (f : (a : α) → motive ⟦a⟧)
    (h : (a b : α) → r a b → f a ≍ f b) :
    motive q :=
  QuotType.recOnQ q f fun a b p ↦ eq_of_heq <| (eqRec_heq_self _ _).trans (h a b p)

theorem hrecOnQ_mkQ {motive : Q → Sort*}
    (a : α)
    (f : (a : α) → motive ⟦a⟧)
    (h : (a b : α) → r a b → f a ≍ f b) :
    QuotType.hrecOnQ (motive := motive) ⟦a⟧ f h = f a := by
  simp

end

section

variable {Qa α : Sort*} {ra : α → α → Prop} [QuotType Qa α ra]
variable {Qb β : Sort*} {rb : β → β → Prop} [QuotType Qb β rb]
variable {Qc γ : Sort*} {rc : γ → γ → Prop} [QuotType Qc γ rc]
variable {φ : Sort*}

open Relator in
/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements to a
function `f : Qa → Qb`. -/
def mapQ (f : α → β) (h : (ra ⇒ rb) f f) : Qa → Qb :=
  (QuotType.liftQ fun x ↦ ⟦f x⟧) fun _ _ ↦ (QuotType.sound <| h ·)

open Relator in
@[simp]
theorem mapQ_mkQ (f : α → β) (h : (ra ⇒ rb) f f) (a : α) :
    QuotType.mapQ f h (⟦a⟧ : Qa) = (⟦f a⟧ : Qb) :=
  liftQ_mkQ _ _ _

/-- Lift a binary function to a quotient on both arguments. -/
def liftQ₂'
    (f : α → β → φ)
    (ha : ∀ a₁ a₂ b, ra a₁ a₂ → f a₁ b = f a₂ b)
    (hb : ∀ a b₁ b₂, rb b₁ b₂ → f a b₁ = f a b₂) :
    Qa → Qb → φ :=
  QuotType.liftQ (fun a ↦ QuotType.liftQ (f a) (hb a))
    (fun a₁ a₂ h ↦ funext (QuotType.ind (fun b ↦ by simpa [liftQ_mkQ] using ha a₁ a₂ b h)))

@[simp]
lemma liftQ₂'_mkQ
    (f : α → β → φ)
    (ha : ∀ a₁ a₂ b, ra a₁ a₂ → f a₁ b = f a₂ b)
    (hb : ∀ a b₁ b₂, rb b₁ b₂ → f a b₁ = f a b₂)
    (a : α) (b : β) :
    QuotType.liftQ₂' f ha hb (⟦a⟧ : Qa) (⟦b⟧ : Qb) = f a b := by
  simp [QuotType.liftQ₂']

/-- Lift a binary function to a quotient on both arguments. -/
abbrev liftOnQ₂'
    (qa : Qa) (qb : Qb)
    (f : α → β → φ)
    (ha : ∀ a₁ a₂ b, ra a₁ a₂ → f a₁ b = f a₂ b)
    (hb : ∀ a b₁ b₂, rb b₁ b₂ → f a b₁ = f a b₂) : φ :=
  QuotType.liftQ₂' f ha hb qa qb

lemma liftOnQ₂'_mkQ
    (a : α) (b : β)
    (f : α → β → φ)
    (ha : ∀ a₁ a₂ b, ra a₁ a₂ → f a₁ b = f a₂ b)
    (hb : ∀ a b₁ b₂, rb b₁ b₂ → f a b₁ = f a b₂) :
    QuotType.liftOnQ₂' (⟦a⟧ : Qa) (⟦b⟧ : Qb) f ha hb = f a b := by
  simp

/-- Lift a binary function to a quotient on both arguments. -/
abbrev liftQ₂ [IsRefl α ra] [IsRefl β rb]
    (f : α → β → φ)
    (h : ∀ a₁ b₁ a₂ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ = f a₂ b₂) :
    Qa → Qb → φ :=
  QuotType.liftQ₂' f (h · _ · · · (refl _)) (h · · _ · (refl _) ·)

lemma liftQ₂_mkQ [IsRefl α ra] [IsRefl β rb]
    (f : α → β → φ)
    (h : ∀ a₁ b₁ a₂ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ = f a₂ b₂)
    (a : α) (b : β) :
    QuotType.liftQ₂ f h (⟦a⟧ : Qa) (⟦b⟧ : Qb) = f a b := by
  simp

/-- Lift a binary function to a quotient on both arguments. -/
abbrev liftOnQ₂ [IsRefl α ra] [IsRefl β rb]
    (qa : Qa) (qb : Qb)
    (f : α → β → φ)
    (h : ∀ a₁ b₁ a₂ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ = f a₂ b₂) : φ :=
  QuotType.liftQ₂ f h qa qb

lemma liftOnQ₂_mkQ [IsRefl α ra] [IsRefl β rb]
    (a : α) (b : β)
    (f : α → β → φ)
    (h : ∀ a₁ b₁ a₂ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ = f a₂ b₂) :
    QuotType.liftOnQ₂ (⟦a⟧ : Qa) (⟦b⟧ : Qb) f h = f a b := by
  simp

open Relator in
/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements to a
function `f : Qa → Qb → Qc`. -/
def mapQ₂ [IsRefl α ra] [IsRefl β rb] (f : α → β → γ)
    (h : (ra ⇒ rb ⇒ rc) f f) : Qa → Qb → Qc :=
  (QuotType.liftQ₂ fun x y ↦ ⟦f x y⟧) fun _ _ _ _ ↦ (QuotType.sound <| h · ·)

open Relator in
@[simp]
theorem mapQ₂_mkQ [IsRefl α ra] [IsRefl β rb] (f : α → β → γ) (h : (ra ⇒ rb ⇒ rc) f f)
    (a : α) (b : β) :
    QuotType.mapQ₂ f h (⟦a⟧ : Qa) (⟦b⟧ : Qb) = (⟦f a b⟧ : Qc) := by
  simp [QuotType.mapQ₂]

@[elab_as_elim]
protected theorem ind₂ {motive : Qa → Qb → Prop}
    (h : (a : α) → (b : β) → motive ⟦a⟧ ⟦b⟧)
    (qa : Qa) (qb : Qb) :
    motive qa qb :=
  QuotType.ind (QuotType.ind h qa) qb

@[elab_as_elim]
protected theorem inductionOn₂ {motive : Qa → Qb → Prop}
    (qa : Qa) (qb : Qb)
    (h : (a : α) → (b : β) → motive ⟦a⟧ ⟦b⟧) :
    motive qa qb :=
  QuotType.ind₂ h qa qb

/-- A binary version of `QuotType.recOnSubsingletonQ`. -/
@[elab_as_elim]
def recOnSubsingletonQ₂ {motive : Qa → Qb → Sort*}
    [_h : ∀ a b, Subsingleton (motive ⟦a⟧ ⟦b⟧)]
    (qa : Qa) (qb : Qb) (f : ∀ a b, motive ⟦a⟧ ⟦b⟧) :
    motive qa qb :=
  QuotType.recOnSubsingletonQ (_h := fun _ ↦ QuotType.ind inferInstance qb) qa
    fun a ↦ QuotType.recOnSubsingletonQ qb fun b ↦ f a b

/-- Recursion on two `QuotType` arguments `qa` and `qb`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
@[elab_as_elim]
def hrecOnQ₂ [IsRefl α ra] [IsRefl β rb] {motive : Qa → Qb → Sort*}
    (qa : Qa) (qb : Qb) (f : ∀ a b, motive ⟦a⟧ ⟦b⟧)
    (h : ∀ a₁ b₁ a₂ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ ≍ f a₂ b₂) :
    motive qa qb :=
  QuotType.hrecOnQ qa
    (fun a ↦ QuotType.hrecOnQ qb (f a) (fun b₁ b₂ pb ↦ h _ _ _ _ (refl _) pb))
    fun a₁ a₂ pa ↦ by exact QuotType.inductionOn qb fun b ↦ by simp [h, pa, refl]

@[simp]
theorem hrecOnQ₂_mkQ [IsRefl α ra] [IsRefl β rb] {motive : Qa → Qb → Sort*}
    (a : α) (b : β) (f : ∀ a b, motive ⟦a⟧ ⟦b⟧)
    (h : ∀ a₁ b₁ a₂ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ ≍ f a₂ b₂) :
    QuotType.hrecOnQ₂ (motive := motive) ⟦a⟧ ⟦b⟧ f h = f a b := by
  simp [QuotType.hrecOnQ₂]

@[elab_as_elim]
protected theorem ind₃ {motive : Qa → Qb → Qc → Prop}
    (h : (a : α) → (b : β) → (c : γ) → motive ⟦a⟧ ⟦b⟧ ⟦c⟧)
    (qa : Qa) (qb : Qb) (qc : Qc) :
    motive qa qb qc :=
  QuotType.ind (QuotType.ind₂ h qa qb) qc

@[elab_as_elim]
protected theorem inductionOn₃ {motive : Qa → Qb → Qc → Prop}
    (qa : Qa) (qb : Qb) (qc : Qc)
    (h : (a : α) → (b : β) → (c : γ) → motive ⟦a⟧ ⟦b⟧ ⟦c⟧) :
    motive qa qb qc :=
  QuotType.ind₃ h qa qb qc

end

section

variable {Q α : Sort*} {r : α → α → Prop} [QuotType Q α r]

/-- Makes a quotient from `Quot r`. -/
def ofQuot : Quot r → Q :=
  Quot.lift mkQ fun _ _ ↦ sound

@[simp]
theorem ofQuot_toQuot (q : Q) : ofQuot (toQuot q) = q :=
  ind (fun a ↦ by rw [toQuot_mkQ, ofQuot]) q

@[simp]
theorem toQuot_ofQuot (q : Quot r) : toQuot (ofQuot q : Q) = q :=
  Quot.ind (β := fun q ↦ toQuot (ofQuot q) = q) toQuot_mkQ q

theorem toQuot_injective : Function.Injective (toQuot (Q := Q)) :=
  Function.LeftInverse.injective ofQuot_toQuot

theorem eq_iff_quotMk {a b : α} : (⟦a⟧ : Q) = ⟦b⟧ ↔ Quot.mk r a = Quot.mk r b := by
  rw [← toQuot_mkQ (Q := Q), ← toQuot_mkQ (Q := Q), toQuot_injective.eq_iff]

theorem Quot.exact {α r} [IsEquiv α r] {a b : α} : Quot.mk r a = Quot.mk r b → r a b :=
  Quotient.exact (s := ⟨r, refl, symm, _root_.trans⟩)

theorem exact [IsEquiv α r] {a b : α} : (⟦a⟧ : Q) = ⟦b⟧ → r a b :=
  fun h ↦ Quot.exact (eq_iff_quotMk.mp h)

@[simp]
theorem eq [IsEquiv α r] {a b : α} : (⟦a⟧ : Q) = ⟦b⟧ ↔ r a b :=
  ⟨exact, sound⟩

alias mkQ_eq_mkQ := eq

protected theorem «forall» {p : Q → Prop} : (∀ q, p q) ↔ ∀ a, p ⟦a⟧ :=
  ⟨fun h _ ↦ h _, QuotType.ind⟩

protected theorem «exists» {p : Q → Prop} : (∃ q, p q) ↔ ∃ a, p ⟦a⟧ :=
  ⟨fun ⟨q, hq⟩ ↦ QuotType.ind .intro q hq, fun ⟨a, ha⟩ ↦ ⟨⟦a⟧, ha⟩⟩

instance (priority := 800) [Nonempty α] : Nonempty Q :=
  Nonempty.map mkQ ‹_›

instance (priority := 800) [Inhabited α] : Inhabited Q :=
  ⟨⟦default⟧⟩

instance (priority := 800) [Subsingleton α] : Subsingleton Q where
  allEq := QuotType.ind₂ fun x y ↦ congrArg mkQ (Subsingleton.elim x y)

instance (priority := 800) [Unique α] : Unique Q := Unique.mk' _

instance (priority := 800) [IsEquiv α r] [dec : DecidableRel r] : DecidableEq Q :=
  fun q₁ q₂ ↦ QuotType.recOnSubsingletonQ₂ q₁ q₂ fun a₁ a₂ ↦
    match dec a₁ a₂ with
    | isTrue  h₁ => isTrue (QuotType.sound h₁)
    | isFalse h₂ => isFalse (fun h ↦ absurd (QuotType.exact h) h₂)

@[simp]
theorem liftQ_surjective {β : Sort*} {f : α → β} {h : ∀ a b, r a b → f a = f b} :
    Function.Surjective (QuotType.liftQ f h : Q → β) ↔ Function.Surjective f :=
  ⟨fun hf => by simpa only [liftQ_mkQ, Function.comp_def] using hf.comp QuotType.exists_rep,
    fun hf y => let ⟨x, hx⟩ := hf y; ⟨mkQ x, by simpa only [liftQ_mkQ] using hx⟩⟩

@[simp]
lemma liftOnQ_surjective {β : Sort*} {f : α → β} {h : ∀ a b, r a b → f a = f b} :
    Function.Surjective (fun x : Q ↦ QuotType.liftOnQ x f h) ↔ Function.Surjective f :=
  liftQ_surjective

@[simp]
theorem liftQ_comp_mkQ {β : Sort*} {f : α → β} (h : ∀ a b, r a b → f a = f b) :
    (QuotType.liftQ f h : Q → β) ∘ mkQ = f :=
  funext <| QuotType.liftQ_mkQ f h

instance (priority := 800) (f : α → Prop) [hf : DecidablePred f] (h : ∀ a b, r a b → f a = f b) :
    DecidablePred (QuotType.liftQ f h : Q → Prop) :=
  fun q ↦ QuotType.recOnSubsingletonQ q fun _ ↦ by simpa using hf _

instance (priority := 800)
    {Qa α : Sort*} {ra : α → α → Prop} [QuotType Qa α ra] [IsRefl α ra]
    {Qb β : Sort*} {rb : β → β → Prop} [QuotType Qb β rb] [IsRefl β rb]
    (f : α → β → Prop) [hf : ∀ a, DecidablePred (f a)]
    (h : ∀ a₁ b₁ a₂ b₂, ra a₁ a₂ → rb b₁ b₂ → f a₁ b₁ = f a₂ b₂)
    (qa : Qa) (qb : Qb) :
    Decidable (QuotType.liftQ₂ f h qa qb) :=
  QuotType.recOnSubsingletonQ₂ qa qb fun _ _ ↦ by simpa using hf _ _

/-- Choose an element of the equivalence class using the axiom of choice. -/
noncomputable def out (q : Q) : α :=
  Classical.choose (exists_rep q)

@[simp]
theorem mkQ_out (q : Q) : ⟦QuotType.out q⟧ = q :=
  Classical.choose_spec (exists_rep q)

theorem mkQ_eq_iff_out [IsEquiv α r] {x : α} {y : Q} :
    ⟦x⟧ = y ↔ r x (out y) := by
  rw [← eq (Q := Q), mkQ_out]

theorem eq_mkQ_iff_out [IsEquiv α r] {x : Q} {y : α} :
    x = ⟦y⟧ ↔ r (out x) y := by
  rw [← eq (Q := Q), mkQ_out]

variable (Q) in
theorem out_mkQ_rel [IsEquiv α r] (a : α) : r (out (⟦a⟧ : Q)) a :=
  exact (mkQ_out _)

variable (Q) in
theorem rel_out_mkQ [IsEquiv α r] (a : α) : r a (out (⟦a⟧ : Q)) :=
  exact (mkQ_out _).symm

variable (Q) in
theorem out_rel_out [IsEquiv α r] {x y : Q} : r (out x) (out y) ↔ x = y := by
  rw [← eq_mkQ_iff_out (Q := Q), mkQ_out]

theorem out_injective [IsEquiv α r] : Function.Injective (QuotType.out : Q → α) :=
  fun _ _ h ↦ out_rel_out _ |>.1 <| h ▸ refl _

@[simp]
theorem out_inj {x y : Q} [IsEquiv α r] : out x = out y ↔ x = y :=
  ⟨fun h ↦ out_injective h, fun h ↦ h ▸ rfl⟩

@[elab_as_elim]
theorem inductionOnPi {ι : Sort*} {Q : ι → Sort*} {α : ι → Sort*}
    {r : (i : ι) → α i → α i → Prop} [∀ i, QuotType (Q i) (α i) (r i)]
    {p : (∀ i, Q i) → Prop} (q : ∀ i, Q i)
    (h : ∀ a : ∀ i, α i, p fun i ↦ ⟦a i⟧) : p q := by
  rw [← (funext fun i ↦ QuotType.mkQ_out (q i) : (fun i ↦ ⟦out (q i)⟧) = q)]
  apply h

theorem nonempty_quotient_iff (s : Setoid α) : Nonempty (Quotient s) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ ↦ Quotient.inductionOn a Nonempty.intro, fun ⟨a⟩ ↦ ⟨⟦a⟧⟩⟩

end

end QuotType

export QuotType (mkQ_eq_mkQ)
