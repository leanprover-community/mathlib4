/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Lean

open Lean Meta

namespace Mathlib.Tactic

namespace BicategoryLike

structure Obj where
  e? : Option Expr
  deriving Inhabited

def Obj.e (a : Obj) : Expr :=
  a.e?.get!

/-- Expressions for atomic 1-morphisms. -/
structure Atom₁ : Type where
  /-- Extract a Lean expression from an `Atom₁` expression. -/
  e : Expr
  /-- The domain of the 1-morphism. -/
  src : Obj
  /-- The codomain of the 1-morphism. -/
  tgt : Obj
  deriving Inhabited

/-- A monad equipped with the ability to construct `Atom₁` terms. -/
class MkAtom₁ (m : Type → Type) where
  ofExpr (e : Expr) : m Atom₁

/-- Expressions for 1-morphisms. -/
inductive Mor₁ : Type
  /-- `id e a` is the expression for `𝟙 a`, where `e` is the underlying lean expression. -/
  | id (e : Expr) (a : Obj) : Mor₁
  /-- `comp e f g` is the expression for `f ≫ g`, where `e` is the underlying lean expression. -/
  | comp (e : Expr) : Mor₁ → Mor₁ → Mor₁
  /-- Construct the expression for an atomic 1-morphism. -/
  | of : Atom₁ → Mor₁
  deriving Inhabited

class MkMor₁ (m : Type → Type) where
  ofExpr (e : Expr) : m Mor₁

def Mor₁.e : Mor₁ → Expr
  | .id e _ => e
  | .comp e _ _ => e
  | .of a => a.e

/-- The domain of a 1-morphism. -/
def Mor₁.src : Mor₁ → Obj
  | .id _ a => a
  | .comp _ f _ => f.src
  | .of f => f.src

/-- The codomain of a 1-morphism. -/
def Mor₁.tgt : Mor₁ → Obj
  | .id _ a => a
  | .comp _ _ g => g.tgt
  | .of f => f.tgt

/-- Converts a 1-morphism into a list of its components. -/
def Mor₁.toList : Mor₁ → List Atom₁
  | .id _ _ => []
  | .comp _ f g => f.toList ++ g.toList
  | .of f => [f]

/-- A monad equipped with the ability to manipulate 1-morphisms. -/
class MonadMor₁ (m : Type → Type) where
  id₁M (a : Obj) : m Mor₁
  comp₁M (f g : Mor₁) : m Mor₁

abbrev Mor₁.compM {m : Type → Type} [MonadMor₁ m] (f g : Mor₁) : m Mor₁ :=
  MonadMor₁.comp₁M f g

abbrev Mor₁.idM {m : Type → Type} [MonadMor₁ m] (a : Obj) : m Mor₁ :=
  MonadMor₁.id₁M a

class Context (ρ : Type) where
  mkContext? : Expr → MetaM (Option ρ)

export Context (mkContext?)

structure State where
  cache : PHashMap Expr Mor₁ := {}

abbrev CoherenceM (ρ : Type) [Context ρ] := ReaderT ρ <| StateT State MetaM

def CoherenceM.run {α ρ : Type} [Context ρ] (x : CoherenceM ρ α) (ctx : ρ) (s : State := {}) :
    MetaM α := do
  Prod.fst <$> ReaderT.run x ctx s

def mkContext {ρ  : Type} [Context ρ] (e : Expr) : MetaM ρ := do
  match ← mkContext? e with
  | some c => return c
  | none => throwError "failed to construct a monoidal category or bicategory context from {e}"

section PureCoherence

structure CoherenceHom where
  e : Expr
  src : Mor₁
  tgt : Mor₁
  inst : Expr
  unfold : Expr
  deriving Inhabited

structure AtomIso where
  e : Expr
  src : Mor₁
  tgt : Mor₁
  deriving Inhabited

inductive StructuralAtom : Type
  /-- The expression for the associator `α_ f g h`. -/
  | associator (e : Expr) (f g h : Mor₁) : StructuralAtom
  /-- The expression for the left unitor `λ_ f`. -/
  | leftUnitor (e : Expr) (f : Mor₁) : StructuralAtom
  /-- The expression for the right unitor `ρ_ f`. -/
  | rightUnitor (e : Expr) (f : Mor₁) : StructuralAtom
  | id (e : Expr) (f : Mor₁) : StructuralAtom
  | coherenceHom (α : CoherenceHom) : StructuralAtom
  deriving Inhabited

inductive Mor₂Iso : Type where
  | structuralAtom (α : StructuralAtom) : Mor₂Iso
  | comp (e : Expr) (f g h : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
  | whiskerLeft (e : Expr) (f g h : Mor₁) (η : Mor₂Iso) : Mor₂Iso
  | whiskerRight (e : Expr) (f g : Mor₁) (η : Mor₂Iso) (h : Mor₁) : Mor₂Iso
  | horizontalComp (e : Expr) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
  | inv (e : Expr) (f g : Mor₁) (η : Mor₂Iso) : Mor₂Iso
  | coherenceComp (e : Expr) (f g h i : Mor₁) (α : CoherenceHom) (η θ : Mor₂Iso) : Mor₂Iso
  | of (η : AtomIso) : Mor₂Iso
  deriving Inhabited

class MonadCoherehnceHom (m : Type → Type) where
  unfoldM (α : CoherenceHom) : m Mor₂Iso

namespace CoherenceHom

export MonadCoherehnceHom (unfoldM)

end CoherenceHom

def StructuralAtom.e : StructuralAtom → Expr
  | .associator e .. => e
  | .leftUnitor e .. => e
  | .rightUnitor e .. => e
  | .id e .. => e
  | .coherenceHom α => α.e

open MonadMor₁

variable {m : Type → Type} [Monad m]

def StructuralAtom.srcM [MonadMor₁ m] : StructuralAtom → m Mor₁
  | .associator _ f g h => do comp₁M (← comp₁M f g) h
  | .leftUnitor _ f => do comp₁M (← id₁M f.src) f
  | .rightUnitor _ f => do comp₁M f (← id₁M f.tgt)
  | .id _ f => return f
  | .coherenceHom α => return α.src

def StructuralAtom.tgtM [MonadMor₁ m] : StructuralAtom → m Mor₁
  | .associator _ f g h => do comp₁M f (← comp₁M g h)
  | .leftUnitor _ f => return f
  | .rightUnitor _ f => return f
  | .id _ f => return f
  | .coherenceHom α => return α.tgt

def Mor₂Iso.e : Mor₂Iso → Expr
  | .structuralAtom α => α.e
  | .comp e .. => e
  | .whiskerLeft e .. => e
  | .whiskerRight e .. => e
  | .horizontalComp e .. => e
  | .inv e .. => e
  | .coherenceComp e .. => e
  | .of η => η.e

def Mor₂Iso.srcM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂Iso → m Mor₁
  | .structuralAtom α => α.srcM
  | .comp _ f .. => return f
  | .whiskerLeft _ f g .. => do comp₁M f g
  | .whiskerRight _ f _ _ h => do comp₁M f h
  | .horizontalComp _ f₁ _ f₂ .. => do comp₁M f₁ f₂
  | .inv _ _ g _ => return g
  | .coherenceComp _ f .. => return f
  | .of η => return η.src

def Mor₂Iso.tgtM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂Iso → m Mor₁
  | .structuralAtom α => α.tgtM
  | .comp _ _ _ h .. => return h
  | .whiskerLeft _ f _ h _ => do comp₁M f h
  | .whiskerRight _ _ g _ h => do comp₁M g h
  | .horizontalComp _ _ g₁ _ g₂ _ _ => do comp₁M g₁ g₂
  | .inv _ f _ _ => return f
  | .coherenceComp _ _ _ _ i .. => return i
  | .of η => return η.tgt

/-- A monad equipped with the ability to manipulate structural isomorphism. -/
class MonadStructuralAtom (m : Type → Type) where
  associatorM (f g h : Mor₁) : m StructuralAtom
  leftUnitorM (f : Mor₁) : m StructuralAtom
  rightUnitorM (f : Mor₁) : m StructuralAtom
  id₂M (f : Mor₁) : m StructuralAtom
  coherenceHomM (f g : Mor₁) (inst : Expr) : m CoherenceHom

namespace StructuralAtom

export MonadStructuralAtom (associatorM leftUnitorM rightUnitorM id₂M)

end StructuralAtom

/-- Type of normalized 1-morphisms, represented by (reversed) lists. -/
inductive NormalizedHom : Type
  /-- The identity 1-morphism `𝟙 a`. -/
  | nil (e : Mor₁) (a : Obj) : NormalizedHom
  /-- The `cons` composes an atomic 1-morphism at the end of a normalized 1-morphism. -/
  | cons (e : Mor₁) : NormalizedHom → Atom₁ → NormalizedHom
  deriving Inhabited

/-- The underlying expression of a normalized 1-morphism. -/
def NormalizedHom.e : NormalizedHom → Mor₁
  | NormalizedHom.nil e _ => e
  | NormalizedHom.cons e _ _  => e

def NormalizedHom.src : NormalizedHom → Obj
  | NormalizedHom.nil _ a => a
  | NormalizedHom.cons _ p _ => p.src

def NormalizedHom.tgt : NormalizedHom → Obj
  | NormalizedHom.nil _ a => a
  | NormalizedHom.cons _ _  f => f.tgt

/-- Construct the `NormalizedHom.nil` term in `m`. -/
def normalizedHom.nilM [MonadMor₁ m] (a : Obj) : m NormalizedHom := do
  return NormalizedHom.nil (← id₁M a) a

/-- Construct a `NormalizedHom.cons` term in `m`. -/
def NormalizedHom.consM [MonadMor₁ m] (p : NormalizedHom) (f : Atom₁) :
    m NormalizedHom := do
  return NormalizedHom.cons (← comp₁M p.e (.of f)) p f

end PureCoherence

section Normalize

variable {m : Type → Type} [Monad m] [MonadMor₁ m]

open MonadMor₁

/-- Expressions for atomic non-structural 2-morphisms. -/
structure Atom where
  /-- Extract a Lean expression from an `Atom` expression. -/
  e : Expr
  /-- The domain of a 2-morphism. -/
  src : Mor₁
  /-- The codomain of a 2-morphism. -/
  tgt : Mor₁
  deriving Inhabited

structure IsoLift where
  iso : Mor₂Iso
  eq : Expr

inductive Mor₂ : Type where
  | isoHom (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
  | isoInv (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
  | id (e : Expr) (isoLift : IsoLift) (f : Mor₁) : Mor₂
  | comp (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η θ : Mor₂) : Mor₂
  | whiskerLeft (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η : Mor₂) : Mor₂
  | whiskerRight (e : Expr) (isoLift? : Option IsoLift) (f g : Mor₁) (η : Mor₂) (h : Mor₁) : Mor₂
  | horizontalComp (e : Expr) (isoLift? : Option IsoLift) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂) : Mor₂
  | coherenceComp (e : Expr) (isoLift? : Option IsoLift) (f g h i : Mor₁) (α : CoherenceHom) (η θ : Mor₂) : Mor₂
  | of (η : Atom) : Mor₂
  deriving Inhabited

class MkMor₂ (m : Type → Type) where
  ofExpr (e : Expr) : m Mor₂

def Mor₂.e : Mor₂ → Expr
  | .isoHom e .. => e
  | .isoInv e .. => e
  | .id e .. => e
  | .comp e .. => e
  | .whiskerLeft e .. => e
  | .whiskerRight e .. => e
  | .horizontalComp e .. => e
  | .coherenceComp e .. => e
  | .of η => η.e

def Mor₂.isoLift? : Mor₂ → Option IsoLift
  | .isoHom _ isoLift .. => some isoLift
  | .isoInv _ isoLift .. => some isoLift
  | .id _ isoLift .. => some isoLift
  | .comp _ isoLift? .. => isoLift?
  | .whiskerLeft _ isoLift? .. => isoLift?
  | .whiskerRight _ isoLift? .. => isoLift?
  | .horizontalComp _ isoLift? .. => isoLift?
  | .coherenceComp _ isoLift? .. => isoLift?
  | .of _ => none

def Mor₂.srcM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂ → m Mor₁
  | .isoHom _ _ iso => iso.srcM
  | .isoInv _ _ iso => iso.tgtM
  | .id _ _ f => return f
  | .comp _ _ f .. => return f
  | .whiskerLeft _ _ f g .. => do comp₁M f g
  | .whiskerRight _ _ f _ _ h => do comp₁M f h
  | .horizontalComp _ _ f₁ _ f₂ .. => do comp₁M f₁ f₂
  | .coherenceComp _ _ f .. => return f
  | .of η => return η.src

def Mor₂.tgtM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂ → m Mor₁
  | .isoHom _ _ iso => iso.tgtM
  | .isoInv _ _ iso => iso.srcM
  | .id _ _ f => return f
  | .comp _ _ _ _ h .. => return h
  | .whiskerLeft _ _ f _ h _ => do comp₁M f h
  | .whiskerRight _ _ _ g _ h => do comp₁M g h
  | .horizontalComp _ _ _ g₁ _ g₂ _ _ => do comp₁M g₁ g₂
  | .coherenceComp _ _ _ _ _ i .. => return i
  | .of η => return η.tgt

class MonadMor₂Iso (m : Type → Type) where
  comp₂M (f g : Mor₂Iso) : m Mor₂Iso
  whiskerLeftM (f : Mor₁) (η : Mor₂Iso) : m Mor₂Iso
  whiskerRightM (η : Mor₂Iso) (h : Mor₁) : m Mor₂Iso
  horizontalCompM (η θ : Mor₂Iso) : m Mor₂Iso
  symmM (η : Mor₂Iso) : m Mor₂Iso
  coherenceCompM (α : CoherenceHom) (η θ : Mor₂Iso) : m Mor₂Iso

namespace Mor₂Iso

export MonadMor₂Iso
  (comp₂M whiskerLeftM whiskerRightM horizontalCompM symmM coherenceCompM)

end Mor₂Iso

class MonadMor₂ (m : Type → Type) where
  homM (iso : Mor₂Iso) : m Mor₂
  atomHomM (η : AtomIso) : m Atom
  invM (iso : Mor₂Iso) : m Mor₂
  atomInvM (η : AtomIso) : m Atom
  id₂M (f : Mor₁) : m Mor₂
  comp₂M (η θ : Mor₂) : m Mor₂
  whiskerLeftM (f : Mor₁) (η : Mor₂) : m Mor₂
  whiskerRightM (η : Mor₂) (h : Mor₁) : m Mor₂
  horizontalCompM (η θ : Mor₂) : m Mor₂
  coherenceCompM (α : CoherenceHom) (η θ : Mor₂) : m Mor₂

namespace Mor₂

export MonadMor₂
  (homM atomHomM invM atomInvM id₂M comp₂M whiskerLeftM whiskerRightM horizontalCompM coherenceCompM)

end Mor₂

namespace Mor₂Iso

variable {m : Type → Type} [Monad m] [MonadStructuralAtom m]

def associatorM' (f g h : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadStructuralAtom.associatorM f g h

def leftUnitorM' (f : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadStructuralAtom.leftUnitorM f

def rightUnitorM' (f : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadStructuralAtom.rightUnitorM f

def id₂M' (f : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadStructuralAtom.id₂M f

def coherenceHomM' (f g : Mor₁) (inst : Expr) : m Mor₂Iso := do
  return .structuralAtom <| .coherenceHom <| ← MonadStructuralAtom.coherenceHomM f g inst

end Mor₂Iso

/-- Expressions of the form `η ▷ f₁ ▷ ... ▷ fₙ`. -/
inductive WhiskerRight : Type
  /-- Construct the expression for an atomic 2-morphism. -/
  | of (η : Atom) : WhiskerRight
  /-- Construct the expression for `η ▷ f`. -/
  | whisker (e : Mor₂) (η : WhiskerRight) (f : Atom₁) : WhiskerRight
  deriving Inhabited

def WhiskerRight.e : WhiskerRight → Mor₂
  | .of η => .of η
  | .whisker e .. => e

/-- Expressions of the form `η₁ ⊗ ... ⊗ ηₙ`. -/
inductive HorizontalComp : Type
  | of (η : WhiskerRight) : HorizontalComp
  | cons (e : Mor₂) (η : WhiskerRight) (ηs : HorizontalComp) :
    HorizontalComp
  deriving Inhabited

def HorizontalComp.e : HorizontalComp → Mor₂
  | .of η => η.e
  | .cons e .. => e

/-- Expressions of the form `f₁ ◁ ... ◁ fₙ ◁ η`. -/
inductive WhiskerLeft : Type
  /-- Construct the expression for a right-whiskered 2-morphism. -/
  | of (η : HorizontalComp) : WhiskerLeft
  /-- Construct the expression for `f ◁ η`. -/
  | whisker (e : Mor₂) (f : Atom₁) (η : WhiskerLeft) : WhiskerLeft
  deriving Inhabited

def WhiskerLeft.e : WhiskerLeft → Mor₂
  | .of η => η.e
  | .whisker e .. => e

abbrev Structural := Mor₂Iso

def Mor₂Iso.isStructural (α : Mor₂Iso) : Bool :=
  match α with
  | .structuralAtom _ => true
  | .comp _ _ _ _ η θ => η.isStructural && θ.isStructural
  | .whiskerLeft _ _ _ _ η => η.isStructural
  | .whiskerRight _ _ _ η _ => η.isStructural
  | .horizontalComp _ _ _ _ _ η θ => η.isStructural && θ.isStructural
  | .inv _ _ _ η => η.isStructural
  | .coherenceComp _ _ _ _ _ _ η θ => η.isStructural && θ.isStructural
  | .of _ => false

/-- Normalized expressions for 2-morphisms. -/
inductive NormalExpr : Type
  /-- Construct the expression for a structural 2-morphism. -/
  | nil (e : Mor₂) (α : Structural) : NormalExpr
  /-- Construct the normalized expression of a 2-morphism `α ≫ η ≫ ηs` recursively. -/
  | cons (e : Mor₂) (α : Structural) (η : WhiskerLeft) (ηs : NormalExpr) : NormalExpr
  deriving Inhabited

def NormalExpr.e : NormalExpr → Mor₂
  | .nil e .. => e
  | .cons e .. => e

class MonadWhiskerRight (m : Type → Type) where
  whiskerRightM (η : WhiskerRight) (f : Atom₁) : m WhiskerRight

class MonadHorizontalComp (m : Type → Type) extends MonadWhiskerRight m where
  hConsM (η : WhiskerRight) (ηs : HorizontalComp) : m HorizontalComp

class MonadWhiskerLeft (m : Type → Type) extends MonadHorizontalComp m where
  whiskerLeftM (f : Atom₁) (η : WhiskerLeft) : m WhiskerLeft

class MonadNormalExpr (m : Type → Type) extends MonadWhiskerLeft m where
  nilM (α : Structural) : m NormalExpr
  consM (headStructural : Structural) (η : WhiskerLeft) (ηs : NormalExpr) : m NormalExpr

/-- The domain of a 2-morphism. -/
def WhiskerRight.srcM : WhiskerRight → m Mor₁
  | WhiskerRight.of η => return η.src
  | WhiskerRight.whisker _ η f => do comp₁M (← η.srcM) (.of f)

/-- The codomain of a 2-morphism. -/
def WhiskerRight.tgtM : WhiskerRight → m Mor₁
  | WhiskerRight.of η => return η.tgt
  | WhiskerRight.whisker _ η f => do comp₁M (← η.tgtM) (.of f)

/-- The domain of a 2-morphism. -/
def HorizontalComp.srcM : HorizontalComp → m Mor₁
  | HorizontalComp.of η => η.srcM
  | HorizontalComp.cons _ η ηs => do comp₁M (← η.srcM) (← ηs.srcM)

/-- The codomain of a 2-morphism. -/
def HorizontalComp.tgtM : HorizontalComp → m Mor₁
  | HorizontalComp.of η => η.tgtM
  | HorizontalComp.cons _ η ηs => do comp₁M (← η.tgtM) (← ηs.tgtM)

/-- The domain of a 2-morphism. -/
def WhiskerLeft.srcM : WhiskerLeft → m Mor₁
  | WhiskerLeft.of η => η.srcM
  | WhiskerLeft.whisker _ f η => do comp₁M (.of f) (← η.srcM)

/-- The codomain of a 2-morphism. -/
def WhiskerLeft.tgtM : WhiskerLeft → m Mor₁
  | WhiskerLeft.of η => η.tgtM
  | WhiskerLeft.whisker _ f η => do comp₁M (.of f) (← η.tgtM)

/-- The domain of a 2-morphism. -/
def NormalExpr.srcM : NormalExpr → m Mor₁
  | NormalExpr.nil _ η => η.srcM
  | NormalExpr.cons _ α _ _ => α.srcM

/-- The codomain of a 2-morphism. -/
def NormalExpr.tgtM : NormalExpr → m Mor₁
  | NormalExpr.nil _ η => η.tgtM
  | NormalExpr.cons _ _ _ ηs => ηs.tgtM

section

variable [MonadStructuralAtom m] [MonadMor₂Iso m] [MonadNormalExpr m]

/-- The identity 2-morphism as a term of `normalExpr`. -/
def NormalExpr.idM (f : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| .structuralAtom <| ← MonadStructuralAtom.id₂M f

/-- The associator as a term of `normalExpr`. -/
def NormalExpr.associatorM (f g h : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| .structuralAtom <| ← MonadStructuralAtom.associatorM f g h

/-- The inverse of the associator as a term of `normalExpr`. -/
def NormalExpr.associatorInvM (f g h : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| ← MonadMor₂Iso.symmM <| .structuralAtom <| ← MonadStructuralAtom.associatorM f g h

/-- The left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitorM (f : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| .structuralAtom <| ← MonadStructuralAtom.leftUnitorM f

/-- The inverse of the left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitorInvM (f : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| ← MonadMor₂Iso.symmM <| .structuralAtom <| ← MonadStructuralAtom.leftUnitorM f

/-- The right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitorM (f : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| .structuralAtom <| ← MonadStructuralAtom.rightUnitorM f

/-- The inverse of the right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitorInvM (f : Mor₁) : m NormalExpr := do
  MonadNormalExpr.nilM <| ← MonadMor₂Iso.symmM <| .structuralAtom <| ← MonadStructuralAtom.rightUnitorM f

/-- Construct a `NormalExpr` expression from a `WhiskerLeft` expression. -/
def NormalExpr.ofM [MonadNormalExpr m] (η : WhiskerLeft) : m NormalExpr := do
  MonadNormalExpr.consM ((.structuralAtom <| ← MonadStructuralAtom.id₂M (← η.srcM))) η
    (← MonadNormalExpr.nilM ((.structuralAtom <| ← MonadStructuralAtom.id₂M (← η.tgtM))))

/-- Construct a `NormalExpr` expression from a Lean expression for an atomic 2-morphism. -/
def NormalExpr.ofAtomM [MonadNormalExpr m] (η : Atom) : m NormalExpr :=
  NormalExpr.ofM <| .of <| .of <| .of η

end

/-- Convert a `NormalExpr` expression into a list of `WhiskerLeft` expressions. -/
def NormalExpr.toList : NormalExpr → List WhiskerLeft
  | NormalExpr.nil _ _ => []
  | NormalExpr.cons _ _ η ηs => η :: NormalExpr.toList ηs

end Normalize
