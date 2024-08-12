/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Lean

open Lean Meta

namespace Mathlib.Tactic

namespace BicategoryLike

class Context (ρ  : Type) where
  mkContext : Expr → MetaM ρ

def mkContext? {ρ : Type} (e : Expr) [Context ρ] : MetaM (Option ρ) := do
  try return some (← Context.mkContext e) catch _ => return none

structure Obj where
  e : Option Expr
  deriving Inhabited

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

section PureCoherence

-- inductive StructuralIso : Type
--   /-- The expression for the associator `α_ f g h`. -/
--   | associator (e : Expr) (f g h : Mor₁) : StructuralIso
--   /-- The expression for the left unitor `λ_ f`. -/
--   | leftUnitor (e : Expr) (f : Mor₁) : StructuralIso
--   /-- The expression for the right unitor `ρ_ f`. -/
--   | rightUnitor (e : Expr) (f : Mor₁) : StructuralIso
--   | id (e : Expr) (f : Mor₁) : StructuralIso
--   | comp (e : Expr) (f g h : Mor₁) (η θ : StructuralIso) : StructuralIso
--   | whiskerLeft (e : Expr) (f g h : Mor₁) (η : StructuralIso) : StructuralIso
--   | whiskerRight (e : Expr) (f g : Mor₁) (η : StructuralIso) (h : Mor₁) : StructuralIso
--   | horizontalComp (e : Expr) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : StructuralIso) : StructuralIso
--   | inv (e : Expr) (f g : Mor₁) (η : StructuralIso) : StructuralIso
--   deriving Inhabited

inductive StructuralIsoAtom : Type
  /-- The expression for the associator `α_ f g h`. -/
  | associator (e : Expr) (f g h : Mor₁) : StructuralIsoAtom
  /-- The expression for the left unitor `λ_ f`. -/
  | leftUnitor (e : Expr) (f : Mor₁) : StructuralIsoAtom
  /-- The expression for the right unitor `ρ_ f`. -/
  | rightUnitor (e : Expr) (f : Mor₁) : StructuralIsoAtom

def StructuralIsoAtom.e : StructuralIsoAtom → Expr
  | .associator e .. => e
  | .leftUnitor e .. => e
  | .rightUnitor e .. => e

inductive StructuralIso : Type
  | atom (α : StructuralIsoAtom) : StructuralIso
  /-- The expression for the associator `α_ f g h`. -/
  | associator (e : Expr) (f g h : Mor₁) : StructuralIso
  /-- The expression for the left unitor `λ_ f`. -/
  | leftUnitor (e : Expr) (f : Mor₁) : StructuralIso
  /-- The expression for the right unitor `ρ_ f`. -/
  | rightUnitor (e : Expr) (f : Mor₁) : StructuralIso
  | id (e : Expr) (f : Mor₁) : StructuralIso
  | comp (e : Expr) (f g h : Mor₁) (η θ : StructuralIso) : StructuralIso
  | whiskerLeft (e : Expr) (f g h : Mor₁) (η : StructuralIso) : StructuralIso
  | whiskerRight (e : Expr) (f g : Mor₁) (η : StructuralIso) (h : Mor₁) : StructuralIso
  | horizontalComp (e : Expr) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : StructuralIso) : StructuralIso
  | inv (e : Expr) (f g : Mor₁) (η : StructuralIso) : StructuralIso
  deriving Inhabited

class MkStructuralIso (m : Type → Type) where
  ofExpr (e : Expr) : m (StructuralIso × Expr)

def StructuralIso.e : StructuralIso → Expr
  | .atom α => α.e
  | .associator e .. => e
  | .leftUnitor e .. => e
  | .rightUnitor e .. => e
  | .id e .. => e
  | .comp e .. => e
  | .whiskerLeft e .. => e
  | .whiskerRight e ..  => e
  | .horizontalComp e .. => e
  | .inv e .. => e

open MonadMor₁

def StructuralIsoAtom.srcM {m : Type → Type} [Monad m] [MonadMor₁ m] : StructuralIsoAtom → m Mor₁
  | .associator _ f g h => do comp₁M (← comp₁M f g) h
  | .leftUnitor _ f => do comp₁M (← id₁M f.src) f
  | .rightUnitor _ f => do comp₁M f (← id₁M f.tgt)

def StructuralIsoAtom.tgtM {m : Type → Type} [Monad m] [MonadMor₁ m] : StructuralIsoAtom → m Mor₁
  | .associator _ f g h => do comp₁M f (← comp₁M g h)
  | .leftUnitor _ f => return f
  | .rightUnitor _ f => return f

def StructuralIso.srcM {m : Type → Type} [Monad m] [MonadMor₁ m] : StructuralIso → m Mor₁
  | .atom α => do α.srcM
  | .associator _ f g h => do comp₁M (← comp₁M f g) h
  | .leftUnitor _ f => do comp₁M (← id₁M f.src) f
  | .rightUnitor _ f => do comp₁M f (← id₁M f.tgt)
  | .id _ f => return f
  | .comp _ f .. => return f
  | .whiskerLeft _ f g _ _ => do comp₁M f g
  | .whiskerRight _ f _ _ h => do comp₁M f h
  | .horizontalComp _ f₁ _ f₂ _ _ _ => do comp₁M f₁ f₂
  | .inv _ _ g _ => return g

def StructuralIso.tgtM {m : Type → Type} [Monad m] [MonadMor₁ m] : StructuralIso → m Mor₁
  | .atom α => do α.tgtM
  | .associator _ f g h => do comp₁M f (← comp₁M g h)
  | .leftUnitor _ f => return f
  | .rightUnitor _ f => return f
  | .id _ f => return f
  | .comp _ _ _ h _ _ => return h
  | .whiskerLeft _ f _ h _ => do comp₁M f h
  | .whiskerRight _ _ g _ h => do comp₁M g h
  | .horizontalComp _ _ g₁ _ g₂ _ _ => do comp₁M g₁ g₂
  | .inv _ f _ _ => return f

-- def StructuralIso.srcM : StructuralIso → Mor₁
--   | .associator _ src .. => src
--   | .leftUnitor _ src .. => src
--   | .rightUnitor _ src .. => src
--   | .id _ f => f
--   | .comp _ f .. => f
--   | .whiskerLeft _ src .. => src
--   | .whiskerRight _ src .. => src
--   | .horizontalComp _ src .. => src
--   | .inv _ _ g _ => g

-- def StructuralIso.tgt : StructuralIso → Mor₁
--   | .associator _ _ tgt .. => tgt
--   | .leftUnitor _ _ tgt .. => tgt
--   | .rightUnitor _ _ tgt .. => tgt
--   | .id _ f => f
--   | .comp _ _ _ h .. => h
--   | .whiskerLeft _ _ tgt .. => tgt
--   | .whiskerRight _ _ tgt .. => tgt
--   | .horizontalComp _ _ tgt .. => tgt
--   | .inv _ f _ _ => f

/-- A monad equipped with the ability to manipulate structural isomorphism. -/
class MonadStructuralIso (m : Type → Type) where
  associatorM (f g h : Mor₁) : m StructuralIso
  leftUnitorM (f : Mor₁) : m StructuralIso
  rightUnitorM (f : Mor₁) : m StructuralIso
  id₂M (f : Mor₁) : m StructuralIso
  comp₂M (η θ : StructuralIso) : m StructuralIso
  whiskerLeftM (f : Mor₁) (η : StructuralIso) : m StructuralIso
  whiskerRightM (η : StructuralIso) (f : Mor₁) : m StructuralIso
  horizontalCompM (η θ : StructuralIso) : m StructuralIso
  invM (η : StructuralIso) : m StructuralIso

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

open MonadMor₁

variable {m : Type → Type} [Monad m]

/-- Construct the `NormalizedHom.nil` term in `m`. -/
def normalizedHom.nilM [MonadMor₁ m] (a : Obj) : m NormalizedHom := do
  return NormalizedHom.nil (← id₁M a) a

/-- Construct a `NormalizedHom.cons` term in `m`. -/
def NormalizedHom.consM [MonadMor₁ m] (p : NormalizedHom) (f : Atom₁) :
    m NormalizedHom := do
  return NormalizedHom.cons (← comp₁M p.e (.of f)) p f

end PureCoherence

section Normalize

/-- Expressions for atomic structural 2-morphisms. -/
inductive StructuralAtom : Type
  | id (e : Expr) (f : Mor₁) : StructuralAtom
  /-- The expression for the associator `(α_ f g h).hom`. -/
  | associator (e : Expr) (f g h : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the associator `(α_ f g h).inv`. -/
  | associatorInv (e : Expr) (f g h : Mor₁) : StructuralAtom
  /-- The expression for the left unitor `(λ_ f).hom`. -/
  | leftUnitor (e : Expr) (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the left unitor `(λ_ f).inv`. -/
  | leftUnitorInv (e : Expr) (f : Mor₁) : StructuralAtom
  /-- The expression for the right unitor `(ρ_ f).hom`. -/
  | rightUnitor (e : Expr) (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the right unitor `(ρ_ f).inv`. -/
  | rightUnitorInv (e : Expr) (f : Mor₁) : StructuralAtom
  /-- Expressions for `α` in the monoidal composition `η ⊗≫ θ := η ≫ α ≫ θ`. -/
  | coherence (e : Expr) (src tgt : Mor₁) (inst : Expr) : StructuralAtom
  deriving Inhabited

class MkStructuralAtom (m : Type → Type) where
  ofExpr (e : Expr) : m StructuralAtom

class MonadStructuralAtom (m : Type → Type) where
  idM (f : Mor₁) : m StructuralAtom
  associatorM (f g h : Mor₁) : m StructuralAtom
  associatorInvM (f g h : Mor₁) : m StructuralAtom
  leftUnitorM (f : Mor₁) : m StructuralAtom
  leftUnitorInvM (f : Mor₁) : m StructuralAtom
  rightUnitorM (f : Mor₁) : m StructuralAtom
  rightUnitorInvM (f : Mor₁) : m StructuralAtom
  coherenceM (src tgt : Mor₁) (inst : Expr) : m StructuralAtom

def StructuralAtom.e : StructuralAtom → Expr
  | .id e .. => e
  | .associator e .. => e
  | .associatorInv e .. => e
  | .leftUnitor e .. => e
  | .leftUnitorInv e .. => e
  | .rightUnitor e .. => e
  | .rightUnitorInv e .. => e
  | .coherence e .. => e

variable {m : Type → Type} [Monad m] [MonadMor₁ m]

open MonadMor₁

/-- The domain of a 2-morphism. -/
def StructuralAtom.srcM : StructuralAtom → m Mor₁
  | .id _ f => return f
  | .associator _ f g h => do comp₁M f (← comp₁M g h)
  | .associatorInv _ f g h => do comp₁M (← comp₁M f g) h
  | .leftUnitor _ f => do comp₁M (← id₁M f.src) f
  | .leftUnitorInv _ f => return f
  | .rightUnitor _ f => do comp₁M f (← id₁M f.src)
  | .rightUnitorInv _ f => return f
  | .coherence _ src _ _ => return src

/-- The codomain of a 2-morphism. -/
def StructuralAtom.tgtM : StructuralAtom → m Mor₁
  | .id _ f => return f
  | .associator _ f g h => do comp₁M f (← comp₁M g h)
  | .associatorInv _ f g h => do comp₁M (← comp₁M f g) h
  | .leftUnitor _ f => return f
  | .leftUnitorInv _ f => do comp₁M (← id₁M f.tgt) f
  | .rightUnitor _ f => return f
  | .rightUnitorInv _ f => do comp₁M f (← id₁M f.tgt)
  | .coherence _ _ tgt _ => return tgt

/-- Expressions for atomic non-structural 2-morphisms. -/
structure Atom where
  /-- Extract a Lean expression from an `Atom` expression. -/
  e : Expr
  /-- The domain of a 2-morphism. -/
  src : Mor₁
  /-- The codomain of a 2-morphism. -/
  tgt : Mor₁
  deriving Inhabited

/-- A monad equipped with the ability to construct `Atom` terms. -/
class MkAtom (m : Type → Type) where
  ofExpr (e : Expr) : m Atom

inductive Mor₂ : Type where
  | structuralAtom (α : StructuralIsoAtom) : Mor₂
  -- | id (e : Expr) (f : Mor₁) : Mor₂
  | comp (e : Expr) (η θ : Mor₂) : Mor₂
  | whiskerLeft (e : Expr) (f : Mor₁) (η : Mor₂) : Mor₂
  | whiskerRight (e : Expr) (η : Mor₂) (h : Mor₁) : Mor₂
  | horizontalComp (e : Expr) (η θ : Mor₂) : Mor₂
  | coherenceComp (e : Expr) (inst : Expr) (α : StructuralIso) (η θ : Mor₂) : Mor₂
  | of (η : Atom) : Mor₂
  -- | coherenceHom (e : Expr) (f g : Mor₁) (inst : Expr) : Mor₂
  deriving Inhabited

class MkMor₂ (m : Type → Type) where
  ofExpr (e : Expr) : m Mor₂

def Mor₂.e : Mor₂ → Expr
  | .structuralAtom α => α.e
  -- | .id e .. => e
  | .comp e .. => e
  | .whiskerLeft e .. => e
  | .whiskerRight e .. => e
  | .horizontalComp e .. => e
  | .coherenceComp e .. => e
  | .of η => η.e
  -- | .coherenceHom e .. => e

-- def Mor₂.srcM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂ → m Mor₁
--   | .structuralAtom α => return α.src
--   | .id _ f => return f
--   | .comp _ f _ => f.srcM
--   | .whiskerLeft _ f η => do (f.compM (← η.srcM))
--   | .whiskerRight _ η _ => η.src
--   | .horizontalComp _ η _ => η.src
--   | .coherenceComp _ _ η _ => η.src
--   | .coherenceHom _ f _ _ => f


class MonadMor₂ (m : Type → Type) where
  id₂M (f : Mor₁) : m Mor₂
  comp₂M (f g : Mor₂) : m Mor₂
  whiskerLeftM (f : Mor₁) (η : Mor₂) : m Mor₂
  whiskerRightM (η : Mor₂) (h : Mor₁) : m Mor₂
  horizontalCompM (η θ : Mor₂) : m Mor₂
  coherenceCompM (inst : Expr) (η θ : Mor₂) : m Mor₂
  -- coherenceHomM (f g : Mor₁) (e : Expr) : m Mor₂

/-- Expressions of the form `η ▷ f₁ ▷ ... ▷ fₙ`. -/
inductive WhiskerRight : Type
  /-- Construct the expression for an atomic 2-morphism. -/
  | of (η : Atom) : WhiskerRight
  /-- Construct the expression for `η ▷ f`. -/
  | whisker (e : Expr) (η : WhiskerRight) (f : Atom₁) : WhiskerRight
  deriving Inhabited

/-- Expressions of the form `η₁ ⊗ ... ⊗ ηₙ`. -/
inductive HorizontalComp : Type
  | of (η : WhiskerRight) : HorizontalComp
  | cons (e : Expr) (η : WhiskerRight) (ηs : HorizontalComp) :
    HorizontalComp
  deriving Inhabited

/-- Expressions of the form `f₁ ◁ ... ◁ fₙ ◁ η`. -/
inductive WhiskerLeft : Type
  /-- Construct the expression for a right-whiskered 2-morphism. -/
  | of (η : HorizontalComp) : WhiskerLeft
  /-- Construct the expression for `f ◁ η`. -/
  | whisker (e : Expr) (f : Atom₁) (η : WhiskerLeft) : WhiskerLeft
  deriving Inhabited

/-- Expressions for structural 2-morphisms. -/
inductive Structural : Type
  /-- Expressions for atomic structural 2-morphisms. -/
  | atom (η : StructuralAtom) : Structural
  -- /-- Expressions for the identity `𝟙 f`. -/
  -- | id (e : Expr) (f : Mor₁) : Structural
  /-- Expressions for the composition `η ≫ θ`. -/
  | comp (e : Expr) (α β : Structural) : Structural
  /-- Expressions for the left whiskering `f ◁ η`. -/
  | whiskerLeft (e : Expr) (f : Mor₁) (η : Structural) : Structural
  /-- Expressions for the right whiskering `η ▷ f`. -/
  | whiskerRight (e : Expr) (η : Structural) (f : Mor₁) : Structural
  /-- Expressions for the tensor `α ⊗ β`. -/
  | horizontalComp (e : Expr) (α β : Structural) : Structural
  deriving Inhabited

def Structural.e : Structural → Expr
  | .atom η => η.e
  -- | .id e _ => e
  | .comp e _ _ => e
  | .whiskerLeft e _ _ => e
  | .whiskerRight e _ _ => e
  | .horizontalComp e _ _ => e

class MonadStructural (m : Type → Type) extends MonadStructuralAtom m where
  -- idM (f : Mor₁) : m Structural
  compM (α β : Structural) : m Structural
  whiskerLeftM (f : Mor₁) (α : Structural) : m Structural
  whiskerRightM (α : Structural) (f : Mor₁) : m Structural
  horizontalCompM (α β : Structural) : m Structural

/-- Normalized expressions for 2-morphisms. -/
inductive NormalExpr : Type
  /-- Construct the expression for a structural 2-morphism. -/
  | nil (α : StructuralIso) : NormalExpr
  /-- Construct the normalized expression of 2-morphisms recursively. -/
  | cons (e : Expr) (headStructural : StructuralIso) (head : WhiskerLeft) (tail : NormalExpr) : NormalExpr
  deriving Inhabited


class MonadWhiskerRight (m : Type → Type) where
  whiskerRightM (η : WhiskerRight) (f : Atom₁) : m WhiskerRight

class MonadHorizontalComp (m : Type → Type) extends MonadWhiskerRight m where
  hConsM (η : WhiskerRight) (ηs : HorizontalComp) : m HorizontalComp

class MonadWhiskerLeft (m : Type → Type) extends MonadHorizontalComp m where
  whiskerLeftM (f : Atom₁) (η : WhiskerLeft) : m WhiskerLeft

class MonadNormalExpr (m : Type → Type) extends MonadWhiskerLeft m where
  consM (headStructural : StructuralIso) (η : WhiskerLeft) (ηs : NormalExpr) : m NormalExpr

variable {m : Type → Type} [Monad m] [MonadMor₁ m]

open MonadMor₁

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
def Structural.srcM : Structural → m Mor₁
  | .atom η => η.srcM
  -- | .id _ f => return f
  | .comp _ α _ => α.srcM
  | .whiskerLeft _ f η => do comp₁M f (← η.srcM)
  | .whiskerRight _ η f => do comp₁M (← η.srcM) f
  | .horizontalComp _ α β => do comp₁M (← α.srcM) (← β.srcM)

/-- The codomain of a 2-morphism. -/
def Structural.tgtM : Structural → m Mor₁
  | .atom η => η.tgtM
  -- | .id _ f => return f
  | .comp _ _ β => β.tgtM
  | .whiskerLeft _ f η => do comp₁M f (← η.tgtM)
  | .whiskerRight _ η f => do comp₁M (← η.tgtM) f
  | .horizontalComp _ α β => do comp₁M (← α.tgtM) (← β.tgtM)

/-- The domain of a 2-morphism. -/
def NormalExpr.srcM : NormalExpr → m Mor₁
  | NormalExpr.nil η => η.srcM
  | NormalExpr.cons _ α _ _ => α.srcM

/-- The codomain of a 2-morphism. -/
def NormalExpr.tgtM : NormalExpr → m Mor₁
  | NormalExpr.nil η => η.tgtM
  | NormalExpr.cons _ _ _ ηs => ηs.tgtM

variable [MonadStructuralAtom m]

variable [MonadStructuralIso m]

/-- The identity 2-morphism as a term of `normalExpr`. -/
def NormalExpr.idM (f : Mor₁) : m NormalExpr :=
  return .nil <| ← MonadStructuralIso.id₂M f

/-- The associator as a term of `normalExpr`. -/
def NormalExpr.associatorM (f g h : Mor₁) : m NormalExpr := do
  return .nil <| ← MonadStructuralIso.associatorM f g h

/-- The inverse of the associator as a term of `normalExpr`. -/
def NormalExpr.associatorInvM (f g h : Mor₁) : m NormalExpr :=
  return .nil <| ← MonadStructuralIso.invM <| ← MonadStructuralIso.associatorM f g h

/-- The left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitorM (f : Mor₁) : m NormalExpr :=
  return .nil <| ← MonadStructuralIso.leftUnitorM f

/-- The inverse of the left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitorInvM (f : Mor₁) : m NormalExpr :=
  return .nil <| ← MonadStructuralIso.invM <| ← MonadStructuralIso.leftUnitorM f

/-- The right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitorM (f : Mor₁) : m NormalExpr :=
  return .nil <| ← MonadStructuralIso.rightUnitorM f

/-- The inverse of the right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitorInvM (f : Mor₁) : m NormalExpr :=
  return .nil <| ← MonadStructuralIso.invM <| ← MonadStructuralIso.rightUnitorM f

/-- Construct a `NormalExpr` expression from a `WhiskerLeft` expression. -/
def NormalExpr.ofM [MonadNormalExpr m] (η : WhiskerLeft) : m NormalExpr := do
  MonadNormalExpr.consM ((← MonadStructuralIso.id₂M (← η.srcM))) η
    (.nil ((← MonadStructuralIso.id₂M (← η.tgtM))))

/-- Construct a `NormalExpr` expression from a Lean expression for an atomic 2-morphism. -/
def NormalExpr.ofAtomM [MonadNormalExpr m] (η : Atom) : m NormalExpr :=
  NormalExpr.ofM <| .of <| .of <| .of η

/-- Convert a `NormalExpr` expression into a list of `WhiskerLeft` expressions. -/
def NormalExpr.toList : NormalExpr → List WhiskerLeft
  | NormalExpr.nil _ => []
  | NormalExpr.cons _ _ η ηs => η :: NormalExpr.toList ηs

end Normalize
