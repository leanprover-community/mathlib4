/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Coherence.Datatypes

open Lean Meta

namespace Mathlib.Tactic

namespace BicategoryLike

structure Normalize.Result where
  /-- The normalized 1-morphism. -/
  normalizedHom : NormalizedHom
  /-- The 2-morphism from the original 1-morphism to the normalized 1-morphism. -/
  toNormalize : StructuralIso
  deriving Inhabited

open MonadStructuralIso

variable {m : Type → Type} [Monad m]

/-- Meta version of `CategoryTheory.FreeBicategory.normalizeIso`. -/
def normalize [MonadMor₁ m] [MonadStructuralIso m] (p : NormalizedHom) (f : Mor₁) :
    m Normalize.Result := do
  match f with
  | .id _ _ =>
    return ⟨p, ← rightUnitorM p.e⟩
  | .comp _ f g =>
    let ⟨pf, η_f⟩ ← normalize p f
    let η_f' ← whiskerRightM η_f g
    let ⟨pfg, η_g⟩ ← normalize pf g
    let η ← comp₂M η_f' η_g
    let alpha ← invM (← associatorM p.e f g)
    let η' ← comp₂M alpha η
    return ⟨pfg, η'⟩
  | .of f =>
    let pf ← NormalizedHom.consM p f
    let α ← id₂M pf.e
    return ⟨pf, α⟩

/-- Lemmas to prove the meta version of `CategoryTheory.FreeBicategory.normalize_naturality`. -/
class MonadNormalizeNaturality (m : Type → Type) where
  mkNaturalityAssociator (p pf pfg pfgh : NormalizedHom) (f g h : Mor₁)
    (η_f η_g η_h : StructuralIso) : m Expr
  mkNaturalityLeftUnitor (p pf : NormalizedHom) (f : Mor₁) (η_f : StructuralIso) : m Expr
  mkNaturalityRightUnitor (p pf : NormalizedHom) (f : Mor₁) (η_f : StructuralIso) : m Expr
  mkNaturalityId (p pf : NormalizedHom) (f : Mor₁) (η_f : StructuralIso) : m Expr
  mkNaturalityComp (p pf : NormalizedHom) (f g h : Mor₁) (η θ η_f η_g η_h : StructuralIso)
    (ih_η ih_θ : Expr) : m Expr
  mkNaturalityWhiskerLeft (p pf pfg : NormalizedHom) (f g h : Mor₁)
    (η η_f η_fg η_fh : StructuralIso) (ih_η : Expr) : m Expr
  mkNaturalityWhiskerRight (p pf pfh : NormalizedHom) (f g h : Mor₁) (η η_f η_g η_fh : StructuralIso)
    (ih_η : Expr) : m Expr
  mkNaturalityHorizontalComp (p pf₁ pf₁f₂ : NormalizedHom) (f₁ g₁ f₂ g₂ : Mor₁)
    (η θ η_f₁ η_g₁ η_f₂ η_g₂ : StructuralIso) (ih_η ih_θ : Expr) : m Expr
  mkNaturalityInv (p pf : NormalizedHom) (f g : Mor₁) (η η_f η_g : StructuralIso) (ih_η : Expr) : m Expr

open MonadNormalizeNaturality

/-- Meta version of `CategoryTheory.FreeBicategory.normalize_naturality`. -/
def naturality [MonadMor₁ m] [MonadStructuralIso m] [MonadNormalizeNaturality m]
    [MonadLift MetaM m] [MonadAlwaysExcept Exception m] [MonadRef m]
    (nm : Name) (p : NormalizedHom) (η : StructuralIso) : m Expr := do
  let result ← match η with
  | .atom η => match η with
    | .associator _  f g h => withTraceNode nm (fun _ => return m!"associator") do
      let ⟨pf, η_f⟩ ← normalize p f
      let ⟨pfg, η_g⟩ ← normalize pf g
      let ⟨pfgh, η_h⟩ ← normalize pfg h
      mkNaturalityAssociator p pf pfg pfgh f g h η_f η_g η_h
    | .leftUnitor _ f => withTraceNode nm (fun _ => return m!"leftUnitor") do
      let ⟨pf, η_f⟩ ← normalize p f
      mkNaturalityLeftUnitor p pf f η_f
    | .rightUnitor _ f => withTraceNode nm (fun _ => return m!"rightUnitor") do
      let ⟨pf, η_f⟩ ← normalize p f
      mkNaturalityRightUnitor p pf f η_f
  | .associator _  f g h => withTraceNode nm (fun _ => return m!"associator") do
    let ⟨pf, η_f⟩ ← normalize p f
    let ⟨pfg, η_g⟩ ← normalize pf g
    let ⟨pfgh, η_h⟩ ← normalize pfg h
    mkNaturalityAssociator p pf pfg pfgh f g h η_f η_g η_h
  | .leftUnitor _ f => withTraceNode nm (fun _ => return m!"leftUnitor") do
    let ⟨pf, η_f⟩ ← normalize p f
    mkNaturalityLeftUnitor p pf f η_f
  | .rightUnitor _ f => withTraceNode nm (fun _ => return m!"rightUnitor") do
    let ⟨pf, η_f⟩ ← normalize p f
    mkNaturalityRightUnitor p pf f η_f
  | .id _ f => withTraceNode nm (fun _ => return m!"id") do
    let ⟨pf, η_f⟩ ← normalize p f
    mkNaturalityId p pf f η_f
  | .comp _ f g h η θ => withTraceNode nm (fun _ => return m!"comp") do
    let ⟨pf, η_f⟩ ← normalize p f
    let ⟨_, η_g⟩ ← normalize p g
    let ⟨_, η_h⟩ ← normalize p h
    let ih_η ← naturality nm p η
    let ih_θ ← naturality nm p θ
    mkNaturalityComp p pf f g h η θ η_f η_g η_h ih_η ih_θ
  | .whiskerLeft _ f g h η => withTraceNode nm (fun _ => return m!"whiskerLeft") do
    let ⟨pf, η_f⟩ ← normalize p f
    let ⟨pfg, η_fg⟩ ← normalize pf g
    let ⟨_, η_fh⟩ ← normalize pf h
    let ih ← naturality nm pf η
    mkNaturalityWhiskerLeft p pf pfg f g h η η_f η_fg η_fh ih
  | .whiskerRight _ f g η h => withTraceNode nm (fun _ => return m!"whiskerRight") do
    let ⟨pf, η_f⟩ ← normalize p f
    let ⟨_, η_g⟩ ← normalize p g
    let ⟨pfh, η_fh⟩ ← normalize pf h
    let ih ← naturality nm p η
    mkNaturalityWhiskerRight p pf pfh f g h η η_f η_g η_fh ih
  | .horizontalComp _ f₁ g₁ f₂ g₂ η θ => withTraceNode nm (fun _ => return m!"hComp") do
    let ⟨pf₁, η_f₁⟩ ← normalize p f₁
    let ⟨_, η_g₁⟩ ← normalize p g₁
    let ⟨pf₁f₂, η_f₂⟩ ← normalize pf₁ f₂
    let ⟨_, η_g₂⟩ ← normalize pf₁ g₂
    let ih_η ← naturality nm p η
    let ih_θ ← naturality nm pf₁ θ
    mkNaturalityHorizontalComp p pf₁ pf₁f₂ f₁ g₁ f₂ g₂ η θ η_f₁ η_g₁ η_f₂ η_g₂ ih_η ih_θ
  | .inv _ f g η => withTraceNode nm (fun _ => return m!"inv") do
    let ⟨pf, η_f⟩ ← normalize p f
    let ⟨_, η_g⟩ ← normalize p g
    let ih_η ← naturality nm p η
    mkNaturalityInv p pf f g η η_f η_g ih_η
  withTraceNode nm (fun _ => return m!"{checkEmoji} {← inferType result}") do
    if ← isTracingEnabledFor nm then addTrace nm m!"proof: {result}"
  return result

def pureCoherence (nm : Name) (ρ : Type) [Context ρ]
    [MonadMor₁ (ReaderT ρ MetaM)]
    [MonadStructuralIso (ReaderT ρ MetaM)]
    [MkStructuralIso (ReaderT ρ MetaM)]
    [MonadNormalizeNaturality (ReaderT ρ MetaM)]
    (mkEqOfNormalizedEq : Array Expr → MetaM Expr)
    (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.withContext do
    withTraceNode nm (fun ex => match ex with
      | .ok _ => return m!"{checkEmoji} coherence equality: {← mvarId.getType}"
      | .error err => return m!"{crossEmoji} {err.toMessageData}") do
      let e ← instantiateMVars <| ← mvarId.getType
      let some (_, η, θ) := (← whnfR e).eq?
        | throwError "coherence requires an equality goal"
      let ctx : ρ ← Context.mkContext η
      ReaderT.run (r := ctx) do
        let (η', Hη) ← MkStructuralIso.ofExpr η
        let (θ', Hθ) ← MkStructuralIso.ofExpr θ
        let f ← η'.srcM
        let g ← η'.tgtM
        let a := f.src
        let nil ← normalizedHom.nilM a
        let ⟨_, η_f⟩ ← normalize nil f
        let ⟨_, η_g⟩ ← normalize nil g
        let Hη' ← withTraceNode nm (fun _ => do return m!"LHS") do
          naturality nm nil η'
        let Hθ' ← withTraceNode nm (fun _ => do return m!"RHS") do
          naturality nm nil θ'
        let H ← mkEqOfNormalizedEq #[η, θ, η'.e, θ'.e, η_f.e, η_g.e, Hη, Hθ, Hη', Hθ']
        mvarId.apply H

end Mathlib.Tactic.BicategoryLike
