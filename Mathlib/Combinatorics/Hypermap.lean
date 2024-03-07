import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Perm
import Mathlib.GroupTheory.Perm.Cycle.Basic

open Function
open Equiv

universe u

instance {α : Type u} (f : Perm α) [Fintype α] [DecidableEq α]
: Fintype (Quotient (Perm.SameCycle.setoid f)) :=
  @Quotient.fintype _ _ _ (show DecidableRel (Perm.SameCycle f) by infer_instance)

structure Hypermap (D : Type u) where
  σ : Perm D
  τ : Perm D

namespace Hypermap
variable {D D' : Type u} [Fintype D] [Fintype D']

@[simp] def φ (m : Hypermap D) : Perm D := Equiv.trans m.σ.symm m.τ.symm

@[reducible] def vertexSetoid (m : Hypermap D) := Perm.SameCycle.setoid m.σ
@[reducible] def edgeSetoid (m : Hypermap D) := Perm.SameCycle.setoid m.τ
@[reducible] def faceSetoid (m : Hypermap D) := Perm.SameCycle.setoid m.φ

@[reducible] def Vertices (m : Hypermap D) := Quotient (vertexSetoid m)
@[reducible] def Edges (m : Hypermap D) := Quotient (edgeSetoid m)
@[reducible] def Faces (m : Hypermap D) := Quotient (faceSetoid m)

@[reducible] def dartVertex (m : Hypermap D) (d : D) : m.Vertices := Quotient.mk (vertexSetoid m) d

def Vertices.deg {m : Hypermap D} [Fintype D] [DecidableEq D] (v : m.Vertices) : ℕ :=
  v.lift (fun v => Finset.card { d | Perm.SameCycle m.σ v d }.toFinset) <| by
    intro a b h
    -- The `congr` tactic fails here :(
    apply congr_arg
    apply Set.toFinset_congr
    ext
    exact ⟨h.symm.trans, h.trans⟩

@[reducible] def EdgeInvolutive (m : Hypermap D) := Involutive m.τ

def eulerCharacteristic (m : Hypermap D) [Fintype D] [DecidableEq D] : ℤ :=
  ↑(Fintype.card m.Vertices) - ↑(Fintype.card m.Edges) + ↑(Fintype.card m.Faces)

inductive Path {m : Hypermap D} : m.Vertices → m.Vertices → Type u
  | refl {v : m.Vertices} : Path v v
  | edge (d : D) : Path (m.dartVertex d) (m.dartVertex (m.τ d))
  | join {u v w : m.Vertices} : Path u v → Path v w → Path u w

def Path.symm {m : Hypermap D} (τ_inv : EdgeInvolutive m) {v w : m.Vertices} : Path v w → Path w v
  | .refl => .refl
  | .join p₁ p₂ => .join (p₂.symm ‹_›) (p₁.symm ‹_›)
  | .edge d => by
    have h : m.dartVertex d = m.dartVertex (m.τ (m.τ d))
    · rw [τ_inv d]
    rw [h]
    exact .edge (m.τ d)

def Path.length {m : Hypermap D} {v w : m.Vertices} : Path v w → ℕ
  | .refl => 0
  | .edge _ => 1
  | .join p₁ p₂ => p₁.length + p₂.length

def glink {m : Hypermap D} (x y : D) : Prop :=
  m.σ x = y ∨ m.τ x = y ∨ m.φ x = y

def Connected {m : Hypermap D} (v w : m.Vertices) := Nonempty (Path v w)

def Connected.equivalence {m : Hypermap D} (τ_inv : EdgeInvolutive m) : Equivalence (@Connected _ m) where
  refl _ := ⟨Path.refl⟩
  symm := Nonempty.map (Path.symm τ_inv)
  trans := Nonempty.map2 Path.join

def Connected.setoid {m : Hypermap D} (τ_inv : EdgeInvolutive m) : Setoid m.Vertices where
  iseqv := Connected.equivalence τ_inv

instance {m : Hypermap D} (τ_inv : EdgeInvolutive m) [DecidableEq D]
: Fintype (Quotient (@Connected.setoid D m τ_inv)) :=
  @Quotient.fintype _ _ _ (show DecidableRel (@Connected D m) by infer_instance)

def Components (m : Hypermap D) (τ_inv : EdgeInvolutive m) := Quotient (Connected.setoid τ_inv)

def eulerLeft (m : Hypermap D) (τ_inv : EdgeInvolutive m) := Fintype.card (m.Components _) + Fintype.card D
