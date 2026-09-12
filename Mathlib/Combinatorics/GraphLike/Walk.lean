/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Thomas Waring
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

public section

namespace HyperGraphLike

variable {V E Gr : Type*} [HyperGraphLike V E Gr]

inductive GLWalk (G : Gr) : V → V → Type _ where
  | nil {x : V} (h : x ∈ verts G) : GLWalk G x x
  | cons {x y z : V} {e : E} (h : IsLink G e x y) (p : GLWalk G y z) : GLWalk G x z

end HyperGraphLike

open HyperGraphLike SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def SimpleGraph.Walk.toGLWalk {x y : V} (p : G.Walk x y) : GLWalk G x y :=
  match p with
  | nil => GLWalk.nil trivial
  | cons h p => GLWalk.cons ⟨h, rfl⟩ (p.toGLWalk)

def HyperGraphLike.GLWalk.toSimpleGraphWalk {x y : V} (p : GLWalk G x y) : G.Walk x y :=
  match p with
  | nil _ => Walk.nil
  | cons h p => Walk.cons h.1 p.toSimpleGraphWalk

def walkEquivGLWalk {x y : V} : G.Walk x y ≃ GLWalk G x y where
  toFun := SimpleGraph.Walk.toGLWalk
  invFun := HyperGraphLike.GLWalk.toSimpleGraphWalk
  left_inv p := by
    induction p <;> simp_all [Walk.toGLWalk, GLWalk.toSimpleGraphWalk]
  right_inv p := by
    induction p with
    | nil => simp [Walk.toGLWalk, GLWalk.toSimpleGraphWalk]
    | cons h _ => simp_all [Walk.toGLWalk, GLWalk.toSimpleGraphWalk, h.2]
