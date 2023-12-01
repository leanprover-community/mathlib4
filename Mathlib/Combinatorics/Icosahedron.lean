/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.DeriveFintype
import Mathlib.Util.Time

/-! # The icosahedron, as a combinatorial object

-/

-- move this
instance Fintype.decidable_existsUnique_fintype {α : Type*} {p : α → Prop}
    [DecidableEq α] [DecidablePred p] [Fintype α] :
    Decidable (∃! a, p a) :=
  Fintype.decidableExistsFintype

-- move this
/-- `Fintype.equivOfBij` is the computable equiv of a bijection `f` of fintypes. This acts
as a computable alternative to `Equiv.ofBijective.`. -/
def Fintype.equivOfBij {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β)
    (f_bij : Function.Bijective f) : α ≃ β where
  toFun := f
  invFun := Fintype.bijInv f_bij
  left_inv := Fintype.leftInverse_bijInv f_bij
  right_inv := Fintype.rightInverse_bijInv f_bij

-- move this
instance {G : Type*} [Group G] (s t : Subgroup G) (g : G) [Decidable (g ∈ s)] [Decidable (g ∈ t)] :
    Decidable (g ∈ s ⊓ t) := by
  show Decidable (g ∈ s ∧ g ∈ t)
  infer_instance

namespace Icosahedron

/-- The 12 vertices of the icosahedron. -/
structure Vert :=
  (a : ZMod 3)
  (e₁ : ZMod 2)
  (eₚ : ZMod 2)
deriving Fintype, DecidableEq, Repr

/-- The 30 edges of the icosahedron. -/
inductive Edge : Type
  | a : ZMod 3 → ZMod 2 → Edge -- 3 . 2 = 6
  | b : ZMod 3 → ZMod 2 → Edge -- 3 . 2 = 6
  | c : ZMod 3 → ZMod 2 → Edge -- 3 . 2 = 6
  | d : ZMod 3 → ZMod 2 → Edge -- 3 . 2 = 6
  | e : ZMod 3 → ZMod 2 → Edge -- 3 . 2 = 6
deriving Fintype, DecidableEq, Repr

/-- The 20 faces of the icosahedron. -/
inductive Face : Type
  | w : ZMod 2 → Face -- 2
  | x : ZMod 3 → ZMod 2 → Face -- 3 . 2 = 6
  | y : ZMod 3 → ZMod 2 → Face -- 3 . 2 = 6
  | z : ZMod 3 → ZMod 2 → Face -- 3 . 2 = 6
deriving Fintype, DecidableEq, Repr

/-- The two vertices bounding each edge of the icosahedron. -/
def Edge.toVert : Edge → Finset Vert
  | Edge.a i u => {⟨i, 0, u⟩, ⟨i, 1, u⟩}
  | Edge.d i u => {⟨i, u, u⟩, ⟨i + 1, u, u⟩}
  | Edge.b i u => {⟨i, u, u⟩, ⟨i + 1, u, 1 + u⟩}
  | Edge.c i u => {⟨i, 1 + u, u⟩, ⟨i + 1, u, u⟩}
  | Edge.e i u => {⟨i, u, 1 + u⟩, ⟨i + 1, 1 + u, u⟩}

/-- The three edges bounding each face of the icosahedron. -/
def Face.toEdge : Face → Finset Edge
  | Face.w u => {Edge.d 0 u, Edge.d 1 u, Edge.d 2 u}
  | Face.x i u => {Edge.b i u, Edge.c (i + 2) u, Edge.e (i + 1) u}
  | Face.y i u => {Edge.d (i + 2) u, Edge.a (i + 2) u, Edge.c (i + 2) u}
  | Face.z i u => {Edge.a i u, Edge.b i u, Edge.e i (1 + u)}

/-- The edges emerging from a given vertex of the icosahedron. -/
def Vert.toEdge (v : Vert) : Finset Edge := Finset.filter (fun e : Edge ↦ v ∈ e.toVert) Finset.univ

-- the edges touching the vertex `⟨1, 0, 0⟩`
#eval Vert.toEdge ⟨1, 0, 0⟩

/- In fact, every vertex touches five edges. -/
#time -- .878 s
example {v : Vert} : v.toEdge.card = 5 := by revert v; decide

/-- The faces touching a given edge of the icosahedron. -/
def Edge.toFace (e : Edge) : Finset Face := Finset.filter (fun f : Face ↦ e ∈ f.toEdge) Finset.univ

#eval Edge.toFace (Edge.a 1 0)

/- In fact, every edge touches two faces. -/
#time  -- 1.854 s
example {e : Edge} : Finset.card (Finset.filter (fun f : Face ↦ e ∈ f.toEdge) Finset.univ) = 2 := by
  revert e
  decide

/- For each (vertex, face) pair, either they don't touch, or there are exactly two edges which bound
the face and which are bounded by the vertex. -/
#time -- 3.114 s
example {v : Vert} {f : Face} : Finset.card (v.toEdge ∩ f.toEdge) ∈ ({0, 2} : Finset ℕ) := by
  revert v f
  decide

section

def mkEdges (p : Equiv.Perm Vert)
    (h₁ : ∀ e : Edge, ∃! e' : Edge, e'.toVert = e.toVert.image p := by decide)
    (h₂ : Function.Bijective (fun e ↦ Fintype.choose _ (h₁ e)) := by decide) :
    Equiv.Perm Edge :=
  Fintype.equivOfBij _ h₂

lemma mkEdges_apply (p : Equiv.Perm Vert)
    (h₁ : ∀ e : Edge, ∃! e' : Edge, e'.toVert = e.toVert.image p)
    (h₂ : Function.Bijective (fun e ↦ Fintype.choose _ (h₁ e)))
    (e : Edge) :
    (mkEdges p h₁ h₂ e).toVert = Finset.image p e.toVert :=
  Fintype.choose_spec (fun e' : Edge ↦ e'.toVert = e.toVert.image p) (h₁ _)

def mkFaces (p : Equiv.Perm Edge)
    (h₁ : ∀ f : Face, ∃! f' : Face, f'.toEdge = f.toEdge.image p := by decide)
    (h₂ : Function.Bijective (fun f ↦ Fintype.choose _ (h₁ f)) := by decide) :
    Equiv.Perm Face :=
  Fintype.equivOfBij _ h₂

def mkFaces_apply (p : Equiv.Perm Edge)
    (h₁ : ∀ f : Face, ∃! f' : Face, f'.toEdge = f.toEdge.image p)
    (h₂ : Function.Bijective (fun f ↦ Fintype.choose _ (h₁ f)))
    (f : Face) :
    (mkFaces p h₁ h₂ f).toEdge = Finset.image p f.toEdge :=
  Fintype.choose_spec (fun f' : Face ↦ f'.toEdge = f.toEdge.image p) (h₁ _)

end

section P

#time -- .297 s
/-- A particular automorphism of the vertex type. -/
def P.vertAut : Equiv.Perm Vert := Fintype.equivOfBij (fun ⟨i, u, u'⟩ ↦ ⟨i - 1, u, u'⟩) (by decide)

#time -- .089 s
example : P.vertAut ^ 3 = 1 := by decide

#time -- 10.762 s
/-- The automorphism `P.vertAut` of the vertex type induces an automorphism of the edge type
preserving the incidence structure between vertices and edges. -/
def P.edgeAut : Equiv.Perm Edge := mkEdges P.vertAut

@[simp] lemma P.toVert_edgeAut (e : Edge) :
    (P.edgeAut e).toVert = Finset.image P.vertAut e.toVert :=
  mkEdges_apply _ _ _ _

#time -- 12.937 s
/-- The automorphism `P.edgeAut` of the edge type induces an automorphism of the face type
preserving the incidence structure between edges and faces. -/
def P.faceAut : Equiv.Perm Face := mkFaces P.edgeAut

@[simp] lemma P.toEdge_faceAut (f : Face) :
    (P.faceAut f).toEdge = Finset.image P.edgeAut f.toEdge :=
  mkFaces_apply _ _ _ _

def P : Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face := ⟨P.vertAut, P.edgeAut, P.faceAut⟩

#time -- 11.140 s
lemma P.pow_three_eq_one : P ^ 3 = 1 := by decide

#time -- .061 s
lemma P.ne_one : P ≠ 1 := by decide

end P

namespace Q

/-- A period-5 bijection, composed of two disjoint 5-cycles
⟨2, 1, 0⟩ → ⟨0, 0, 1⟩ → ⟨1, 1, 0⟩ → ⟨1, 0, 0⟩ → ⟨0, 0, 0⟩ →
⟨2, 0, 1⟩ → ⟨0, 1, 0⟩ → ⟨1, 0, 1⟩ → ⟨1, 1, 1⟩ → ⟨0, 1, 1⟩ →
and fixing ⟨2, 0, 0⟩ and ⟨2, 1, 1⟩.
-/
protected def vertAutAux : ZMod 3 → ZMod 2 → ZMod 2 → Vert :=
  ![![![⟨2, 1, 0⟩, ⟨1, 1, 0⟩],  -- images of ⟨0, 0, 0⟩, ⟨0, 0, 1⟩
      ![⟨1, 0, 1⟩, ⟨2, 0, 1⟩]], -- images of ⟨0, 1, 0⟩, ⟨0, 1, 1⟩
    ![![⟨0, 0, 0⟩, ⟨1, 1, 1⟩],  -- images of ⟨1, 0, 0⟩, ⟨1, 0, 1⟩
      ![⟨1, 0, 0⟩, ⟨0, 1, 1⟩]], -- images of ⟨1, 1, 0⟩, ⟨1, 1, 1⟩
    ![![⟨2, 0, 0⟩, ⟨0, 1, 0⟩],  -- images of ⟨2, 0, 0⟩, ⟨2, 0, 1⟩
      ![⟨0, 0, 1⟩, ⟨2, 1, 1⟩]]] -- images of ⟨2, 1, 0⟩, ⟨2, 1, 1⟩

#time -- .292 s
protected def vertAut : Equiv.Perm Vert :=
  Fintype.equivOfBij (fun ⟨i, u, u'⟩ ↦ Q.vertAutAux i u u') (by decide)

example : Q.vertAut ^ 5 = 1 := by decide

#time -- 11.229 s
/-- The automorphism `Q.vertAut` of the vertex type induces an automorphism of the edge type
preserving the incidence structure between vertices and edges. -/
protected def edgeAut : Equiv.Perm Edge := mkEdges Q.vertAut

@[simp] protected lemma toVert_edgeAut (e : Edge) :
    (Q.edgeAut e).toVert = Finset.image Q.vertAut e.toVert :=
  mkEdges_apply _ _ _ _

#time -- 11.931 s
/-- The automorphism `P.edgeAut` of the edge type induces an automorphism of the face type
preserving the incidence structure between edges and faces. -/
protected def faceAut : Equiv.Perm Face := mkFaces Q.edgeAut

@[simp] protected lemma toEdge_faceAut (f : Face) :
    (Q.faceAut f).toEdge = Finset.image Q.edgeAut f.toEdge :=
  mkFaces_apply _ _ _ _

end Q

/-- A period-5 automorphism of the icosahedron, acting on the vertex set in two disjoint 5-cycles
⟨2, 1, 0⟩ → ⟨0, 0, 1⟩ → ⟨1, 1, 0⟩ → ⟨1, 0, 0⟩ → ⟨0, 0, 0⟩ →
⟨2, 0, 1⟩ → ⟨0, 1, 0⟩ → ⟨1, 0, 1⟩ → ⟨1, 1, 1⟩ → ⟨0, 1, 1⟩ →
and fixing ⟨2, 0, 0⟩ and ⟨2, 1, 1⟩. -/
def Q : Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face := ⟨Q.vertAut, Q.edgeAut, Q.faceAut⟩

namespace Q

#time -- 10.512 s
protected lemma pow_five_eq_one : Q ^ 5 = 1 := by decide

#time -- .060 s
protected lemma ne_one : Q ≠ 1 := by decide

end Q

#time -- 16.830 s
set_option maxRecDepth 500 in
example : (P * Q) ^ 2 = 1 := by decide


section automorphisms

def automorphismVertEdgeIncidence :
    Subgroup (Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) where
  carrier := {p | ∀ e, (p.2.1 e).toVert = e.toVert.image p.1}
  mul_mem' {p p'} hp hp' e :=
    calc _ = _ := hp (p'.2.1 e)
      _ = _ := by rw [hp' e]; sorry
      _ = _ := Finset.image_image
  one_mem' e := Finset.image_id.symm
  inv_mem' {p} hp e :=
    let q₀ : Equiv.Perm Vert := p.1⁻¹
    let q₁ : Equiv.Perm Edge := p.2.1⁻¹
    calc (q₁ e).toVert
        = (q₁ e).toVert.image id := Finset.image_id.symm
      _ = (q₁ e).toVert.image (q₀ ∘ p.1) := by congr; exact p.1.symm_comp_self.symm
      _ = ((q₁ e).toVert.image p.1).image q₀ := by rw [Finset.image_image]
      _ = (p.2.1 (q₁ e)).toVert.image q₀ := by rw [hp (q₁ e)]
      _ = e.toVert.image q₀ := by congr; exact p.2.1.right_inv e

instance (p : Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) :
    Decidable (p ∈ automorphismVertEdgeIncidence) := by
  show Decidable (∀ e, (p.2.1 e).toVert = e.toVert.image p.1)
  infer_instance

def automorphismEdgeFaceIncidence :
    Subgroup (Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) where
  carrier := {p | ∀ f, (p.2.2 f).toEdge = f.toEdge.image p.2.1}
  mul_mem' {p p'} hp hp' f :=
    calc _ = _ := hp (p'.2.2 f)
      _ = _ := by rw [hp' f]; sorry
      _ = _ := Finset.image_image
  one_mem' f := Finset.image_id.symm
  inv_mem' {p} hp f :=
    let q₁ : Equiv.Perm Edge := p.2.1⁻¹
    let q₂ : Equiv.Perm Face := p.2.2⁻¹
    calc (q₂ f).toEdge
        = (q₂ f).toEdge.image id := Finset.image_id.symm
      _ = (q₂ f).toEdge.image (q₁ ∘ p.2.1) := by congr; exact p.2.1.symm_comp_self.symm
      _ = ((q₂ f).toEdge.image p.2.1).image q₁ := by rw [Finset.image_image]
      _ = (p.2.2 (q₂ f)).toEdge.image q₁ := by rw [hp (q₂ f)]
      _ = f.toEdge.image q₁ := by congr; exact p.2.2.right_inv f

instance (p : Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) :
    Decidable (p ∈ automorphismEdgeFaceIncidence) := by
  show Decidable (∀ f, (p.2.2 f).toEdge = f.toEdge.image p.2.1)
  infer_instance

abbrev signPreserving : Subgroup (Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) :=
  MonoidHom.ker $ (Equiv.Perm.sign.comp (MonoidHom.fst _ _))

-- FIXME ugly statement, some bad SetLike simp lemmas?
instance (p : Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) :
    Decidable (p ∈ SetLike.coe signPreserving.toSubmonoid) := by
  show Decidable (Equiv.Perm.sign p.1 = 1)
  infer_instance

/-- The automorphisms of the icosahedron, considered as a subgroup of the product of the
automorphism groups of the vertices, edges and faces. -/
def automorphism : Subgroup (Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) :=
  automorphismVertEdgeIncidence ⊓ automorphismEdgeFaceIncidence ⊓ signPreserving

instance (p : Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) :
    Decidable (p ∈ automorphism) := by
  dsimp [automorphism]
  infer_instance

lemma P_mem_automorphism : P ∈ automorphism := ⟨⟨P.toVert_edgeAut, P.toEdge_faceAut⟩, by decide⟩
lemma Q_mem_automorphism : Q ∈ automorphism := ⟨⟨Q.toVert_edgeAut, Q.toEdge_faceAut⟩, by decide⟩

def XYZ_to_XY :
    Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face →* Equiv.Perm Vert × Equiv.Perm Edge :=
  (MonoidHom.fst ..).prod <| (MonoidHom.fst _ _).comp (MonoidHom.snd _ _)

/-- An automorphism of the icosahedron is uniquely characterized by its behaviour on the vertices
and edges.

... (or even just on the vertices). -/
example : Set.InjOn XYZ_to_XY automorphism := sorry

-- associated subgroup of the vertex-and-edge automorphisms
example : Subgroup (Equiv.Perm Vert × Equiv.Perm Edge) := automorphism.map XYZ_to_XY

-- TODO: acts freely and transitively on incident (vertex, edge) pairs

example : automorphism = Subgroup.closure {P, Q} := by
  symm
  apply Subgroup.closure_eq_of_le
  · -- the easy part: `P` and `Q` are automorphisms
    rintro - (rfl | rfl : _ = P ∨ _ = Q)
    · exact P_mem_automorphism
    · exact Q_mem_automorphism
  -- the hard part: every automorphism is a word in `P` and `Q`
  sorry

def automorphismFinset : Finset (Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) :=
  Finset.filter (· ∈ automorphism) Finset.univ

-- #time
-- set_option maxRecDepth 1000 in
-- example : Finset.card automorphismFinset = 60 := by decide

end automorphisms

end Icosahedron
