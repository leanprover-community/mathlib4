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
@[pp_dot] def Edge.toVert : Edge → Finset Vert
  | Edge.a i u => {⟨i, 0, u⟩, ⟨i, 1, u⟩}
  | Edge.d i u => {⟨i, u, u⟩, ⟨i + 1, u, u⟩}
  | Edge.b i u => {⟨i, u, u⟩, ⟨i + 1, u, 1 + u⟩}
  | Edge.c i u => {⟨i, 1 + u, u⟩, ⟨i + 1, u, u⟩}
  | Edge.e i u => {⟨i, u, 1 + u⟩, ⟨i + 1, 1 + u, u⟩}

/-
a: Edge := Edge.a 0 0  {⟨0, 0, 0⟩, ⟨0, 1, 0⟩}
b: Edge := Edge.d 0 0  {⟨0, 0, 0⟩, ⟨1, 0, 0⟩}
c: Edge := Edge.d 2 0  {⟨2, 0, 0⟩, ⟨0, 0, 0⟩}

-/

#time -- 3.48 s
/-- An edge is uniquely characterized by the pair of vertices it connects. -/
lemma Edge.toVert_injective : Function.Injective Edge.toVert := by decide

/-- The three edges bounding each face of the icosahedron. -/
@[pp_dot] def Face.toEdge : Face → Finset Edge
  | Face.w u => {Edge.d 0 u, Edge.d 1 u, Edge.d 2 u}
  | Face.x i u => {Edge.b i u, Edge.c (i + 2) u, Edge.e (i + 1) u}
  | Face.y i u => {Edge.d (i + 2) u, Edge.a (i + 2) u, Edge.c (i + 2) u}
  | Face.z i u => {Edge.a i u, Edge.b i u, Edge.e i (1 + u)}

#time -- 2.244 s
/-- A face is uniquely characterized by the triple of edges bounding it. -/
lemma Face.toEdge_injective : Function.Injective Face.toEdge := by decide

/-- The edges emerging from a given vertex of the icosahedron. -/
@[pp_dot] def Vert.toEdge (v : Vert) : Finset Edge :=
  Finset.filter (fun e : Edge ↦ v ∈ e.toVert) Finset.univ

-- the edges touching the vertex `⟨1, 0, 0⟩`
#eval Vert.toEdge ⟨1, 0, 0⟩

/- In fact, every vertex touches five edges. -/
#time -- .878 s
example {v : Vert} : v.toEdge.card = 5 := by revert v; decide

/-- The faces touching a given edge of the icosahedron. -/
@[pp_dot] def Edge.toFace (e : Edge) : Finset Face :=
  Finset.filter (fun f : Face ↦ e ∈ f.toEdge) Finset.univ

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

/-- A triangle in the (vertex, edge) incidence relation. -/
def Chain (v : ZMod 3 → Vert) (e : ZMod 3 → Edge) : Prop :=
  ∀ i, v i ≠ v (i + 1) ∧ e i ≠ e (i + 1) ∧ v i ∈ (e i).toVert ∩ (e (i + 1)).toVert

instance (v e) : Decidable (Chain v e) := by dsimp [Chain]; infer_instance

/-- Alternative definition of a triangle in the (vertex, edge) incidence relation, as an attempt to
make decidability check faster (still doesn't work). -/
def Triangle (x y z : Vert) (a b c : Edge) : Prop :=
  (x ≠ y ∧ a ≠ b ∧ x ∈ a.toVert ∩ b.toVert)
  ∧ (y ≠ z ∧ b ≠ c ∧ y ∈ b.toVert ∩ c.toVert)
  ∧ (z ≠ x ∧ c ≠ a ∧ z ∈ c.toVert ∩ a.toVert)

instance (x y z : Vert) {a b c : Edge} : Decidable (Triangle x y z a b c) := by
  dsimp [Triangle]
  infer_instance

theorem mem_range_of_triangle (x y z : Vert) {a b c : Edge} (h : Triangle x y z a b c) :
    ∃ f : Face, f.toEdge = {c, b, a} := by
  -- revert x y z a b c; decide -- times out
  sorry

theorem triangle_of_mem_range (f : Face) :
    ∃ (x y z : Vert) (a b c : Edge),  Triangle x y z a b c ∧ f.toEdge = {a, b, c} := by
  -- revert f; decide -- times out
  sorry

lemma foo {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin (n + 1) → α) :
    Finset.image f Finset.univ
    = insert (f n) (Finset.image (f ∘ Fin.castSucc) Finset.univ) := by
  sorry

lemma mem_range_faceToEdge_iff (s : Finset Edge) :
    s ∈ Finset.image Face.toEdge Finset.univ
    ↔ ∃ v e, Chain v e ∧ s = Finset.image e Finset.univ := by
  -- revert s; decide -- times out
  constructor
  · intro h
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨f, rfl⟩ := h
    obtain ⟨x, y, z, a, b, c, ⟨h1, h2, h3⟩, h4⟩ := triangle_of_mem_range f
    refine ⟨![x,y,z], ![a,b,c], fun i ↦ ⟨?_, ?_, ?_⟩, ?_⟩
    · fin_cases i
      exacts [h1.1, h2.1, h3.1]
    · fin_cases i
      exacts [h1.2.1, h2.2.1, h3.2.1]
    · fin_cases i
      exacts [h1.2.2, h2.2.2, h3.2.2]
    · rw [h4]
      ext x
      simp only [Finset.mem_image, Finset.mem_singleton, Finset.mem_insert, Finset.mem_univ,
        true_and]
      constructor
      · rintro (rfl | rfl | rfl)
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
  · rintro ⟨v, e, he, rfl⟩
    suffices : ∃ a : Face, a.toEdge = {e 2, e 1, e 0}
    · rw [foo, foo, foo]
      simpa using this
    apply mem_range_of_triangle (v 0) (v 1) (v 2) ⟨he 0, he 1, he 2⟩

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
    Subgroup (Equiv.Perm Vert × Equiv.Perm Edge) where
  carrier := {p | ∀ e, (p.2 e).toVert = e.toVert.image p.1}
  mul_mem' {p p'} hp hp' e :=
    calc _ = _ := hp (p'.2 e)
      _ = _ := by rw [hp' e]; sorry
      _ = _ := Finset.image_image
  one_mem' e := Finset.image_id.symm
  inv_mem' {p} hp e :=
    let q₀ : Equiv.Perm Vert := p.1⁻¹
    let q₁ : Equiv.Perm Edge := p.2⁻¹
    calc (q₁ e).toVert
        = (q₁ e).toVert.image id := Finset.image_id.symm
      _ = (q₁ e).toVert.image (q₀ ∘ p.1) := by congr; exact p.1.symm_comp_self.symm
      _ = ((q₁ e).toVert.image p.1).image q₀ := by rw [Finset.image_image]
      _ = (p.2 (q₁ e)).toVert.image q₀ := by rw [hp (q₁ e)]
      _ = e.toVert.image q₀ := by congr; exact p.2.right_inv e

lemma toVert_perm_of_mem_automorphismEdgeFaceIncidence {p : Equiv.Perm Vert × Equiv.Perm Edge}
    (hp : p ∈ automorphismVertEdgeIncidence) (f : Edge) :
    (p.2 f).toVert = f.toVert.image p.1 :=
  hp f

instance (p : Equiv.Perm Vert × Equiv.Perm Edge) :
    Decidable (p ∈ automorphismVertEdgeIncidence) := by
  show Decidable (∀ e, (p.2 e).toVert = e.toVert.image p.1)
  infer_instance

lemma chain_comp_of_mem_automorphismVertEdgeIncidence {p : Equiv.Perm Vert × Equiv.Perm Edge}
    (hp : p ∈ automorphismVertEdgeIncidence) {v : ZMod 3 → Vert} {e : ZMod 3 → Edge} (hc : Chain v e) :
    Chain (p.1 ∘ v) (p.2 ∘ e) := by
  intro i
  obtain ⟨hv, he, hev⟩ := hc i
  dsimp at *
  refine ⟨p.1.injective.ne hv, p.2.injective.ne he, ?_⟩
  simp only [toVert_perm_of_mem_automorphismEdgeFaceIncidence hp,
    ←Finset.image_inter _ _ p.1.injective]
  exact Finset.mem_image_of_mem p.1 hev

def automorphismEdgeFaceIncidence :
    Subgroup (Equiv.Perm Edge × Equiv.Perm Face) where
  carrier := {p | ∀ f, (p.2 f).toEdge = f.toEdge.image p.1}
  mul_mem' {p p'} hp hp' f :=
    calc _ = _ := hp (p'.2 f)
      _ = _ := by rw [hp' f]; sorry
      _ = _ := Finset.image_image
  one_mem' f := Finset.image_id.symm
  inv_mem' {p} hp f :=
    let q₁ : Equiv.Perm Edge := p.1⁻¹
    let q₂ : Equiv.Perm Face := p.2⁻¹
    calc (q₂ f).toEdge
        = (q₂ f).toEdge.image id := Finset.image_id.symm
      _ = (q₂ f).toEdge.image (q₁ ∘ p.1) := by congr; exact p.1.symm_comp_self.symm
      _ = ((q₂ f).toEdge.image p.1).image q₁ := by rw [Finset.image_image]
      _ = (p.2 (q₂ f)).toEdge.image q₁ := by rw [hp (q₂ f)]
      _ = f.toEdge.image q₁ := by congr; exact p.2.right_inv f

lemma toEdge_perm_of_mem_automorphismEdgeFaceIncidence {p : Equiv.Perm Edge × Equiv.Perm Face}
    (hp : p ∈ automorphismEdgeFaceIncidence) (f : Face) :
    (p.2 f).toEdge = f.toEdge.image p.1 :=
  hp f

instance (p : Equiv.Perm Edge × Equiv.Perm Face) :
    Decidable (p ∈ automorphismEdgeFaceIncidence) := by
  show Decidable (∀ f, (p.2 f).toEdge = f.toEdge.image p.1)
  infer_instance

abbrev signPreserving : Subgroup (Equiv.Perm Vert × Equiv.Perm Edge) :=
  MonoidHom.ker $ (Equiv.Perm.sign.comp (MonoidHom.fst _ _))

-- FIXME ugly statement, some bad SetLike simp lemmas?
instance (p : Equiv.Perm Vert × Equiv.Perm Edge) :
    Decidable (p ∈ SetLike.coe signPreserving.toSubmonoid) := by
  show Decidable (Equiv.Perm.sign p.1 = 1)
  infer_instance

abbrev automorphismVertEdgeIncidenceSigned := automorphismVertEdgeIncidence ⊓ signPreserving

abbrev XYZ_to_XY :
    Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face →* Equiv.Perm Vert × Equiv.Perm Edge :=
  (MonoidHom.fst ..).prod <| (MonoidHom.fst _ _).comp (MonoidHom.snd _ _)

abbrev XYZ_to_YZ :
    Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face →* Equiv.Perm Edge × Equiv.Perm Face :=
  MonoidHom.snd ..

/-- The automorphisms of the icosahedron, considered as a subgroup of the product of the
automorphism groups of the vertices, edges and faces. -/
def automorphism : Subgroup (Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) :=
  automorphismVertEdgeIncidenceSigned.comap XYZ_to_XY
  ⊓ automorphismEdgeFaceIncidence.comap XYZ_to_YZ

-- instance (p : Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) :
--     Decidable (p ∈ automorphism) := by
--   dsimp [automorphism]
--   infer_instance

lemma P_mem_automorphismVertEdgeIncidenceSigned :
    XYZ_to_XY P ∈ automorphismVertEdgeIncidenceSigned :=
  ⟨P.toVert_edgeAut, by decide⟩

lemma Q_mem_automorphismVertEdgeIncidenceSigned :
    XYZ_to_XY Q ∈ automorphismVertEdgeIncidenceSigned :=
  ⟨Q.toVert_edgeAut, by decide⟩

lemma P_mem_automorphism : P ∈ automorphism :=
  ⟨P_mem_automorphismVertEdgeIncidenceSigned, P.toEdge_faceAut⟩
lemma Q_mem_automorphism : Q ∈ automorphism :=
  ⟨Q_mem_automorphismVertEdgeIncidenceSigned, Q.toEdge_faceAut⟩

/-- An automorphism of the icosahedron is uniquely characterized by its behaviour on the vertices
and edges.

... (or even just on the vertices). -/
lemma injOn_automorphism : Set.InjOn XYZ_to_XY automorphism := by
  rintro a ⟨_, haEdgeFace⟩ b ⟨_, hbEdgeFace⟩ hab
  apply Prod.ext
  · convert congr_arg Prod.fst hab
  have H : a.2.1 = b.2.1 := congr_arg Prod.snd hab
  apply Prod.ext H
  ext f
  apply Face.toEdge_injective
  calc (a.2.2 f).toEdge = f.toEdge.image a.2.1 :=
        toEdge_perm_of_mem_automorphismEdgeFaceIncidence haEdgeFace f
    _ = f.toEdge.image b.2.1 := by rw [H]
    _ = (b.2.2 f).toEdge :=
        (toEdge_perm_of_mem_automorphismEdgeFaceIncidence hbEdgeFace f).symm

theorem zz {p} (hp : p ∈ automorphismVertEdgeIncidenceSigned) (f : Face) :
    ∃ a : Face, a.toEdge = Finset.image (p.2) f.toEdge := by
  have hf : f.toEdge ∈ Finset.image Face.toEdge Finset.univ :=
    Finset.mem_image_of_mem Face.toEdge (Finset.mem_univ f)
  obtain ⟨v, e, he, hev⟩ := (mem_range_faceToEdge_iff _).1 hf
  have he' : Chain (p.1 ∘ v) (p.2 ∘ e) := chain_comp_of_mem_automorphismVertEdgeIncidence hp.1 he
  have hev' : Finset.image p.2 f.toEdge = Finset.image (p.2 ∘ e) Finset.univ := by
    rw [hev, Finset.image_image]
  have H : Finset.image p.2 f.toEdge ∈ Finset.image _ _ :=
    (mem_range_faceToEdge_iff _).2 ⟨_, _, he', hev'⟩
  rw [Finset.mem_image] at H
  exact ⟨H.choose, H.choose_spec.2⟩

/-- An automorphism of the (vertex, edge) relation of the icosahedron extends to an automorphism of
the icosahedron proper (including the faces). -/
lemma surjOn_automorphism :
    Set.SurjOn XYZ_to_XY automorphism automorphismVertEdgeIncidenceSigned := by
  intro p hp
  have H := zz hp
  choose P hP using H
  have H' := zz (Subgroup.inv_mem _ hp)
  choose P' hP' using H'
  have h₁ (f : Face) : P' (P f) = f := by
    apply Face.toEdge_injective
    rw [hP', hP, Finset.image_image]
    trans Finset.image id f.toEdge
    · congr
      exact congr_arg FunLike.coe (mul_left_inv p.2)
    · simp
  have h₂ (f : Face) : P (P' f) = f := by
    apply Face.toEdge_injective
    rw [hP, hP', Finset.image_image]
    trans Finset.image id f.toEdge
    · congr
      exact congr_arg FunLike.coe (mul_right_inv p.2)
    · simp
  let a : Equiv.Perm Face := ⟨P, P', h₁, h₂⟩
  exact ⟨⟨p.1, ⟨p.2, a⟩⟩, ⟨hp, hP⟩, rfl⟩

theorem bijOn_automorphim :
    Set.BijOn XYZ_to_XY automorphism automorphismVertEdgeIncidenceSigned :=
  ⟨fun _ hp ↦ hp.1, injOn_automorphism, surjOn_automorphism⟩

-- associated subgroup of the vertex-and-edge automorphisms, follows from previous
example : automorphism.map XYZ_to_XY = automorphismVertEdgeIncidenceSigned := by
  apply SetLike.coe_injective
  exact bijOn_automorphim.image_eq

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

example : automorphismVertEdgeIncidenceSigned = Subgroup.closure {XYZ_to_XY P, XYZ_to_XY Q} := by
  symm
  apply Subgroup.closure_eq_of_le
  · -- the easy part: `P` and `Q` are automorphisms
    rintro - (rfl | rfl : _ = XYZ_to_XY P ∨ _ = XYZ_to_XY Q)
    · exact P_mem_automorphismVertEdgeIncidenceSigned
    · exact Q_mem_automorphismVertEdgeIncidenceSigned
  -- the hard part: every automorphism is a word in `P` and `Q`
  sorry

-- def automorphismFinset : Finset (Equiv.Perm Vert × Equiv.Perm Edge × Equiv.Perm Face) :=
--   Finset.filter (· ∈ automorphism) Finset.univ

-- #time
-- set_option maxRecDepth 1000 in
-- example : Finset.card automorphismFinset = 60 := by decide

end automorphisms

end Icosahedron
