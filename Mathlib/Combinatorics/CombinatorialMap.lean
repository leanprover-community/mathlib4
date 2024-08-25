import Mathlib.Data.List.Perm
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Equiv.Perm

variable {D : Type}

lemma SameCycle.Equiv (f : Equiv.Perm D) : Equivalence (Equiv.Perm.SameCycle f) where
  refl := Equiv.Perm.SameCycle.refl f
  symm := Equiv.Perm.SameCycle.symm
  trans := Equiv.Perm.SameCycle.trans

def PSetoid (f : Equiv.Perm D) : Setoid D :=
  ⟨Equiv.Perm.SameCycle f, Equiv.Perm.SameCycle.Equiv f⟩

instance PSetoid.Quotient.Fintype {α : Type} (f : Equiv.Perm α) [Fintype α] [DecidableEq α] :
    Fintype (Quotient (PSetoid f)) := by
  haveI : DecidableRel (PSetoid f).r := by
    change DecidableRel (Equiv.Perm.SameCycle _)
    infer_instance
  exact Quotient.fintype f.PSetoid

end Equiv.Perm

-- A two-dimension combinatorial map is a collection D of darts, a
-- permutation σ whose orbits correspond to vertices, and a
-- fixed-point-free involution τ whose orbits correspond to edges.  We
-- think of σ as giving the next dart counterclockwise around an edge,
-- and τ as giving the opposite dart of an edge. (Note: this
-- definition excludes disjoint isolated vertices.)
--
-- We only care about the case where the orbits of σ are finite, but
-- we do not require it in the definition.
structure CombinatorialMap (D : Type) where
  σ : Equiv.Perm D
  α : Equiv.Perm D
  involutive : Function.Involutive α
  fixedPoints_isEmpty : IsEmpty (Function.fixedPoints α)

namespace CombinatorialMap

variable {D D' : Type} {M : CombinatorialMap D} {M' : CombinatorialMap D'}

-- The next dart counter-clockwise around a face
@[simp]
lemma involutive_apply {x : D} : M.α (M.α x) = x :=
  M.involutive x

-- The next dart counter-clockwise around a face
@[simp]
def φ (M : CombinatorialMap D) : Equiv.Perm D :=
  M.σ.symm.trans M.α

@[simp]
theorem composition_eq_id : M.φ * M.σ * M.α = 1 := by
  ext
  simp

-- We only will care about the case of equivalences, but in this
-- definition a homomorphism of combinatorial maps is sort of like a
-- branched covering map of surfaces branched over the vertices.
def Hom (M : CombinatorialMap D) (M' : CombinatorialMap D') (f : D → D') : Prop :=
  f ∘ M.σ = M'.σ ∘ f ∧
  f ∘ M.α = M'.α ∘ f

theorem hom_inv_is_hom (M : CombinatorialMap D) (M' : CombinatorialMap D') (f : Equiv D D')
    (h : Hom M M' f) : Hom M' M f.symm := by
  apply And.intro
  · calc f.symm ∘ M'.σ = f.symm ∘ M'.σ ∘ id := rfl
      _ = f.symm ∘ M'.σ ∘ (f ∘ f.symm) := by rw [← Equiv.self_comp_symm]
      _ = f.symm ∘ (M'.σ ∘ f) ∘ f.symm := rfl
      _ = f.symm ∘ (f ∘ M.σ) ∘ f.symm := by rw [← h.1]
      _ = (f.symm ∘ f) ∘ M.σ ∘ f.symm := rfl
      _ = id ∘ M.σ ∘ f.symm := by rw [Equiv.symm_comp_self]
  · calc f.symm ∘ M'.α = f.symm ∘ M'.α ∘ id := rfl
      _ = f.symm ∘ M'.α ∘ (f ∘ f.symm) := by rw [← Equiv.self_comp_symm]
      _ = f.symm ∘ (M'.α ∘ f) ∘ f.symm := rfl
      _ = f.symm ∘ (f ∘ M.α) ∘ f.symm := by rw [← h.2]
      _ = (f.symm ∘ f) ∘ M.α ∘ f.symm := rfl
      _ = id ∘ M.α ∘ f.symm := by rw [Equiv.symm_comp_self]

-- In light of `hom_inv_is_hom`, we define an equivalence of maps as
-- an equivalence of their dart sets that is a homomorphism.
def equiv_maps (M : CombinatorialMap D) (M' : CombinatorialMap D') (f : Equiv D D') :=
  Hom M M' f

-- We define the opposite of a map to be the one which reverses
-- the identities of the darts on each edge
def opp (M : CombinatorialMap D) : CombinatorialMap D :=
  ⟨Equiv.trans (Equiv.trans M.α M.σ) M.α, M.α, M.involutive, M.fixedPoints_isEmpty⟩

-- Form the dual map.  This swaps the roles of vertices and faces
def dual (M : CombinatorialMap D) : CombinatorialMap D :=
  ⟨M.φ, M.α, M.involutive, M.fixedPoints_isEmpty⟩

lemma double_dual_is_opp (M : CombinatorialMap D) : M.dual.dual = M.opp := by
  dsimp [opp, dual]
  congr
  convert_to M.α.symm.trans M.σ.symm.symm = M.α.trans M.σ
  rw [Equiv.symm_symm, M.involutive.symm_eq_self_of_involutive]

-- The opposite of a map (and hence the double dual) is equivalent to the original map.
lemma double_dual (M : CombinatorialMap D) : ∃ (f : Equiv D D), Hom M M.opp f :=
  ⟨M.α, ⟨by rw [← (M.α ∘ M.σ).comp_id, ← Function.RightInverse.id M.involutive]; rfl, rfl⟩⟩

-- A "dual homomorphism" is a homomorphism that sends vertices to
-- faces and faces to vertices.  The entire point of this definition
-- is purely for `dual_dequiv`.
def DHom (M : CombinatorialMap D) (M' : CombinatorialMap D') (f : D → D') :=
  f ∘ M.σ = M'.φ ∘ f ∧
  f ∘ M.α = M'.α ∘ f

-- This is a DHom from a map to its dual.  See `dual_dequiv`.
def to_dual (M : CombinatorialMap D) : D → D :=
  M.α

-- A map and its dual are dual equivalent (hence the name)
lemma dual_dequiv (M : CombinatorialMap D) : DHom M M.dual M.to_dual :=
  ⟨funext fun _ ↦ by simp [dual, to_dual], rfl⟩

@[reducible] def vertex_setoid (M : CombinatorialMap D) :=
  Equiv.Perm.PSetoid M.σ

@[reducible] def edge_setoid (M : CombinatorialMap D) :=
  Equiv.Perm.PSetoid M.α

@[reducible] def face_setoid (M : CombinatorialMap D) :=
  Equiv.Perm.PSetoid M.φ

@[reducible] def vertices (M : CombinatorialMap D) :=
  Quotient (vertex_setoid M)

@[reducible] def edges (M : CombinatorialMap D) :=
  Quotient (edge_setoid M)

@[reducible] def faces (M : CombinatorialMap D) :=
  Quotient (face_setoid M)

-- The vertex at the dart
@[reducible] def dart_vertex (M : CombinatorialMap D) (d : D) : M.vertices :=
  @Quotient.mk _ (vertex_setoid M) d

-- The edge on the the dart
@[reducible] def dart_edge (M : CombinatorialMap D) (d : D) : M.edges :=
  @Quotient.mk _ (edge_setoid M) d

-- The face to the left of the dart.  That is, the one traced out by `m.ϕ`
@[reducible] def dart_face (M : CombinatorialMap D) (d : D) : M.faces :=
  @Quotient.mk _ (face_setoid M) d

end CombinatorialMap

structure CombinatorialMap' (D : Type) where
  σ : Equiv.Perm D
  α : Equiv.Perm D
  φ : Equiv.Perm D
  composition : α.trans (σ.trans φ) = 1
  involutive : Function.Involutive α
  fixedPoints_isEmpty : IsEmpty (Function.fixedPoints α)

namespace CombinatorialMap'

variable {D D' : Type} {M : CombinatorialMap' D} {M' : CombinatorialMap' D'}

@[simp]
lemma involutive_trans : M.α.trans M.α = 1 := by
  rw [Equiv.trans]
  congr <;> simp [M.involutive, M.involutive.symm_eq_self_of_involutive]

lemma composition_apply {x : D} : M.φ (M.σ (M.α x)) = x := by
  convert_to M.α.trans (M.σ.trans M.φ) x = x
  simp [M.composition]

lemma composition' : M.α * M.φ * M.σ = 1 := by
  have : ∀ x, (M.α * M.φ * M.σ) (M.α x) = M.α x := by simp [composition_apply]
  have (y : D) : (M.α * M.φ * M.σ) y = y := by
    obtain ⟨t, h⟩ := M.α.surjective y
    rw [← h, this]
  ext x
  exact this x

lemma composition'_apply {x : D} : M.α (M.φ (M.σ x)) = x := by
  convert_to (M.α * M.φ * M.σ) x = x
  simp [M.composition']

-- We only will care about the case of equivalences, but in this
-- definition a homomorphism of combinatorial maps is sort of like a
-- branched covering map of surfaces branched over the vertices.
def Hom (M : CombinatorialMap' D) (M' : CombinatorialMap' D') (f : D → D') : Prop :=
  f ∘ M.σ = M'.σ ∘ f ∧
  f ∘ M.α = M'.α ∘ f ∧
  f ∘ M.φ = M'.φ ∘ f

lemma hom_inv_is_hom_aux {p₁ : Equiv.Perm D} {p₂ : Equiv.Perm D'} {f : Equiv D D'}
    (h : f ∘ p₁ = p₂ ∘ f) : f.symm ∘ p₂ = p₁ ∘ f.symm :=
  calc f.symm ∘ p₂ = f.symm ∘ p₂ ∘ id := rfl
    _ = f.symm ∘ p₂ ∘ (f ∘ f.symm) := by rw [← Equiv.self_comp_symm]
    _ = f.symm ∘ (p₂ ∘ f) ∘ f.symm := rfl
    _ = f.symm ∘ (f ∘ p₁) ∘ f.symm := by rw [← h]
    _ = (f.symm ∘ f) ∘ p₁ ∘ f.symm := rfl
    _ = id ∘ p₁ ∘ f.symm := by rw [Equiv.symm_comp_self]

lemma hom_inv_is_hom (M : CombinatorialMap' D) (M' : CombinatorialMap' D') (f : Equiv D D')
    (h : Hom M M' f) : Hom M' M f.symm :=
  ⟨hom_inv_is_hom_aux h.1, hom_inv_is_hom_aux h.2.1, hom_inv_is_hom_aux h.2.2⟩

-- In light of `hom_inv_is_hom`, we define an equivalence of maps as
-- an equivalence of their dart sets that is a homomorphism.
def equiv_maps (M : CombinatorialMap' D) (M' : CombinatorialMap' D') (f : Equiv D D') :=
  Hom M M' f

-- We define the opposite of a map to be the one which reverses
-- the identities of the darts on each edge
def opp (M : CombinatorialMap' D) : CombinatorialMap' D where
  σ := (M.α.trans M.σ).trans M.α
  α := M.α
  φ := (M.α.trans M.φ).trans M.α
  involutive := M.involutive
  fixedPoints_isEmpty := M.fixedPoints_isEmpty
  composition := by
    ext x
    simp only [Equiv.trans_apply, Equiv.Perm.coe_one, id_eq]
    rw [M.involutive, M.involutive, composition'_apply]

lemma φ_eq : M.φ = M.σ.symm.trans M.α := by
  have h : M.φ * M.σ * M.α = 1 := M.composition
  replace h := congr($h * M.α⁻¹ * M.σ⁻¹)
  rw [mul_inv_cancel_right, mul_inv_cancel_right, one_mul] at h
  rw [← M.involutive.symm_eq_self_of_involutive, h]
  rfl

end CombinatorialMap'
