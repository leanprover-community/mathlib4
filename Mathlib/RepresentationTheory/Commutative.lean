import Mathlib.RepresentationTheory.Character

namespace FDRep
variable {k G : Type u} [Field k] [CommMonoid G]


theorem existsUnique_smul_id_eq_of_simple [IsAlgClosed k] {V : FDRep k G} [Simple V] (f : V ⟶ V) :
    f.1.1.tr • 𝟙 V = f := by
  apply existsUnique_of_exists_of_uniq  ue
  · have : finrank k (V ⟶ V) = 1 := by
      rw[finrank_hom_simple_simple]; simp
    apply exists_smul_eq_of_finrank_eq_one this <| id_nonzero _
  · intro x y hx hy
    rw[← hy] at hx
    refine smul_left_injective k (x := 𝟙 V) ?_ hx
    exact id_nonzero V


open Module


def end_hom_of_commMonoid (g : G) {V : FDRep k G} : V ⟶ V := _ -- does this exist already

theorem finrank_eq_one_simple_of_commMonoid [IsAlgClosed k]
    {V : FDRep k G} [Simple V] : finrank k V = 1 := by
  have finrank_pos : 0 < finrank k V := by
    sorry
  rw[finrank_pos_iff_exists_ne_zero] at finrank_pos
  obtain ⟨x, ne⟩ := finrank_pos
  let W := ↥ (Submodule.span k {x})

  let rho : G →* W →ₗ[k] W := ⟨⟨fun g => (end_scalar_simple (V.ρ g)) • 𝟙 W, _⟩, _⟩





end FDRep
