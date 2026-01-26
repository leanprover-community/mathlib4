
/-!
# Infinite sums and products in topological fields

Lemmas on topological sums in rings with a strictly multiplicative norm, of which normed fields are
the most familiar examples.
-/

public section


section NormMulClass

variable {α E : Type*} [SeminormedCommRing E] [NormMulClass E] [NormOneClass E]
 {f : α → E} {x : E}

nonrec theorem HasProd.norm (hfx : HasProd f x) : HasProd (‖f ·‖) ‖x‖ := by
  simp only [HasProd, ← norm_prod]
  exact hfx.norm

theorem Multipliable.norm (hf : Multipliable f) : Multipliable (‖f ·‖) :=
  let ⟨x, hx⟩ := hf; ⟨‖x‖, hx.norm⟩

protected theorem Multipliable.norm_tprod (hf : Multipliable f) : ‖∏' i, f i‖ = ∏' i, ‖f i‖ :=
  hf.hasProd.norm.tprod_eq.symm

end NormMulClass
