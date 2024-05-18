import Mathlib.RingTheory.RingOfDefinition

namespace Algebra

namespace RingOfDefinition

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]
variable (f : R →+* S)

section

variable (I : Ideal R) (J : Ideal S)
variable (A : Set R) (B : Set S)

section

variable {f A B}

noncomputable def setMap (h : Set.MapsTo f A B) : MvPolynomial A R →+* MvPolynomial B S :=
  RingHom.comp (MvPolynomial.rename h.restrict).toRingHom (MvPolynomial.map f)

@[simp]
lemma setMap_apply (h : Set.MapsTo f A B) (p : MvPolynomial A R) :
    setMap h p = MvPolynomial.rename h.restrict (MvPolynomial.map f p) :=
  rfl

lemma MvPolynomial.isHomogeneous_of_setMap (h : Set.MapsTo f A B) (hinj : Function.Injective f)
    (p : MvPolynomial A R) {n : ℕ} (homog : MvPolynomial.IsHomogeneous (setMap h p) n) :
    MvPolynomial.IsHomogeneous p n := by
  simp only [setMap_apply] at homog
  have h1 : Function.Injective h.restrict := by
    rw [Set.MapsTo.restrict_inj]
    apply Set.injOn_of_injective hinj
  rw [MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff h1] at homog
  apply MvPolynomial.isHomogeneous_of_map f hinj
  exact homog

variable (hf : Set.MapsTo f A B)

lemma diag_rename_comm :
    f.comp (MvPolynomial.eval Subtype.val)
    = (MvPolynomial.eval Subtype.val).comp
      ((MvPolynomial.map f).comp (MvPolynomial.rename hf.restrict).toRingHom) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro a
    simp

lemma diag_rename_comm_apply (p : MvPolynomial A R) :
    f ((MvPolynomial.eval Subtype.val) p) =
      (MvPolynomial.eval Subtype.val) ((MvPolynomial.map f) (MvPolynomial.rename hf.restrict p)) := by
  change (f.comp (MvPolynomial.eval Subtype.val)) p
    = ((MvPolynomial.eval Subtype.val).comp
      ((MvPolynomial.map f).comp (MvPolynomial.rename hf.restrict).toRingHom)) p
  rw [diag_rename_comm]

end

end

variable {f}
variable {ι : Type*} {A : Set (MvPolynomial ι R)} {B : Set (MvPolynomial ι S)}
variable (h : Set.MapsTo (MvPolynomial.map f) A B)

variable (p : MvPolynomial B (MvPolynomial ι S))
variable (coeffs : MvPolynomial.Set.coefficients (MvPolynomial.coefficients p) ⊆ Set.range f)
variable (coeffsB : MvPolynomial.Set.coefficients B ⊆ Set.range f)

lemma setMap_exists_repr (hpreim : MvPolynomial.map f ⁻¹' B = A) (hfinj : Function.Injective f) :
    ∃ q : MvPolynomial A (MvPolynomial ι R),
    setMap h q = p := by
  have hc : MvPolynomial.coefficients p ⊆ Set.range (MvPolynomial.map f) := by
    intro r hr
    apply RingOfDefinition.exists_preimage_of_coefficients' f r
    apply Set.Subset.trans ?_ coeffs
    apply MvPolynomial.Set.coefficients_in
    exact hr
  obtain ⟨q', hq'⟩ := RingOfDefinition.exists_preimage_of_coefficients' (MvPolynomial.map f) p hc
  have hresinj : Function.Injective h.restrict := by
    rw [Set.MapsTo.restrict_inj]
    apply Set.injOn_of_injective
    exact MvPolynomial.map_injective f hfinj
  have hressurj : Function.Surjective h.restrict := by
    intro ⟨p, hp⟩
    have : MvPolynomial.coefficients p ⊆ Set.range f := by
      intro r hr
      have h1 := MvPolynomial.Set.coefficients_in B p hp hr
      have h2 := coeffsB h1
      exact h2
    obtain ⟨p', hp'⟩ :=
      RingOfDefinition.exists_preimage_of_coefficients' f
      p
      this
    have : p' ∈ A := by
      rw [← hpreim]
      change (MvPolynomial.map f) p' ∈ B
      rw [hp']
      exact hp
    use ⟨p', this⟩
    apply Subtype.ext
    simpa
  let g : A ≃ B := Equiv.ofBijective h.restrict ⟨hresinj, hressurj⟩
  let q : MvPolynomial A (MvPolynomial ι R) := MvPolynomial.rename g.symm q'
  use q
  have : (MvPolynomial.rename h.restrict) q = q' := by
    simp only [MvPolynomial.rename_rename, q]
    change MvPolynomial.rename (g ∘ g.symm) q' = q'
    simp
  simp only [setMap_apply, q, MvPolynomial.map_rename, MvPolynomial.rename_rename]
  change MvPolynomial.rename (g ∘ g.symm) _ = _
  simpa

noncomputable def setMapRepr (hpreim : MvPolynomial.map f ⁻¹' B = A) (hfinj : Function.Injective f) :
    MvPolynomial A (MvPolynomial ι R) :=
  (setMap_exists_repr h p coeffs coeffsB hpreim hfinj).choose

lemma setMap_mapRepr (hpreim : MvPolynomial.map f ⁻¹' B = A) (hfinj : Function.Injective f) :
    setMap h (setMapRepr h p coeffs coeffsB hpreim hfinj) = p :=
  Exists.choose_spec (setMap_exists_repr h p coeffs coeffsB hpreim hfinj)

lemma setMapRepr_homog (hpreim : MvPolynomial.map f ⁻¹' B = A) {n : ℕ} (hfinj : Function.Injective f)
    (homog : MvPolynomial.IsHomogeneous p n) :
    MvPolynomial.IsHomogeneous (setMapRepr h p coeffs coeffsB hpreim hfinj) n := by
  apply MvPolynomial.isHomogeneous_of_setMap h
  · apply MvPolynomial.map_injective f hfinj
  · rwa [setMap_mapRepr]

@[simp]
lemma setMapRepr_eval (hpreim : MvPolynomial.map f ⁻¹' B = A) (hfinj : Function.Injective f) :
    MvPolynomial.map f (MvPolynomial.eval Subtype.val (setMapRepr h p coeffs coeffsB hpreim hfinj))
      = MvPolynomial.eval Subtype.val p := by
  rw [diag_rename_comm_apply h, MvPolynomial.map_rename, ← setMap_apply, setMap_mapRepr]
