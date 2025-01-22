import Mathlib
import Mathlib.RingTheory.EGA48.IsDirectLimit

section

noncomputable
def AlgHom.liftOfSurjective {R A B C : Type*} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (g : A →ₐ[R] C) (hker : RingHom.ker f ≤ RingHom.ker g) :
    B →ₐ[R] C where
  __ := RingHom.liftOfSurjective (f : A →+* B) hf ⟨(g : A →+* C), hker⟩
  commutes' r := by
    rw [← f.map_algebraMap]
    dsimp
    erw [RingHom.liftOfRightInverse_comp_apply]
    simp

@[simp]
lemma AlgHom.liftOfSurjective_comp_apply {R A B C : Type*} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (g : A →ₐ[R] C) (hker : RingHom.ker f ≤ RingHom.ker g)
    (x : A) :
    f.liftOfSurjective hf g hker (f x) = g x := by
  apply RingHom.liftOfRightInverse_comp_apply

end

variable {ι E G L : Type*} [Preorder ι]
  {F : ι → Type*} [CommRing E] [CommRing L] [Algebra E L]
  [∀ i, CommRing (F i)]
  [∀ i, Algebra E (F i)]
  (g : ∀ ⦃i j⦄, i ≤ j → F i →ₐ[E] F j)
  (f : ∀ i, F i →ₐ[E] L)
  [DirectedSystem F (@g · · ·)]
  (hg : IsDirectLimit (@g · · ·) (f ·))
  [CommRing G] [Algebra E G]

include hg

lemma Algebra.FiniteType.exists_ge_ge_comp_eq_comp [Nonempty ι]
    [Algebra.FiniteType E G]
    {i : ι} (a : G →ₐ[E] F i)
    {j : ι} (b : G →ₐ[E] F j)
    (hab : (f i).comp a = (f j).comp b) :
    ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
      (g hik).comp a = (g hjk).comp b := by
  classical
  obtain ⟨s, hs⟩ := ‹Algebra.FiniteType E G›
  have : IsDirected ι (· ≤ ·) := by
    constructor
    intro a b
    simpa using hg.exists_of_eq (i := a) (j := b) 0 0 (by simp)
  have (x : G) : ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
      g hik (a x) = g hjk (b x) := by
    apply hg.exists_of_eq
    exact DFunLike.congr_fun hab x
  choose k hik hjk heq using this
  obtain ⟨m, hm⟩ := (s.image k).exists_le
  cases' s.eq_empty_or_nonempty with h hs
  · subst h
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    use k, hik, hjk
    apply AlgHom.ext_of_adjoin_eq_top hs
    simp
  obtain ⟨x, hx⟩ := hs
  simp at hm
  have := hm x hx
  refine ⟨m, ?_, ?_, ?_⟩
  · apply le_trans (hik x) this
  · apply le_trans (hjk x) this
  · apply AlgHom.ext_of_adjoin_eq_top hs
    intro y hy
    simp only [AlgHom.coe_comp, Function.comp_apply]
    rw [← DirectedSystem.map_map (f := (@g · · ·)) (hik y) (hm y hy) (a y)]
    rw [← DirectedSystem.map_map (f := (@g · · ·)) (hjk y) (hm y hy) (b y)]
    rw [heq]

open MvPolynomial
lemma Algebra.FinitePresentation.exists_lift [Nonempty ι] [Algebra.FinitePresentation E G]
    (a : G →ₐ[E] L) :
    ∃ (k : ι) (b : G →ₐ[E] F k), (f k).comp b = a := by
  classical
  obtain ⟨I, _, B, hB, hBG⟩ :=
    Algebra.FinitePresentation.iff_quotient_mvPolynomial'.{_, _, 0}.mp
      ‹Algebra.FinitePresentation E G›
  obtain ⟨n, u, hu⟩ := hBG.exists_fun
  have : IsDirected ι (· ≤ ·) := by
    constructor
    intro a b
    simpa using hg.exists_of_eq (i := a) (j := b) 0 0 (by simp)
  choose k y hy using hg.jointly_surjective
  obtain ⟨m, hm⟩ := (Finset.univ.image (k ∘ a ∘ B ∘ MvPolynomial.X)).exists_le
  simp at hm
  have (i : Fin n) :
      f m (MvPolynomial.aeval (fun j ↦ g (hm j) (y <| a (B (X j)))) (u i)) = f m 0 := by
    rw [MvPolynomial.comp_aeval_apply]
    simp_rw [hg.naturality, hy]
    rw [← MvPolynomial.comp_aeval_apply]
    rw [← MvPolynomial.comp_aeval_apply]
    simp only [aeval_eq_bind₁, bind₁_X_left, AlgHom.coe_id, id_eq, map_zero]
    have : u i ∈ RingHom.ker B := hu.ge <| Ideal.subset_span ⟨i, rfl⟩
    simp only [RingHom.mem_ker] at this
    simp only [this, map_zero]
  choose l hml _ hl using fun i ↦ hg.exists_of_eq _ _ (this i)
  obtain ⟨l', hl'⟩ := (Finset.univ.image l).exists_le
  obtain ⟨l'', hml'', hll''⟩ := exists_ge_ge m l'
  refine ⟨l'', ?_, ?_⟩
  · apply AlgHom.liftOfSurjective B hB
      (MvPolynomial.aeval (fun j ↦ g ((hm j).trans hml'') (y <| a (B (X j)))))
    erw [hu]
    rw [Ideal.span_le]
    rintro p ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    simp_rw [← DirectedSystem.map_map (f := (@g · · ·)) (hm _) hml'']
    rw [← MvPolynomial.comp_aeval_apply]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff] at hl'
    rw [← DirectedSystem.map_map (f := (@g · · ·)) (hml i) ((hl' i).trans hll''), hl i]
    simp
  · ext x
    obtain ⟨x, rfl⟩ := hB x
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.liftOfSurjective_comp_apply]
    rw [MvPolynomial.comp_aeval_apply]
    simp_rw [hg.naturality, hy]
    rw [← MvPolynomial.comp_aeval_apply]
    rw [← MvPolynomial.comp_aeval_apply]
    simp
