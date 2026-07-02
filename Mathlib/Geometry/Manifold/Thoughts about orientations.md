## Thoughts about orientations

- intuition/textbook definition: an orientation on a manifold `M` (with an implicitly given atlas `𝓐`)
  is a choice of basis of each tangent space `T_pM` such that, for each chart `(φ, U)` in the atlas, each induced basis of T_x M (for `x ∈ U`) has the same sign
  (i.e., either matches our chosen standard basis, or dismatches it).

In Lean, it's nicer to not choose

- an orientation on a manifold M (with a fixed atlas A) is a choice of sign ε x at each point,
  such that for each chart `(φ, U)` in the atlas, each induced basis of T_x M (for `x ∈ U`)
  has the same sign




   (or: each preferred chart?=)all charts in the atlas, the sign of the
  \ep
  is a
