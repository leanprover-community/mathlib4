import Lake

open Lake DSL

package mathlib where
  -- As mathlib does not produce an executable,
  -- we set the default "facet" to `oleans`,
  -- so that we can use `lake build`.
  defaultFacet := PackageFacet.oleans
