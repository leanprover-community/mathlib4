import Mathlib.All
import Mathlib.Extras

/-!
# `Mathlib.lean` imports `Mathlib/All.lean` and `Mathlib/Extras.lean`.

`Mathlib/All.lean` imports everything *except* the `Extras/` directory,
`Extras.lean`, and `All.lean` itself.
This allows us to do some "post-processing" tasks in `Extras/`,
importing all the rest of the content of mathlib.
`Mathlib/Extras.lean` imports everything in the `Extras/` directory.
-/
