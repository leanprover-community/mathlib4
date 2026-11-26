import Lake

open Lake DSL

package "side-skimmer"

require "skimmer" from git "https://github.com/thorimur/skimmer" @ "v0.0.1+try-this"
require mathlib from ".." / ".."
