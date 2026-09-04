/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Requests

/-!
# Per-SHA cache markers

A marker is a tiny blob at `/m/{repo}/{sha}` whose existence signals that the
full `.ltar` upload for a commit completed. `cache put` writes it as the last
upload step, and `cache query` probes it to discover cached commits with a
cheap HEAD request instead of a blob listing.
-/

namespace Cache.Requests

open System (FilePath)

/--
Read-side URL for the per-SHA marker blob: probes follow the read base
(`Container.getURL`), unlike marker writes, which follow the resolved
upload destination (`StagedUploadDest.markerURL`).
-/
def markerReadURL (container : Container) (repo sha : String) : IO String := do
  return s!"{← container.getURL}/{markerPath repo sha}"

end Cache.Requests
