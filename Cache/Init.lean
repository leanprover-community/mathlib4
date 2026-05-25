/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

namespace Cache.Requests

open System (FilePath)

-- Cloudflare cache may be flaky: https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/The.20cache.20doesn't.20work/near/411058849
-- This is defined in a separate file because it is used in the definition of `URL` and `UPLOAD_URL`
-- and Lean does not allow one `initialize` to use another `initialize` defined in the same file
initialize useCloudflareCache : Bool ← do
  let cache ← IO.getEnv "MATHLIB_CACHE_USE_CLOUDFLARE"
  return cache == some "1" || cache == some "true"
