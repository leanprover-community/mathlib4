# The `build` benchmark

This benchmark executes a complete build and collects global and per-module metrics.

The following metrics are collected by a wrapper around the entire build process:

- `build//instructions`
- `build//maxrss`
- `build//task-clock`
- `build//wall-clock`

The following metrics are collected from `lean --profile` and summed across all modules:

- `build/profile/<name>//wall-clock`

The following metrics are collected from `lakeprof report`:

- `build/lakeprof/longest build path//wall-clock`
- `build/lakeprof/longest rebuild path//wall-clock`

The following metrics are collected from a combination of `lakeprof report` and the per-module instructions:

- `build/lakeprof/longest build path//instructions`
- `build/lakeprof/longest rebuild path//instructions`

The following metrics are collected individually for each module:

- `build/module/<name>//lines`
- `build/module/<name>//instructions`

If the `LAKEPROF_UPLOAD_URL` environment variable is set,
the lakeprof report will be uploaded to that URL prefix once the benchmark run concludes.
