## Contributing

The complete documentation for contributing to ``mathlib`` is located
[on the community guide contribute to mathlib](https://leanprover-community.github.io/contribute/index.html)

You may want to subscribe to the `mathlib4` channel on [Zulip](https://leanprover.zulipchat.com/) to introduce yourself and your plan to the community.
Often you can find community members willing to help you get started and advise you on the fit and
feasibility of your project.

* To obtain precompiled `olean` files, run `lake exe cache get`. (Skipping this step means the next step will be very slow.)
* To build `mathlib4` run `lake build`.
* To build and run all tests, run `lake test`.
* You can use `lake build Mathlib.Import.Path` to build a particular file, e.g. `lake build Mathlib.Algebra.Group.Defs`.
* If you added a new file, run the following command to update `Mathlib.lean`

  ```shell
  lake exe mk_all
  ```

### Guidelines

Mathlib has the following guidelines and conventions that must be followed

 - The [style guide](https://leanprover-community.github.io/contribute/style.html)
 - A guide on the [naming convention](https://leanprover-community.github.io/contribute/naming.html)
 - The [documentation style](https://leanprover-community.github.io/contribute/doc.html)

### Downloading cached build files

You can run `lake exe cache get` to download cached build files that are computed by `mathlib4`'s automated workflow.

If something goes mysteriously wrong,
you can try one of `lake clean` or `rm -rf .lake` before trying `lake exe cache get` again.
In some circumstances you might try `lake exe cache get!`
which re-downloads cached build files even if they are available locally.

Call `lake exe cache` to see its help menu.

### Building HTML documentation

The [mathlib4_docs repository](https://github.com/leanprover-community/mathlib4_docs)
is responsible for generating and publishing the
[mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/index.html).

That repo can be used to build the docs locally:
```shell
git clone https://github.com/leanprover-community/mathlib4_docs.git
cd mathlib4_docs
cp ../mathlib4/lean-toolchain .
lake exe cache get
lake build Mathlib:docs
```
The last step may take a while (>20 minutes).
The HTML files can then be found in `.lake/build/doc`.
