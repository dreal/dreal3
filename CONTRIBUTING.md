How to contribute to dReal
===================================

Did you find a bug?
-------------------

* **Ensure the bug was not already reported** by searching on GitHub under [Issues](https://github.com/dreal/dreal3/issues).

* If you're unable to find an open issue addressing the problem, [open a new one](https://github.com/dreal/dreal3/issues/new). Be sure to include a **title and clear description**, as much relevant information as possible including:

 - dReal version (output of `dReal --version`)
 - `smt2` or `drh` files with the expected behavior that is not occurring (i.e. `delta-sat` / `unsat`).
 - Environment including OS and Compiler (for example, `OS X 10.11.4` + `clang-3.6.2`)

Did you write code adding a new feature or fixing a bug?
---------------------------------------------------------

* [Rebase your commits based on master branch][git-rebase] of dreal/dreal3 repository.

* Follow our [Git commit message convention][git-commit-msg-convention].

* Follow [Google C++ Style Guide](https://google.github.io/styleguide/cppguide.html). Run `make style` and check there is no style error.

* Run `make` and check the code compiles. Please try both of [gcc](https://gcc.gnu.org/) and [clang](http://clang.llvm.org/).

* Open a [new GitHub pull request](https://github.com/dreal/dreal3/pull/new/master) with the commits.

* Ensure the PR description clearly describes the problem and solution. Include the relevant issue number if applicable.

[git-rebase]: https://robots.thoughtbot.com/git-interactive-rebase-squash-amend-rewriting-history
[git-commit-msg-convention]: https://github.com/dreal/dreal3/blob/master/doc/commit_convention.md
