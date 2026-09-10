# The affine Tverberg theorem in Lean

This project provides a computer-checked proof of the main theorem of
*The affine Tverberg theorem revisited* by Sergey Avvakumov and Roman Karasev.
The proof is formalized in Lean 4 using the mathlib mathematical library.

Informally, the theorem guarantees that when an appropriate higher-dimensional
shape is mapped into lower-dimensional space, several pairwise disjoint faces
on its boundary have images that all meet at a common point.

The completed Lean theorem is

```lean
AffineTverberg.mainTheorem : AffineTverberg.mainTheoremStatement
```

Its [statement and definitions](AffineTverberg/MainTheorem.lean) are separate
from the [final proof](AffineTverberg/MainTheoremProof.lean).

## Mathematical scope

Let `d >= 1` and `N = (d + 1) * (r - 1)`.

- **Polytopes, every `r >= 2`:** an affine map from a full-dimensional convex
  `N`-polytope to real `d`-space has `r` pairwise disjoint proper faces whose
  images have a common point.
- **Simplicial balls, every `r >= 3`:** a continuous map from a finite pure
  geometric simplicial `N`-ball to real `d`-space, affine on every simplex,
  has `r` pairwise disjoint boundary faces whose images have a common point.

The simplicial ball is assumed homeomorphic to the closed `N`-ball; no PL,
shellability, prime-power, or additional link-homology hypothesis is imposed.
The separately cited **`r = 2` simplicial-ball case is deliberately excluded**.
The Lean statement also explicitly assumes continuity in the polytopal case.

## Versions

- Lean: `leanprover/lean4:v4.34.0-rc2`.
- Mathlib: `v4.34.0-rc2`, commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`.

The toolchain and dependency revisions are pinned in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`.
Do not run `lake update` when reproducing this pinned version.

## Independently verify the proof

Install Git and Lean following [the official Lean installation instructions](https://lean-lang.org/install/manual/).
Download or clone this repository and open a terminal in its root directory
(the directory containing `lakefile.toml`). No separate verification script
is needed.

### 1. Build the project

Run:

```text
lake exe cache get
lake build
```

The first command downloads precompiled mathlib dependencies. The second checks
the project sources and should finish with `Build completed successfully`
(possibly followed by a job count), with no errors or warnings. The first build
of the project can take time; subsequent builds reuse unchanged compiled files.

### 2. Check the exact theorem and its axioms

Create a file named `Check.lean` in the repository's root directory containing
these Lean commands:

```lean
import AffineTverberg.MainTheoremProof

example : AffineTverberg.mainTheoremStatement :=
  AffineTverberg.mainTheorem

#check AffineTverberg.mainTheorem
#print axioms AffineTverberg.mainTheorem
```

Then run:

```text
lake env lean Check.lean
```

The expected output is:

```text
AffineTverberg.mainTheorem : AffineTverberg.mainTheoremStatement
'AffineTverberg.mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All commands must finish successfully, with no errors or warnings.
The `example` produces no output when it succeeds: it checks that the supplied
proof has exactly the type `mainTheoremStatement`. The `#check` command displays
that type. The `#print axioms` command reports the axioms used throughout the
theorem's proof dependencies, not just those mentioned in the final proof file.

The three listed axioms are Lean's standard propositional extensionality,
classical choice, and quotient soundness. There must be no `sorryAx` (an unproved
placeholder) and no additional axiom. A successful build alone is not enough:
the theorem check and axiom report above are also required.

### 3. Inspect what was proved

Read [MainTheorem.lean](AffineTverberg/MainTheorem.lean), which defines
`mainTheoremStatement` and the geometric notions it uses. This confirms that the
formal proposition expresses the intended mathematical theorem, with the scope
described above. Lean verifies the proof of that precise proposition; matching
the formal definitions to the paper is a separate mathematical review.

The repository's GitHub Actions workflow builds the project and checks the same
main theorem and expected axiom report. The result is visible in the **Actions**
tab. The commands above allow readers to reproduce the check themselves.

## Development

The development used AI-assisted proof generation, including Aristotle. The
resulting proof is checked by Lean and is available for independent inspection.
This project does not claim to formalize every auxiliary paper lemma separately
in its most general form.
