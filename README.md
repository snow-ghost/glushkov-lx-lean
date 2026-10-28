# Glushkov's L/X problem: exact diameter in Lean 4

**Authors: S. Uskov, A. Chervov, F. Levkovich-Maslyuk, I. Litvak, A. Smolensky.** [Authorship](AUTHORS.md) · [Русский](README.ru.md)
S. Uskov — ORCID: [0009-0006-5845-7013](https://orcid.org/0009-0006-5845-7013).

This repository formalizes the exact **directed** diameter of the symmetric
group Sₙ with two generators: L, a cyclic shift, and X, the transposition of the
first two positions. Each letter costs one move. This is the problem recorded
in [OEIS A039745](https://oeis.org/A039745).

For every integer n ≥ 5:

| n | Diameter D(n) |
|---|---|
| Odd | (3n² − 8n + 9) / 4 |
| Even | (3n² − 8n + 12) / 4 |

Both upper and lower bounds are formalized. The main theorem has no additional
combinatorial hypotheses. `NeZero n` is the typeclass required to define the
cyclic generators and follows from n ≥ 5.

## Main theorem

[`LX.exact_diameter_all`](LX/SharpDiameterAll.lean):

```lean
import LX.SharpDiameterAll

example (n : ℕ) [NeZero n] (hn : 5 ≤ n) :
    (LX.diameter n : ℚ) =
      (3 * (n : ℚ)^2 - 8 * n + 12 - 3 * ((n % 2 : ℕ) : ℚ)) / 4 :=
  LX.exact_diameter_all n hn
```

The formula uses rational arithmetic; subtraction is not truncated natural-number
subtraction. [`LX.WordMetric`](LX/WordMetric.lean) defines the actual minimum
word length and diameter. Reachability is proved, and
`LX.diameter_eq_max_dist` identifies the diameter with the maximum directed
distance over all ordered pairs of vertices.

| Result | Lean declaration |
|---|---|
| Exact diameter for all n ≥ 5 | `LX.exact_diameter_all` |
| Same equality multiplied by 4, over integers | `LX.exact_diameter_all_int` |
| Exact odd formula | `LX.odd_diameter_conjecture` |
| Exact even formula | `LX.even_diameter_conjecture` |
| Word within the sharp bound for every permutation | `LX.sharp_word_all` |
| Word within the sharp bound between any two vertices | `LX.sharp_route_all` |

The word existence proofs use classical reasoning. This repository does not
provide an executable shortest-word solver.

## Reproduce the verification

Install [Elan](https://github.com/leanprover/elan), Git, and the usual Lean build
prerequisites. Then:

```sh
git clone https://github.com/snow-ghost/glushkov-lx-lean.git
cd glushkov-lx-lean
lake exe cache get
lake build LX
lake env lean VerifyLXExact.lean
```

The toolchain is pinned to **Lean 4.34.0**. Mathlib is pinned to commit
`5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0); all dependency revisions
are recorded in `lake-manifest.json`. The cache command downloads Mathlib
artifacts. The build checks this repository's local proof sources.

[`VerifyLXExact.lean`](VerifyLXExact.lean) checks the full public theorem types
and audits every project theorem in the main theorem's transitive import closure.
It fails if a theorem uses an axiom outside:

- `propext`
- `Classical.choice`
- `Quot.sound`

In particular, the audit rejects `sorryAx` and nonstandard postulated axioms.
The [verification workflow](.github/workflows/lean.yml) runs the build and audit
on pushes and pull requests. Its actual status is shown in the repository's
Actions tab.

## Proof structure

- [`EvenConjecture`](LX/EvenConjecture.lean): the even upper bound.
- [`OddConjecture`](LX/OddConjecture.lean): the odd upper bound.
- [`ConjectureLower`](LX/ConjectureLower.lean): matching lower bounds.
- [`SharpDiameterAll`](LX/SharpDiameterAll.lean): the combined theorem and routing.

All 310 proof modules are in `LX/`, built as one Lean library. The shared
permutation, lift, and finite-window machinery uses the namespace `LX.Core`;
the directed L/X metric and diameter theorems use `LX`. The symmetric
word machinery is in [`SymmetricWordMetric`](LX/SymmetricWordMetric.lean),
and the directed metric is in [`WordMetric`](LX/WordMetric.lean).

The source set is restricted to dependencies of the public diameter and
routing results. Unused bound specifications, certificates, and auxiliary
proofs have been removed, including references used only by `#print axioms`.
Seven definitional simplification lemmas are retained because the proof sources
refer to them, even though their applications disappear from the compiled
proof terms. All other remaining source declarations occur in the dependency
closure of the public results, including private helper declarations.
The public diameter and routing statements are unchanged.

## Citation and license

Please cite **S. Uskov, A. Chervov, F. Levkovich-Maslyuk, I. Litvak, A. Smolensky, _Glushkov's L/X problem: exact directed diameter of
the symmetric group in Lean 4_** and link to this repository, preferably with
a commit. GitHub's “Cite this repository” button uses
[`CITATION.cff`](CITATION.cff).

The project is licensed under [MIT](LICENSE). Retain the copyright and
permission notices when redistributing the code. See [authorship](AUTHORS.md).
