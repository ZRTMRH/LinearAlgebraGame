# Linear Algebra Game

An interactive game that teaches linear algebra through theorem proving in [Lean 4](https://lean-lang.org/), built with the [lean4game](https://github.com/leanprover-community/lean4game) framework. Based on Sheldon Axler's *Linear Algebra Done Right*.

Developed at Duke University as part of a Duke MATH+ program led by Professor Colleen Robles. No advanced linear algebra prerequisite is required.

**Play now: [Linear Algebra Game](https://adam.math.hhu.de/#/g/zrtmrh/linearalgebragame)**

## Game Content

The game contains **43 levels** across 5 worlds, progressing from basic proof tactics to the triangle inequality:

| World | Levels | Topics | Highlight |
|-------|--------|--------|-----------|
| **Tutorial World** | 10 | Introduction to Lean 4 tactics (`rfl`, `rw`, `apply`, `intro`, `induction`, ...) | Proof by induction |
| **Vector Space World** | 5 | Scalar multiplication, additive inverses, subspaces | Negatives in a subspace |
| **Linear Independence & Span World** | 9 | Linear combinations, independence, span | span(S) = span(S \ {w}) when w is redundant |
| **Linear Maps World** | 11 | Linear transformations, kernel, range | Isomorphism iff injective and surjective |
| **Inner Product World** | 8 | Inner products, norms, Cauchy-Schwarz inequality | Triangle inequality |

## Building Locally

To run the game locally, see the lean4game documentation on [running locally](https://github.com/leanprover-community/lean4game/blob/main/doc/running_locally.md).

## Contributing

PRs and issues for typos, missing hints, or unclear explanations are welcome! Please open them at [Issues](https://github.com/ZRTMRH/LinearAlgebraGame/issues).

For more information about the project, see the [project page](https://sites.duke.edu/linearalgebragame/).

## Credits

**Duke University Mathematics Department**

- **Team:** Huiyu Chen, Adam Kern, Justin Morrill, and Letian Yang
- **Project Manager:** Daniel Zhou
- **Project Leader:** Colleen Robles
- **2023 Lean 3 Version:** Yannan Bai, Annapurna Bhattacharya, Chun-Hsien Hsu, Stavan Jain, Kurt Ma, Ricardo Prado Cunha, Anoushka Sinha (Project Manager: Chun-Hsien Hsu)
- **Game Engine:** [lean4game](https://github.com/leanprover-community/lean4game) by Alexander Bentkamp and Jon Eugster et al.
- **Cover Image:** Daniel Zhou, Nina Ma
