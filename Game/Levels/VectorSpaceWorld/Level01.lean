import Game.Metadata.Metadata

namespace LinearAlgebraGame

World "VectorSpaceWorld"
Level 1

Title "Welcome to Vector Space World!"

Introduction
"
## Welcome to Vector Space World!

In this world, you'll build up the basic theory of vector spaces through formal proofs in Lean.

### What You'll Learn

Vector spaces are fundamental structures in linear algebra. You will learn:

- **Vector Space Definition**: A vector space V over a field K with four key axioms
- **Zero Properties**: How multiplication by zero scalars and zero vectors behaves  
- **Inverse Operations**: Understanding scalar multiplication by -1
- **Subspaces**: Subsets of vector spaces that preserve vector space structure

### The Mathematical Foundation

We define a vector space `V` over a field `K` as an abelian group with four fundamental axioms:

- **Distributivity over vector addition:** `a • (x + y) = a • x + a • y`
- **Distributivity over scalar addition:** `(a + b) • x = a • x + b • x`  
- **Associativity:** `(a * b) • x = a • (b • x)`
- **Identity:** `1 • x = x`

In this game, `VectorSpace K V` is built on Mathlib's robust `Module K V` over a field, which provides standard mathematical notation and many helpful theorems.

### Getting Started

Note that to write the scalar multiplication symbol `•`, type `\\smul`.

This introductory level uses a trivial proof to get you comfortable with the interface. 

Ready to begin your journey into vector spaces? Let's prove our first statement!
"

Statement : True := by trivial

Conclusion 
"
Perfect! You've completed the introduction to Vector Space World.

In the next level, you'll dive into proving real theorems about vector spaces, starting with zero scalar multiplication.

Click 'Next Level' to continue!
"

end LinearAlgebraGame