import Game.Levels.VectorSpaceWorld.Level06

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Level 1

Title "Welcome to Linear Independence and Span World!"

Introduction
"
## Welcome to Linear Independence and Span World!

This world introduces the fundamental concepts of linear independence, linear dependence, and the span of a set of vectors.

### What You'll Learn

Linear independence and span are central concepts in linear algebra that help us understand:

- **Linear Combinations**: How to express vectors as sums of scaled vectors
- **Linear Independence**: When vectors don't depend on each other
- **Linear Dependence**: When one vector can be written in terms of others  
- **Span**: The set of all possible linear combinations of a given set
- **Bases and Dimensions**: Minimal spanning sets and vector space structure

### Mathematical Foundation

A **linear combination** of vectors v₁, v₂, ..., vₙ is any expression of the form:
```
a₁ • v₁ + a₂ • v₂ + ... + aₙ • vₙ
```
where a₁, a₂, ..., aₙ are scalars from the field K.

A set of vectors is **linearly independent** if the only way to make a linear combination equal zero is by setting all coefficients to zero.

The **span** of a set S is the collection of all possible linear combinations of vectors from S.

### What Makes This World Challenging

The proofs in this world are more sophisticated than previous worlds. You'll work with:
- Set theory and subset relationships
- Existential and universal quantifiers  
- Proof by cases and contradiction
- Complex logical structures

### Getting Started

This introductory level uses a simple proof to prepare you for the mathematical rigor ahead.

The real mathematical journey begins in Level 2 with linear combinations!
"

Statement : True := by trivial

Conclusion 
"
Excellent! You're ready to tackle the challenging world of linear independence and span.

In Level 2, you'll dive into the formal definition of linear combinations and prove your first theorem about them.

The mathematical adventure begins now - click 'Next Level'!
"

end LinearAlgebraGame