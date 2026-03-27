import Game.Levels.LinearIndependenceSpanWorld.Level01
import Game.Levels.LinearIndependenceSpanWorld.Level02
import Game.Levels.LinearIndependenceSpanWorld.Level03
import Game.Levels.LinearIndependenceSpanWorld.Level04
import Game.Levels.LinearIndependenceSpanWorld.Level05
import Game.Levels.LinearIndependenceSpanWorld.Level06
import Game.Levels.LinearIndependenceSpanWorld.Level07
import Game.Levels.LinearIndependenceSpanWorld.Level08
import Game.Levels.LinearIndependenceSpanWorld.Level09

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Title "Linear Independence and Span World"


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

The real mathematical journey begins with linear combinations - let's get started!
"

end LinearAlgebraGame
