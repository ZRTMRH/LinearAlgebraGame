import Game.Levels.LinearMapsWorld.Level01
import Game.Levels.LinearMapsWorld.Level02
import Game.Levels.LinearMapsWorld.Level03
import Game.Levels.LinearMapsWorld.Level04
import Game.Levels.LinearMapsWorld.Level05
import Game.Levels.LinearMapsWorld.Level06
import Game.Levels.LinearMapsWorld.Level07
import Game.Levels.LinearMapsWorld.Level08
import Game.Levels.LinearMapsWorld.Level09
import Game.Levels.LinearMapsWorld.Level10
import Game.Levels.LinearMapsWorld.Level11

namespace LinearAlgebraGame

World "LinearMapsWorld"
Title "Linear Maps World"

Dependency LinearIndependenceSpanWorld → LinearMapsWorld

Introduction "
Welcome to Linear Maps World! This world will introduce you to formalizing proofs about linear maps
in Lean. This world includes proofs about null spaces and ranges, and about injective, surjective, and
bijective linear maps, for example a linear map is injective if and only if its null space contains only zero.
"

end LinearAlgebraGame
