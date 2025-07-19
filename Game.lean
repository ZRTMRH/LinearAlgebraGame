import Game.Levels.TutorialWorld
import Game.Levels.VectorSpaceWorld
import Game.Levels.LinearIndependenceSpanWorld
import Game.Levels.InnerProductWorld
import Game.Levels.LinearMapsWorld
-- Explicit import for InnerProductSpace_v class and theorem aliases  
import Game.Levels.InnerProductWorld.LemmasAndDefs

-- Here's what we'll put on the title screen
Title "Linear Algebra Game"
Introduction
"
# Welcome to the Linear Algebra Game!

This game works as a learning tool for linear algebra,
based on the textbook \"Linear Algebra Done Right\" by Sheldon Axler. It also serves as an
introduction to Lean 4, a proof assistant that provides an environment to encode proofs formally.

Proofs in Lean can are written in precise syntax, using tactics and theorems, and can be algorithmically
checked for correctness by a computer.

This game covers many areas of linear algebra, including vector spaces, linear independence, bases,
linear mappings, and isomorphisms.

To start, click on \"Tutorial World\"
"

Info "
*Game version: 1.0*

## Progress saving

The game stores your progress in your local browser storage.
If you delete it, your progress will be lost!

Warning: In most browsers, deleting cookies will also clear the local storage
(or \"local site data\"). Make sure to download your game progress first!

## Credits

* **Team:** Huiyu Chen, Adam Kern, Justin Morrill, and Letian Yang
* **Project Manager:** Daniel Zhou
* **Project Leader:** Professor Colleen Robles
* **2023 Lean 3 Version:** Yannan Bai, Annapurna Bhattacharya, Chun-Hsien Hsu, Stavan Jain, Kurt Ma, Ricardo Prado Cunha, Anoushka Sinha (Project Manager: Chun-Hsien Hsu)
* **Game Engine:** Alexander Bentkamp, Jon Eugster, Patrick Massot
* **Inspiration:** Kevin Buzzard's Natural Number Game (https://adam.math.hhu.de/#/g/leanprover-community/nng4)
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

-- Dependency VectorSpaceWorld → LinearIndependenceSpanWorld

namespace LinearAlgebraGame

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame

end LinearAlgebraGame
