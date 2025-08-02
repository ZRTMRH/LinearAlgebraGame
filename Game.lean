-- Test with minimal single world to reproduce finalizeExtensions deadlock
import Game.Levels.TutorialWorld
-- Other worlds disabled to isolate the issue
-- import Game.Levels.VectorSpaceWorld
-- import Game.Levels.LinearIndependenceSpanWorld
-- import Game.Levels.InnerProductWorld
-- import Game.Levels.LinearMapsWorld

Title "Linear Algebra Game"  
Introduction
"
# Welcome to the Linear Algebra Game!

**Note**: This is currently running with only TutorialWorld enabled due to deployment issues.

Click on \"Tutorial World\" to test if the levels load properly.

**Expected behavior**: 
- You should be able to click into Tutorial World 
- Then click on Level 1 to test the Lean server
- If it hangs with a blue loading circle, that's the finalizeExtensions bug we're trying to fix

The complete game with all worlds is available at: https://github.com/ZRTMRH/LinearAlgebraGame
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

-- No world imports to test if the issue is import-related
-- This should create an empty game that just displays the title screen
-- If this works, we can gradually add worlds back

namespace LinearAlgebraGame

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame

end LinearAlgebraGame
