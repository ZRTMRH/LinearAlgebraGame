-- Bypass problematic imports that cause finalizeExtensions deadlock
-- Create minimal game configuration for Render deployment
-- import Game.Levels.TutorialWorld
-- import Game.Levels.VectorSpaceWorld
-- import Game.Levels.LinearIndependenceSpanWorld
-- import Game.Levels.InnerProductWorld
-- import Game.Levels.LinearMapsWorld

-- Minimal configuration to bypass finalizeExtensions deadlock on Render
Title "Linear Algebra Game - Deployment Test"
Introduction
"
# Linear Algebra Game - Render Deployment Test

This is a test deployment to resolve server initialization issues on Render.

The complete game with all levels is available at:
https://github.com/ZRTMRH/LinearAlgebraGame

**Issue**: The Lean server hangs during the finalizeExtensions phase in the Render 
cloud environment, preventing the game from loading properly.

**Next Steps**: Once the deployment infrastructure is stable, all worlds and levels 
will be re-enabled for the full educational experience.
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
