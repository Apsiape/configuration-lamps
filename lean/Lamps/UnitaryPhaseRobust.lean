import Lamps.UnitaryProjMain
import Lamps.SharpPair

/-!
# `UnitaryPhaseRobust`, unconditionally

Assembled from the sharp pair entropy estimate (`sharpPairEntropy`) and the two projection
estimates (`unitaryAhatProj`, `unitaryBhatProj`) via `unitaryPhaseRobust_of_proj`.
-/

namespace Lamps

theorem unitaryPhaseRobust : UnitaryPhaseRobust :=
  unitaryPhaseRobust_of_proj sharpPairEntropy unitaryAhatProj unitaryBhatProj

end Lamps
