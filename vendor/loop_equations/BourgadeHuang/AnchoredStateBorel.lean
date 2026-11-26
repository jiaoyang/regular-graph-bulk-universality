import BourgadeHuang.NevanlinnaState

/-! The Borel measurable structure on valid anchored counting states. -/
noncomputable section
open MeasureTheory
namespace BourgadeHuang

instance : BorelSpace AnchoredCountingState :=
  Subtype.borelSpace {p : LocalCountingMeasure × ℂ | ValidAnchoredCountingState p}

end BourgadeHuang
