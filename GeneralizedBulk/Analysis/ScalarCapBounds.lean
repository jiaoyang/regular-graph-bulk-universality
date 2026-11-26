import GeneralizedBulk.Analysis.LogarithmicCaps

/-! Explicit cap and bound functions for the physical scalar tail estimates. -/
noncomputable section
namespace GeneralizedBulk.Analysis

def affineScalarCap (a b B step : ℝ) (N : ℕ) : ℝ :=
  a+b*(B+step*(logarithmicCap N : ℝ))

def affineScalarMomentBound (a b B step : ℝ) (error : ℝ) (N q : ℕ) : ℝ :=
  (2 : ℝ)^(q-1)*((a+b*B)^q+b^q*step^q*(geometricMomentConstant q+
    2*error*(logarithmicCap N : ℝ)*(((logarithmicCap N+1 : ℕ) : ℝ)^q)))

def affineScalarMomentLimit (a b B step : ℝ) (q : ℕ) : ℝ :=
  (2 : ℝ)^(q-1)*((a+b*B)^q+b^q*step^q*geometricMomentConstant q)

end GeneralizedBulk.Analysis
