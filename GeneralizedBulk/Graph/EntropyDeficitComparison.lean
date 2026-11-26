import Mathlib

/-! Combining the actual channel inequality, local entropy comparisons,
and the evaluated global Gaussian baseline. -/
noncomputable section
namespace GeneralizedBulk.Entropy

theorem entropy_deficit_of_channel_comparisons
    (d global star edge idealStar idealEdge jacobian baseline deficit : ℝ)
    (channelError starError edgeError globalError : ℝ) (hd : 0 ≤ d)
    (hchannel : global ≤ star-d/2*edge+channelError)
    (hstar : |star-(idealStar-jacobian)| ≤ starError)
    (hedge : |edge-idealEdge| ≤ edgeError)
    (hglobal : |global-baseline| ≤ globalError)
    (hcancel : idealStar-d/2*idealEdge-jacobian=baseline-deficit) :
    deficit ≤ channelError+starError+d/2*edgeError+globalError := by
  have hs := (abs_le.mp hstar).2
  have he := mul_le_mul_of_nonneg_left (abs_le.mp hedge).1 (div_nonneg hd (by norm_num : (0:ℝ)≤2))
  have hg := (abs_le.mp hglobal).1
  nlinarith only [hchannel,hs,he,hg,hcancel]

end GeneralizedBulk.Entropy
