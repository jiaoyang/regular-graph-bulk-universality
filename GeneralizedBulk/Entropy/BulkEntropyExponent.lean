import GeneralizedBulk.Entropy.UniformLocalEntropyRate
import GeneralizedBulk.Entropy.BulkNoiseRate
import GeneralizedBulk.Entropy.ChannelTotalRate

/-! A concrete positive mesoscopic height and final exponent compatible
with the actual channel, local comparison, and bulk-noise estimates. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace GeneralizedBulk.Entropy.ChannelRates

def entropyHeight (k d : ℕ) (rigidity : ℝ) : ℝ :=
  min (channelNoiseExponent (channelTheta k d)/2) (min (rigidity/2) (1/32))

theorem entropyHeight_bounds (k d : ℕ) (rigidity : ℝ) (hr : 0 < rigidity) :
    0 < entropyHeight k d rigidity ∧
    entropyHeight k d rigidity < channelNoiseExponent (channelTheta k d) ∧
    entropyHeight k d rigidity < rigidity ∧ entropyHeight k d rigidity ≤ 1/16 := by
  have hθ : 0 < channelNoiseExponent (channelTheta k d) := by
    unfold channelNoiseExponent
    exact div_pos (channelTheta_pos k d) (by norm_num)
  have hb1 := min_le_left (channelNoiseExponent (channelTheta k d)/2) (min (rigidity/2) (1/32 : ℝ))
  have hb2 := (min_le_right (channelNoiseExponent (channelTheta k d)/2) (min (rigidity/2) (1/32 : ℝ))).trans (min_le_left _ _)
  have hb3 := (min_le_right (channelNoiseExponent (channelTheta k d)/2) (min (rigidity/2) (1/32 : ℝ))).trans (min_le_right _ _)
  refine ⟨lt_min (by positivity) (lt_min (by positivity) (by norm_num)),?_,?_,?_⟩
  all_goals change _ at hb1 hb2 hb3; dsimp only [entropyHeight]; linarith

def bulkEntropyExponent (k d : ℕ) (rigidity localExponent height : ℝ) : ℝ :=
  min (channelTheta k d/4)
    (min (localComparisonExponent localExponent height/2) (bulkNoiseExponent rigidity height/4))

theorem bulkEntropyExponent_pos (k d : ℕ) (rigidity localExponent height : ℝ)
    (hl : 0 < localExponent) (hh : 0 < height) (hr : height < rigidity) (h1 : height < 1) :
    0 < bulkEntropyExponent k d rigidity localExponent height :=
  lt_min (div_pos (channelTheta_pos k d) (by norm_num))
    (lt_min (div_pos (localComparisonExponent_pos localExponent height hl hh) (by norm_num))
      (div_pos (bulkNoiseExponent_pos rigidity height hh hr h1) (by norm_num)))

def bulkEntropyError (k d : ℕ) (rigidity localExponent height : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)^(-channelTheta k d/2)+
    (1+(d : ℝ)/2)*(N : ℝ)^(-localComparisonExponent localExponent height)+
    (N : ℝ)^(-bulkNoiseExponent rigidity height/2)

theorem eventually_bulkEntropyError_polynomial (k d : ℕ) (rigidity localExponent height : ℝ)
    (hl : 0 < localExponent) (hh : 0 < height) (hr : height < rigidity) (h1 : height < 1) :
    ∀ᶠ N : ℕ in atTop,bulkEntropyError k d rigidity localExponent height N ≤
      (N : ℝ)^(-bulkEntropyExponent k d rigidity localExponent height) := by
  let γ := bulkEntropyExponent k d rigidity localExponent height
  have hγ : 0 < γ := bulkEntropyExponent_pos k d rigidity localExponent height hl hh hr h1
  have hθ : γ ≤ channelTheta k d/4 := min_le_left _ _
  have hloc : γ ≤ localComparisonExponent localExponent height/2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hbulk : γ ≤ bulkNoiseExponent rigidity height/4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hc := nat_rpow_bigO_mono (-channelTheta k d/2) (-2*γ) (by linarith only [hθ])
  have hs := (nat_rpow_bigO_mono (-localComparisonExponent localExponent height) (-2*γ)
    (by linarith only [hloc])).const_mul_left (1+(d : ℝ)/2)
  have hg := nat_rpow_bigO_mono (-bulkNoiseExponent rigidity height/2) (-2*γ) (by linarith only [hbulk])
  exact nat_rpow_bigO_eventually_le ((hc.add hs).add hg) (by linarith only [hγ])

end GeneralizedBulk.Entropy.ChannelRates
