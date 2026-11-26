import GeneralizedBulk.Entropy.ChannelRateTools

/-! Polynomial rate of the proved whole colored resolvent Gaussian entropy
error. Constants and the number of colors are fixed; the graph size varies. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace GeneralizedBulk.Entropy.ChannelRates

def bulkNoiseError (k A C rigidity height : ℝ) (N : ℕ) : ℝ :=
  k*((N : ℝ)^(-rigidity)/(N : ℝ)^(-height)+
    A/((N : ℝ)*(N : ℝ)^(-height))+C*(N : ℝ)^(-height))

def bulkNoiseExponent (rigidity height : ℝ) : ℝ :=
  min height (min (rigidity-height) (1-height))

theorem bulkNoiseExponent_pos (rigidity height : ℝ)
    (hh : 0 < height) (hr : height < rigidity) (h1 : height < 1) :
    0 < bulkNoiseExponent rigidity height :=
  lt_min hh (lt_min (sub_pos.mpr hr) (sub_pos.mpr h1))

set_option maxHeartbeats 1500000 in
theorem bulkNoiseError_bigO (k A C rigidity height : ℝ) :
    bulkNoiseError k A C rigidity height =O[atTop]
      fun N => (N : ℝ)^(-bulkNoiseExponent rigidity height) := by
  let β := bulkNoiseExponent rigidity height
  have hb₁ : β ≤ height := min_le_left _ _
  have hb₂ : β ≤ rigidity-height := (min_le_right _ _).trans (min_le_left _ _)
  have hb₃ : β ≤ 1-height := (min_le_right _ _).trans (min_le_right _ _)
  have h₁ := nat_rpow_bigO_mono (-rigidity+height) (-β) (by linarith)
  have h₂ := (nat_rpow_bigO_mono (height-1) (-β) (by linarith)).const_mul_left A
  have h₃ := (nat_rpow_bigO_mono (-height) (-β) (by linarith)).const_mul_left C
  apply ((h₁.add h₂).add h₃).const_mul_left k |>.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  unfold bulkNoiseError
  have hdiv : (N : ℝ)^(-rigidity)/(N : ℝ)^(-height) = (N : ℝ)^(-rigidity+height) := by
    rw [← Real.rpow_sub hn]
    congr 1
    ring
  have hden : (N : ℝ)*(N : ℝ)^(-height) = (N : ℝ)^(1-height) := by
    calc
      (N : ℝ)*(N : ℝ)^(-height) = (N : ℝ)^(1 : ℝ)*(N : ℝ)^(-height) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn]; congr 1
  rw [hdiv,hden,div_eq_mul_inv,← Real.rpow_neg hn.le]
  congr 2
  congr 1
  ring

theorem eventually_bulkNoiseError_polynomial (k A C rigidity height : ℝ)
    (hh : 0 < height) (hr : height < rigidity) (h1 : height < 1) :
    ∀ᶠ N : ℕ in atTop,bulkNoiseError k A C rigidity height N ≤
      (N : ℝ)^(-bulkNoiseExponent rigidity height/2) := by
  apply nat_rpow_bigO_eventually_le (bulkNoiseError_bigO k A C rigidity height)
  have h := bulkNoiseExponent_pos rigidity height hh hr h1
  linarith

end GeneralizedBulk.Entropy.ChannelRates
