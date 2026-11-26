import GaussianWave.BS.GaussianGramAlgebra
import GaussianWave.BS.GaussianRadialAsymptotic

/-!
# The computed determinant gains are the actual radial asymptotic sequences
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace GaussianWave.BS

def radialEnergy (m : ℕ) (x : ℝ) : ℝ := 2 * Real.sqrt (m + 1) * x

theorem abs_two_sqrt_mul_lt_add_one {q x : ℝ} (hq : 0 < q) (hx : |x| < 1) :
    |2 * Real.sqrt q * x| < q + 1 := by
  have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hsp := Real.sqrt_pos.mpr hq
  calc
    _ = (2 * Real.sqrt q) * |x| := by rw [abs_mul, abs_of_pos (mul_pos (by norm_num) hsp)]
    _ < 2 * Real.sqrt q := by nlinarith
    _ ≤ q + 1 := by nlinarith [sq_nonneg (Real.sqrt q - 1)]

theorem abs_radialEnergy_lt_degree (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    |radialEnergy m x| < (m + 2 : ℝ) := by
  have h := abs_two_sqrt_mul_lt_add_one (q := (m + 1 : ℝ)) (by positivity) hx
  simpa only [radialEnergy, add_assoc, one_add_one_eq_two] using h

theorem branchMeanEnergy_radial_profile (m k : ℕ) {x : ℝ} (hx : |x| < 1) (root parent : ℝ) :
    branchMeanEnergy (m + 1) (radialEnergy m x) k root parent =
      ∑ n ∈ Finset.range (k + 1),
        (radialChebyshev x n * root - radialChebyshevPrev x n / Real.sqrt (m + 1) * parent) ^ 2 := by
  rw [branchMeanEnergy_eq_profile_sum m k _ (abs_radialEnergy_lt_degree m hx)]
  apply Finset.sum_congr rfl
  intro n _
  exact branchMean_scaled_quadratic (by positivity : (0 : ℝ) < m + 1) x root parent n

theorem siblingVariance_radialEnergy (m : ℕ) (x : ℝ) :
    siblingVariance (m + 2) (radialEnergy m x) = radialInnovationVariance (m + 1) x := by
  have hs : Real.sqrt (m + 1 : ℝ) ^ 2 = (m + 1) := Real.sq_sqrt (by positivity)
  have he : (2 * Real.sqrt (m + 1 : ℝ) * x) ^ 2 = 4 * (m + 1) * x ^ 2 := by
    rw [mul_pow, mul_pow, hs]
    ring
  unfold siblingVariance radialEnergy radialInnovationVariance
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  rw [he, show (m : ℝ) + 2 - 1 = (m : ℝ) + 1 by ring]
  congr 2 <;> ring

theorem vertexRadialGain_radialEnergy (m k : ℕ) {x : ℝ} (hx : |x| < 1) :
    vertexRadialGain m k (radialEnergy m x) = radialVertexExceptional (m + 1) x k := by
  calc
    _ = 1 + (m + 2 : ℝ) * branchMeanEnergy (m + 1) (radialEnergy m x) k
        (radialEnergy m x / (m + 2)) 1 := by unfold vertexRadialGain branchMeanEnergy; ring
    _ = _ := by
      rw [branchMeanEnergy_radial_profile m k hx,
        radialVertexExceptional_branch_form (by positivity : (0 : ℝ) < m + 1)]
      simp only [mul_one, radialEnergy, add_assoc, one_add_one_eq_two]

theorem branchEnergy_root_radialEnergy (m k : ℕ) {x : ℝ} (hx : |x| < 1) :
    (branchEnergyCoefficients (m + 1) (radialEnergy m x) k).1 =
      ∑ n ∈ Finset.range (k + 1), radialChebyshev x n ^ 2 := by
  have h := branchMeanEnergy_radial_profile m k hx 1 0
  simpa only [branchMeanEnergy, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_one, mul_zero,
    add_zero, sub_zero] using h

theorem vertexContrastGain_radialEnergy (m k : ℕ) {x : ℝ} (hx : |x| < 1) :
    vertexContrastGain m k (radialEnergy m x) = radialBranchExceptional (m + 1) x k := by
  unfold vertexContrastGain radialBranchExceptional
  rw [siblingVariance_radialEnergy, branchEnergy_root_radialEnergy m k hx]

theorem edgePlusGain_radialEnergy (m k : ℕ) {x : ℝ} (hx : |x| < 1) :
    edgePlusGain m k (radialEnergy m x) = radialEdgePlusExceptional (m + 1) x k := by
  calc
    _ = (1 + radialEnergy m x / (m + 2)) * branchMeanEnergy (m + 1) (radialEnergy m x) k 1 1 := by
      unfold edgePlusGain branchMeanEnergy
      ring
    _ = _ := by
      rw [branchMeanEnergy_radial_profile m k hx]
      simp only [mul_one, radialEdgePlusExceptional, radialEnergy, add_assoc, one_add_one_eq_two]

theorem edgeMinusGain_radialEnergy (m k : ℕ) {x : ℝ} (hx : |x| < 1) :
    edgeMinusGain m k (radialEnergy m x) = radialEdgeMinusExceptional (m + 1) x k := by
  calc
    _ = (1 - radialEnergy m x / (m + 2)) * branchMeanEnergy (m + 1) (radialEnergy m x) k 1 (-1) := by
      unfold edgeMinusGain branchMeanEnergy
      ring
    _ = _ := by
      rw [branchMeanEnergy_radial_profile m k hx]
      simp only [mul_one, mul_neg_one, sub_neg_eq_add, radialEdgeMinusExceptional, radialEnergy,
        add_assoc, one_add_one_eq_two]

theorem exceptional_gain_log_balance_tendsto_zero (m : ℕ) (hm : 0 < m)
    {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun k => Real.log (vertexRadialGain m k (radialEnergy m x)) +
      (m + 1 : ℝ) * Real.log (vertexContrastGain m k (radialEnergy m x)) -
      (m + 2 : ℝ) / 2 *
        (Real.log (edgePlusGain m k (radialEnergy m x)) + Real.log (edgeMinusGain m k (radialEnergy m x))))
      atTop (𝓝 0) := by
  have hq : (1 : ℝ) < (m + 1 : ℝ) := by exact_mod_cast (by omega : 1 < m + 1)
  convert radial_exceptional_log_balance_tendsto_zero hq hx using 1
  ext k
  rw [vertexRadialGain_radialEnergy m k hx, vertexContrastGain_radialEnergy m k hx,
    edgePlusGain_radialEnergy m k hx, edgeMinusGain_radialEnergy m k hx]
  ring

end GaussianWave.BS
