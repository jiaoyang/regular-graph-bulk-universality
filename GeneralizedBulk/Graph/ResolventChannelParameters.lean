import GeneralizedBulk.Graph.ColoredResolventNoise
import GeneralizedBulk.Graph.GaussianChannelPolynomial
import GeneralizedBulk.Graph.EmpiricalSignalBounds

/-! Actual resolvent covariance and HY eigenvector signals satisfy the
numeric polynomial-channel regime at every sufficiently small fixed height
exponent. The estimates are uniform in all admissible channel selections. -/
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped BigOperators Topology Classical Matrix.L2OpNorm

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy GeneralizedBulk.Entropy.ChannelRates

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2000000 in
theorem colored_resolvent_channel_bounds_eventually {k : ℕ} (θ c0 : ℝ)
    (hc0 : 0 < c0) (hsmall : c0 < channelNoiseExponent θ) (s S : ℝ) (hs : 0 < s) (hS : 0 < S) :
    ∀ᶠ n in atTop,∀ ω (E sigma : Fin k → ℝ) (hsigma : ∀ a,s ≤ sigma a ∧ sigma a ≤ S) (hE : ∀ a,|E a| ≤ d),
      let eta := (N n : ℝ)^(-c0)
      let A := D.coloredResolventCovarianceFactor n ω E eta sigma
      ‖A*A.transpose‖ ≤ channelNoiseBound θ (N n) ∧
        ∀ x : Fin k × Fin (N n) → ℝ,channelCovarianceFloor θ (N n)*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x) := by
  let B : ℝ := S*((2*(d : ℝ))^2+1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hpow : (fun M : ℕ => (M : ℝ)^c0) =O[atTop] (fun M => (M : ℝ)^c0) := isBigO_refl _ _
  have hu := D.size_tendsto.eventually (nat_rpow_bigO_eventually_le (hpow.const_mul_left (1/s)) hsmall)
  have hl := D.size_tendsto.eventually (nat_rpow_bigO_eventually_le (hpow.const_mul_left B) hsmall)
  filter_upwards [hu,hl] with n hu hl
  intro ω E sigma hsigma hE eta A
  have hN : (1 : ℝ) ≤ N n := by exact_mod_cast D.size_pos n
  have hNp : 0 < (N n : ℝ) := by exact_mod_cast D.size_pos n
  have heta : 0 < eta := Real.rpow_pos_of_pos hNp _
  have heta1 : eta ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hfac := D.coloredResolventCovariance_factor n ω E eta sigma heta (fun a => hs.trans_le (hsigma a).1)
  have hupper : 1/(s*eta) ≤ channelNoiseBound θ (N n) := by
    convert hu using 1
    dsimp [eta]
    rw [Real.rpow_neg hNp.le]
    field_simp
  have hlower : channelCovarianceFloor θ (N n) ≤ eta/B := by
    have h := one_div_le_one_div_of_le (mul_pos hB (Real.rpow_pos_of_pos hNp c0)) hl
    simpa only [eta,channelCovarianceFloor,Real.rpow_neg hNp.le,one_div,mul_inv_rev,
      div_eq_mul_inv,mul_comm,one_mul] using h
  constructor
  · rw [hfac]
    exact (D.coloredResolventCovariance_opNorm n ω E eta sigma heta heta1 s S hs hS hsigma hE).trans hupper
  · intro x
    rw [hfac]
    exact (mul_le_mul_of_nonneg_right hlower (Finset.sum_nonneg (fun i hi => sq_nonneg _))).trans
      (D.coloredResolventCovariance_uniform_bounds n ω E eta sigma heta heta1 s S hs hS hsigma hE x).1

def rawEigenSignal {k : ℕ} (n : ℕ) (ω : Ω) (selection : Fin k → Fin (N n)) (i : Fin k × Fin (N n)) : ℝ :=
  Real.sqrt (N n)*D.eigenvector n ω (selection i.1) i.2

theorem HY_rawEigenSignal_bound {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n,Fin (N n) → ℝ} (H : HYCoarseInput D P quantile)
    (n : ℕ) (hn : H.events.threshold ≤ n) (ω : Ω) (hgood : ω ∈ H.events.good n)
    {k : ℕ} (selection : Fin k → Fin (N n)) (i : Fin k × Fin (N n)) :
    |D.rawEigenSignal n ω selection i| ≤ H.events.constant*Real.log (N n)^H.logPower := by
  rw [rawEigenSignal,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply H.delocalization n hn ω hgood _ (D.eigenvalue n ω (selection i.1)) ?_ ?_ i.2
  · simpa only [pow_two,ite_true] using D.orthonormal n ω (selection i.1) (selection i.1)
  · exact D.eigen_equation n ω (selection i.1)

theorem HY_rawEigenSignal_polynomial_eventually {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n,Fin (N n) → ℝ} (H : HYCoarseInput D P quantile) (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ n in atTop,∀ ω ∈ H.events.good n,∀ {k : ℕ} (selection : Fin k → Fin (N n)) (i : Fin k × Fin (N n)),
      |D.rawEigenSignal n ω selection i| ≤ channelNoiseBound θ (N n) := by
  have hc : 0 < channelNoiseExponent θ := by unfold channelNoiseExponent; linarith
  have hl := ((isLittleO_log_rpow_rpow_atTop (H.logPower : ℝ) hc).comp_tendsto
    (tendsto_natCast_atTop_atTop.comp D.size_tendsto)).const_mul_left H.events.constant
  have hb := hl.bound (c := 1) (by norm_num)
  filter_upwards [hb,eventually_ge_atTop H.events.threshold] with n hn hn0
  intro ω hω k selection i
  apply (D.HY_rawEigenSignal_bound H n hn0 ω hω selection i).trans
  have h : H.events.constant*Real.log (N n)^H.logPower ≤ channelNoiseBound θ (N n) := by
    have hh := (le_abs_self (H.events.constant*Real.log (N n)^H.logPower))
    apply hh.trans
    simpa only [Function.comp_apply,Real.rpow_natCast,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),one_mul,channelNoiseBound] using hn
  exact h

end GeneralizedBulk.External.RegularSpectralData
