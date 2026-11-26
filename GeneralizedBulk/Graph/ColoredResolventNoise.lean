import GeneralizedBulk.Graph.ResolventCovarianceBounds
import GeneralizedBulk.Matrix.ColorBlocks
import GeneralizedBulk.Matrix.QuadraticOpNorm

/-! The actual colored resolvent Gaussian factor, with exact covariance and
dimension-free global bounds. -/
noncomputable section
open scoped BigOperators Classical Matrix.L2OpNorm

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Covariance

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def coloredResolventCovariance {k : ℕ} (E : Fin k → ℝ) (eta : ℝ) (sigma : Fin k → ℝ) :
    Matrix (Fin k × Fin (N n)) (Fin k × Fin (N n)) ℝ :=
  colorBlock (fun a => D.resolventCovariance n ω (E a) eta (sigma a))

def coloredResolventCovarianceFactor {k : ℕ} (E : Fin k → ℝ) (eta : ℝ) (sigma : Fin k → ℝ) :
    Matrix (Fin k × Fin (N n)) (Fin k × Fin (N n)) ℝ :=
  colorBlock (fun a => D.resolventCovarianceFactor n ω (E a) eta (sigma a))

theorem coloredResolventCovariance_factor {k : ℕ} (E : Fin k → ℝ) (eta : ℝ) (sigma : Fin k → ℝ)
    (heta : 0 < eta) (hsigma : ∀ a,0 < sigma a) :
    D.coloredResolventCovarianceFactor n ω E eta sigma*(D.coloredResolventCovarianceFactor n ω E eta sigma).transpose =
      D.coloredResolventCovariance n ω E eta sigma := by
  rw [coloredResolventCovarianceFactor,colorBlock_transpose,colorBlock_mul]
  exact congrArg colorBlock (funext (fun a => D.resolventCovariance_factor n ω (E a) eta (sigma a) heta (hsigma a)))

set_option maxHeartbeats 1500000 in
theorem coloredResolventCovariance_uniform_bounds {k : ℕ}
    (E : Fin k → ℝ) (eta : ℝ) (sigma : Fin k → ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (s S : ℝ) (hs : 0 < s) (hS : 0 < S) (hsigma : ∀ a,s ≤ sigma a ∧ sigma a ≤ S)
    (hE : ∀ a,|E a| ≤ d) (x : Fin k × Fin (N n) → ℝ) :
    (eta/(S*((2*(d : ℝ))^2+1)))*(∑ i,x i^2) ≤
      dotProduct x ((D.coloredResolventCovariance n ω E eta sigma).mulVec x) ∧
    dotProduct x ((D.coloredResolventCovariance n ω E eta sigma).mulVec x) ≤
      (1/(s*eta))*(∑ i,x i^2) := by
  have hlow (a : Fin k) : eta/(S*((2*(d : ℝ))^2+1)) ≤
      (eta/sigma a)/(((d : ℝ)+|E a|)^2+eta^2) := by
    rw [div_div]
    have hsp : 0 < sigma a := hs.trans_le (hsigma a).1
    apply div_le_div_of_nonneg_left heta.le (mul_pos hsp (by positivity))
    have hpow : ((d : ℝ)+|E a|)^2 ≤ (2*(d : ℝ))^2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (by nlinarith [hE a])
    have hetaSq : eta^2 ≤ 1 := by nlinarith
    exact mul_le_mul (hsigma a).2 (by linarith) (by positivity) hS.le
  have hupp (a : Fin k) : 1/(sigma a*eta) ≤ 1/(s*eta) :=
    one_div_le_one_div_of_le (mul_pos hs heta) (mul_le_mul_of_nonneg_right (hsigma a).1 heta.le)
  constructor
  · apply colorBlock_quadratic_floor
    intro a y
    have h := (D.resolventCovariance_quadratic_bounds n ω (E a) eta (sigma a) heta (hs.trans_le (hsigma a).1) y).1
    exact (mul_le_mul_of_nonneg_right (hlow a) (Finset.sum_nonneg (fun i hi => sq_nonneg _))).trans h
  · apply colorBlock_quadratic_upper
    intro a y
    have h := (D.resolventCovariance_quadratic_bounds n ω (E a) eta (sigma a) heta (hs.trans_le (hsigma a).1) y).2
    exact h.trans (mul_le_mul_of_nonneg_right (hupp a) (Finset.sum_nonneg (fun i hi => sq_nonneg _)))

theorem coloredResolventCovariance_opNorm {k : ℕ}
    (E : Fin k → ℝ) (eta : ℝ) (sigma : Fin k → ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (s S : ℝ) (hs : 0 < s) (hS : 0 < S) (hsigma : ∀ a,s ≤ sigma a ∧ sigma a ≤ S)
    (hE : ∀ a,|E a| ≤ d) : ‖D.coloredResolventCovariance n ω E eta sigma‖ ≤ 1/(s*eta) := by
  have hfac := D.coloredResolventCovariance_factor n ω E eta sigma heta (fun a => hs.trans_le (hsigma a).1)
  have hHerm : (D.coloredResolventCovariance n ω E eta sigma).IsHermitian := by
    rw [← hfac]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_conjTranspose_self (D.coloredResolventCovarianceFactor n ω E eta sigma)
  apply hermitian_opNorm_le_of_quadratic _ hHerm _ (by positivity)
  · intro x
    exact (show 0 ≤ (eta/(S*((2*(d : ℝ))^2+1)))*(∑ i,x i^2) by positivity).trans
      (D.coloredResolventCovariance_uniform_bounds n ω E eta sigma heta heta1 s S hs hS hsigma hE x).1
  · intro x
    exact (D.coloredResolventCovariance_uniform_bounds n ω E eta sigma heta heta1 s S hs hS hsigma hE x).2

end GeneralizedBulk.External.RegularSpectralData
