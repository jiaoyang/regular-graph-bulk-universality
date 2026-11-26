import GeneralizedBulk.Graph.HYLocalStarCovariance
import GeneralizedBulk.Graph.StarRescaleRate

/-! The actual HY good roots have uniformly stable full-star covariances
after the constructed normal rescaling. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open Set MeasureTheory GeneralizedBulk.KestenMcKay GeneralizedBulk.Gaussian GeneralizedBulk.Entropy
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem starRescale_coefficient_simplify (hd : 0 < d) (E sigma : ℝ) (hsigma : 0 < sigma) :
    Real.sqrt (sigma*((d : ℝ)+E^2))/(sigma*Real.sqrt ((d : ℝ)+E^2)) = 1/Real.sqrt sigma := by
  have hb : 0 < (d : ℝ)+E^2 := add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hd) (sq_nonneg E)
  rw [Real.sqrt_mul hsigma.le]
  have hs := Real.sq_sqrt hsigma.le
  have hs0 := (Real.sqrt_pos.mpr hsigma).ne'
  have hb0 := (Real.sqrt_pos.mpr hb).ne'
  field_simp
  calc
    _ = (Real.sqrt sigma)^2*Real.sqrt ((d : ℝ)+E^2) := by ring
    _ = _ := by rw [hs]

theorem bulk_abs_lt_degree (hd : 3 ≤ (d : ℝ)) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) : |E| < d := by
  have hh : E^2 < (d : ℝ)^2 := by nlinarith [sq_nonneg ((d : ℝ)-2)]
  exact (sq_lt_sq₀ (abs_nonneg E) (by linarith : (0:ℝ) ≤ d)).mp (by simpa using hh)

theorem HYLocalStar_rescaled_covariance_uniform {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd)) :
    ∃ C : ℝ,0 < C ∧ ∀ n,H.events.threshold ≤ n → ∀ ω ∈ H.events.good n,
      ∀ root : Fin (N n),root ∉ H.badRoots n ω → ∀ E ∈ K,
      let eta := (N n : ℝ)^(-c0)
      let sigma := (diagonalBoundary d E).im
      matrixEntryL1 (D.rescaledLocalStarCovariance n ω root E eta sigma-starReferenceCovariance d E) ≤
        C*((N n : ℝ)^(-H.local_exponent)+Real.sqrt eta) := by
  obtain ⟨C0,hC0,hclose⟩ := D.HYLocalStar_covariance_rate_uniform hd K hK hbulk c0 H
  obtain ⟨c,hc,hfloor⟩ := diagonalBoundary_im_uniform d hd K hK hbulk
  let m : ℝ := d+1
  let A := 4*m^4*C0
  let B := 12*m^3/Real.sqrt c+3*m
  have hm : 0 < m := by dsimp [m]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A+B,by positivity,?_⟩
  intro n hn ω hω root hroot E hE
  let eta := (N n : ℝ)^(-c0)
  let sigma := (diagonalBoundary d E).im
  let r := (N n : ℝ)^(-H.local_exponent)
  have hN : (1:ℝ) ≤ N n := by exact_mod_cast D.size_pos n
  have heta : 0 < eta := Real.rpow_pos_of_pos (by linarith : (0:ℝ)<N n) _
  have heta1 : eta ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith [H.height_range.1])
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith [H.local_exponent_pos])
  have hsigma : 0 < sigma := hc.trans_le (hfloor E hE).1
  have hd2 : 2 ≤ d := by exact_mod_cast (show (2:ℝ) ≤ d by linarith)
  have hdpos : 0 < d := by omega
  have hg : ∀ j : Fin (d+1),‖D.resolvent n ω (⟨E,eta⟩ : ℂ) root (D.entropyStarVertex n ω root j)‖ ≤ 3 := by
    intro j
    have hh := D.HYLocalStar_resolvent_entry_norm hd K c0 H n hn ω hω root hroot E hE 0 j
    have hz : (⟨E,eta⟩ : ℂ) = (E : ℂ)+(eta : ℂ)*Complex.I := by apply Complex.ext <;> simp
    rw [hz]
    exact hh.trans (by change 2+r ≤ 3; linarith)
  have hc0 : ∀ i j,|(D.localEntropyStarCovariance n ω root E eta sigma-starWaveCovariance d E) i j| ≤ C0*(r+eta) := by
    intro i j
    exact hclose n hn ω hω root hroot E hE i j
  have hh := D.rescaledLocalStarCovariance_sqrt_height_bound n ω hd2 root E eta sigma (C0*(r+eta)) 3
    (bulk_abs_lt_degree hd E (hbulk E hE)) heta heta1 hsigma (by positivity) (by norm_num) hc0 hg
  have hcoeff :
      4*m^3*3*Real.sqrt (sigma*((d : ℝ)+E^2))/(sigma*Real.sqrt ((d : ℝ)+E^2))+m*3 ≤ B := by
    have hs : Real.sqrt c ≤ Real.sqrt sigma := Real.sqrt_le_sqrt (hfloor E hE).1
    have hi : 1/Real.sqrt sigma ≤ 1/Real.sqrt c := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hc) hs
    have heq : 4*m^3*3*Real.sqrt (sigma*((d : ℝ)+E^2))/(sigma*Real.sqrt ((d : ℝ)+E^2)) = 12*m^3*(1/Real.sqrt sigma) := by
      rw [mul_div_assoc,starRescale_coefficient_simplify hdpos E sigma hsigma]
      ring
    rw [heq]
    dsimp [B]
    have hi' := mul_le_mul_of_nonneg_left hi (by positivity : (0:ℝ) ≤ 12*m^3)
    simp only [div_eq_mul_inv,one_mul] at hi' ⊢
    nlinarith only [hi']
  have hs : eta ≤ Real.sqrt eta := by
    have hsq := Real.sq_sqrt heta.le
    have hsr := Real.sqrt_nonneg eta
    have hs1 : Real.sqrt eta ≤ 1 := by nlinarith
    nlinarith [mul_nonneg hsr (sub_nonneg.mpr hs1)]
  have hh' : matrixEntryL1 (D.rescaledLocalStarCovariance n ω root E eta sigma-starReferenceCovariance d E) ≤
      A*(r+eta)+B*Real.sqrt eta := by
    refine hh.trans ?_
    have hcoef := mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg eta)
    dsimp [A,m] at hcoef ⊢
    convert add_le_add_left hcoef (4*((d : ℝ)+1)^4*(C0*(r+eta))) using 1 <;> push_cast <;> ring
  have hnext := mul_le_mul_of_nonneg_left hs hA.le
  change matrixEntryL1 (D.rescaledLocalStarCovariance n ω root E eta sigma-starReferenceCovariance d E) ≤ (A+B)*(r+Real.sqrt eta)
  exact hh'.trans (by nlinarith [mul_nonneg hB.le hr])

end GeneralizedBulk.External.RegularSpectralData
