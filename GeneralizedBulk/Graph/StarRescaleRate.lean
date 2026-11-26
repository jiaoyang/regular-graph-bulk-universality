import GeneralizedBulk.Graph.StarRescaledCovariance

/-! The actual normal rescaling loses only a square root of the noise height. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Covariance GeneralizedBulk.Gaussian GeneralizedBulk.Entropy
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem starNormalRescaleFactor_mul_height (hd : 0 < d) (E eta sigma : ℝ)
    (heta : 0 < eta) (hsigma : 0 < sigma) :
    starNormalRescaleFactor d E eta sigma * eta = Real.sqrt (sigma*((d : ℝ)+E^2))*Real.sqrt eta := by
  unfold starNormalRescaleFactor
  rw [Real.sqrt_div (by positivity : 0 ≤ sigma*((d : ℝ)+E^2))]
  calc
    _ = Real.sqrt (sigma*((d : ℝ)+E^2))*(eta/Real.sqrt eta) := by ring
    _ = _ := by rw [Real.div_sqrt]

theorem rescaledLocalStarCovariance_sqrt_height_bound (hd : 2 ≤ d) (o : Fin (N n))
    (E eta sigma e M : ℝ) (hE : |E| < d) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hsigma : 0 < sigma) (he : 0 ≤ e) (hM : 0 ≤ M)
    (hclose : ∀ i j, |(D.localEntropyStarCovariance n ω o E eta sigma-starWaveCovariance d E) i j| ≤ e)
    (hG : ∀ j : Fin (d+1), ‖D.resolvent n ω (⟨E,eta⟩ : ℂ) o (D.entropyStarVertex n ω o j)‖ ≤ M) :
    matrixEntryL1 (D.rescaledLocalStarCovariance n ω o E eta sigma-starReferenceCovariance d E) ≤
      4*((d+1 : ℕ) : ℝ)^4*e+
      (4*((d+1 : ℕ) : ℝ)^3*M*Real.sqrt (sigma*((d : ℝ)+E^2))/(sigma*Real.sqrt ((d : ℝ)+E^2))+
        ((d+1 : ℕ) : ℝ)*M)*Real.sqrt eta := by
  let P := starNormalProjection d E
  let Q := D.localEntropyStarCovariance n ω o E eta sigma
  let t := starNormalRescaleFactor d E eta sigma
  let m : ℝ := d+1
  let gam := eta/sigma/Real.sqrt ((d : ℝ)+E^2)
  have hdpos : 0 < d := by omega
  have hb : 0 < (d : ℝ)+E^2 := add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hdpos) (sq_nonneg E)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hgam : 0 ≤ gam := by dsimp [gam]; positivity
  have ht : 0 < t := starNormalRescaleFactor_pos hdpos E eta sigma heta hsigma
  have hp := matrixEntryL1_unitNormalProjection_le _ (normalizedStarNormal_sq_sum d hdpos E)
  have hT := matrixEntryL1_tangentProjection_le _ (normalizedStarNormal_sq_sum d hdpos E)
  have hraw := matrixEntryL1_le_of_entrywise (Q-starWaveCovariance d E) e hclose
  have hPQ := D.normalProjection_local_covariance_L1_bound n ω hdpos o E eta sigma M heta hsigma hM
    (fun j => (Complex.abs_re_le_norm _).trans (hG j))
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hp hT hraw hPQ
  have hDiag : sigma*|D.resolventCovariance n ω E eta sigma o o| ≤ M := by
    rw [D.resolventCovariance_entry n ω E eta sigma heta o o, abs_div, abs_of_pos hsigma,
      mul_div_cancel₀ _ hsigma.ne']
    exact (Complex.abs_im_le_norm _).trans (hG 0)
  have hte : t*gam=Real.sqrt (sigma*((d : ℝ)+E^2))/(sigma*Real.sqrt ((d : ℝ)+E^2))*Real.sqrt eta := by
    calc
      _ = (t*eta)/(sigma*Real.sqrt ((d : ℝ)+E^2)) := by dsimp [gam]; ring
      _ = _ := by rw [starNormalRescaleFactor_mul_height hdpos E eta sigma heta hsigma]; ring
  have hTan : matrixEntryL1 (1-P)^2*matrixEntryL1 (Q-starWaveCovariance d E) ≤ 4*m^4*e := by
    have hh := mul_le_mul (pow_le_pow_left₀ (matrixEntryL1_nonneg _) hT 2) hraw
      (matrixEntryL1_nonneg _) (by positivity : 0 ≤ (2*m)^2)
    convert hh using 1 <;> dsimp [m] <;> ring
  have hCross : 2*|t| *matrixEntryL1 (1-P)*matrixEntryL1 (P*Q) ≤
      (4*m^3*M*Real.sqrt (sigma*((d : ℝ)+E^2))/(sigma*Real.sqrt ((d : ℝ)+E^2)))*Real.sqrt eta := by
    have hpq := mul_le_mul hT hPQ (matrixEntryL1_nonneg _) (by positivity : 0 ≤ 2*m)
    have hh := mul_le_mul_of_nonneg_left hpq (show 0 ≤ 2*t by positivity)
    rw [abs_of_pos ht]
    have heq : (2*t)*((2*m)*(m^2*gam*M)) =
        (4*m^3*M*Real.sqrt (sigma*((d : ℝ)+E^2))/(sigma*Real.sqrt ((d : ℝ)+E^2)))*Real.sqrt eta := by
      calc
        _ = 4*m^3*M*(t*gam) := by ring
        _ = _ := by rw [hte]; ring
    have hi : 2*t*matrixEntryL1 (1-P)*matrixEntryL1 (P*Q) ≤ (2*t)*((2*m)*(m^2*gam*M)) := by
      convert hh using 1 <;> dsimp [P,Q,m,gam,starNormalProjection] <;> ring
    exact hi.trans_eq heq
  have hVar : sigma*eta*|D.resolventCovariance n ω E eta sigma o o| *matrixEntryL1 P ≤ m*M*Real.sqrt eta := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hDiag heta.le) hp (matrixEntryL1_nonneg _) (mul_nonneg heta.le hM)
    have hs : eta ≤ Real.sqrt eta := by
      have hs1 : Real.sqrt eta ≤ 1 := by nlinarith [Real.sq_sqrt heta.le,Real.sqrt_nonneg eta]
      nlinarith [Real.sq_sqrt heta.le,Real.sqrt_nonneg eta,mul_nonneg (Real.sqrt_nonneg eta) (sub_nonneg.mpr hs1)]
    have hnext := mul_le_mul_of_nonneg_left hs (mul_nonneg hm hM)
    change eta*(sigma*|D.resolventCovariance n ω E eta sigma o o|)*matrixEntryL1 P ≤ eta*M*m at hh
    nlinarith only [hh,hnext]
  have hg := D.rescaledLocalStarCovariance_error_bound n ω hd o E eta sigma hE heta hsigma
  refine hg.trans ?_
  dsimp [P,Q,t,m] at hTan hCross hVar
  simp only [Nat.cast_add,Nat.cast_one]
  nlinarith only [hTan,hCross,hVar]

end GeneralizedBulk.External.RegularSpectralData
