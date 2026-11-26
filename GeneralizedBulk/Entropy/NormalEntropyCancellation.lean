import GeneralizedBulk.Entropy.StarEdgeFunctional
import GeneralizedBulk.Graph.StarRescale

/-! The genuine star normal-rescaling Jacobian cancels the remaining
star Gaussian baseline against the evaluated global Kesten--McKay noise
entropy, exactly in every color. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.External.RegularSpectralData

theorem starNormalRescaleFactor_log (d : ℕ) (hd : 0 < d) (E eta sigma : ℝ)
    (heta : 0 < eta) (hsigma : 0 < sigma) :
    Real.log (starNormalRescaleFactor d E eta sigma) =
      (Real.log sigma + Real.log ((d : ℝ)+E^2) - Real.log eta) / 2 := by
  have hdE : 0 < (d : ℝ)+E^2 := add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hd) (sq_nonneg E)
  rw [starNormalRescaleFactor, Real.log_sqrt (div_pos (mul_pos hsigma hdE) heta).le,
    Real.log_div (mul_pos hsigma hdE).ne' heta.ne', Real.log_mul hsigma.ne' hdE.ne']

theorem starNormal_gaussianBaseline (d : ℕ) (hd : 0 < d) (E eta sigma : ℝ)
    (heta : 0 < eta) (hsigma : 0 < sigma) :
    (1+Real.log (2*Real.pi))/2 + Real.log ((d : ℝ)+E^2)/2 -
        GeneralizedBulk.KestenMcKay.bulkPotential d E - Real.log (starNormalRescaleFactor d E eta sigma) =
      (1+Real.log (2*Real.pi)+Real.log (eta/sigma))/2 -
        GeneralizedBulk.KestenMcKay.bulkPotential d E := by
  rw [starNormalRescaleFactor_log d hd E eta sigma heta hsigma, Real.log_div heta.ne' hsigma.ne']
  ring

theorem coloredNormal_gaussianBaseline (d k : ℕ) (hd : 0 < d) (energy sigma : Fin k → ℝ)
    (eta : ℝ) (heta : 0 < eta) (hsigma : ∀ a, 0 < sigma a) :
    (k : ℝ)/2*(1+Real.log (2*Real.pi)) +
        (∑ a, (Real.log ((d : ℝ)+energy a^2)/2 - GeneralizedBulk.KestenMcKay.bulkPotential d (energy a))) -
        (∑ a, Real.log (starNormalRescaleFactor d (energy a) eta (sigma a))) =
      ∑ a, ((1+Real.log (2*Real.pi)+Real.log (eta/sigma a))/2 -
        GeneralizedBulk.KestenMcKay.bulkPotential d (energy a)) := by
  calc
    _ = ∑ a, ((1+Real.log (2*Real.pi))/2 + Real.log ((d : ℝ)+energy a^2)/2 -
        GeneralizedBulk.KestenMcKay.bulkPotential d (energy a) -
          Real.log (starNormalRescaleFactor d (energy a) eta (sigma a))) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := Finset.sum_congr rfl (fun a _ => starNormal_gaussianBaseline d hd _ _ _ heta (hsigma a))

end GeneralizedBulk.Entropy
