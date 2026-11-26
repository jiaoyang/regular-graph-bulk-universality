import GeneralizedBulk.Gaussian.ExtendedWhiteningLaw
import GeneralizedBulk.Graph.EmpiricalEdgeReversal

/-! The actual empirical normalized signal is mapped by the extended
whitening factor to the literal physical eigenvector star, with zero normal
mean. -/
noncomputable section
open scoped BigOperators Matrix
open MeasureTheory
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Entropy.Channel
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem empirical_extendedWhitening_mean {k : ℕ} (hd : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) (s : EmpiricalStarSample d (N n)) :
    (coloredExtendedCoefficients d k hd (fun a => D.eigenvalue n ω (selection a))).mulVec
      (Sum.elim ((D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s) (fun _ : Fin k => 0)) =
      D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s := by
  rw [D.empiricalNormalizedSignal_values]
  funext aj
  rw [coloredExtendedCoefficients_scalarCoordinates]
  simp only [mul_zero, add_zero]
  have hh := D.empiricalWhiteStar_row n ω hd selection hE s aj
  simpa only [coloredPhysicalRow, blockVector_inner] using hh

/-- The literal physical reference Gaussian component is the pushforward of
whitened empirical signal plus tangent standard normals and independent
normal standard coordinates. -/
theorem empirical_extendedGaussian_product {k : ℕ} (hd : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) (s : EmpiricalStarSample d (N n)) :
    GeneralizedBulk.Entropy.affineGaussian
      (D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s)
      (coloredExtendedFactor d k hd (fun a => D.eigenvalue n ω (selection a))) =
      ((standardVector (ScalarCoordinate d k)).prod (standardVector (Fin k))).map
        (fun xy : (ScalarCoordinate d k → ℝ) × (Fin k → ℝ) =>
          (coloredExtendedCoefficients d k hd (fun a => D.eigenvalue n ω (selection a))).mulVec
            (Sum.elim ((D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s + xy.1) xy.2)) := by
  rw [← D.empirical_extendedWhitening_mean n ω hd selection hinj hE s]
  exact coloredExtendedGaussian_product d k hd _ hE _

end GeneralizedBulk.External.RegularSpectralData
