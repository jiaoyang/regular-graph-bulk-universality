import GeneralizedBulk.Gaussian.FiniteVector
import GeneralizedBulk.Graph.StarGaussianLimit
import GeneralizedBulk.Entropy.ChannelGeometry

/-!
# The actual normalized Gaussian star law

Independent standard real normals are mapped through the fixed whitened star
space and its physical root/leaf rows. Their row Gram matrix is proved to be
the exact regular-star covariance. Multiple channels use disjoint independent
normal coordinates, so their full joint law is constructed as well.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Gaussian
open Entropy.Channel External.RegularSpectralData

def starRho (d : ℕ) (E : ℝ) : ℝ := Real.sqrt (1 - (E / d) ^ 2)

theorem starRho_sq (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    starRho d E ^ 2 = 1 - (E / d) ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hc : |E / (d : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos hdR, div_lt_one hdR]
    exact hE
  exact Real.sq_sqrt (sub_nonneg.mpr ((sq_lt_one_iff_abs_lt_one (E / d)).mpr hc).le)

def starRow (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (j : Fin (d + 1)) : WhiteStar d :=
  Fin.cases (rootVector d) (fun i => leafVector d hd (E / d) (starRho d E) i) j

theorem starRow_gram (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d)
    (j l : Fin (d + 1)) :
    @inner ℝ (WhiteStar d) _ (starRow d hd E j) (starRow d hd E l) = starWaveCovariance d E j l := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  refine Fin.cases ?_ (fun j => ?_) j
  · refine Fin.cases ?_ (fun l => ?_) l
    · exact root_inner_root d
    · exact root_leaf_correlation d hd _ _ l
  · refine Fin.cases ?_ (fun l => ?_) l
    · rw [real_inner_comm]
      exact root_leaf_correlation d hd _ _ j
    · change @inner ℝ (WhiteStar d) _ (leafVector d hd (E / d) (starRho d E) j)
        (leafVector d hd (E / d) (starRho d E) l) = _
      rw [leaf_leaf_correlation, starRho_sq d hd E hE]
      simp only [starWaveCovariance, Fin.cases_succ]
      by_cases hjl : j = l
      · simp only [hjl, ↓reduceIte]
        ring
      · simp only [hjl, ↓reduceIte]
        field_simp
        ring

abbrev StarNormalIndex (d : ℕ) := Fin (Module.finrank ℝ (WhiteStar d))

def starNormalBasis (d : ℕ) : OrthonormalBasis (StarNormalIndex d) ℝ (WhiteStar d) :=
  stdOrthonormalBasis ℝ (WhiteStar d)

def starCoefficients (d : ℕ) (hd : 2 ≤ d) (E : ℝ) :
    Matrix (Fin (d + 1)) (StarNormalIndex d) ℝ :=
  fun j a => (starNormalBasis d).repr (starRow d hd E j) a

theorem starCoefficients_gram (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    starCoefficients d hd E * (starCoefficients d hd E).transpose = starWaveCovariance d E := by
  ext j l
  change (∑ a, (starNormalBasis d).repr (starRow d hd E j) a *
    (starNormalBasis d).repr (starRow d hd E l) a) = _
  calc
    _ = @inner ℝ (EuclideanSpace ℝ (StarNormalIndex d)) _
        ((starNormalBasis d).repr (starRow d hd E j))
        ((starNormalBasis d).repr (starRow d hd E l)) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = @inner ℝ (WhiteStar d) _ (starRow d hd E j) (starRow d hd E l) :=
      (starNormalBasis d).repr.inner_map_map _ _
    _ = _ := starRow_gram d hd E hE j l

def starGaussianLaw (d : ℕ) (hd : 2 ≤ d) (E : ℝ) : Measure (Fin (d + 1) → ℝ) :=
  linearImageGaussian (starCoefficients d hd E)

instance (d : ℕ) (hd : 2 ≤ d) (E : ℝ) : IsProbabilityMeasure (starGaussianLaw d hd E) :=
  inferInstanceAs (IsProbabilityMeasure (linearImageGaussian (starCoefficients d hd E)))

theorem starGaussianLaw_characteristic (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d)
    (t : Fin (d + 1) → ℝ) :
    (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂starGaussianLaw d hd E) =
      Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic (starWaveCovariance d E) t) : ℂ) := by
  simpa only [starGaussianLaw, starCoefficients_gram d hd E hE] using
    linearImageGaussian_characteristic (starCoefficients d hd E) t

def jointStarCoefficients (d k : ℕ) (hd : 2 ≤ d) (E : ℝ) :
    Matrix (Fin k × Fin (d + 1)) (Fin k × StarNormalIndex d) ℝ :=
  fun aj ba => if aj.1 = ba.1 then starCoefficients d hd E aj.2 ba.2 else 0

theorem jointStarCoefficients_gram (d k : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    jointStarCoefficients d k hd E * (jointStarCoefficients d k hd E).transpose =
      jointStarCovariance d k E := by
  ext aj bl
  simp only [Matrix.mul_apply, Matrix.transpose_apply, jointStarCoefficients, Fintype.sum_prod_type,
    jointStarCovariance]
  by_cases hab : aj.1 = bl.1
  · simp only [hab, ↓reduceIte, one_mul]
    have heq := congrArg (fun M => M aj.2 bl.2) (starCoefficients_gram d hd E hE)
    simpa [mul_ite, ite_mul, Finset.sum_ite_irrel, Matrix.mul_apply, Matrix.transpose_apply] using heq
  · have heq (a : Fin k) : ¬(aj.1 = a ∧ bl.1 = a) := by
      rintro ⟨hja, hla⟩
      exact hab (hja.trans hla.symm)
    simp only [hab, ↓reduceIte, zero_mul]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hja : aj.1 = a <;> by_cases hla : bl.1 = a <;> simp_all

def jointStarGaussianLaw (d k : ℕ) (hd : 2 ≤ d) (E : ℝ) :
    Measure ((Fin k × Fin (d + 1)) → ℝ) := linearImageGaussian (jointStarCoefficients d k hd E)

instance (d k : ℕ) (hd : 2 ≤ d) (E : ℝ) : IsProbabilityMeasure (jointStarGaussianLaw d k hd E) :=
  inferInstanceAs (IsProbabilityMeasure (linearImageGaussian (jointStarCoefficients d k hd E)))

theorem jointStarGaussianLaw_characteristic (d k : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d)
    (t : (Fin k × Fin (d + 1)) → ℝ) :
    (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂jointStarGaussianLaw d k hd E) =
      Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic (jointStarCovariance d k E) t) : ℂ) := by
  simpa only [jointStarGaussianLaw, jointStarCoefficients_gram d k hd E hE] using
    linearImageGaussian_characteristic (jointStarCoefficients d k hd E) t

end GeneralizedBulk.Gaussian
