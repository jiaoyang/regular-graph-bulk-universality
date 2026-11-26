import GaussianWave.BS.GaussianLabelRestriction

/-! Actual second moments and collision bounds for finitely supported
Gaussian rules. A cover may merge labels, but its coefficient l1 bound stays
finite and independent of the size of the target graph. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

/-- Every sampled coordinate has all integer moments, derived from the actual
Gaussian source. -/
theorem finiteSupportGaussianLaw_integrable_pow {V J : Type*} [Fintype J]
    (a : J → V →₀ ℝ) (j : J) (p : ℕ) :
    Integrable (fun z => z j^p) (finiteSupportGaussianLaw a) := by
  let L := finiteSupportGaussianMatrix a
  have hL : (L*L.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose,star_trivial,Matrix.map_id] using
      Matrix.posSemidef_self_mul_conjTranspose L
  have he := eq_gaussianCovarianceLaw (finiteSupportGaussianLaw a)
    (L*L.transpose) hL (finiteSupportGaussianLaw_gaussian a)
  rw [he]
  exact gaussianCovarianceLaw_coordinate_integrable_pow _ _ j p

/-- The variance is the literal sum of squared coefficient values. -/
theorem finiteSupportGaussianLaw_second {V J : Type*} [Fintype J]
    (a : J → V →₀ ℝ) (j : J) :
    (∫ z,z j^2 ∂finiteSupportGaussianLaw a)=finsuppPairing (a j) (a j) := by
  let L := finiteSupportGaussianMatrix a
  have hL : (L*L.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose,star_trivial,Matrix.map_id] using
      Matrix.posSemidef_self_mul_conjTranspose L
  have he := eq_gaussianCovarianceLaw (finiteSupportGaussianLaw a)
    (L*L.transpose) hL (finiteSupportGaussianLaw_gaussian a)
  rw [he,gaussianCovarianceLaw_coordinate_second]
  exact finiteSupportGaussianMatrix_gram a j j

/-- Integrability at the original iid-label source. -/
theorem integrable_finiteSupportGaussianSample_pow {V J : Type*} [Fintype J]
    (a : J → V →₀ ℝ) (j : J) (p : ℕ) :
    Integrable (fun ξ => (finiteSupportGaussianSample a ξ j)^p) (gaussianLabelLaw V) := by
  exact (integrable_map_measure (((continuous_apply j).pow p).aestronglyMeasurable)
    (measurable_finiteSupportGaussianSample a).aemeasurable).mp
      (finiteSupportGaussianLaw_integrable_pow a j p)

/-- The literal sampler's second moment is its computed row norm. -/
theorem integral_finiteSupportGaussianSample_sq {V J : Type*} [Fintype J]
    (a : J → V →₀ ℝ) (j : J) :
    (∫ ξ,(finiteSupportGaussianSample a ξ j)^2 ∂gaussianLabelLaw V)=
      finsuppPairing (a j) (a j) := by
  rw [← finiteSupportGaussianLaw_second a j]
  exact (integral_map (measurable_finiteSupportGaussianSample a).aemeasurable
    (((continuous_apply j).pow 2).aestronglyMeasurable)).symm

/-- Merging coefficient indices under a map can enlarge the squared norm by
at most the squared l1 norm of the original finite row. -/
theorem finsuppPairing_mapDomain_le_l1_sq {V W : Type*} (F : V → W) (a : V →₀ ℝ) :
    finsuppPairing (Finsupp.mapDomain F a) (Finsupp.mapDomain F a) ≤
      (a.sum (fun _ c => |c|))^2 := by
  have he : finsuppPairing (Finsupp.mapDomain F a) (Finsupp.mapDomain F a) =
      ∑ v ∈ a.support,∑ w ∈ a.support,
        if F v=F w then a v*a w else 0 := by
    rw [Finsupp.mapDomain,Finsupp.sum,map_sum]
    try simp only [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro v hv
    rw [finsuppPairing_single_right,Finsupp.finset_sum_apply,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [Finsupp.single_apply]
    by_cases h : F v=F w
    · simp [h,mul_comm]
    · simp [h,Ne.symm h]
  rw [he]
  calc
    _ ≤ ∑ v ∈ a.support,∑ w ∈ a.support,|a v| * |a w| := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro w hw
      split_ifs
      · simpa only [abs_mul] using le_abs_self (a v*a w)
      · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    _ = _ := by
      simp only [Finsupp.sum,pow_two,Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm

end GaussianWave.BS
