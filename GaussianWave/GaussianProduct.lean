import GaussianWave.GaussianLaws

/-!
# Actual product structure of Gaussian channels

A Gaussian law with block diagonal covariance is proved equal to the flattened
finite product of the actual Gaussian probability measures in its blocks.
The covariances of different channels may differ and may be singular.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology Classical NNReal

namespace GaussianWave

/-- Forget only the currying of channel/site indices. -/
def flattenChannels {κ ι : Type*} (x : κ → ι → ℝ) : (κ × ι) → ℝ :=
  fun p => x p.1 p.2

lemma measurable_flattenChannels {κ ι : Type*} :
    Measurable (@flattenChannels κ ι) := by
  apply measurable_pi_lambda
  intro p
  exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

/-- A covariance in channel-first coordinates, with zero cross-channel blocks. -/
def channelBlockCovariance {κ ι : Type*} [DecidableEq κ]
    (C : κ → Matrix ι ι ℝ) : Matrix (κ × ι) (κ × ι) ℝ :=
  fun p q => if p.1 = q.1 then C p.1 p.2 q.2 else 0

lemma finiteLinearForm_flatten {κ ι : Type*} [Fintype κ] [Fintype ι]
    (t : (κ × ι) → ℝ) (x : κ → ι → ℝ) :
    finiteLinearForm t (flattenChannels x) =
      ∑ a, finiteLinearForm (fun i => t (a, i)) (x a) := by
  simp only [finiteLinearForm, flattenChannels, Fintype.sum_prod_type]

lemma finiteCovarianceQuadratic_channelBlock {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq κ]
    (C : κ → Matrix ι ι ℝ) (t : (κ × ι) → ℝ) :
    finiteCovarianceQuadratic (channelBlockCovariance C) t =
      ∑ a, finiteCovarianceQuadratic (C a) (fun i => t (a, i)) := by
  classical
  simp [finiteCovarianceQuadratic, channelBlockCovariance, Fintype.sum_prod_type,
    Finset.mul_sum, ← Finset.sum_mul]

lemma finiteCovarianceQuadratic_nonneg_of_posSemidef {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (t : ι → ℝ) :
    0 ≤ finiteCovarianceQuadratic C t := by
  simpa only [finiteCovarianceQuadratic, dotProduct, Matrix.mulVec,
    Pi.star_apply, star_trivial, Finset.mul_sum, mul_assoc] using hC.2 t

/-- Positive semidefinite blocks give a positive semidefinite channel matrix;
no invertibility or positive-definiteness hypothesis is needed. -/
theorem channelBlockCovariance_posSemidef {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq κ]
    (C : κ → Matrix ι ι ℝ) (hC : ∀ a, (C a).PosSemidef) :
    (channelBlockCovariance C).PosSemidef := by
  constructor
  · ext p q
    rcases p with ⟨a, i⟩
    rcases q with ⟨b, j⟩
    simp only [Matrix.conjTranspose_apply, star_trivial, channelBlockCovariance]
    by_cases hab : a = b
    · subst b
      simp only [↓reduceIte]
      have hh := congrFun (congrFun (hC a).1 i) j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using hh
    · simp only [hab, Ne.symm hab, ↓reduceIte]
  · intro t
    have hh : 0 ≤ finiteCovarianceQuadratic (channelBlockCovariance C) t := by
      rw [finiteCovarianceQuadratic_channelBlock]
      exact Finset.sum_nonneg (fun a _ => finiteCovarianceQuadratic_nonneg_of_posSemidef
        (C a) (hC a) _)
    simpa only [finiteCovarianceQuadratic, dotProduct, Matrix.mulVec,
      Pi.star_apply, star_trivial, Finset.mul_sum, mul_assoc] using hh

/-- Fubini with an explicit family of measures; unlike a constant `volume`,
the coordinate laws are allowed to differ. -/
lemma integral_pi_prod_complex {κ X : Type*} [Fintype κ] [MeasurableSpace X]
    (μ : κ → Measure X) [∀ a, SigmaFinite (μ a)] (f : κ → X → ℂ) :
    (∫ x, ∏ a, f a (x a) ∂Measure.pi μ) = ∏ a, ∫ y, f a y ∂μ a := by
  let ms : ∀ a : κ, MeasureSpace X := fun a => ⟨μ a⟩
  have h := @integral_fintype_prod_eq_prod ℂ inferInstance κ inferInstance
    (fun _ => X) f ms (fun a => (inferInstance : SigmaFinite (μ a)))
  simpa only [volume_pi] using h

/-- A literal finite product law, mapped into the physical flattened coordinates. -/
def channelGaussianProduct {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] (C : κ → Matrix ι ι ℝ) (hC : ∀ a, (C a).PosSemidef) :
    Measure ((κ × ι) → ℝ) :=
  Measure.map flattenChannels (Measure.pi (fun a => gaussianCovarianceLaw (C a) (hC a)))

instance {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (C : κ → Matrix ι ι ℝ) (hC : ∀ a, (C a).PosSemidef) :
    IsProbabilityMeasure (channelGaussianProduct C hC) :=
  MeasureTheory.isProbabilityMeasure_map measurable_flattenChannels.aemeasurable

/-- The characteristic function is calculated from an actual product measure. -/
theorem channelGaussianProduct_characteristic {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (C : κ → Matrix ι ι ℝ) (hC : ∀ a, (C a).PosSemidef) :
    HasGaussianCovariance (channelGaussianProduct C hC) (channelBlockCovariance C) := by
  intro t
  rw [channelGaussianProduct, integral_map measurable_flattenChannels.aemeasurable]
  · simp_rw [finiteLinearForm_flatten]
    have hexp (x : κ → ι → ℝ) :
        Complex.exp ((↑(∑ a, finiteLinearForm (fun i => t (a, i)) (x a)) : ℂ) * Complex.I) =
          ∏ a, Complex.exp ((↑(finiteLinearForm (fun i => t (a, i)) (x a)) : ℂ) * Complex.I) := by
      simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    simp_rw [hexp]
    rw [integral_pi_prod_complex (fun a => gaussianCovarianceLaw (C a) (hC a))
      (fun a x => Complex.exp ((↑(finiteLinearForm (fun i => t (a, i)) x) : ℂ) * Complex.I))]
    have hchar (a : κ) :
        (∫ x, Complex.exp ((↑(finiteLinearForm (fun i => t (a, i)) x) : ℂ) * Complex.I)
          ∂gaussianCovarianceLaw (C a) (hC a)) =
            Complex.exp (↑(-(1 / 2 : ℝ) *
              finiteCovarianceQuadratic (C a) (fun i => t (a, i))) : ℂ) :=
      gaussianCovarianceLaw_characteristic (C a) (hC a) _
    simp_rw [hchar]
    rw [← Complex.exp_sum]
    congr 1
    rw [finiteCovarianceQuadratic_channelBlock]
    push_cast
    rw [Finset.mul_sum]
  · exact Complex.continuous_exp.measurable.comp
      ((((continuous_finiteLinearForm t).measurable).complex_ofReal).mul measurable_const)
      |>.aestronglyMeasurable

/-- Joint Gaussianity and block covariance imply equality with the actual
flattened product measure, including zero-variance or other singular blocks. -/
theorem gaussian_eq_flattened_product {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (ν : Measure ((κ × ι) → ℝ)) [IsProbabilityMeasure ν]
    (C : κ → Matrix ι ι ℝ) (hC : ∀ a, (C a).PosSemidef)
    (hν : HasGaussianCovariance ν (channelBlockCovariance C)) :
    ν = Measure.map flattenChannels
      (Measure.pi (fun a => gaussianCovarianceLaw (C a) (hC a))) := by
  change ν = channelGaussianProduct C hC
  apply measure_eq_of_linear_characteristic
  intro t
  exact (hν t).trans (channelGaussianProduct_characteristic C hC t).symm

/-- The canonical Gaussian covariance law has the same actual product form. -/
theorem gaussianCovarianceLaw_channelBlock_eq_product {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (C : κ → Matrix ι ι ℝ) (hC : ∀ a, (C a).PosSemidef)
    (hBlock : (channelBlockCovariance C).PosSemidef) :
    gaussianCovarianceLaw (channelBlockCovariance C) hBlock =
      Measure.map flattenChannels
        (Measure.pi (fun a => gaussianCovarianceLaw (C a) (hC a))) :=
  gaussian_eq_flattened_product _ C hC (gaussianCovarianceLaw_characteristic _ hBlock)

/-- Canonical form, with block positivity proved from the component blocks. -/
theorem gaussianCovarianceLaw_channel_product {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (C : κ → Matrix ι ι ℝ) (hC : ∀ a, (C a).PosSemidef) :
    gaussianCovarianceLaw (channelBlockCovariance C)
      (channelBlockCovariance_posSemidef C hC) =
        Measure.map flattenChannels
          (Measure.pi (fun a => gaussianCovarianceLaw (C a) (hC a))) :=
  gaussianCovarianceLaw_channelBlock_eq_product C hC _

/-- A general centered real Gaussian is an actual scaled standard-normal law. -/
lemma centeredGaussian_eq_scaled_standard (v : ℝ≥0) :
    Measure.map (fun x : ℝ => Real.sqrt (v : ℝ) * x) standardNormal = gaussianReal 0 v := by
  have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    (Real.sqrt (v : ℝ))
  simpa only [standardNormal, mul_zero, mul_one, Real.sq_sqrt v.coe_nonneg,
    NNReal.coe_mk] using h

/-- The fourth moment is computed from the independent standard-normal model. -/
theorem centeredGaussian_fourth_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  rw [← centeredGaussian_eq_scaled_standard v,
    integral_map (by fun_prop : AEMeasurable (fun x : ℝ => Real.sqrt (v : ℝ) * x) standardNormal)
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 4)
        (Measure.map (fun x : ℝ => Real.sqrt (v : ℝ) * x) standardNormal))]
  simp_rw [mul_pow]
  rw [integral_const_mul, standardNormal_moment_four]
  have hs := Real.sq_sqrt v.coe_nonneg
  nlinarith [sq_nonneg (v : ℝ)]

lemma posSemidef_diagonal_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (i : ι) : 0 ≤ C i i := by
  have h := finiteCovarianceQuadratic_nonneg_of_posSemidef C hC
    (fun j => if j = i then 1 else 0)
  simpa [finiteCovarianceQuadratic, mul_ite, ite_mul] using h

/-- Each coordinate marginal has its own diagonal variance, with degeneracy
allowed. This is an equality of actual real probability measures. -/
theorem gaussianCovarianceLaw_coordinate_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (i : ι) :
    Measure.map (fun x : ι → ℝ => x i) (gaussianCovarianceLaw C hC) =
      gaussianReal 0 ⟨C i i, posSemidef_diagonal_nonneg C hC i⟩ := by
  have h := centeredGaussian_linearProjection (gaussianCovarianceLaw C hC) C
    (finiteCovarianceQuadratic_nonneg_of_posSemidef C hC)
    (gaussianCovarianceLaw_characteristic C hC) (fun j => if j = i then 1 else 0)
  have hl : finiteLinearForm (fun j => if j = i then 1 else 0) = (fun x : ι → ℝ => x i) := by
    funext x
    simp [finiteLinearForm, ite_mul]
  rw [hl] at h
  simpa [finiteCovarianceQuadratic, mul_ite, ite_mul] using h

/-- Every coordinate of an actual Gaussian covariance law has all integer moments. -/
theorem gaussianCovarianceLaw_coordinate_integrable_pow {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (i : ι) (n : ℕ) :
    Integrable (fun x : ι → ℝ => x i ^ n) (gaussianCovarianceLaw C hC) := by
  have hi := centeredGaussian_integrable_pow
    ⟨C i i, posSemidef_diagonal_nonneg C hC i⟩ n
  rw [← gaussianCovarianceLaw_coordinate_map C hC i] at hi
  exact (integrable_map_measure (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y ^ n)
    (Measure.map (fun x : ι → ℝ => x i) (gaussianCovarianceLaw C hC)))
      (measurable_pi_apply i).aemeasurable).mp hi

theorem gaussianCovarianceLaw_coordinate_second {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (i : ι) :
    (∫ x, x i ^ 2 ∂gaussianCovarianceLaw C hC) = C i i := by
  calc
    _ = ∫ y : ℝ, y ^ 2 ∂Measure.map (fun x : ι → ℝ => x i)
        (gaussianCovarianceLaw C hC) :=
      (integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)).symm
    _ = _ := by
      rw [gaussianCovarianceLaw_coordinate_map, centeredGaussian_second_moment]
      rfl

theorem gaussianCovarianceLaw_coordinate_fourth {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (i : ι) :
    (∫ x, x i ^ 4 ∂gaussianCovarianceLaw C hC) = 3 * (C i i) ^ 2 := by
  calc
    _ = ∫ y : ℝ, y ^ 4 ∂Measure.map (fun x : ι → ℝ => x i)
        (gaussianCovarianceLaw C hC) :=
      (integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)).symm
    _ = _ := by
      rw [gaussianCovarianceLaw_coordinate_map, centeredGaussian_fourth_moment]
      rfl

/-- Bounded covariance diagonals give a uniform fourth bound for the whole
physical vector, supplying the moment input for Gaussian-target continuity. -/
theorem gaussianCovarianceLaw_squareMass_fourth_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i, C i i ≤ B) :
    Integrable (fun x => squareMass x ^ 2) (gaussianCovarianceLaw C hC) ∧
      (∫ x, squareMass x ^ 2 ∂gaussianCovarianceLaw C hC) ≤
        3 * B ^ 2 * (Fintype.card ι : ℝ) ^ 2 := by
  apply integral_squareMass_sq_le _
    (fun i => gaussianCovarianceLaw_coordinate_integrable_pow C hC i 4) (3 * B ^ 2)
  intro i
  rw [gaussianCovarianceLaw_coordinate_fourth]
  have hi := posSemidef_diagonal_nonneg C hC i
  nlinarith [hB i]

/-- The corresponding sup-norm fourth bound for the compactness API. -/
theorem gaussianCovarianceLaw_norm_fourth_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i, C i i ≤ B) :
    Integrable (fun x => ‖x‖ ^ 4) (gaussianCovarianceLaw C hC) ∧
      (∫ x, ‖x‖ ^ 4 ∂gaussianCovarianceLaw C hC) ≤
        3 * B ^ 2 * (Fintype.card ι : ℝ) ^ 2 := by
  apply integral_pi_norm_fourth_le _
    (fun i => gaussianCovarianceLaw_coordinate_integrable_pow C hC i 4) (3 * B ^ 2)
  intro i
  rw [gaussianCovarianceLaw_coordinate_fourth]
  have hi := posSemidef_diagonal_nonneg C hC i
  nlinarith [hB i]

end GaussianWave
