import GeneralizedBulk.Entropy.GaussianPoincare

/-! Gaussian Poincaré for the actual possibly singular linear-image Gaussian
law, with the actual covariance operator norm. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix.L2OpNorm
namespace GeneralizedBulk.Entropy.Hermite
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def rectangularMatrixCLM (A : Matrix I J ℝ) : (J → ℝ) →L[ℝ] (I → ℝ) :=
  (Matrix.toLin' A).toContinuousLinearMap

@[simp] theorem rectangularMatrixCLM_apply (A : Matrix I J ℝ) (x : J → ℝ) :
    rectangularMatrixCLM A x = A.mulVec x := rfl

theorem finitePi_eq_sum_single (v : I → ℝ) : v = ∑ i, v i • (Pi.single i (1 : ℝ) : I → ℝ) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  simp

/-- Actual chain rule for rectangular Gaussian observation maps. -/
theorem coordinateGradient_comp_matrix (A : Matrix I J ℝ) (f : (I → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (j : J) (x : J → ℝ) :
    coordinateGradient (fun x => f (A.mulVec x)) j x =
      ∑ i, A i j * coordinateGradient f i (A.mulVec x) := by
  have hh := ((hf.differentiable le_rfl) (A.mulVec x)).hasFDerivAt.comp x (rectangularMatrixCLM A).hasFDerivAt
  change fderiv ℝ (f ∘ A.mulVec) x (Pi.single j 1) = _
  rw [hh.fderiv]
  change fderiv ℝ f (A.mulVec x) (A.mulVec (Pi.single j 1)) = _
  rw [Matrix.mulVec_single_one, finitePi_eq_sum_single (A.transpose j)]
  simp only [map_sum, map_smul, smul_eq_mul, coordinateGradient, Matrix.transpose_apply]

theorem euclidean_toLp_norm_sq {T : Type*} [Fintype T] (v : T → ℝ) :
    ‖(WithLp.equiv 2 (T → ℝ)).symm v‖ ^ 2 = ∑ t, v t ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]
  rfl

/-- The covariance controls the squared coordinate derivative of the linear
pullback; its coefficient is the actual Euclidean matrix operator norm. -/
theorem matrix_gradient_energy_le_covariance (A : Matrix I J ℝ) (u : I → ℝ) :
    (∑ j, (∑ i, A i j * u i) ^ 2) ≤ ‖A * A.transpose‖ * ∑ i, u i ^ 2 := by
  let v : EuclideanSpace ℝ I := (WithLp.equiv 2 (I → ℝ)).symm u
  have hb := Matrix.l2_opNorm_mulVec A.transpose v
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow] at hs
  have he : ‖A * A.transpose‖ = ‖A.transpose‖ ^ 2 := by
    have hh := Matrix.l2_opNorm_conjTranspose_mul_self A.transpose
    simpa only [Matrix.conjTranspose, star_trivial, Matrix.map_id, Matrix.transpose_transpose, pow_two] using hh
  change ‖(WithLp.equiv 2 (J → ℝ)).symm (A.transpose.mulVec u)‖ ^ 2 ≤
    ‖A.transpose‖ ^ 2 * ‖(WithLp.equiv 2 (I → ℝ)).symm u‖ ^ 2 at hs
  rw [euclidean_toLp_norm_sq, euclidean_toLp_norm_sq, ← he] at hs
  simpa only [Matrix.mulVec, Matrix.transpose_apply, dotProduct] using hs


/-- Sharp Poincaré for an actual correlated Gaussian linear image. It remains
valid for singular covariance; the coefficient is its actual operator norm. -/
theorem correlated_gaussian_poincare_bounded_C1 (A : Matrix I J ℝ)
    (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (M : ℝ) (hM : ∀ x, |f x| ≤ M)
    (L : I → ℝ) (hL : ∀ i x, |coordinateGradient f i x| ≤ L i) :
    (∫ y, (f y - ∫ z, f z ∂GeneralizedBulk.Gaussian.linearImageGaussian A) ^ 2
      ∂GeneralizedBulk.Gaussian.linearImageGaussian A) ≤
      ‖A * A.transpose‖ * ∫ y, ∑ i, coordinateGradient f i y ^ 2
        ∂GeneralizedBulk.Gaussian.linearImageGaussian A := by
  let ψ := fun x : J → ℝ => f (A.mulVec x)
  let Lj := fun j : J => ∑ i : I, |A i j| * L i
  have hψ : ContDiff ℝ 1 ψ := hf.comp (rectangularMatrixCLM A).contDiff
  have hψb (x : J → ℝ) : |ψ x| ≤ M := hM _
  have hψL (j : J) (x : J → ℝ) : |coordinateGradient ψ j x| ≤ Lj j := by
    rw [coordinateGradient_comp_matrix A f hf]
    calc
      _ ≤ ∑ i, |A i j * coordinateGradient f i (A.mulVec x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hL i _) (abs_nonneg _)
  have hstd := gaussian_poincare_bounded_C1 ψ hψ M hψb Lj hψL
  have henergy (x : J → ℝ) : (∑ j, coordinateGradient ψ j x ^ 2) ≤
      ‖A * A.transpose‖ * ∑ i, coordinateGradient f i (A.mulVec x) ^ 2 := by
    change (∑ j, coordinateGradient (fun x => f (A.mulVec x)) j x ^ 2) ≤ _
    simp_rw [coordinateGradient_comp_matrix A f hf]
    exact matrix_gradient_energy_le_covariance A _
  have hjint (j : J) : Integrable (fun x => coordinateGradient ψ j x ^ 2) (standardGaussian J) :=
    (MemLp.of_bound (p := (2 : ENNReal)) (continuous_coordinateGradient ψ hψ j).aestronglyMeasurable
      (Lj j) (Filter.Eventually.of_forall (hψL j))).integrable_sq
  have hiint (i : I) : Integrable (fun x : J → ℝ => coordinateGradient f i (A.mulVec x) ^ 2) (standardGaussian J) :=
    (MemLp.of_bound (p := (2 : ENNReal))
      ((continuous_coordinateGradient f hf i).comp (rectangularMatrixCLM A).continuous).aestronglyMeasurable
      (L i) (Filter.Eventually.of_forall (fun x => hL i (A.mulVec x)))).integrable_sq
  have hsumj := integrable_finset_sum Finset.univ (fun j _ => hjint j)
  have hsumi := integrable_finset_sum Finset.univ (fun i _ => hiint i)
  have hbound : (∫ x, ∑ j, coordinateGradient ψ j x ^ 2 ∂standardGaussian J) ≤
      ‖A * A.transpose‖ * ∫ x, ∑ i, coordinateGradient f i (A.mulVec x) ^ 2 ∂standardGaussian J := by
    calc
      _ ≤ ∫ x, ‖A * A.transpose‖ * ∑ i, coordinateGradient f i (A.mulVec x) ^ 2 ∂standardGaussian J :=
        integral_mono_ae hsumj (hsumi.const_mul _) (Filter.Eventually.of_forall henergy)
      _ = _ := integral_const_mul _ _
  have hAm := GeneralizedBulk.Gaussian.measurable_finiteMatrixAction A
  have hmean : (∫ y, f y ∂GeneralizedBulk.Gaussian.linearImageGaussian A) =
      ∫ x, ψ x ∂standardGaussian J := by
    change (∫ y, f y ∂Measure.map (fun x => A.mulVec x) (standardGaussian J)) = _
    rw [integral_map hAm.aemeasurable hf.continuous.aestronglyMeasurable]
  have hEcont : Continuous (fun y : I → ℝ => ∑ i, coordinateGradient f i y ^ 2) :=
    continuous_finset_sum _ (fun i _ => (continuous_coordinateGradient f hf i).pow 2)
  have hmapE : (∫ y, ∑ i, coordinateGradient f i y ^ 2 ∂GeneralizedBulk.Gaussian.linearImageGaussian A) =
      ∫ x, ∑ i, coordinateGradient f i (A.mulVec x) ^ 2 ∂standardGaussian J := by
    change (∫ y, ∑ i, coordinateGradient f i y ^ 2 ∂Measure.map (fun x => A.mulVec x) (standardGaussian J)) = _
    rw [integral_map hAm.aemeasurable hEcont.aestronglyMeasurable]
  rw [hmapE, hmean]
  change (∫ y, (f y - ∫ x, ψ x ∂standardGaussian J) ^ 2
    ∂Measure.map (fun x => A.mulVec x) (standardGaussian J)) ≤ _
  rw [integral_map hAm.aemeasurable ((hf.continuous.sub continuous_const).pow 2).aestronglyMeasurable]
  exact hstd.trans hbound


/-- A proved pointwise squared-gradient sensitivity gives the corresponding
actual correlated Gaussian variance bound with the covariance operator norm. -/
theorem correlated_gaussian_variance_le_energy_constant (A : Matrix I J ℝ)
    (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (M : ℝ) (hM : ∀ x, |f x| ≤ M)
    (L : I → ℝ) (hL : ∀ i x, |coordinateGradient f i x| ≤ L i)
    (E : ℝ) (hE : ∀ x, (∑ i, coordinateGradient f i x ^ 2) ≤ E) :
    (∫ y, (f y - ∫ z, f z ∂GeneralizedBulk.Gaussian.linearImageGaussian A) ^ 2
      ∂GeneralizedBulk.Gaussian.linearImageGaussian A) ≤ ‖A * A.transpose‖ * E := by
  have hi (i : I) : Integrable (fun x : I → ℝ => coordinateGradient f i x ^ 2)
      (GeneralizedBulk.Gaussian.linearImageGaussian A) :=
    (MemLp.of_bound (p := (2 : ENNReal)) (continuous_coordinateGradient f hf i).aestronglyMeasurable
      (L i) (Filter.Eventually.of_forall (hL i))).integrable_sq
  have hh : (∫ y, ∑ i, coordinateGradient f i y ^ 2 ∂GeneralizedBulk.Gaussian.linearImageGaussian A) ≤ E := by
    have hmono := integral_mono (integrable_finset_sum _ (fun i _ => hi i)) (integrable_const E) hE
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hmono
  exact (correlated_gaussian_poincare_bounded_C1 A f hf M hM L hL).trans
    (mul_le_mul_of_nonneg_left hh (norm_nonneg _))

end GeneralizedBulk.Entropy.Hermite
