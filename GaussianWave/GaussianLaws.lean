import GaussianWave.GaussianNormalization

/-! Actual finite Gaussian probability measures, their characteristic functions,
uniqueness, and covariance factors. Adapted from the user's earlier standalone
Gaussian algebra proofs; no earlier project is imported. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology Classical
namespace GaussianWave

def standardNormal : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure standardNormal := by
  unfold standardNormal
  infer_instance

theorem standardNormal_mgf (t : ℝ) :
    mgf id standardNormal t = Real.exp (t ^ 2 / 2) := by
  have hm : Measure.map id standardNormal = gaussianReal 0 1 := by
    simp [standardNormal]
  simpa using mgf_gaussianReal hm t

theorem standardNormal_integrableExpSet : integrableExpSet id standardNormal = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact mgf_pos_iff.mp (by rw [standardNormal_mgf]; exact Real.exp_pos _)

theorem standardNormal_zero_interior :
    (0 : ℝ) ∈ interior (integrableExpSet id standardNormal) := by
  rw [standardNormal_integrableExpSet, interior_univ]
  trivial

theorem standardNormal_integrable_pow (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) standardNormal := by
  exact integrable_pow_of_mem_interior_integrableExpSet standardNormal_zero_interior n

private def f0 (x : ℝ) : ℝ := Real.exp (x ^ 2 / 2)
private def f1 (x : ℝ) : ℝ := x * f0 x
private def f2 (x : ℝ) : ℝ := (x ^ 2 + 1) * f0 x
private def f3 (x : ℝ) : ℝ := (x ^ 3 + 3 * x) * f0 x
private def f4 (x : ℝ) : ℝ := (x ^ 4 + 6 * x ^ 2 + 3) * f0 x

private theorem df0 (x : ℝ) : HasDerivAt f0 (f1 x) x := by
  have hd := ((hasDerivAt_id x).pow 2).div_const 2
  convert hd.exp using 1; simp [f0, f1]; ring

private theorem df1 (x : ℝ) : HasDerivAt f1 (f2 x) x := by
  convert (hasDerivAt_id x).mul (df0 x) using 1; simp [f0, f1, f2]; ring

private theorem df2 (x : ℝ) : HasDerivAt f2 (f3 x) x := by
  convert (((hasDerivAt_id x).pow 2).add_const 1).mul (df0 x) using 1;
    simp [f0, f1, f2, f3]; ring

private theorem df3 (x : ℝ) : HasDerivAt f3 (f4 x) x := by
  convert (((hasDerivAt_id x).pow 3).add ((hasDerivAt_id x).const_mul 3)).mul (df0 x)
    using 1; simp [f0, f1, f3, f4]; ring

private theorem iterated_f1 : iteratedDeriv 1 f0 = f1 := by
  funext x
  simpa using (df0 x).deriv

private theorem iterated_f2 : iteratedDeriv 2 f0 = f2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iterated_f1]
  funext x
  exact (df1 x).deriv

private theorem iterated_f3 : iteratedDeriv 3 f0 = f3 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, iterated_f2]
  funext x
  exact (df2 x).deriv

private theorem iterated_f4 : iteratedDeriv 4 f0 = f4 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, iterated_f3]
  funext x
  exact (df3 x).deriv

theorem standardNormal_moment_zero : (∫ x : ℝ, x ^ 0 ∂standardNormal) = 1 := by simp

theorem standardNormal_moment_one : (∫ x : ℝ, x ∂standardNormal) = 0 := by
  have h := iteratedDeriv_mgf_zero standardNormal_zero_interior 1
  rw [show mgf id standardNormal = f0 from funext standardNormal_mgf, iterated_f1] at h
  simpa [f1, f0] using h.symm

theorem standardNormal_moment_two : (∫ x : ℝ, x ^ 2 ∂standardNormal) = 1 := by
  have h := iteratedDeriv_mgf_zero standardNormal_zero_interior 2
  rw [show mgf id standardNormal = f0 from funext standardNormal_mgf, iterated_f2] at h
  simpa [f2, f0] using h.symm

theorem standardNormal_moment_three : (∫ x : ℝ, x ^ 3 ∂standardNormal) = 0 := by
  have h := iteratedDeriv_mgf_zero standardNormal_zero_interior 3
  rw [show mgf id standardNormal = f0 from funext standardNormal_mgf, iterated_f3] at h
  simpa [f3, f0] using h.symm

theorem standardNormal_moment_four : (∫ x : ℝ, x ^ 4 ∂standardNormal) = 3 := by
  have h := iteratedDeriv_mgf_zero standardNormal_zero_interior 4
  rw [show mgf id standardNormal = f0 from funext standardNormal_mgf, iterated_f4] at h
  simpa [f4, f0] using h.symm


theorem measure_eq_of_linear_characteristic
    {ι : Type*} [Fintype ι]
    (μ ν : Measure (ι → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ι → ℝ,
      (∫ x, Complex.exp ((↑(∑ i, t i * x i) : ℂ) * Complex.I) ∂μ) =
      (∫ x, Complex.exp ((↑(∑ i, t i * x i) : ℂ) * Complex.I) ∂ν)) :
    μ = ν := by
  let e := EuclideanSpace.measurableEquiv ι
  apply MeasurableEquiv.map_measurableEquiv_injective e.symm
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, charFun_apply]
  have hc : Continuous (fun x : EuclideanSpace ℝ ι =>
      Complex.exp ((↑(@inner ℝ _ _ x t) : ℂ) * Complex.I)) := by fun_prop
  rw [integral_map e.symm.measurable.aemeasurable hc.stronglyMeasurable.aestronglyMeasurable,
    integral_map e.symm.measurable.aemeasurable hc.stronglyMeasurable.aestronglyMeasurable]
  simpa [PiLp.inner_apply, mul_comm] using h (fun i => t i)


theorem scalar_characteristic (t : ℝ) :
    (∫ x : ℝ, Complex.exp ((↑(t * x) : ℂ) * Complex.I) ∂standardNormal) =
      Complex.exp (-((t : ℂ) ^ 2) / 2) := by
  calc
    _ = complexMGF id standardNormal ((t : ℂ) * Complex.I) := by
      unfold complexMGF
      apply integral_congr_ae
      filter_upwards with x
      congr 1
      simp only [id_eq]
      push_cast
      ring
    _ = _ := by
      rw [standardNormal, complexMGF_id_gaussianReal]
      congr 1
      norm_num [mul_pow, Complex.I_sq]


def standardVector (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => standardNormal)

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (standardVector ι) := by
  unfold standardVector
  infer_instance

theorem standardVector_characteristic {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂standardVector ι) =
      Complex.exp (↑(-(1 / 2 : ℝ) * ∑ i, t i ^ 2) : ℂ) := by
  have hprod : (fun x : ι → ℝ => Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I)) =
      (fun x => ∏ i, Complex.exp ((↑(t i * x i) : ℂ) * Complex.I)) := by
    funext x
    simp only [finiteLinearForm, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  rw [hprod]
  have hfub : (∫ x, ∏ i, Complex.exp ((↑(t i * x i) : ℂ) * Complex.I) ∂standardVector ι) =
      ∏ i, ∫ a : ℝ, Complex.exp ((↑(t i * a) : ℂ) * Complex.I) ∂standardNormal := by
    letI : MeasureSpace ℝ := ⟨standardNormal⟩
    letI : IsProbabilityMeasure (volume : Measure ℝ) :=
      (inferInstance : IsProbabilityMeasure standardNormal)
    simpa only [standardVector, volume_pi] using integral_fintype_prod_eq_prod ι
      (fun i : ι => fun a : ℝ => Complex.exp ((↑(t i * a) : ℂ) * Complex.I))
  rw [hfub]
  simp_rw [scalar_characteristic]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem measurable_finiteMatrixAction {ι κ : Type*} [Fintype ι]
    (O : Matrix κ ι ℝ) : Measurable (fun x : ι → ℝ => O.mulVec x) := by
  apply measurable_pi_lambda
  intro i
  exact Finset.measurable_sum _ (fun j hj => measurable_const.mul (measurable_pi_apply j))

theorem finiteLinearForm_matrixAction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (O : Matrix κ ι ℝ) (t : κ → ℝ) (x : ι → ℝ) :
    finiteLinearForm t (O.mulVec x) = finiteLinearForm (Matrix.vecMul t O) x :=
  Matrix.dotProduct_mulVec t O x

theorem vecMul_sq_sum_of_orthogonal {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℝ) (hO : O * O.transpose = 1) (t : ι → ℝ) :
    (∑ i, (Matrix.vecMul t O i) ^ 2) = ∑ i, t i ^ 2 := by
  calc
    _ = Matrix.vecMul t O ⬝ᵥ (O.transpose.mulVec t) := by
      rw [Matrix.mulVec_transpose]
      simp only [dotProduct, pow_two]
    _ = t ⬝ᵥ O.mulVec (O.transpose.mulVec t) := (Matrix.dotProduct_mulVec ..).symm
    _ = t ⬝ᵥ (O * O.transpose).mulVec t := by rw [Matrix.mulVec_mulVec]
    _ = _ := by rw [hO, Matrix.one_mulVec]; simp only [dotProduct, pow_two]

/-- Orthogonal invariance is proved for the actual finite independent normal
product law, and works in every finite dimension used by channel whitening. -/
theorem standardVector_orthogonal_invariant {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℝ) (hO : O * O.transpose = 1) :
    Measure.map (fun x : ι → ℝ => O.mulVec x) (standardVector ι) = standardVector ι := by
  letI : IsProbabilityMeasure (Measure.map (fun x : ι → ℝ => O.mulVec x) (standardVector ι)) :=
    MeasureTheory.isProbabilityMeasure_map (measurable_finiteMatrixAction O).aemeasurable
  apply measure_eq_of_linear_characteristic
  intro t
  change (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I)
    ∂Measure.map (fun x : ι → ℝ => O.mulVec x) (standardVector ι)) = _
  rw [integral_map (measurable_finiteMatrixAction O).aemeasurable]
  · simp_rw [finiteLinearForm_matrixAction]
    rw [standardVector_characteristic, vecMul_sq_sum_of_orthogonal O hO t,
      ← standardVector_characteristic]
    rfl
  · apply Measurable.aestronglyMeasurable
    exact Complex.continuous_exp.measurable.comp
      ((((continuous_finiteLinearForm t).measurable).complex_ofReal).mul measurable_const)

theorem standardVector_orthogonal_measurePreserving {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℝ) (hO : O * O.transpose = 1) :
    MeasurePreserving (fun x : ι → ℝ => O.mulVec x) (standardVector ι) (standardVector ι) :=
  ⟨measurable_finiteMatrixAction O, standardVector_orthogonal_invariant O hO⟩

theorem finiteCovarianceQuadratic_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : Matrix κ ι ℝ) (t : κ → ℝ) :
    finiteCovarianceQuadratic (L * L.transpose) t = ∑ i, (Matrix.vecMul t L i) ^ 2 := by
  calc
    _ = t ⬝ᵥ (L * L.transpose).mulVec t := by
      simp only [finiteCovarianceQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    _ = t ⬝ᵥ L.mulVec (L.transpose.mulVec t) := by rw [Matrix.mulVec_mulVec]
    _ = Matrix.vecMul t L ⬝ᵥ (L.transpose.mulVec t) := Matrix.dotProduct_mulVec ..
    _ = _ := by rw [Matrix.mulVec_transpose]; simp only [dotProduct, pow_two]

def linearImageGaussian {ι κ : Type*} [Fintype ι] (L : Matrix κ ι ℝ) : Measure (κ → ℝ) :=
  Measure.map (fun x : ι → ℝ => L.mulVec x) (standardVector ι)

instance {ι κ : Type*} [Fintype ι] (L : Matrix κ ι ℝ) :
    IsProbabilityMeasure (linearImageGaussian L) :=
  MeasureTheory.isProbabilityMeasure_map (measurable_finiteMatrixAction L).aemeasurable

/-- Every finite rectangular linear image of actual independent standard
normals has its computed row-Gram characteristic function, even when singular. -/
theorem linearImageGaussian_characteristic {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : Matrix κ ι ℝ) (t : κ → ℝ) :
    (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂linearImageGaussian L) =
      Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic (L * L.transpose) t) : ℂ) := by
  rw [linearImageGaussian, integral_map (measurable_finiteMatrixAction L).aemeasurable]
  · simp_rw [finiteLinearForm_matrixAction]
    rw [standardVector_characteristic, finiteCovarianceQuadratic_gram]
  · exact Complex.continuous_exp.measurable.comp
      ((((continuous_finiteLinearForm t).measurable).complex_ofReal).mul measurable_const)
      |>.aestronglyMeasurable


/-- An actual possibly singular Gaussian law with any positive semidefinite
finite covariance, constructed from independent standard normal coordinates. -/
def gaussianCovarianceLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) : Measure (ι → ℝ) :=
  linearImageGaussian hC.sqrt

instance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    IsProbabilityMeasure (gaussianCovarianceLaw C hC) :=
  inferInstanceAs (IsProbabilityMeasure (linearImageGaussian hC.sqrt))

theorem gaussianCovarianceLaw_characteristic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    HasGaussianCovariance (gaussianCovarianceLaw C hC) C := by
  have hs : hC.sqrt.transpose = hC.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial, Matrix.map_id] using
      hC.posSemidef_sqrt.1
  intro t
  simpa only [gaussianCovarianceLaw, hs, hC.sqrt_mul_self] using
    linearImageGaussian_characteristic hC.sqrt t

theorem eq_gaussianCovarianceLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hν : HasGaussianCovariance ν C) :
    ν = gaussianCovarianceLaw C hC := by
  apply measure_eq_of_linear_characteristic
  intro t
  exact (hν t).trans (gaussianCovarianceLaw_characteristic C hC t).symm

end GaussianWave
