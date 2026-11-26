import GaussianWave.BS.IndependentAddition
import GaussianWave.BS.SecondMomentTransport

/-! Actual second moments of independent sums. Only the noise must be
centered; the signal needs no density or higher moments. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

variable {I : Type*} [Fintype I]

theorem independentAddLaw_integrable_squareRadius
    (μ ν : Measure (I → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (squareRadius (I := I)) μ)
    (hν : Integrable (squareRadius (I := I)) ν) :
    Integrable (squareRadius (I := I)) (independentAddLaw μ ν 1) := by
  have hA : Measurable (fun p : (I → ℝ) × (I → ℝ) => p.1+(1 : ℝ) • p.2) :=
    (continuous_fst.add (continuous_const.smul continuous_snd)).measurable
  apply (integrable_map_measure continuous_squareRadius.measurable.aestronglyMeasurable hA.aemeasurable).mpr
  have hl : Integrable (fun p : (I → ℝ) × (I → ℝ) => squareRadius p.1) (μ.prod ν) := by
    simpa only [mul_one] using hμ.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : I → ℝ => (1 : ℝ)) ν)
  have hr : Integrable (fun p : (I → ℝ) × (I → ℝ) => squareRadius p.2) (μ.prod ν) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) : Integrable (fun _ : I → ℝ => (1 : ℝ)) μ).mul_prod hν
  refine ((hl.add hr).const_mul 2).mono' (continuous_squareRadius.measurable.comp hA).aestronglyMeasurable ?_
  filter_upwards [] with p
  change |squareRadius (p.1+(1 : ℝ) • p.2)| ≤ 2*(squareRadius p.1+squareRadius p.2)
  rw [abs_of_nonneg (squareRadius_nonneg _)]
  simp only [one_smul]
  unfold squareRadius
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change (p.1 i+p.2 i)^2 ≤ 2*(p.1 i^2+p.2 i^2)
  nlinarith [sq_nonneg (p.1 i-p.2 i)]

theorem independentAddLaw_secondMoments
    (μ ν : Measure (I → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (squareRadius (I := I)) μ)
    (hν : Integrable (squareRadius (I := I)) ν)
    (hmean : ∀ i,(∫ y,y i ∂ν)=0)
    (C S : Matrix I I ℝ) (hC : HasSecondMoments μ C) (hS : HasSecondMoments ν S) :
    HasSecondMoments (independentAddLaw μ ν 1) (C+S) := by
  intro i j
  let L := fun p : (I → ℝ) × (I → ℝ) => p.1 i*p.1 j
  let R := fun p : (I → ℝ) × (I → ℝ) => p.2 i*p.2 j
  let U := fun p : (I → ℝ) × (I → ℝ) => p.1 i*p.2 j
  let V := fun p : (I → ℝ) × (I → ℝ) => p.1 j*p.2 i
  have hiμ := integrable_coordinate_of_squareRadius μ hμ i
  have hjμ := integrable_coordinate_of_squareRadius μ hμ j
  have hiν := integrable_coordinate_of_squareRadius ν hν i
  have hjν := integrable_coordinate_of_squareRadius ν hν j
  have hL : Integrable L (μ.prod ν) := by
    simpa only [mul_one] using (integrable_coordinate_mul_of_squareRadius μ hμ i j).mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : I → ℝ => (1 : ℝ)) ν)
  have hR : Integrable R (μ.prod ν) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) : Integrable (fun _ : I → ℝ => (1 : ℝ)) μ).mul_prod
      (integrable_coordinate_mul_of_squareRadius ν hν i j)
  have hU : Integrable U (μ.prod ν) := hiμ.mul_prod hjν
  have hV : Integrable V (μ.prod ν) := hjμ.mul_prod hiν
  have hLi : (∫ p,L p ∂μ.prod ν)=C i j := by
    have h := integral_prod_mul (μ := μ) (ν := ν) (fun x : I → ℝ => x i*x j) (fun _ => (1 : ℝ))
    simpa only [mul_one,integral_const,measureReal_univ_eq_one,one_smul,hC i j] using h
  have hRi : (∫ p,R p ∂μ.prod ν)=S i j := by
    have h := integral_prod_mul (μ := μ) (ν := ν) (fun _ => (1 : ℝ)) (fun x : I → ℝ => x i*x j)
    simpa only [one_mul,integral_const,measureReal_univ_eq_one,one_smul,hS i j] using h
  have hUi : (∫ p,U p ∂μ.prod ν)=0 := by
    simpa only [hmean,mul_zero] using integral_prod_mul (μ := μ) (ν := ν)
      (fun x : I → ℝ => x i) (fun y : I → ℝ => y j)
  have hVi : (∫ p,V p ∂μ.prod ν)=0 := by
    simpa only [hmean,mul_zero] using integral_prod_mul (μ := μ) (ν := ν)
      (fun x : I → ℝ => x j) (fun y : I → ℝ => y i)
  have hA : Measurable (fun p : (I → ℝ) × (I → ℝ) => p.1+(1 : ℝ) • p.2) :=
    (continuous_fst.add (continuous_const.smul continuous_snd)).measurable
  have hf : AEStronglyMeasurable (fun x : I → ℝ => x i*x j)
      (Measure.map (fun p : (I → ℝ) × (I → ℝ) => p.1+(1 : ℝ) • p.2) (μ.prod ν)) :=
    ((continuous_apply i).mul (continuous_apply j)).measurable.aestronglyMeasurable
  rw [independentAddLaw,integral_map hA.aemeasurable hf]
  have he (p : (I → ℝ) × (I → ℝ)) :
      (p.1+(1 : ℝ) • p.2) i*(p.1+(1 : ℝ) • p.2) j=L p+U p+V p+R p := by
    simp only [one_smul,Pi.add_apply,L,R,U,V]
    ring
  simp_rw [he]
  rw [integral_add (μ := μ.prod ν) (f := fun p => L p+U p+V p) (g := R) ((hL.add hU).add hV) hR,
    integral_add (μ := μ.prod ν) (f := fun p => L p+U p) (g := V) (hL.add hU) hV,
    integral_add (μ := μ.prod ν) (f := L) (g := U) hL hU,hLi,hUi,hVi,hRi]
  simp only [add_zero,Matrix.add_apply]

end GaussianWave.BS
