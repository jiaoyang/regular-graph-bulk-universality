import GaussianWave.GaussianProduct
import GaussianWave.StarComparison

/-! Actual Gaussian mixed fourth moments, including repeated coordinates and
singular covariance. Scalar Gaussian projections and a polarization identity
prove Wick's formula without an extra Gaussian-moment premise. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped BigOperators Classical NNReal

namespace GaussianWave

theorem gaussianCovarianceLaw_projection_fourth {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (hC : C.PosSemidef) (t : I → ℝ) :
    Integrable (fun x => finiteLinearForm t x^4) (gaussianCovarianceLaw C hC) ∧
      (∫ x,finiteLinearForm t x^4 ∂gaussianCovarianceLaw C hC)=
        3*finiteCovarianceQuadratic C t^2 := by
  let v : ℝ≥0 := ⟨finiteCovarianceQuadratic C t,
    finiteCovarianceQuadratic_nonneg_of_posSemidef C hC t⟩
  have hmap : Measure.map (finiteLinearForm t) (gaussianCovarianceLaw C hC)=
      ProbabilityTheory.gaussianReal 0 v :=
    centeredGaussian_linearProjection _ C (finiteCovarianceQuadratic_nonneg_of_posSemidef C hC)
      (gaussianCovarianceLaw_characteristic C hC) t
  have hm := centeredGaussian_fourth_moment v
  have hi := centeredGaussian_integrable_pow v 4
  rw [←hmap] at hi hm
  have hmeas := (continuous_finiteLinearForm t).measurable
  have hpow : AEStronglyMeasurable (fun y : ℝ => y^4)
      (Measure.map (finiteLinearForm t) (gaussianCovarianceLaw C hC)) := by fun_prop
  refine ⟨(integrable_map_measure hpow hmeas.aemeasurable).mp hi,?_⟩
  rw [integral_map hmeas.aemeasurable hpow] at hm
  exact hm

private def fourCoefficient {I : Type*} [DecidableEq I]
    (i j k l : I) (b c d : ℝ) : I → ℝ := fun a =>
  (if a=i then 1 else 0)+(if a=j then b else 0)+
    (if a=k then c else 0)+(if a=l then d else 0)

private theorem fourCoefficient_linear {I : Type*} [Fintype I] [DecidableEq I]
    (i j k l : I) (b c d : ℝ) (x : I → ℝ) :
    finiteLinearForm (fourCoefficient i j k l b c d) x =
      x i+b*x j+c*x k+d*x l := by
  simp [finiteLinearForm,fourCoefficient,add_mul,Finset.sum_add_distrib,ite_mul]

private theorem fourCoefficient_quadratic {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (hsym : ∀ a b,C b a=C a b)
    (i j k l : I) (b c d : ℝ) :
    finiteCovarianceQuadratic C (fourCoefficient i j k l b c d) =
      C i i+b^2*C j j+c^2*C k k+d^2*C l l+
        2*b*C i j+2*c*C i k+2*d*C i l+
        2*b*c*C j k+2*b*d*C j l+2*c*d*C k l := by
  simp only [finiteCovarianceQuadratic,fourCoefficient,add_mul,mul_add,
    Finset.sum_add_distrib,ite_mul,mul_ite,zero_mul,mul_zero,one_mul,mul_one,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [hsym j i,hsym k i,hsym l i,hsym k j,hsym l j,hsym l k]
  ring

/-- Wick's actual mixed fourth-moment formula for the covariance Gaussian
law. All four indices may coincide, and C may be degenerate. -/
theorem gaussianCovarianceLaw_mixed_fourth {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (hC : C.PosSemidef) (i j k l : I) :
    (∫ x,x i*x j*x k*x l ∂gaussianCovarianceLaw C hC)=
      C i j*C k l+C i k*C j l+C i l*C j k := by
  classical
  have hsym (a b : I) : C b a=C a b := by
    have h := congrFun (congrFun hC.1 a) b
    simpa only [Matrix.conjTranspose_apply,star_trivial] using h
  let b : Fin 8 → ℝ := ![1,1,1,1,-1,-1,-1,-1]
  let c : Fin 8 → ℝ := ![1,1,-1,-1,1,1,-1,-1]
  let d : Fin 8 → ℝ := ![1,-1,1,-1,1,-1,1,-1]
  let weight (a : Fin 8) := b a*c a*d a
  let t (a : Fin 8) := fourCoefficient i j k l (b a) (c a) (d a)
  have hpol (x : I → ℝ) :
      (192 : ℝ)*(x i*x j*x k*x l)=∑ a : Fin 8,weight a*finiteLinearForm (t a) x^4 := by
    norm_num [t,fourCoefficient_linear,weight,b,c,d,Fin.sum_univ_succ]
    ring
  have hcalc : (∑ a : Fin 8,weight a*(3*finiteCovarianceQuadratic C (t a)^2)) =
      192*(C i j*C k l+C i k*C j l+C i l*C j k) := by
    norm_num [t,fourCoefficient_quadratic C hsym,weight,b,c,d,Fin.sum_univ_succ]
    ring
  have hmoment : (192 : ℝ)*(∫ x,x i*x j*x k*x l ∂gaussianCovarianceLaw C hC)=
      192*(C i j*C k l+C i k*C j l+C i l*C j k) := by
    calc
      _ = ∫ x,(192 : ℝ)*(x i*x j*x k*x l) ∂gaussianCovarianceLaw C hC :=
        (integral_const_mul _ _).symm
      _ = ∫ x,∑ a : Fin 8,weight a*finiteLinearForm (t a) x^4 ∂gaussianCovarianceLaw C hC := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpol
      _ = ∑ a : Fin 8,∫ x,weight a*finiteLinearForm (t a) x^4 ∂gaussianCovarianceLaw C hC :=
        integral_finset_sum _ (fun a _ => (gaussianCovarianceLaw_projection_fourth C hC (t a)).1.const_mul _)
      _ = ∑ a : Fin 8,weight a*(3*finiteCovarianceQuadratic C (t a)^2) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [integral_const_mul,(gaussianCovarianceLaw_projection_fourth C hC (t a)).2]
      _ = _ := hcalc
  linarith

namespace RegularEigenData

theorem eigenStarGaussian_mixed_fourth {d N k : ℕ} (A : RegularEigenData d N k)
    (hd : 2≤d) (i j p q : Fin k × Fin (d+1)) :
    (∫ x,x i*x j*x p*x q ∂A.eigenStarGaussian hd)=
      A.eigenStarCovariance i j*A.eigenStarCovariance p q+
        A.eigenStarCovariance i p*A.eigenStarCovariance j q+
        A.eigenStarCovariance i q*A.eigenStarCovariance j p :=
  gaussianCovarianceLaw_mixed_fourth _ (A.eigenStarCovariance_posSemidef hd) i j p q

end RegularEigenData
end GaussianWave
