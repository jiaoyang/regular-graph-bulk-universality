import BourgadeHuang.RationalBulk.FiniteLoopAlgebra
import BourgadeHuang.RationalBulk.GaussianScoreIntegrability

/-! Global bounds and genuine integrability of the actual finite-particle tests
used in the Gaussian beta integration-by-parts identity. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

private theorem continuous_particle_reciprocal {N : ℕ} (i : Fin N) {w : ℂ} (hw : w.im≠0) :
    Continuous (fun x : Fin N → ℝ => ((x i:ℂ)-w)⁻¹) :=
  ((Complex.continuous_ofReal.comp (continuous_apply i)).sub continuous_const).inv₀
    (fun x => real_sub_ne_zero (x i) hw)

private theorem continuous_finite_resolvent {N : ℕ} {w : ℂ} (hw : w.im≠0) :
    Continuous (fun x : Fin N → ℝ => microscopicResolvent x 0 w) := by
  unfold microscopicResolvent
  exact (continuous_finset_sum _ (fun i _ => continuous_particle_reciprocal i hw)).sub continuous_const

theorem continuous_resolventTest {N n : ℕ} (i : Fin N) {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im≠0) (ha : ∀ a,(aux a).im≠0) :
    Continuous (fun x : Fin N → ℝ => resolventTest x w aux i) :=
  (continuous_particle_reciprocal i hw).mul
    (continuous_finset_prod _ (fun a _ => continuous_finite_resolvent (ha a)))

theorem continuous_resolventTestDerivative {N n : ℕ} (i : Fin N)
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im≠0) (ha : ∀ a,(aux a).im≠0) :
    Continuous (fun x : Fin N → ℝ => resolventTestDerivative x w aux i) := by
  unfold resolventTestDerivative excludedProduct
  exact (((continuous_particle_reciprocal i hw).pow 2).neg.mul
    (continuous_finset_prod _ (fun a _ => continuous_finite_resolvent (ha a)))).sub
      ((continuous_particle_reciprocal i hw).mul
        (continuous_finset_sum _ (fun a _ => ((continuous_particle_reciprocal i (ha a)).pow 2).mul
          (continuous_finset_prod _ (fun b _ => continuous_finite_resolvent (ha b))))))

private theorem norm_finite_resolvent_le {N : ℕ} (x : Fin N → ℝ) {w : ℂ} (hw : w.im≠0) :
    ‖microscopicResolvent x 0 w‖ ≤ (N:ℝ)/|w.im| := by
  simpa using norm_microscopicResolvent_le x 0 hw

private theorem norm_finite_resolvent_product_le {N n : ℕ} (x : Fin N → ℝ)
    (S : Finset (Fin n)) {aux : Fin n → ℂ} (ha : ∀ a,(aux a).im≠0) :
    ‖∏ a∈S,microscopicResolvent x 0 (aux a)‖ ≤ ∏ a∈S,(N:ℝ)/|(aux a).im| := by
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun a _ => norm_finite_resolvent_le x (ha a))

/-- A finite, deterministic bound independent of the particle positions. -/
theorem bounded_resolventTest {N n : ℕ} (i : Fin N) {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im≠0) (ha : ∀ a,(aux a).im≠0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin N → ℝ, ‖resolventTest x w aux i‖ ≤ C := by
  refine ⟨(1/|w.im|)*(∏ a,(N:ℝ)/|(aux a).im|),by positivity,fun x => ?_⟩
  rw [resolventTest,norm_mul]
  exact mul_le_mul (norm_reciprocal_le_im (x i) hw)
    (norm_finite_resolvent_product_le x Finset.univ ha) (norm_nonneg _) (by positivity)

/-- The derivative is bounded as well, even with coincident spectral parameters. -/
theorem bounded_resolventTestDerivative {N n : ℕ} (i : Fin N)
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im≠0) (ha : ∀ a,(aux a).im≠0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin N → ℝ, ‖resolventTestDerivative x w aux i‖ ≤ C := by
  let R := (1/|w.im|)
  let P := ∏ a,(N:ℝ)/|(aux a).im|
  let Q := fun a => ∏ b∈Finset.univ.erase a,(N:ℝ)/|(aux b).im|
  let T := ∑ a,(1/|(aux a).im|)^2*Q a
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : ∀ a,0 ≤ Q a := by intro a; dsimp [Q]; positivity
  have hT : 0 ≤ T := Finset.sum_nonneg (fun a _ => mul_nonneg (sq_nonneg _) (hQ a))
  refine ⟨R^2*P+R*T,by positivity,fun x => ?_⟩
  have hlead : ‖-(((x i:ℂ)-w)⁻¹)^2 * ∏ a,microscopicResolvent x 0 (aux a)‖ ≤ R^2*P := by
    rw [norm_mul,norm_neg,norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_reciprocal_le_im (x i) hw) 2)
      (norm_finite_resolvent_product_le x Finset.univ ha) (norm_nonneg _) (sq_nonneg R)
  have htail : ‖∑ a,(((x i:ℂ)-aux a)⁻¹)^2 *
      excludedProduct (fun b=>microscopicResolvent x 0 (aux b)) a‖ ≤ T := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    rw [norm_mul,norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_reciprocal_le_im (x i) (ha a)) 2)
      (norm_finite_resolvent_product_le x (Finset.univ.erase a) ha)
        (norm_nonneg _) (sq_nonneg _)
  apply (norm_sub_le _ _).trans
  apply add_le_add hlead
  rw [norm_mul]
  exact mul_le_mul (norm_reciprocal_le_im (x i) hw) htail (norm_nonneg _) hR

/-- Finite-measure integrability holds without any information about the particle law. -/
theorem integrable_resolventTest {N n : ℕ} (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ]
    (i : Fin N) {w : ℂ} {aux : Fin n → ℂ} (hw : w.im≠0) (ha : ∀ a,(aux a).im≠0) :
    Integrable (fun x => resolventTest x w aux i) μ := by
  obtain ⟨C,_,hC⟩ := bounded_resolventTest i hw ha
  exact (integrable_const C).mono' (continuous_resolventTest i hw ha).aestronglyMeasurable
    (Eventually.of_forall hC)

theorem integrable_resolventTestDerivative {N n : ℕ}
    (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ] (i : Fin N)
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im≠0) (ha : ∀ a,(aux a).im≠0) :
    Integrable (fun x => resolventTestDerivative x w aux i) μ := by
  obtain ⟨C,_,hC⟩ := bounded_resolventTestDerivative i hw ha
  exact (integrable_const C).mono' (continuous_resolventTestDerivative i hw ha).aestronglyMeasurable
    (Eventually.of_forall hC)

theorem gaussianBeta_integrable_resolventTest {N n : ℕ} {β : ℝ} (hβ : 0<β)
    (hN : 0<N) (i : Fin N) {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im≠0) (ha : ∀ a,(aux a).im≠0) :
    Integrable (fun x => resolventTest x w aux i) (gaussianBetaMeasure β N) := by
  letI := gaussianBetaMeasure_probability hβ hN
  exact integrable_resolventTest _ i hw ha

theorem gaussianBeta_integrable_resolventTestDerivative {N n : ℕ} {β : ℝ} (hβ : 0<β)
    (hN : 0<N) (i : Fin N) {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im≠0) (ha : ∀ a,(aux a).im≠0) :
    Integrable (fun x => resolventTestDerivative x w aux i) (gaussianBetaMeasure β N) := by
  letI := gaussianBetaMeasure_probability hβ hN
  exact integrable_resolventTestDerivative _ i hw ha

end BourgadeHuang.RationalBulk
