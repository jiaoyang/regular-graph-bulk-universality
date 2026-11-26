import BourgadeHuang.HolomorphicProduct
import BourgadeHuang.CountingParticleLabels
import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative genus-one factors for real counting configurations. -/
noncomputable section
open scoped Topology BigOperators
open MeasureTheory Filter
namespace BourgadeHuang

def genusOneFactor (w : ℂ) : ℂ := (1-w)*Complex.exp w

theorem hasDerivAt_genusOneFactor (w : ℂ) :
    HasDerivAt genusOneFactor (-w*Complex.exp w) w := by
  convert ((hasDerivAt_const w (1:ℂ)).sub (hasDerivAt_id w)).mul (Complex.hasDerivAt_exp w) using 1
  dsimp [genusOneFactor]
  ring

theorem differentiable_genusOneFactor : Differentiable ℂ genusOneFactor :=
  fun w => (hasDerivAt_genusOneFactor w).differentiableAt

/-- The first-order terms cancel globally, with an explicit quadratic remainder. -/
theorem norm_genusOneFactor_sub_one_le (w : ℂ) :
    ‖genusOneFactor w-1‖ ≤ ‖w‖^2*Real.exp ‖w‖ := by
  have hd (z : ℂ) : HasDerivWithinAt genusOneFactor (-z*Complex.exp z)
      (Metric.closedBall (0:ℂ) ‖w‖) z := (hasDerivAt_genusOneFactor z).hasDerivWithinAt
  have hb (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) ‖w‖) :
      ‖-z*Complex.exp z‖ ≤ ‖w‖*Real.exp ‖w‖ := by
    have hz' : ‖z‖ ≤ ‖w‖ := by simpa using hz
    rw [norm_mul,norm_neg]
    exact mul_le_mul hz' ((Complex.norm_exp_le_exp_norm z).trans (Real.exp_le_exp.mpr hz'))
      (norm_nonneg _) (norm_nonneg _)
  have h := (convex_closedBall (0:ℂ) ‖w‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => hd z) hb (Metric.mem_closedBall_self (norm_nonneg w))
    (show w ∈ Metric.closedBall (0:ℂ) ‖w‖ by simp)
  simpa only [genusOneFactor,sub_zero,Complex.exp_zero,mul_one,norm_sub_rev] using
    h.trans_eq (by ring)

/-- The canonical factor is normalized at i and has its only zero at the particle. -/
def canonicalParticleFactor (x : ℝ) (z : ℂ) : ℂ :=
  genusOneFactor ((z-Complex.I)/((x:ℂ)-Complex.I))

@[simp] theorem canonicalParticleFactor_I (x : ℝ) : canonicalParticleFactor x Complex.I = 1 := by
  simp [canonicalParticleFactor,genusOneFactor]

theorem differentiable_canonicalParticleFactor (x : ℝ) :
    Differentiable ℂ (canonicalParticleFactor x) :=
  differentiable_genusOneFactor.comp ((differentiable_id.sub_const _).div_const _)

theorem canonicalParticleFactor_ne_zero (x : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    canonicalParticleFactor x z ≠ 0 := by
  unfold canonicalParticleFactor genusOneFactor
  apply mul_ne_zero _ (Complex.exp_ne_zero _)
  intro h
  have hdiv : (z-Complex.I)/((x:ℂ)-Complex.I) = 1 := (sub_eq_zero.mp h).symm
  have he := (div_eq_one_iff_eq (real_sub_offReal_ne_zero x (by simp : Complex.I.im ≠ 0))).mp hdiv
  have hzx : z = (x:ℂ) := sub_left_inj.mp he
  exact hz (by simp [hzx])

theorem norm_real_sub_I_sq (x : ℝ) : ‖(x:ℂ)-Complex.I‖^2 = 1+x^2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

theorem norm_real_sub_I_ge_one (x : ℝ) : 1 ≤ ‖(x:ℂ)-Complex.I‖ := by
  have hh := norm_real_sub_I_sq x
  nlinarith [norm_nonneg ((x:ℂ)-Complex.I),sq_nonneg x]

/-- The canonical quadratic remainder is bounded by the finite Nevanlinna weight. -/
theorem norm_canonicalParticleFactor_sub_one_le (R : ℝ) (_hR : 0 ≤ R)
    (x : ℝ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖canonicalParticleFactor x z-1‖ ≤
      ((R+1)^2*Real.exp (R+1))*nevanlinnaWeight x := by
  have hnorm : ‖z-Complex.I‖ ≤ R+1 :=
    (norm_sub_le z Complex.I).trans (by simpa using add_le_add_right hz 1)
  have hy : ‖(z-Complex.I)/((x:ℂ)-Complex.I)‖ ≤ R+1 := by
    rw [norm_div]
    exact (div_le_self (norm_nonneg _) (norm_real_sub_I_ge_one x)).trans hnorm
  have hsq : ‖(z-Complex.I)/((x:ℂ)-Complex.I)‖^2 = ‖z-Complex.I‖^2*nevanlinnaWeight x := by
    rw [norm_div,div_pow,norm_real_sub_I_sq]
    rfl
  calc
    _ ≤ ‖(z-Complex.I)/((x:ℂ)-Complex.I)‖^2 *
        Real.exp ‖(z-Complex.I)/((x:ℂ)-Complex.I)‖ := norm_genusOneFactor_sub_one_le _
    _ = (‖z-Complex.I‖^2*nevanlinnaWeight x)*
        Real.exp ‖(z-Complex.I)/((x:ℂ)-Complex.I)‖ := by rw [hsq]
    _ ≤ ((R+1)^2*nevanlinnaWeight x)*Real.exp (R+1) := by
      gcongr
      · exact mul_nonneg (sq_nonneg _) (nevanlinnaWeight_nonneg x)
      · exact nevanlinnaWeight_nonneg x
    _ = _ := by ring

/-- The logarithmic derivative is the absolutely summable reciprocal difference. -/
theorem hasDerivAt_canonicalParticleFactor (x : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (canonicalParticleFactor x)
      ((((x:ℂ)-Complex.I)⁻¹-((x:ℂ)-z)⁻¹)*canonicalParticleFactor x z) z := by
  have hd := (hasDerivAt_genusOneFactor ((z-Complex.I)/((x:ℂ)-Complex.I))).comp z
    (((hasDerivAt_id z).sub_const Complex.I).div_const ((x:ℂ)-Complex.I))
  convert hd using 1
  unfold canonicalParticleFactor genusOneFactor
  have hxI := real_sub_offReal_ne_zero x (by simp : Complex.I.im ≠ 0)
  have hxz := real_sub_offReal_ne_zero x hz
  field_simp
  ring

/-- Weighted local finiteness supplies the compact summability needed by the
holomorphic infinite-product theorem. -/
theorem locallySummable_canonicalParticleFactors (s : AnchoredCountingState) :
    LocallySummableProduct (fun i : s.val.1.ParticleLabels => canonicalParticleFactor (s.val.1.particleLocation i)) := by
  intro R hR
  refine ⟨fun i => ((R+1)^2*Real.exp (R+1))*nevanlinnaWeight (s.val.1.particleLocation i),
    s.summable_particle_weight.mul_left _,fun i z hz => ?_⟩
  exact norm_canonicalParticleFactor_sub_one_le R hR.le _ z hz

end BourgadeHuang
