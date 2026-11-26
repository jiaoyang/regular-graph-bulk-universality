import GeneralizedBulk.Entropy.DirectionalCalculus
import GeneralizedBulk.Entropy.GaussianSubspaceChannels

/-! Actual Gaussian L² directional derivatives and polynomial null-set removal. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]

def directionalLp (a : K → I → ℕ) (coeff : K → ℝ) (v : I → ℝ) : Lp ℝ 2 (standardGaussian I) :=
  ∑ i, v i • chaosDerivativeLp a coeff i

def directionalFunction (a : K → I → ℕ) (coeff : K → ℝ) (v : I → ℝ) (x : I → ℝ) : ℝ :=
  ∑ i, v i * chaosDerivativeFunction a coeff i x

theorem directionalLp_ae (a : K → I → ℕ) (coeff : K → ℝ) (v : I → ℝ) :
    (directionalLp a coeff v : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] directionalFunction a coeff v := by
  apply finite_real_Lp_sum_ae _ _ _ _
  intro i
  filter_upwards [Lp.coeFn_smul (v i) (chaosDerivativeLp a coeff i), chaosDerivativeLp_ae a coeff i]
    with x hs hx
  simpa only [Pi.smul_apply, smul_eq_mul, hx] using hs

/-- This L² vector is the actual Fréchet directional derivative of the actual
Gaussian polynomial function. -/
theorem directionalLp_ae_fderiv (a : K → I → ℕ) (coeff : K → ℝ) (v : I → ℝ) :
    (directionalLp a coeff v : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      (fun x => fderiv ℝ (chaosFunction a coeff) x v) := by
  exact (directionalLp_ae a coeff v).trans (Eventually.of_forall (fun x =>
    (fderiv_chaosFunction_apply a coeff x v).symm))

/-- Directional differentiation stays in the finite polynomial filtration.
This bound deliberately allows the zero coordinate terms, so no index choices
are required for a pointwise polynomial identity. -/
theorem directionalFunction_mem_functionFiltration (a : K → I → ℕ) (coeff : K → ℝ)
    (v : I → ℝ) (degree : ℕ) (hdegree : ∀ k, (∑ i, a k i) ≤ degree) :
    directionalFunction a coeff v ∈ functionFiltration degree := by
  have hs : (∑ i : I, ∑ k : K, (v i * coeff k * (a k i : ℝ)) •
      multiHermite I (lower (a k) i)) ∈ functionFiltration degree := by
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    exact multiHermite_mem_functionFiltration _ degree ((lower_degree_le (a k) i).trans (hdegree k))
  convert hs using 1
  funext x
  simp only [directionalFunction, chaosDerivativeFunction, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem fderiv_mem_functionFiltration (a : K → I → ℕ) (coeff : K → ℝ)
    (v : I → ℝ) (degree : ℕ) (hdegree : ∀ k, (∑ i, a k i) ≤ degree) :
    (fun x => fderiv ℝ (chaosFunction a coeff) x v) ∈ functionFiltration degree := by
  have heq : (fun x => fderiv ℝ (chaosFunction a coeff) x v) = directionalFunction a coeff v := by
    funext x
    exact fderiv_chaosFunction_apply a coeff x v
  rw [heq]
  exact directionalFunction_mem_functionFiltration a coeff v degree hdegree

/-- Vanishing of the true L² directional derivative implies a literal
polynomial identity at every point. This is used after zero-defect cancellation. -/
theorem fderiv_eq_zero_of_directionalLp_eq_zero (a : K → I → ℕ) (coeff : K → ℝ)
    (v : I → ℝ) (degree : ℕ) (hdegree : ∀ k, (∑ i, a k i) ≤ degree)
    (hzero : directionalLp a coeff v = 0) (x : I → ℝ) :
    fderiv ℝ (chaosFunction a coeff) x v = 0 := by
  have hae : (fun x => fderiv ℝ (chaosFunction a coeff) x v) =ᵐ[standardGaussian I] (fun _ => 0) := by
    filter_upwards [directionalLp_ae_fderiv a coeff v, Lp.coeFn_zero ℝ 2 (standardGaussian I)] with y hy h0
    rw [hzero, h0] at hy
    exact hy.symm
  have hf := functionFiltration_eq_zero_of_ae_zero I
    (fderiv_mem_functionFiltration a coeff v degree hdegree) hae
  exact congrFun hf x

/-- Equality of two L² directional derivatives gives a pointwise identity of
the corresponding actual polynomial derivatives, with no exceptional set. -/
theorem fderiv_eq_of_directionalLp_eq {J : Type*} [Fintype J]
    (a : K → I → ℕ) (coeff : K → ℝ) (v : I → ℝ)
    (b : J → I → ℕ) (other : J → ℝ) (w : I → ℝ) (degree : ℕ)
    (ha : ∀ k, (∑ i, a k i) ≤ degree) (hb : ∀ j, (∑ i, b j i) ≤ degree)
    (heq : directionalLp a coeff v = directionalLp b other w) :
    (fun x => fderiv ℝ (chaosFunction a coeff) x v) =
      (fun x => fderiv ℝ (chaosFunction b other) x w) := by
  have hae : (fun x => fderiv ℝ (chaosFunction a coeff) x v) =ᵐ[standardGaussian I]
      (fun x => fderiv ℝ (chaosFunction b other) x w) := by
    filter_upwards [directionalLp_ae_fderiv a coeff v, directionalLp_ae_fderiv b other w] with x ha hb
    rw [heq] at ha
    exact ha.symm.trans hb
  exact functionFiltration_eq_of_ae_eq I (fderiv_mem_functionFiltration a coeff v degree ha)
    (fderiv_mem_functionFiltration b other w degree hb) hae

theorem directionalFunction_memLp_two (a : K → I → ℕ) (coeff : K → ℝ) (v : I → ℝ) :
    MemLp (directionalFunction a coeff v) 2 (standardGaussian I) :=
  (memLp_congr_ae (directionalLp_ae a coeff v)).1 (Lp.memLp _)

theorem integral_directionalFunction_sq (a : K → I → ℕ) (coeff : K → ℝ) (v : I → ℝ) :
    (∫ x, directionalFunction a coeff v x ^ 2 ∂standardGaussian I) = ‖directionalLp a coeff v‖ ^ 2 := by
  rw [← integral_sq_real_Lp]
  exact integral_congr_ae ((directionalLp_ae a coeff v).symm.mono (fun x hx => congrArg (fun z : ℝ => z ^ 2) hx))

/-- The actual continuous linear coordinate map used by directional chain rules. -/
def matrixActionCLM (R : Matrix I I ℝ) : (I → ℝ) →L[ℝ] (I → ℝ) :=
  (Matrix.toLin' R).toContinuousLinearMap

@[simp] theorem matrixActionCLM_apply (R : Matrix I I ℝ) (v : I → ℝ) :
    matrixActionCLM R v = R.mulVec v := rfl

/-- Actual directional chain rule under an arbitrary linear coordinate map. -/
theorem fderiv_comp_matrix (R : Matrix I I ℝ) (f : (I → ℝ) → ℝ)
    (hf : Differentiable ℝ f) (x v : I → ℝ) :
    fderiv ℝ (fun y => f (R.mulVec y)) x v = fderiv ℝ f (R.mulVec x) (R.mulVec v) := by
  have h := ((hf (R.mulVec x)).hasFDerivAt).comp x (matrixActionCLM R).hasFDerivAt
  change fderiv ℝ (f ∘ R.mulVec) x v = _
  rw [h.fderiv]
  rfl

/-- Invariance of an actual Gaussian polynomial under an orthogonal action
interchanges its directional L² energies whenever the action interchanges
the two directions. This proves the symmetry step in the weighted frame. -/
theorem directionalLp_norm_eq_of_symmetry (a : K → I → ℕ) (coeff : K → ℝ)
    (R : Matrix I I ℝ) (hR : R * R.transpose = 1) (v w : I → ℝ)
    (hvw : R.mulVec v = w)
    (hsym : ∀ x, chaosFunction a coeff (R.mulVec x) = chaosFunction a coeff x) :
    ‖directionalLp a coeff v‖ = ‖directionalLp a coeff w‖ := by
  have hf : Differentiable ℝ (chaosFunction a coeff) :=
    (contDiff_chaosFunction a coeff).differentiable (by simp)
  have hfun : (fun x => chaosFunction a coeff (R.mulVec x)) = chaosFunction a coeff := funext hsym
  have hdir (x : I → ℝ) :
      fderiv ℝ (chaosFunction a coeff) x v = fderiv ℝ (chaosFunction a coeff) (R.mulVec x) w := by
    have h := fderiv_comp_matrix R (chaosFunction a coeff) hf x v
    rw [hfun, hvw] at h
    exact h
  have heq : directionalLp a coeff v = gaussianPullback R hR (directionalLp a coeff w) := by
    apply Lp.ext
    have hae := (standardGaussian_matrixAction_measurePreserving R hR).quasiMeasurePreserving.ae_eq_comp
      (directionalLp_ae_fderiv a coeff w)
    filter_upwards [directionalLp_ae_fderiv a coeff v,
      gaussianPullback_ae R hR (directionalLp a coeff w), hae] with x hv hp hw
    simp only [Function.comp_apply] at hw
    rw [hv, hp, hw]
    exact hdir x
  rw [heq, (gaussianPullback R hR).norm_map]


/-- Equality in Gaussian L² of polynomial representatives remains pointwise
under orthogonal substitution, so differentiation transports without a
null-set derivative argument. -/
theorem chaosFunction_eq_pullback_of_lp_eq {J : Type*} [Fintype J]
    (a : K → I → ℕ) (coeff : K → ℝ) (b : J → I → ℕ) (other : J → ℝ)
    (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (degree : ℕ)
    (ha : ∀ k, (∑ i, a k i) ≤ degree) (hb : ∀ j, (∑ i, b j i) ≤ degree)
    (heq : chaosLp b other = gaussianPullback O hO (chaosLp a coeff)) :
    chaosFunction b other = fun x => chaosFunction a coeff (O.mulVec x) := by
  apply functionFiltration_eq_of_ae_eq I (chaosFunction_mem_functionFiltration I b other degree hb)
    (linearSubstitution_mem (chaosFunction_mem_functionFiltration I a coeff degree ha) O)
  have hae := (standardGaussian_matrixAction_measurePreserving O hO).quasiMeasurePreserving.ae_eq_comp
    (chaosLp_ae a coeff)
  filter_upwards [chaosLp_ae b other, gaussianPullback_ae O hO (chaosLp a coeff), hae]
    with x hb hp ha
  simp only [Function.comp_apply] at ha
  rw [heq, hp] at hb
  exact hb.symm.trans ha

/-- The actual directional L² derivative is natural under genuine Gaussian
orthogonal pullback. -/
theorem directionalLp_pullback {J : Type*} [Fintype J]
    (a : K → I → ℕ) (coeff : K → ℝ) (b : J → I → ℕ) (other : J → ℝ)
    (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (degree : ℕ)
    (ha : ∀ k, (∑ i, a k i) ≤ degree) (hb : ∀ j, (∑ i, b j i) ≤ degree)
    (heq : chaosLp b other = gaussianPullback O hO (chaosLp a coeff)) (v : I → ℝ) :
    directionalLp b other v = gaussianPullback O hO (directionalLp a coeff (O.mulVec v)) := by
  have hfun := chaosFunction_eq_pullback_of_lp_eq a coeff b other O hO degree ha hb heq
  have hf : Differentiable ℝ (chaosFunction a coeff) :=
    (contDiff_chaosFunction a coeff).differentiable (by simp)
  apply Lp.ext
  have hae := (standardGaussian_matrixAction_measurePreserving O hO).quasiMeasurePreserving.ae_eq_comp
    (directionalLp_ae_fderiv a coeff (O.mulVec v))
  filter_upwards [directionalLp_ae_fderiv b other v,
    gaussianPullback_ae O hO (directionalLp a coeff (O.mulVec v)), hae] with x hb hp ha
  simp only [Function.comp_apply] at ha
  rw [hb, hp, ha, hfun]
  exact fderiv_comp_matrix O (chaosFunction a coeff) hf x v

end GeneralizedBulk.Entropy.Hermite
