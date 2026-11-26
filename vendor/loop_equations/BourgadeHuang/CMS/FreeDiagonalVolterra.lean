import BourgadeHuang.CMS.ComplexVolterraOperators
import BourgadeHuang.CMS.FilteredOperatorInverse

/-! Actual complex Volterra operators for the free diagonal radial system.
Their spectral-gap estimates are uniform on the entire half-line. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option linter.unusedSectionVars false
variable {J : Type*} [Fintype J]

/-- Diagonal multiplication on the finite supremum-norm space. -/
def complexDiagonalOperator (v : J → ℂ) : (J → ℂ) →L[ℂ] (J → ℂ) :=
  ContinuousLinearMap.pi (fun i => v i • ContinuousLinearMap.proj i)

@[simp] theorem complexDiagonalOperator_apply (v x : J → ℂ) (i : J) :
    complexDiagonalOperator v x i=v i*x i := rfl

theorem norm_complexDiagonalOperator_le {v : J → ℂ} {B : ℝ}
    (hB : 0≤B) (hv : ∀i,‖v i‖≤B) : ‖complexDiagonalOperator v‖≤B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg x))).mpr
  intro i
  exact (norm_mul _ _).le.trans (mul_le_mul (hv i) (norm_le_pi_norm x i) (norm_nonneg _) hB)

/-- The diagonal assembly is bounded and complex-linear in its entries. -/
def complexDiagonalAssembly : (J → ℂ) →L[ℂ] ((J → ℂ) →L[ℂ] (J → ℂ)) :=
  LinearMap.mkContinuous
    { toFun := complexDiagonalOperator
      map_add' := by intro v w; ext x i; simp [complexDiagonalOperator_apply,add_mul]
      map_smul' := by intro c v; ext x i; simp [complexDiagonalOperator_apply,mul_assoc] }
    1 (fun v => by
      simpa only [one_mul] using norm_complexDiagonalOperator_le (norm_nonneg v)
        (fun i => norm_le_pi_norm v i))

theorem continuous_complexDiagonalOperator :
    Continuous (complexDiagonalOperator (J:=J)) := complexDiagonalAssembly.continuous

/-- The free backward evolution, whose diagonal entries have exact
exponential decay from the radial spectral gap. -/
def freeDiagonalEvolution (lam : J → ℂ) (u : ℝ) : (J → ℂ) →L[ℂ] (J → ℂ) :=
  complexDiagonalOperator (fun i => Complex.exp (-lam i*(u:ℂ)))

theorem continuous_freeDiagonalEvolution (lam : J → ℂ) :
    Continuous (freeDiagonalEvolution lam) := by
  apply continuous_complexDiagonalOperator.comp
  exact continuous_pi (fun i => Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal))

theorem norm_freeDiagonalEvolution_le (lam : J → ℂ) {a u : ℝ}
    (hlam : ∀i,a≤(lam i).re) (hu : 0≤u) :
    ‖freeDiagonalEvolution lam u‖≤Real.exp (-a*u) := by
  apply norm_complexDiagonalOperator_le (Real.exp_pos _).le
  intro i
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_le_mul_of_nonneg_right (neg_le_neg (hlam i)) hu

variable {R a : ℝ} (hR : 0<R) (ha : 0<a) (lam : J → ℂ)
  (hlam : ∀i,a≤(lam i).re)

private theorem freeDiagonal_continuous :
    Continuous (Function.uncurry (fun (_t : Tail R) u =>
      (freeDiagonalEvolution lam u).restrictScalars ℝ)) :=
  (ContinuousLinearMap.continuous_restrictScalars ℝ).comp
    ((continuous_freeDiagonalEvolution lam).comp continuous_snd)

include hlam in
private theorem freeDiagonal_bound (_t : Tail R) (u : ℝ) (hu : 0<u) :
    ‖(freeDiagonalEvolution lam u).restrictScalars ℝ‖≤1*Real.exp (-a*u) := by
  rw [ContinuousLinearMap.norm_restrictScalars,one_mul]
  exact norm_freeDiagonalEvolution_le lam hlam hu.le

/-- The true free forcing convolution `-t ∫ exp(-λu)f(t+u)/(t+u) du`. -/
def freeForcingOperator :
    (Tail R →ᵇ (J → ℂ)) →L[ℂ] (Tail R →ᵇ (J → ℂ)) :=
  (exponentialForcingKernel hR ha (by norm_num : (0:ℝ)≤1)
    (fun _ u => (freeDiagonalEvolution lam u).restrictScalars ℝ)
    (freeDiagonal_continuous lam) (freeDiagonal_bound lam hlam)).complexOperator
    (mul_nonneg (by norm_num) (inv_nonneg.mpr ha.le)) (by
      intro t u c v
      change (-(t.val*(tailShift t u).val⁻¹)) •
        freeDiagonalEvolution lam u (c • v)=c •
        ((-(t.val*(tailShift t u).val⁻¹)) • freeDiagonalEvolution lam u v)
      rw [map_smul,smul_comm])

/-- The true free remainder convolution, with one further inverse power. -/
def freeRemainderOperator :
    (Tail R →ᵇ (J → ℂ)) →L[ℂ] (Tail R →ᵇ (J → ℂ)) :=
  (exponentialTailKernel hR ha (by norm_num : (0:ℝ)≤1)
    (fun _ u => (freeDiagonalEvolution lam u).restrictScalars ℝ)
    (freeDiagonal_continuous lam) (freeDiagonal_bound lam hlam)).complexOperator
    (by positivity) (by
      intro t u c v
      change (-(t.val*(tailShift t u).val⁻¹^2)) •
        freeDiagonalEvolution lam u (c • v)=c •
        ((-(t.val*(tailShift t u).val⁻¹^2)) • freeDiagonalEvolution lam u v)
      rw [map_smul,smul_comm])

theorem norm_freeForcingOperator_le : ‖freeForcingOperator hR ha lam hlam‖≤a⁻¹ := by
  simpa only [one_mul] using ContinuousIntegralKernel.norm_complexOperator_le
    (exponentialForcingKernel hR ha (by norm_num : (0:ℝ)≤1)
      (fun _ u => (freeDiagonalEvolution lam u).restrictScalars ℝ)
      (freeDiagonal_continuous lam) (freeDiagonal_bound lam hlam)) _ _

theorem norm_freeRemainderOperator_le :
    ‖freeRemainderOperator hR ha lam hlam‖≤R⁻¹*a⁻¹ := by
  simpa only [one_mul] using ContinuousIntegralKernel.norm_complexOperator_le
    (exponentialTailKernel hR ha (by norm_num : (0:ℝ)≤1)
      (fun _ u => (freeDiagonalEvolution lam u).restrictScalars ℝ)
      (freeDiagonal_continuous lam) (freeDiagonal_bound lam hlam)) _ _

/-- The exact componentwise Bochner integral formula. -/
theorem freeForcingOperator_apply (f : Tail R →ᵇ (J → ℂ)) (t : Tail R) (i : J) :
    freeForcingOperator hR ha lam hlam f t i=
      ∫u,(-(t.val*(tailShift t u).val⁻¹):ℝ) •
        (Complex.exp (-lam i*(u:ℂ))*f (tailShift t u) i)
        ∂(volume.restrict (Ioi (0:ℝ))) := by
  let K := exponentialForcingKernel hR ha (by norm_num : (0:ℝ)≤1)
    (fun _ u => (freeDiagonalEvolution lam u).restrictScalars ℝ)
    (freeDiagonal_continuous lam) (freeDiagonal_bound lam hlam)
  exact ((ContinuousLinearMap.proj i : (J → ℂ) →L[ℝ] ℂ).integral_comp_comm
    (K.integrable_integrand f t)).symm

/-- The diagonal convolution preserves every vanishing component. -/
theorem freeForcingOperator_component_zero (f : Tail R →ᵇ (J → ℂ)) (i : J)
    (hf : ∀t,f t i=0) : ∀t,freeForcingOperator hR ha lam hlam f t i=0 := by
  intro t
  rw [freeForcingOperator_apply]
  simp only [hf,mul_zero,smul_zero,integral_zero]

theorem freeForcingOperator_vanishesBelow {degree : J → ℕ} {k : ℕ}
    {f : Tail R →ᵇ (J → ℂ)} (hf : VanishesBelow degree k f) :
    VanishesBelow degree k (freeForcingOperator hR ha lam hlam f) := by
  intro t i hi
  exact freeForcingOperator_component_zero hR ha lam hlam f i (fun t => hf t i hi) t

end BourgadeHuang.CMS
