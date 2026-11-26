import GeneralizedBulk.Spectral.PoissonFourier

/-! Exact Poisson Fourier moments, with termwise integration justified by an
actual summable geometric majorant. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace GeneralizedBulk.Spectral

def poissonModeTerm (r : ℝ) (k n : ℕ) (theta : ℝ) : ℂ :=
  (r : ℂ) ^ n * (angularMode ((n : ℤ) + k) theta + angularMode ((k : ℤ) - n) theta) -
    if n = 0 then angularMode k theta else 0

theorem poissonModeTerm_integral (r : ℝ) (k n : ℕ) :
    (∫ theta in -(Real.pi / 2)..Real.pi / 2, poissonModeTerm r k n theta) =
      if n = k then (Real.pi : ℂ) * (r : ℂ) ^ k else 0 := by
  by_cases hn : n = 0
  · subst n
    have ht : poissonModeTerm r k 0 = angularMode k := by
      funext theta
      simp only [poissonModeTerm, pow_zero, Int.ofNat_zero, zero_add, sub_zero,
        one_mul, ↓reduceIte]
      ring
    rw [ht, integral_angularMode]
    by_cases hk : k = 0
    · subst k; simp
    · simp [hk, (by exact_mod_cast hk : (k : ℤ) ≠ 0), Ne.symm hk]
  · have ht : poissonModeTerm r k n = fun theta =>
        (r : ℂ) ^ n * (angularMode ((n : ℤ) + k) theta + angularMode ((k : ℤ) - n) theta) := by
      funext theta; simp only [poissonModeTerm, if_neg hn, sub_zero]
    rw [ht, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((continuous_angularMode _).intervalIntegrable _ _)
        ((continuous_angularMode _).intervalIntegrable _ _), integral_angularMode, integral_angularMode]
    have hp : (n : ℤ) + k ≠ 0 := by omega
    rw [if_neg hp]
    by_cases hnk : n = k
    · subst n; simp [mul_comm]
    · have hm : (k : ℤ) - n ≠ 0 := by omega
      simp only [if_neg hm, if_neg hnk, add_zero, mul_zero]

theorem poissonModeTerm_continuous (r : ℝ) (k n : ℕ) : Continuous (poissonModeTerm r k n) := by
  unfold poissonModeTerm
  by_cases hn : n = 0 <;> simp only [hn, ↓reduceIte] <;>
    exact (continuous_const.mul ((continuous_angularMode _).add (continuous_angularMode _))).sub (by first | exact continuous_angularMode _ | exact continuous_const)

theorem poissonModeTerm_bound (r : ℝ) (k n : ℕ) (theta : ℝ) :
    ‖poissonModeTerm r k n theta‖ ≤ 3 * |r| ^ n := by
  by_cases hn : n = 0
  · subst n
    have he : poissonModeTerm r k 0 theta = angularMode k theta := by
      simp only [poissonModeTerm, pow_zero, Int.ofNat_zero, zero_add, sub_zero, one_mul, ↓reduceIte]
      ring
    rw [he, angularMode_norm, pow_zero]
    norm_num
  · unfold poissonModeTerm
    rw [if_neg hn, sub_zero, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hh := norm_add_le (angularMode ((n : ℤ) + k) theta) (angularMode ((k : ℤ) - n) theta)
    rw [angularMode_norm, angularMode_norm] at hh
    have ht := mul_le_mul_of_nonneg_left hh (pow_nonneg (abs_nonneg r) n)
    nlinarith [pow_nonneg (abs_nonneg r) n]

theorem poissonModeTerm_hasSum (r : ℝ) (hr : |r| < 1) (k : ℕ) (theta : ℝ) :
    HasSum (fun n => poissonModeTerm r k n theta) ((poissonKernel r (2 * theta) : ℂ) * angularMode k theta) := by
  have hh := (poissonKernel_hasSum_modes r theta hr).mul_right (angularMode k theta)
  convert hh using 1
  funext n
  unfold poissonModeTerm
  rw [sub_mul, mul_assoc, add_mul, ← angularMode_add, ← angularMode_add]
  have he : -(n : ℤ) + k = (k : ℤ) - n := by omega
  rw [he]
  by_cases hn : n = 0 <;> simp only [hn, ↓reduceIte, one_mul, zero_mul]

/-- Exact Fourier moments of the actual Poisson kernel. The passage through
the infinite series uses a proved summable geometric majorant. -/
theorem integral_poissonKernel_mode (r : ℝ) (hr : |r| < 1) (k : ℕ) :
    (∫ theta in -(Real.pi / 2)..Real.pi / 2, (poissonKernel r (2 * theta) : ℂ) * angularMode k theta) =
      (Real.pi : ℂ) * (r : ℂ) ^ k := by
  let mu := volume.restrict (Ioc (-(Real.pi / 2)) (Real.pi / 2))
  have hs : Summable (fun n : ℕ => 3 * |r| ^ n) :=
    (summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_abs] using hr)).mul_left 3
  have hh := hasSum_integral_of_dominated_convergence
    (μ := mu) (fun n _theta => 3 * |r| ^ n)
    (fun n => (poissonModeTerm_continuous r k n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (poissonModeTerm_bound r k n))
    (Filter.Eventually.of_forall (fun _ => hs))
    (by exact integrable_const _)
    (Filter.Eventually.of_forall (poissonModeTerm_hasSum r hr k))
  have hab : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hterm (n : ℕ) : (∫ theta, poissonModeTerm r k n theta ∂mu) =
      if n = k then (Real.pi : ℂ) * (r : ℂ) ^ k else 0 := by
    rw [← intervalIntegral.integral_of_le hab]
    exact poissonModeTerm_integral r k n
  have ht : HasSum (fun n : ℕ => if n = k then (Real.pi : ℂ) * (r : ℂ) ^ k else 0)
      ((Real.pi : ℂ) * (r : ℂ) ^ k) := hasSum_ite_eq k _
  simp_rw [hterm] at hh
  rw [intervalIntegral.integral_of_le hab]
  exact hh.unique ht

end GeneralizedBulk.Spectral
