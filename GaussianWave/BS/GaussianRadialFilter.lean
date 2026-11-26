import GaussianWave.BS.RadialTreeGeometry
import GaussianWave.BS.GaussianRadialAsymptotic
import GaussianWave.BS.GaussianLocalSampler

/-! Actual finite-radius Gaussian radial samplers on the constructed tree.
Their coefficients, normalization, and boundary errors are derived from the
spherical recurrence and the exact sphere counts. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS

/-- An actual finitely supported radial coefficient vector. -/
def regularTreeRadialFinsupp (d R : ℕ) (u : RegularTreeVertex d) (f : ℕ → ℝ) :
    RegularTreeVertex d →₀ ℝ :=
  Finsupp.onFinset (Finset.univ.image (fun z : RegularTreeBall d u R => z.val))
    (fun z => if (regularWordTree d).dist z u ≤ R then f ((regularWordTree d).dist z u) else 0)
    (by
      intro z hz
      by_cases h : (regularWordTree d).dist z u ≤ R
      · exact Finset.mem_image.2 ⟨⟨z,h⟩,Finset.mem_univ _,rfl⟩
      · simp only [if_neg h] at hz
        exact False.elim (hz rfl))

@[simp] theorem regularTreeRadialFinsupp_apply (d R : ℕ) (u z : RegularTreeVertex d) (f : ℕ → ℝ) :
    regularTreeRadialFinsupp d R u f z =
      if (regularWordTree d).dist z u ≤ R then f ((regularWordTree d).dist z u) else 0 := rfl

theorem regularTreeRadialFinsupp_square_sum (d R : ℕ) (u : RegularTreeVertex d) (f : ℕ → ℝ) :
    (regularTreeRadialFinsupp d R u f).sum (fun _ a => a^2) =
      ∑ z : RegularTreeBall d u R, f ((regularWordTree d).dist z u)^2 := by
  unfold regularTreeRadialFinsupp
  rw [Finsupp.onFinset_sum _ (by intro a; simp)]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [if_pos z.property]
  · intro a ha b hb hab
    exact Subtype.ext hab

/-- The scaled spherical covariance is exactly the radial wave recurrence. -/
theorem sphericalCovariance_scaled_radial (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (n : ℕ) :
    Real.sqrt ((d : ℝ)-1)^n * sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) n =
      radialScaledWave ((d : ℝ)-1) x n := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : 0 < (d : ℝ)-1 := by linarith
  have h := branchMean_scaled_eq_radialChebyshev hq x n
  rw [← branchMean_inside_covariance d hd]
  unfold radialScaledWave
  calc
    _ = Real.sqrt ((d : ℝ)-1)^n * branchMeanA ((d : ℝ)-1)
          (2*Real.sqrt ((d : ℝ)-1)*x) n +
        (Real.sqrt ((d : ℝ)-1)^(n+1)*branchMeanB ((d : ℝ)-1)
          (2*Real.sqrt ((d : ℝ)-1)*x) n)*(2*x/d) := by rw [pow_succ]; ring
    _ = _ := by rw [h.1,h.2]; ring

private theorem radial_sphere_square_term (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (n : ℕ) :
    (d : ℝ)*((d-1 : ℕ) : ℝ)^n *
        sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) (n+1)^2 =
      (((d : ℝ)-1)*radialChebyshev x (n+1)-radialChebyshevPrev x n)^2/
        ((((d : ℝ)-1)+1)*((d : ℝ)-1)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq0 : (d : ℝ)-1 ≠ 0 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hs := Real.sq_sqrt (show 0 ≤ (d : ℝ)-1 by linarith)
  have he := sphericalCovariance_scaled_radial d hd x (n+1)
  have hpow : (((d : ℝ)-1)^n)*((d : ℝ)-1)*
        sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) (n+1)^2 =
      radialScaledWave ((d : ℝ)-1) x (n+1)^2 := by
    rw [← he, mul_pow, ← pow_mul, mul_comm (n+1) 2, pow_mul, hs]
    simp only [pow_succ]
  have hscale : radialScaledWave ((d : ℝ)-1) x (n+1) =
      (((d : ℝ)-1)*radialChebyshev x (n+1)-radialChebyshevPrev x n)/d := by
    unfold radialScaledWave
    rw [radialChebyshevPrev_succ]
    have hr := radialChebyshev_succ x n
    field_simp
    nlinarith [hr]
  rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  rw [hscale] at hpow
  field_simp
  field_simp at hpow
  nlinarith [hpow]

/-- The actual squared coefficient norm is the exact exceptional radial
variance appearing in the Gaussian reference calculation. -/
theorem regularTree_spherical_filter_norm (d : ℕ) (hd : 2 ≤ d) (x : ℝ)
    (k : ℕ) (u : RegularTreeVertex d) :
    (regularTreeRadialFinsupp d (k+1) u
      (sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x))).sum (fun _ a => a^2) =
      radialVertexExceptional ((d : ℝ)-1) x k := by
  rw [regularTreeRadialFinsupp_square_sum,
    regularTree_sum_ball_radial d (by omega) u (k+1)
      (fun n => sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x) n ^ 2)]
  simp only [sphericalCovariance_zero, one_pow]
  unfold radialVertexExceptional
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact radial_sphere_square_term d hd x n

theorem radialVertexExceptional_pos {q x : ℝ} (hq : 0 < q) (k : ℕ) :
    0 < radialVertexExceptional q x k := by
  unfold radialVertexExceptional
  have hs : 0 ≤ ∑ n ∈ Finset.range (k+1),
      (q*radialChebyshev x (n+1)-radialChebyshevPrev x n)^2/((q+1)*q) :=
    Finset.sum_nonneg (fun n hn => by positivity)
  linarith

/-- The normalized local coefficient rule used at every tree vertex. -/
def radialGaussianBlockCoefficient (d : ℕ) (x : ℝ) (k : ℕ) (u : RegularTreeVertex d) :
    RegularTreeVertex d →₀ ℝ :=
  (Real.sqrt (radialVertexExceptional ((d : ℝ)-1) x k))⁻¹ •
    regularTreeRadialFinsupp d (k+1) u
      (sphericalCovariance d (2*Real.sqrt ((d : ℝ)-1)*x))

/-- The actual Gaussian block-factor process law, as a measurable image of
independent labels on the countable regular tree. -/
def radialGaussianBlockLaw (d : ℕ) (x : ℝ) (k : ℕ) : Measure (RegularTreeVertex d → ℝ) :=
  finiteSupportGaussianLaw (radialGaussianBlockCoefficient d x k)

instance radialGaussianBlockLaw_isProbability (d : ℕ) (x : ℝ) (k : ℕ) :
    IsProbabilityMeasure (radialGaussianBlockLaw d x k) := by
  unfold radialGaussianBlockLaw
  infer_instance

/-- Every actual finite window of the block factor has its computed
Gaussian row-Gram characteristic function. -/
theorem radialGaussianBlockLaw_finite_gaussian (d : ℕ) (x : ℝ) (k : ℕ)
    {I : Type*} [Fintype I] (v : I → RegularTreeVertex d) :
    HasGaussianCovariance
      (Measure.map (fun z : RegularTreeVertex d → ℝ => fun i => z (v i)) (radialGaussianBlockLaw d x k))
      (finiteSupportGaussianMatrix (fun i => radialGaussianBlockCoefficient d x k (v i))*
        (finiteSupportGaussianMatrix (fun i => radialGaussianBlockCoefficient d x k (v i))).transpose) := by
  have he : Measure.map (fun z : RegularTreeVertex d → ℝ => fun i => z (v i))
      (radialGaussianBlockLaw d x k) =
        finiteSupportGaussianLaw (fun i => radialGaussianBlockCoefficient d x k (v i)) := by
    unfold radialGaussianBlockLaw finiteSupportGaussianLaw
    rw [Measure.map_map (measurable_pi_lambda _ (fun i => measurable_pi_apply (v i)))
      (measurable_finiteSupportGaussianSample _)]
    rfl
  rw [he]
  exact finiteSupportGaussianLaw_gaussian _

end GaussianWave.BS
