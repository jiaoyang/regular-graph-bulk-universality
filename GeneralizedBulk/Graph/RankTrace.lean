import GeneralizedBulk.Graph.SchurExterior

/-!
# Rank-sensitive trace estimates for finite resolvent differences

The trace is first restricted to the image of the operator. An orthonormal
basis of that image bounds it by rank times operator norm; no eigenvalue
interlacing theorem is needed.
-/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace GeneralizedBulk.Graph

/-- Trace is controlled by the dimension of the actual operator range. -/
theorem norm_trace_le_finrank_range_mul_opNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (f : E →L[ℂ] E) :
    ‖LinearMap.trace ℂ E (f : E →ₗ[ℂ] E)‖ ≤
      (Module.finrank ℂ (LinearMap.range (f : E →ₗ[ℂ] E)) : ℝ) * ‖f‖ := by
  let W := LinearMap.range (f : E →ₗ[ℂ] E)
  have hW : ∀ x : E, (f : E →ₗ[ℂ] E) x ∈ W := fun x => ⟨x, rfl⟩
  let g : W →ₗ[ℂ] W := (f : E →ₗ[ℂ] E).restrict (fun x _ => hW x)
  let b := stdOrthonormalBasis ℂ W
  have ht : LinearMap.trace ℂ W g = LinearMap.trace ℂ E (f : E →ₗ[ℂ] E) :=
    LinearMap.trace_restrict_eq_of_forall_mem W (f : E →ₗ[ℂ] E) hW
  rw [← ht, LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  calc
    _ ≤ ∑ i, ‖@inner ℂ W _ (b i) (g (b i))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℂ W), ‖f‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖@inner ℂ W _ (b i) (g (b i))‖ ≤ ‖b i‖ * ‖g (b i)‖ := norm_inner_le_norm _ _
        _ = ‖g (b i)‖ := by rw [b.norm_eq_one i, one_mul]
        _ = ‖f (b i : E)‖ := rfl
        _ ≤ ‖f‖ * ‖(b i : E)‖ := f.le_opNorm _
        _ = ‖f‖ := by change ‖f‖ * ‖b i‖ = ‖f‖; rw [b.norm_eq_one i, mul_one]
    _ = _ := by simp [W]

/-- Energy estimate for a right inverse of a nonreal shift of a symmetric
operator. It proves the resolvent operator norm directly from Cauchy--Schwarz. -/
theorem norm_nonreal_rightInverse_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T R : E →L[ℂ] E) (hT : (T : E →ₗ[ℂ] E).IsSymmetric)
    (z : ℂ) (hz : z.im ≠ 0) (hInv : (T - z • 1) * R = 1) :
    ‖R‖ ≤ |z.im|⁻¹ := by
  have hreal (y : E) : (@inner ℂ E _ y (T y)).im = 0 := by
    have h := congrArg Complex.im (hT.conj_inner_sym y y)
    rw [hT y y] at h
    simp only [Complex.conj_im] at h
    change -(@inner ℂ E _ y (T y)).im = (@inner ℂ E _ y (T y)).im at h
    linarith
  apply R.opNorm_le_bound (inv_nonneg.mpr (abs_nonneg _))
  intro x
  let y := R x
  have hxy : T y - z • y = x := by
    have h := congrArg (fun f : E →L[ℂ] E => f x) hInv
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] using h
  have he : (@inner ℂ E _ y x).im = -z.im * ‖y‖ ^ 2 := by
    have hyy : (@inner ℂ E _ y y).re = ‖y‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) y).symm
    have hiy : (@inner ℂ E _ y y).im = 0 := inner_self_im (𝕜 := ℂ) y
    rw [← hxy, inner_sub_right, inner_smul_right]
    simp only [Complex.sub_im, hreal y, Complex.mul_im, hiy, hyy,
      mul_zero, zero_add, zero_sub]
    ring
  have hb : |z.im| * ‖y‖ ^ 2 ≤ ‖y‖ * ‖x‖ := by
    calc
      _ = |(@inner ℂ E _ y x).im| := by
        rw [he, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ‖y‖)]
      _ ≤ ‖@inner ℂ E _ y x‖ := Complex.abs_im_le_norm _
      _ ≤ ‖y‖ * ‖x‖ := norm_inner_le_norm _ _
  change ‖y‖ ≤ |z.im|⁻¹ * ‖x‖
  by_cases hy : ‖y‖ = 0
  · rw [hy]
    positivity
  · have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
    have hb' : ‖y‖ * (|z.im| * ‖y‖) ≤ ‖y‖ * ‖x‖ := by
      simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using hb
    have hc := (mul_le_mul_iff_of_pos_left hypos).mp hb'
    calc
      ‖y‖ ≤ ‖x‖ / |z.im| := (le_div_iff₀ (abs_pos.mpr hz)).mpr (by simpa only [mul_comm] using hc)
      _ = _ := by rw [div_eq_mul_inv, mul_comm]

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Matrix trace has the corresponding Euclidean operator-norm bound. -/
theorem norm_matrix_trace_le_rank_mul_opNorm (A : Matrix m m ℂ) :
    ‖Matrix.trace A‖ ≤ (A.rank : ℝ) * ‖(Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)) A‖ := by
  let b := (EuclideanSpace.basisFun m ℂ).toBasis
  have ht : LinearMap.trace ℂ (EuclideanSpace ℂ m)
      ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)) A : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ m) =
      Matrix.trace A := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      LinearMap.trace_eq_matrix_trace ℂ b, Matrix.toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_toLin]
  have hr : A.rank = Module.finrank ℂ (LinearMap.range
      ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)) A : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ m)) := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact A.rank_eq_finrank_range_toLin _ _
  rw [hr, ← ht]
  exact norm_trace_le_finrank_range_mul_opNorm ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)) A)

/-- Operator norm of every finite Hermitian resolvent, with both half-planes
covered by the absolute imaginary height. -/
theorem norm_hermitian_resolvent_operator_le (A : Matrix m m ℂ) (hA : A.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    ‖(Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)) (A - z • 1)⁻¹‖ ≤ |z.im|⁻¹ := by
  let F := Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)
  have hu := hermitian_shift_isUnit A hA z hz
  have hmatrix := Matrix.mul_nonsing_inv (A - z • (1 : Matrix m m ℂ))
    ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hInv : (F A - z • 1) * F (A - z • 1)⁻¹ = 1 := by
    simpa only [map_mul, map_sub, map_smul, map_one] using congrArg F hmatrix
  have hsym : (F A : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ m).IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isHermitian_iff_isSymmetric.mp hA
  exact norm_nonreal_rightInverse_le (F A) (F (A - z • 1)⁻¹) hsym z hz hInv

/-- The resolvent difference factors through the perturbation itself. -/
theorem hermitian_resolvent_difference_identity (A B : Matrix m m ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    (A - z • 1)⁻¹ - (B - z • 1)⁻¹ =
      (A - z • 1)⁻¹ * (B - A) * (B - z • 1)⁻¹ := by
  have hRA := Matrix.nonsing_inv_mul (A - z • (1 : Matrix m m ℂ))
    ((Matrix.isUnit_iff_isUnit_det _).mp (hermitian_shift_isUnit A hA z hz))
  have hRB := Matrix.mul_nonsing_inv (B - z • (1 : Matrix m m ℂ))
    ((Matrix.isUnit_iff_isUnit_det _).mp (hermitian_shift_isUnit B hB z hz))
  have hdiff : B - A = (B - z • (1 : Matrix m m ℂ)) - (A - z • 1) := by abel
  rw [hdiff, Matrix.mul_sub, Matrix.sub_mul]
  rw [Matrix.mul_assoc, hRB, mul_one, hRA, one_mul]

/-- A rank-`r` Hermitian perturbation changes the raw resolvent trace by at
most `2r/|Im z|`. Any fixed bound of this form supplies the reversible tail
recursion's finite scalar shift. -/
theorem norm_hermitian_resolvent_trace_sub_le (A B : Matrix m m ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    ‖Matrix.trace (A - z • 1)⁻¹ - Matrix.trace (B - z • 1)⁻¹‖ ≤
      ((B - A).rank : ℝ) * (2 / |z.im|) := by
  let F := Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)
  let X := (A - z • (1 : Matrix m m ℂ))⁻¹ - (B - z • 1)⁻¹
  have hrank : X.rank ≤ (B - A).rank := by
    rw [show X = (A - z • 1)⁻¹ * (B - A) * (B - z • 1)⁻¹ from
      hermitian_resolvent_difference_identity A B hA hB z hz]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hnorm : ‖F X‖ ≤ 2 / |z.im| := by
    change ‖F ((A - z • 1)⁻¹ - (B - z • 1)⁻¹)‖ ≤ _
    rw [map_sub]
    calc
      _ ≤ ‖F (A - z • 1)⁻¹‖ + ‖F (B - z • 1)⁻¹‖ := norm_sub_le _ _
      _ ≤ |z.im|⁻¹ + |z.im|⁻¹ := add_le_add
        (norm_hermitian_resolvent_operator_le A hA z hz)
        (norm_hermitian_resolvent_operator_le B hB z hz)
      _ = _ := by ring
  rw [← Matrix.trace_sub]
  change ‖Matrix.trace X‖ ≤ _
  exact (norm_matrix_trace_le_rank_mul_opNorm X).trans
    (mul_le_mul (Nat.cast_le.mpr hrank) hnorm (norm_nonneg _) (Nat.cast_nonneg _))

end GeneralizedBulk.Graph
