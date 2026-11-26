import GaussianWave.BS.StarFrame
import GaussianWave.BS.ThirdDerivativeSymmetry
import GaussianWave.BS.ScoreRigidity

/-!
# The mixed third-derivative kernel for the actual scalar BS star

This file treats the finite-dimensional algebra needed in the equality case.
The projections are constructed from the literal white-coordinate root and
simplex vectors. The mixed-kernel hypothesis is a local derivative condition;
Gaussianity and a quadratic log-density shape are not assumptions.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

abbrev TrilinearForm (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ

/-- Projection onto the constant root line. -/
def starRootPart (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun x := fun _ => (∑ j, x j) / d
  map_add' x y := by ext j; simp [Finset.sum_add_distrib, add_div]
  map_smul' a x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

def starTransversePart (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  LinearMap.id - starRootPart d

/-- Linear evaluation in an actual finite-coordinate direction. -/
def starDirectionForm {d : ℕ} (v : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ j, v j * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Orthogonal projection onto the root/simplex plane of edge i. -/
def starPlaneProjection (d : ℕ) (i : Fin d) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  starRootPart d +
    (starDirectionForm (starSimplexDirection d i)).smulRight (starSimplexDirection d i)

lemma starRootPart_apply {d : ℕ} (x : Fin d → ℝ) (j : Fin d) :
    starRootPart d x j = (∑ k, x k) / d := rfl

lemma starTransversePart_apply {d : ℕ} (x : Fin d → ℝ) (j : Fin d) :
    starTransversePart d x j = starCenteredCoordinate x j := rfl

lemma starPlaneProjection_apply {d : ℕ} (i : Fin d) (x : Fin d → ℝ) (j : Fin d) :
    starPlaneProjection d i x j = starRootPart d x j +
      (∑ k, starSimplexDirection d i k * x k) * starSimplexDirection d i j := rfl

lemma starRootPart_add_transversePart (d : ℕ) (x : Fin d → ℝ) :
    starRootPart d x + starTransversePart d x = x := by
  simp [starTransversePart]

lemma starRootPart_eq_rootForm_smul {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) :
    starRootPart d x = starRootForm x • starRootDirection d := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hs := Real.sq_sqrt hdp.le
  have hs0 := (Real.sqrt_pos.mpr hdp).ne'
  have hd0 : (d : ℝ) ≠ 0 := hdp.ne'
  ext j
  simp only [starRootPart_apply, starRootForm, Pi.smul_apply, starRootDirection, smul_eq_mul]
  field_simp

lemma sum_starRootPart {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) :
    (∑ j, starRootPart d x j) = ∑ j, x j := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [starRootPart_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma sum_starTransversePart {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) :
    (∑ j, starTransversePart d x j) = 0 :=
  sum_starCenteredCoordinate hd x

lemma starRootPart_of_sum_zero {d : ℕ} (x : Fin d → ℝ) (hx : ∑ j, x j = 0) :
    starRootPart d x = 0 := by ext j; simp [starRootPart_apply, hx]

lemma starRootPart_rootPart {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) :
    starRootPart d (starRootPart d x) = starRootPart d x := by
  ext j
  rw [starRootPart_apply, sum_starRootPart hd]
  rfl

lemma starPlaneProjection_rootPart {d : ℕ} (hd : 0 < d) (i : Fin d) (x : Fin d → ℝ) :
    starPlaneProjection d i (starRootPart d x) = starRootPart d x := by
  have hzero : (∑ j, starSimplexDirection d i j * starRootPart d x j) = 0 := by
    simp only [starRootPart_apply, ← Finset.sum_mul, sum_starSimplexDirection d hd i, zero_mul]
  ext j
  rw [starPlaneProjection_apply, hzero, zero_mul, add_zero, starRootPart_rootPart hd]

lemma starPlaneProjection_of_sum_zero {d : ℕ} (i : Fin d) (x : Fin d → ℝ)
    (hx : ∑ j, x j = 0) :
    starPlaneProjection d i x =
      (∑ j, starSimplexDirection d i j * x j) • starSimplexDirection d i := by
  ext j
  simp [starPlaneProjection_apply, starRootPart_apply, hx]

lemma starSimplex_inner (d : ℕ) (hd : 2 ≤ d) (i j : Fin d) :
    (∑ l, starSimplexDirection d i l * starSimplexDirection d j l) =
      if i = j then 1 else -1 / ((d : ℝ) - 1) := by
  have hdpos : 0 < d := by omega
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [starSimplexDirection_apply]
  rw [starCenteredCoordinate, sum_starSimplexDirection d hdpos j]
  simp only [zero_div, sub_zero]
  rw [starSimplexDirection_entry, ← mul_assoc, ← pow_two, transverseScale_sq d hd]
  split_ifs <;> field_simp
  ring

/-- The actual regular-simplex frame resolves every centered leaf vector. -/
lemma starSimplex_reconstruction (d : ℕ) (hd : 2 ≤ d) (x : Fin d → ℝ)
    (hx : ∑ j, x j = 0) :
    (∑ i, (∑ j, starSimplexDirection d i j * x j) • starSimplexDirection d i) =
      ((d : ℝ) / ((d : ℝ) - 1)) • x := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [starSimplexDirection_apply, starCenteredCoordinate, hx, zero_div, sub_zero,
    starSimplexDirection_entry]
  calc
    _ = ∑ i, transverseScale d ^ 2 *
        (x i * (if j = i then 1 else 0) - x i / d) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = transverseScale d ^ 2 *
        ((∑ i, x i * (if j = i then 1 else 0)) - (∑ i, x i) / d) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_div]
    _ = _ := by
      rw [hx, zero_div, sub_zero, transverseScale_sq d hd]
      simp [mul_ite]

lemma starPlaneProjection_sum_rootPart (d : ℕ) (hd : 0 < d) (x : Fin d → ℝ) :
    (∑ i, starPlaneProjection d i (starRootPart d x)) = (d : ℝ) • starRootPart d x := by
  simp only [starPlaneProjection_rootPart hd, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  exact_mod_cast (rfl : d • starRootPart d x = d • starRootPart d x)

lemma starPlaneProjection_sum_transversePart (d : ℕ) (hd : 2 ≤ d) (x : Fin d → ℝ) :
    (∑ i, starPlaneProjection d i (starTransversePart d x)) =
      ((d : ℝ) / ((d : ℝ) - 1)) • starTransversePart d x := by
  have hz := sum_starTransversePart (by omega : 0 < d) x
  simp_rw [starPlaneProjection_of_sum_zero _ _ hz]
  exact starSimplex_reconstruction d hd _ hz

lemma starPlaneProjection_simplex (d : ℕ) (hd : 2 ≤ d) (i j : Fin d) :
    starPlaneProjection d i (starSimplexDirection d j) =
      (if i = j then 1 else -1 / ((d : ℝ) - 1)) • starSimplexDirection d i := by
  rw [starPlaneProjection_of_sum_zero _ _ (sum_starSimplexDirection d (by omega) j),
    starSimplex_inner d hd]

/-- The constructed plane is exactly the range projection of the literal
orthonormal-row edge matrix, independently of the BS rotation parameter. -/
theorem starPlaneProjection_eq_transpose_mulVec (d : ℕ) (hd : 2 ≤ d)
    (c : ℝ) (hc : |c| < 1) (i : Fin d) (x : Fin d → ℝ) :
    starPlaneProjection d i x =
      (starEdgeProjection d c i).transpose.mulVec ((starEdgeProjection d c i).mulVec x) := by
  have hs := alpha_sq_add_beta_sq c hc
  have hroot := starRootPart_eq_rootForm_smul (by omega : 0 < d) x
  ext j
  rw [starPlaneProjection_apply, starSimplexDirection_apply]
  have hj := congrFun hroot j
  simp only [Pi.smul_apply, smul_eq_mul] at hj
  rw [hj]
  change _ = ∑ b : Bool, starEdgeProjection d c i b j *
    ((starEdgeProjection d c i).mulVec x b)
  rw [Fintype.sum_bool, starEdgeProjection_apply_false, starEdgeProjection_apply_true]
  simp only [starEdgeProjection, Bool.false_eq_true, ↓reduceIte, scoreA, scoreB, smul_eq_mul]
  linear_combination -(starRootForm x * starRootDirection d j +
    (transverseScale d * starCenteredCoordinate x i) * starSimplexDirection d i j) * hs

section TensorKernel
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma trilinear_commute_of_mixed (T : TrilinearForm E) (P : E →ₗ[ℝ] E)
    (hs : ∀ x y z, T x y z = T y x z)
    (hm : ∀ x y z, T (x - P x) (P y) z = 0) (x y z : E) :
    T (P x) y z = T x (P y) z := by
  have h1 := hm x y z
  have h2 := hm y x z
  rw [← hs (P x) (y - P y) z] at h2
  simp only [map_sub, LinearMap.sub_apply] at h1 h2
  linarith

lemma trilinear_spectral_separation {J : Type*} [Fintype J]
    (T : TrilinearForm E) (P : J → E →ₗ[ℝ] E)
    (hc : ∀ i x y z, T (P i x) y z = T x (P i y) z)
    (x y z : E) (a b : ℝ) (hne : a ≠ b)
    (hx : (∑ i, P i x) = a • x) (hy : (∑ i, P i y) = b • y) : T x y z = 0 := by
  have h : a * T x y z = b * T x y z := by
    calc
      _ = T (∑ i, P i x) y z := by rw [hx]; simp
      _ = ∑ i, T (P i x) y z := by simp
      _ = ∑ i, T x (P i y) z := Finset.sum_congr rfl (fun i _ => hc i x y z)
      _ = T x (∑ i, P i y) z := by simp
      _ = _ := by rw [hy]; simp
  exact (mul_eq_zero.mp (show (a - b) * T x y z = 0 by nlinarith)).resolve_left
    (sub_ne_zero.mpr hne)

end TensorKernel

section ScalarKernel
variable (d : ℕ) (hd : 3 ≤ d) (T : TrilinearForm (Fin d → ℝ))
variable (hs : ∀ x y z, T x y z = T y x z)
variable (hm : ∀ i : Fin d, ∀ x y z,
  T (x - starPlaneProjection d i x) (starPlaneProjection d i y) z = 0)

include hd hs hm in
lemma trilinear_root_transverse_zero (x y z : Fin d → ℝ) :
    T (starRootPart d x) (starTransversePart d y) z = 0 := by
  apply trilinear_spectral_separation T (starPlaneProjection d)
    (fun i => trilinear_commute_of_mixed T _ hs (hm i)) _ _ z
    (d : ℝ) ((d : ℝ) / ((d : ℝ) - 1))
  · have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    intro he
    have hh := (eq_div_iff (by linarith : (d : ℝ) - 1 ≠ 0)).mp he
    nlinarith
  · exact starPlaneProjection_sum_rootPart d (by omega) x
  · exact starPlaneProjection_sum_transversePart d (by omega) y

include hd hs hm in
lemma trilinear_centered_simplex (i : Fin d) (u z : Fin d → ℝ) (hu : ∑ j, u j = 0) :
    T u (starSimplexDirection d i) z =
      (∑ j, starSimplexDirection d i j * u j) *
        T (starSimplexDirection d i) (starSimplexDirection d i) z := by
  have h := trilinear_commute_of_mixed T (starPlaneProjection d i) hs (hm i)
    u (starSimplexDirection d i) z
  rw [starPlaneProjection_of_sum_zero _ _ hu, starPlaneProjection_simplex d (by omega),
    if_pos rfl, one_smul] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact h.symm

include hd hs hm in
lemma trilinear_simplex_diagonal_constant (i j : Fin d) (z : Fin d → ℝ) :
    T (starSimplexDirection d i) (starSimplexDirection d i) z =
      T (starSimplexDirection d j) (starSimplexDirection d j) z := by
  by_cases hij : i = j
  · subst j; rfl
  have hi := trilinear_centered_simplex d hd T hs hm i (starSimplexDirection d j) z
    (sum_starSimplexDirection d (by omega) j)
  have hj := trilinear_centered_simplex d hd T hs hm j (starSimplexDirection d i) z
    (sum_starSimplexDirection d (by omega) i)
  rw [starSimplex_inner d (by omega), if_neg hij] at hi
  rw [starSimplex_inner d (by omega), if_neg (Ne.symm hij)] at hj
  rw [hs] at hj
  have hnonzero : -1 / ((d : ℝ) - 1) ≠ 0 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact div_ne_zero (by norm_num) (by linarith)
  apply mul_left_cancel₀ hnonzero
  exact hi.symm.trans hj

include hd hs hm in
lemma trilinear_centered_factor (i₀ : Fin d) (u v z : Fin d → ℝ)
    (hu : ∑ j, u j = 0) (hv : ∑ j, v j = 0) :
    T u v z = (∑ j, u j * v j) *
      T (starSimplexDirection d i₀) (starSimplexDirection d i₀) z := by
  have hframe := starSimplex_reconstruction d (by omega) v hv
  have he := congrArg (fun w : Fin d → ℝ => T u w z) hframe
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at he
  have hsum : (∑ i : Fin d, (∑ j, starSimplexDirection d i j * v j) *
      T u (starSimplexDirection d i) z) =
      (∑ i : Fin d, (∑ j, starSimplexDirection d i j * v j) *
        (∑ j, starSimplexDirection d i j * u j)) *
        T (starSimplexDirection d i₀) (starSimplexDirection d i₀) z := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [trilinear_centered_simplex d hd T hs hm i u z hu,
      trilinear_simplex_diagonal_constant d hd T hs hm i i₀ z]
    ring
  rw [hsum] at he
  have hip' : (∑ i, (∑ j, starSimplexDirection d i j * v j) *
      (∑ j, starSimplexDirection d i j * u j)) =
      ((d : ℝ) / ((d : ℝ) - 1)) * ∑ j, u j * v j := by
    calc
      _ = ∑ j, u j * (∑ i, (∑ l, starSimplexDirection d i l * v l) *
          starSimplexDirection d i j) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        have hframe_apply (j : Fin d) :
            (∑ i, (∑ l, starSimplexDirection d i l * v l) * starSimplexDirection d i j) =
              ((d : ℝ) / ((d : ℝ) - 1)) * v j := by
          simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hframe j
        simp_rw [hframe_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [hip'] at he
  have hnonzero : (d : ℝ) / ((d : ℝ) - 1) ≠ 0 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact div_ne_zero (by linarith) (by linarith)
  apply mul_left_cancel₀ hnonzero
  nlinarith only [he]

include hd hs hm in
lemma trilinear_centered_coefficient_zero
    (hsyz : ∀ x y z, T x y z = T x z y) (i₀ l : Fin d) :
    T (starSimplexDirection d i₀) (starSimplexDirection d i₀)
      (starSimplexDirection d l) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin d, j ≠ l := by
    by_cases hl : l.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
  let C : (Fin d → ℝ) → ℝ := fun z =>
    T (starSimplexDirection d i₀) (starSimplexDirection d i₀) z
  let r : ℝ := -1 / ((d : ℝ) - 1)
  have hr2 : r ^ 2 < 1 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [r]
    rw [div_pow]
    norm_num only [neg_one_sq]
    exact (div_lt_one (by nlinarith : (0 : ℝ) < ((d : ℝ) - 1) ^ 2)).2 (by nlinarith)
  have hrel (a b : Fin d) (hab : a ≠ b) :
      C (starSimplexDirection d b) = r * C (starSimplexDirection d a) := by
    have h := hsyz (starSimplexDirection d a) (starSimplexDirection d a)
      (starSimplexDirection d b)
    rw [trilinear_centered_factor d hd T hs hm i₀ _ _ _
      (sum_starSimplexDirection d (by omega) a) (sum_starSimplexDirection d (by omega) a),
      trilinear_centered_factor d hd T hs hm i₀ _ _ _
      (sum_starSimplexDirection d (by omega) a) (sum_starSimplexDirection d (by omega) b),
      starSimplex_inner d (by omega), if_pos rfl,
      starSimplex_inner d (by omega), if_neg hab, one_mul] at h
    exact h
  have h1 := hrel j l hj
  have h2 := hrel l j (Ne.symm hj)
  have hzero : (1 - r ^ 2) * C (starSimplexDirection d l) = 0 := by
    rw [h2] at h1
    nlinarith only [h1]
  exact (mul_eq_zero.mp hzero).resolve_left (by linarith)

include hd hs hm in
lemma trilinear_centered_triple_zero
    (hsyz : ∀ x y z, T x y z = T x z y) (u v w : Fin d → ℝ)
    (hu : ∑ j, u j = 0) (hv : ∑ j, v j = 0) (hw : ∑ j, w j = 0) : T u v w = 0 := by
  let i₀ : Fin d := ⟨0, by omega⟩
  have hz : T (starSimplexDirection d i₀) (starSimplexDirection d i₀) w = 0 := by
    have hframe := starSimplex_reconstruction d (by omega) w hw
    have h := congrArg (fun v : Fin d → ℝ =>
      T (starSimplexDirection d i₀) (starSimplexDirection d i₀) v) hframe
    simp only [map_sum, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    simp_rw [trilinear_centered_coefficient_zero d hd T hs hm hsyz i₀] at h
    simp only [mul_zero, Finset.sum_const_zero] at h
    have hnonzero : (d : ℝ) / ((d : ℝ) - 1) ≠ 0 := by
      have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
      exact div_ne_zero (by linarith) (by linarith)
    exact (mul_eq_zero.mp h.symm).resolve_left hnonzero
  rw [trilinear_centered_factor d hd T hs hm i₀ u v w hu hv, hz, mul_zero]

include hd hs hm in
lemma trilinear_transverse_first_zero
    (hsyz : ∀ x y z, T x y z = T x z y) (x y z : Fin d → ℝ) :
    T (starTransversePart d x) y z = 0 := by
  have h1 : T (starTransversePart d x) (starRootPart d y) (starRootPart d z) = 0 := by
    rw [hs]
    exact trilinear_root_transverse_zero d hd T hs hm y x _
  have h2 : T (starTransversePart d x) (starRootPart d y) (starTransversePart d z) = 0 := by
    rw [hs]
    exact trilinear_root_transverse_zero d hd T hs hm y x _
  have h3 : T (starTransversePart d x) (starTransversePart d y) (starRootPart d z) = 0 := by
    rw [hsyz, hs]
    exact trilinear_root_transverse_zero d hd T hs hm z x _
  have h4 := trilinear_centered_triple_zero d hd T hs hm hsyz
    (starTransversePart d x) (starTransversePart d y) (starTransversePart d z)
    (sum_starTransversePart (by omega) x) (sum_starTransversePart (by omega) y)
    (sum_starTransversePart (by omega) z)
  calc
    _ = T (starTransversePart d x) (starRootPart d y + starTransversePart d y)
        (starRootPart d z + starTransversePart d z) := by
      rw [starRootPart_add_transversePart, starRootPart_add_transversePart]
    _ = 0 := by simp only [map_add, LinearMap.add_apply, h1, h2, h3, h4, add_zero]

include hd hs hm in
/-- The actual scalar BS mixed-fiber kernel is root-only. This is an algebraic
statement about the genuine third derivative tensor once score-fiber equality
has supplied its mixed-kernel hypothesis. -/
theorem star_mixed_third_derivative_kernel
    (hsyz : ∀ x y z, T x y z = T x z y) (x y z : Fin d → ℝ) :
    T x y z = T (starRootPart d x) (starRootPart d y) (starRootPart d z) := by
  have hzero (u v w : Fin d → ℝ) := trilinear_transverse_first_zero d hd T hs hm hsyz u v w
  have hx : T x y z = T (starRootPart d x) y z := by
    calc
      _ = T (starRootPart d x + starTransversePart d x) y z := by rw [starRootPart_add_transversePart]
      _ = _ := by simp only [map_add, LinearMap.add_apply, hzero, add_zero]
  have hy : T (starRootPart d x) y z = T (starRootPart d x) (starRootPart d y) z := by
    calc
      _ = T (starRootPart d x) (starRootPart d y + starTransversePart d y) z := by
        rw [starRootPart_add_transversePart]
      _ = _ := by
        rw [map_add, LinearMap.add_apply, hs (starRootPart d x) (starTransversePart d y) z, hzero]
        simp
  have hz : T (starRootPart d x) (starRootPart d y) z =
      T (starRootPart d x) (starRootPart d y) (starRootPart d z) := by
    calc
      _ = T (starRootPart d x) (starRootPart d y) (starRootPart d z + starTransversePart d z) := by
        rw [starRootPart_add_transversePart]
      _ = _ := by
        rw [map_add, hsyz (starRootPart d x) (starRootPart d y) (starTransversePart d z),
          hs (starRootPart d x) (starTransversePart d z) (starRootPart d y), hzero]
        simp
  exact hx.trans (hy.trans hz)

end ScalarKernel

section SmoothCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual nested third Fréchet derivative. -/
def thirdFDeriv (L : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (fderiv ℝ L)) x

/-- Forget continuity of the derivative tensor while preserving its actual
linear evaluations, for the finite projection algebra above. -/
def trilinearOfContinuous (U : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : TrilinearForm E where
  toFun u :=
    { toFun := fun v => (U u v).toLinearMap
      map_add' v w := by ext z; simp
      map_smul' a v := by ext z; simp }
  map_add' u v := by ext w z; simp
  map_smul' a u := by ext w z; simp

@[simp] lemma trilinearOfContinuous_apply (U : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (u v w : E) : trilinearOfContinuous U u v w = U u v w := rfl

lemma hasFDerivAt_evaluate_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : E → E →L[ℝ] F} {U' : E →L[ℝ] E →L[ℝ] F} {x : E}
    (hU : HasFDerivAt U U' x) (v : E) :
    HasFDerivAt (fun y => U y v) (U'.flip v) x := by
  simpa only [ContinuousLinearMap.comp_zero, zero_add] using
    hU.clm_apply (hasFDerivAt_const v x)

/-- A third derivative that vanishes whenever the middle direction is u
makes the corresponding Hessian coefficient constant over the whole space. -/
theorem hessian_coefficient_constant_of_third_zero (L : E → ℝ)
    (hL : ContDiff ℝ 3 L) (u v : E)
    (hzero : ∀ x w, thirdFDeriv L x w u v = 0) (x : E) :
    fderiv ℝ (fderiv ℝ L) x u v = fderiv ℝ (fderiv ℝ L) 0 u v := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ L) := hL.fderiv_right (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ (fderiv ℝ L)) :=
    (h1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hq (y : E) : HasFDerivAt
      (fun z => fderiv ℝ (fderiv ℝ L) z u v)
      (((thirdFDeriv L y).flip u).flip v) y :=
    hasFDerivAt_evaluate_const (hasFDerivAt_evaluate_const (h2 y).hasFDerivAt u) v
  apply is_const_of_fderiv_eq_zero (fun y => (hq y).differentiableAt) _ x 0
  intro y
  rw [(hq y).fderiv]
  ext w
  exact hzero y w

/-- Elementary antiderivative uniqueness, proved by the zero-derivative mean
value theorem. -/
lemma eq_add_mul_of_hasDerivAt_const (q : ℝ → ℝ) (a : ℝ)
    (hq : ∀ t, HasDerivAt q a t) (t : ℝ) : q t = q 0 + t * a := by
  have hz (s : ℝ) : HasDerivAt (fun t => q t - t * a) 0 s := by
    simpa using (hq s).sub ((hasDerivAt_id s).mul_const a)
  have heq := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
    (fun s => (hz s).deriv) t 0
  simp only [zero_mul, sub_zero] at heq
  linarith

/-- Integrating an actual constant Hessian along a transverse line gives its
quadratic Taylor formula, with no density-shape assumption. -/
theorem quadratic_along_of_hessian_constant (L : E → ℝ) (hL : ContDiff ℝ 2 L)
    (r u : E) (B : ℝ)
    (hH : ∀ x, fderiv ℝ (fderiv ℝ L) x u u = B) :
    L (r + u) = L r + fderiv ℝ L r u + B / 2 := by
  have hL1 : Differentiable ℝ L := hL.differentiable (by norm_num)
  have hL2 : Differentiable ℝ (fderiv ℝ L) :=
    (hL.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hcurve (t : ℝ) : HasDerivAt (fun s : ℝ => r + s • u) u t := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const t r).add ((hasDerivAt_id t).smul_const u)
  let q : ℝ → ℝ := fun t => fderiv ℝ L (r + t • u) u
  have hq (t : ℝ) : HasDerivAt q B t := by
    have h := (hasFDerivAt_evaluate_const (hL2 (r + t • u)).hasFDerivAt u).comp_hasDerivAt t (hcurve t)
    simpa only [ContinuousLinearMap.flip_apply, hH] using h
  have hqeq (t : ℝ) : q t = fderiv ℝ L r u + t * B := by
    simpa [q] using eq_add_mul_of_hasDerivAt_const q B hq t
  let p : ℝ → ℝ := fun t => L (r + t • u) -
    (L r + t * fderiv ℝ L r u + (t ^ 2 / 2) * B)
  have hp (t : ℝ) : HasDerivAt p 0 t := by
    have hf := (hL1 (r + t • u)).hasFDerivAt.comp_hasDerivAt t (hcurve t)
    have hg := ((hasDerivAt_const t (L r)).add
      ((hasDerivAt_id t).mul_const (fderiv ℝ L r u))).add
        (((hasDerivAt_id t).pow 2).div_const 2 |>.mul_const B)
    norm_num only [id_eq, Nat.reduceSub, Nat.cast_ofNat, pow_one, one_mul, mul_one, zero_add] at hg
    convert hf.sub hg using 1
    dsimp [q] at hqeq
    nlinarith [hqeq t]
  have heq := is_const_of_deriv_eq_zero (fun t => (hp t).differentiableAt)
    (fun t => (hp t).deriv) 1 0
  dsimp [p] at heq
  simp only [one_smul, zero_smul, add_zero, one_mul, one_pow, zero_mul, zero_pow
    (by norm_num : 2 ≠ 0), zero_div] at heq
  linarith

end SmoothCalculus

section PermutationSymmetry

/-- Actual coordinate permutation, as a continuous linear operator. -/
def starPermutationLinear {d : ℕ} (p : Equiv.Perm (Fin d)) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x j => x (p j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] lemma starPermutationLinear_apply {d : ℕ} (p : Equiv.Perm (Fin d))
    (x : Fin d → ℝ) (j : Fin d) : starPermutationLinear p x j = x (p j) := rfl

lemma starPermutationLinear_rootPart {d : ℕ} (p : Equiv.Perm (Fin d)) (x : Fin d → ℝ) :
    starPermutationLinear p (starRootPart d x) = starRootPart d x := by ext j; rfl

lemma starPermutationLinear_coordinate {d : ℕ} (p : Equiv.Perm (Fin d)) (i : Fin d) :
    starPermutationLinear p (starCoordinateVector i) = starCoordinateVector (p.symm i) := by
  ext j
  change (if p j = i then (1 : ℝ) else 0) = (if j = p.symm i then 1 else 0)
  simp only [p.apply_eq_iff_eq_symm_apply]

/-- Neighbor permutation invariance removes every transverse component of
the gradient at a constant root point. -/
theorem derivative_rootPart_centered_eq_zero {d : ℕ} (hd : 0 < d)
    (L : (Fin d → ℝ) → ℝ) (hL : Differentiable ℝ L)
    (hperm : ∀ p : Equiv.Perm (Fin d), ∀ x, L (fun j => x (p j)) = L x)
    (x u : Fin d → ℝ) (hu : ∑ j, u j = 0) :
    fderiv ℝ L (starRootPart d x) u = 0 := by
  let r := starRootPart d x
  have hD (p : Equiv.Perm (Fin d)) :
      (fderiv ℝ L r).comp (starPermutationLinear p) = fderiv ℝ L r := by
    have heq : L ∘ starPermutationLinear p = L := by funext y; exact hperm p y
    have h := (hL (starPermutationLinear p r)).hasFDerivAt.comp r
      (starPermutationLinear p).hasFDerivAt
    have hfix : starPermutationLinear p r = r := starPermutationLinear_rootPart p x
    rw [heq, hfix] at h
    exact h.unique (hL r).hasFDerivAt
  let i₀ : Fin d := ⟨0, hd⟩
  have hcoef (i : Fin d) :
      fderiv ℝ L r (starCoordinateVector i) = fderiv ℝ L r (starCoordinateVector i₀) := by
    have h := congrArg (fun A : (Fin d → ℝ) →L[ℝ] ℝ => A (starCoordinateVector i))
      (hD (Equiv.swap i i₀))
    simp only [ContinuousLinearMap.comp_apply, starPermutationLinear_coordinate,
      Equiv.symm_swap, Equiv.swap_apply_left] at h
    exact h.symm
  have hreconstruct : u = ∑ i : Fin d, u i • starCoordinateVector i := by
    ext j
    simp [starCoordinateVector, mul_ite]
  change fderiv ℝ L r u = 0
  rw [hreconstruct, map_sum]
  simp_rw [map_smul, smul_eq_mul, hcoef]
  rw [← Finset.sum_mul, hu, zero_mul]

end PermutationSymmetry

section SmoothStarRigidity
variable {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- Differentiating a genuine mixed Hessian identity supplies the mixed third
kernel; its symmetry follows from C3 regularity. -/
theorem third_mixed_zero_of_hessian_mixed_zero
    (L : (Fin d → ℝ) → ℝ) (hL : ContDiff ℝ 3 L)
    (hH : ∀ x i u v,
      fderiv ℝ (fderiv ℝ L) x (u - starPlaneProjection d i u)
        (starPlaneProjection d i v) = 0)
    (x : Fin d → ℝ) (i : Fin d) (u v w : Fin d → ℝ) :
    thirdFDeriv L x (u - starPlaneProjection d i u) (starPlaneProjection d i v) w = 0 := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ L) := hL.fderiv_right (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ (fderiv ℝ L)) :=
    (h1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  let a : Fin d → ℝ := u - starPlaneProjection d i u
  let b : Fin d → ℝ := starPlaneProjection d i v
  have heq : (fun y => fderiv ℝ (fderiv ℝ L) y a b) = (fun _ => (0 : ℝ)) := by
    funext y
    exact hH y i u v
  have h : HasFDerivAt (fun y => fderiv ℝ (fderiv ℝ L) y a b)
      (((thirdFDeriv L x).flip a).flip b) x :=
    hasFDerivAt_evaluate_const (hasFDerivAt_evaluate_const (h2 x).hasFDerivAt a) b
  rw [heq] at h
  have hz := congrArg (fun A : (Fin d → ℝ) →L[ℝ] ℝ => A w)
    (h.unique (hasFDerivAt_const (0 : ℝ) x))
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply] at hz
  change thirdDifferential L x a b w = 0
  rw [← thirdDifferential_swap_last L hL x a w b,
    ← thirdDifferential_swap_first L hL x w a b]
  exact hz

/-- The actual C3 third derivative is root-only once its mixed Hessian
coefficients vanish across all actual edge planes. -/
theorem thirdFDeriv_root_only (hd : 3 ≤ d)
    (L : (Fin d → ℝ) → ℝ) (hL : ContDiff ℝ 3 L)
    (hH : ∀ x i u v,
      fderiv ℝ (fderiv ℝ L) x (u - starPlaneProjection d i u)
        (starPlaneProjection d i v) = 0)
    (x u v w : Fin d → ℝ) :
    thirdFDeriv L x u v w = thirdFDeriv L x
      (starRootPart d u) (starRootPart d v) (starRootPart d w) := by
  apply star_mixed_third_derivative_kernel d hd (trilinearOfContinuous (thirdFDeriv L x))
  · exact thirdDifferential_swap_first L hL x
  · exact third_mixed_zero_of_hessian_mixed_zero L hL hH x
  · exact thirdDifferential_swap_last L hL x

/-- Constant transverse Hessian entries are derived by differentiating the
actual Hessian and applying the mixed third-derivative kernel. -/
theorem transverse_hessian_constant (hd : 3 ≤ d)
    (L : (Fin d → ℝ) → ℝ) (hL : ContDiff ℝ 3 L)
    (hH : ∀ x i u v,
      fderiv ℝ (fderiv ℝ L) x (u - starPlaneProjection d i u)
        (starPlaneProjection d i v) = 0)
    (u v : Fin d → ℝ) (hu : ∑ j, u j = 0) (x : Fin d → ℝ) :
    fderiv ℝ (fderiv ℝ L) x u v = fderiv ℝ (fderiv ℝ L) 0 u v := by
  apply hessian_coefficient_constant_of_third_zero L hL u v _ x
  intro y w
  rw [thirdFDeriv_root_only hd L hL hH, starRootPart_of_sum_zero u hu]
  simp

/-- A genuine smooth permutation-invariant log density with vanishing mixed
Hessian across the actual BS planes is a root function plus a constant
transverse quadratic. This conclusion is obtained by calculus and symmetry,
not supplied as a density-shape premise. -/
theorem logDensity_root_plus_constant_quadratic (hd : 3 ≤ d)
    (L : (Fin d → ℝ) → ℝ) (hL : ContDiff ℝ 3 L)
    (hH : ∀ x i u v,
      fderiv ℝ (fderiv ℝ L) x (u - starPlaneProjection d i u)
        (starPlaneProjection d i v) = 0)
    (hperm : ∀ p : Equiv.Perm (Fin d), ∀ x, L (fun j => x (p j)) = L x)
    (x : Fin d → ℝ) :
    L x = L (starRootPart d x) +
      fderiv ℝ (fderiv ℝ L) 0 (starTransversePart d x) (starTransversePart d x) / 2 := by
  let r := starRootPart d x
  let u := starTransversePart d x
  have hu : ∑ j, u j = 0 := sum_starTransversePart (by omega) x
  have hquad := quadratic_along_of_hessian_constant L (hL.of_le (by decide)) r u
    (fderiv ℝ (fderiv ℝ L) 0 u u)
    (fun y => transverse_hessian_constant hd L hL hH u u hu y)
  have hgrad : fderiv ℝ L r u = 0 :=
    derivative_rootPart_centered_eq_zero (by omega) L (hL.differentiable (by norm_num)) hperm x u hu
  rw [hgrad, add_zero] at hquad
  simpa only [r, u, starRootPart_add_transversePart] using hquad

end SmoothStarRigidity

section IsotropicQuadratic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def bilinearOfContinuous (B : E →L[ℝ] E →L[ℝ] ℝ) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun u := (B u).toLinearMap
  map_add' u v := by ext w; simp
  map_smul' a u := by ext w; simp

def bilinearTimesLinear (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (l : E →ₗ[ℝ] ℝ) : TrilinearForm E where
  toFun u :=
    { toFun := fun v => (B u v) • l
      map_add' v w := by ext z; simp [add_mul]
      map_smul' a v := by ext z; simp [mul_assoc] }
  map_add' u v := by ext w z; simp [add_mul]
  map_smul' a u := by ext w z; simp [mul_assoc]

/-- A symmetric Hessian with zero mixed blocks across all actual star planes
has a scalar transverse block. This is forced by the simplex geometry. -/
theorem bilinear_centered_factor {d : ℕ} (hd : 3 ≤ d)
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ)
    (hs : ∀ u v, B u v = B v u)
    (hm : ∀ i u v, B (u - starPlaneProjection d i u) (starPlaneProjection d i v) = 0)
    (i₀ : Fin d) (u v : Fin d → ℝ) (hu : ∑ j, u j = 0) (hv : ∑ j, v j = 0) :
    B u v = (∑ j, u j * v j) * B (starSimplexDirection d i₀) (starSimplexDirection d i₀) := by
  let l : (Fin d → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i₀
  let T := bilinearTimesLinear (bilinearOfContinuous B) l
  have hsT : ∀ x y z, T x y z = T y x z := by
    intro x y z
    change B x y * l z = B y x * l z
    rw [hs]
  have hmT : ∀ i x y z,
      T (x - starPlaneProjection d i x) (starPlaneProjection d i y) z = 0 := by
    intro i x y z
    change B (x - starPlaneProjection d i x) (starPlaneProjection d i y) * l z = 0
    rw [hm, zero_mul]
  have h := trilinear_centered_factor d hd T hsT hmT i₀ u v (starCoordinateVector i₀) hu hv
  simpa [T, bilinearTimesLinear, bilinearOfContinuous, l, starCoordinateVector] using h

/-- The fully explicit scalar shape forced by the mixed Hessian condition:
a root function plus one fixed scalar multiple of the transverse radius. -/
theorem logDensity_root_plus_isotropic_quadratic {d : ℕ} (hd : 3 ≤ d)
    (L : (Fin d → ℝ) → ℝ) (hL : ContDiff ℝ 3 L)
    (hH : ∀ x i u v,
      fderiv ℝ (fderiv ℝ L) x (u - starPlaneProjection d i u)
        (starPlaneProjection d i v) = 0)
    (hperm : ∀ p : Equiv.Perm (Fin d), ∀ x, L (fun j => x (p j)) = L x)
    (i₀ : Fin d) (x : Fin d → ℝ) :
    L x = L (starRootPart d x) +
      (fderiv ℝ (fderiv ℝ L) 0 (starSimplexDirection d i₀) (starSimplexDirection d i₀) / 2) *
        squareRadius (starTransversePart d x) := by
  have hs : ∀ u v, fderiv ℝ (fderiv ℝ L) 0 u v = fderiv ℝ (fderiv ℝ L) 0 v u :=
    hL.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
  have hu := sum_starTransversePart (by omega : 0 < d) x
  have hfactor := bilinear_centered_factor hd (fderiv ℝ (fderiv ℝ L) 0) hs (hH 0)
    i₀ (starTransversePart d x) (starTransversePart d x) hu hu
  calc
    L x = L (starRootPart d x) +
        fderiv ℝ (fderiv ℝ L) 0 (starTransversePart d x) (starTransversePart d x) / 2 :=
      logDensity_root_plus_constant_quadratic hd L hL hH hperm x
    _ = _ := by rw [hfactor]; simp only [squareRadius, pow_two]; ring

end IsotropicQuadratic

section ActualHeatRigidity
open MeasureTheory

lemma heatKernel_permutation {d : ℕ} (p : Equiv.Perm (Fin d)) (t : ℝ) (x : Fin d → ℝ) :
    heatKernel t (fun j => x (p j)) = heatKernel t x := by
  exact Equiv.prod_comp p (fun j => ProbabilityTheory.gaussianPDFReal 0 (heatVariance t) (x j))

/-- Actual permutation invariance of the mixing law passes to its pointwise
heat density. This uses the Gaussian product kernel and an integral map. -/
theorem heatDensity_permutation_of_law {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (p : Equiv.Perm (Fin d))
    (hperm : Measure.map (fun x : Fin d → ℝ => fun j => x (p j)) μ = μ)
    (t : ℝ) (x : Fin d → ℝ) :
    heatDensity μ t (fun j => x (p j)) = heatDensity μ t x := by
  let P : (Fin d → ℝ) → (Fin d → ℝ) := fun y j => y (p j)
  have hP : Measurable P := (starPermutationLinear p).continuous.measurable
  calc
    _ = heatDensity (Measure.map P μ) t (P x) := by rw [hperm]
    _ = ∫ y, heatKernel t (P x - P y) ∂μ := by
      have hf : AEStronglyMeasurable (fun y : Fin d → ℝ => heatKernel t (P x - y))
          (Measure.map P μ) :=
        (((continuous_heatKernel t).comp (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
      exact integral_map hP.aemeasurable hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact heatKernel_permutation p t (x - y)

/-- Zero actual strict-bulk Fisher defect yields the root-plus-Gaussian-form
log-density shape. Smoothness, pointwise fiber rigidity, mixed derivatives,
constant Hessian, and permutation removal of linear terms are all proved
internally from the actual heated probability law. The coefficient is still
identified analytically from normalization/covariance in the next stage. -/
theorem log_heatDensity_root_plus_isotropic_quadratic_of_fisherDefect_zero
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    (hzero : heatFrameFisherDefect μ (starEdgeProjection d c) t = 0)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : Fin d → ℝ => fun j => x (p j)) μ = μ)
    (i₀ : Fin d) (x : Fin d → ℝ) :
    let L := fun y => Real.log (heatDensity μ t y)
    L x = L (starRootPart d x) +
      (fderiv ℝ (fderiv ℝ L) 0 (starSimplexDirection d i₀) (starSimplexDirection d i₀) / 2) *
        squareRadius (starTransversePart d x) := by
  apply logDensity_root_plus_isotropic_quadratic hd _ (contDiff_three_log_heatDensity μ ht)
  · intro y i u v
    have h := star_log_heatDensity_hessian_mixed_of_fisherDefect_zero
      d hd c hbulk μ ht hrev hzero y i u v
    dsimp only at h
    have hc := (bulk_rho_lower d hd c hbulk).1
    rw [← starPlaneProjection_eq_transpose_mulVec d (by omega) c hc i u,
      ← starPlaneProjection_eq_transpose_mulVec d (by omega) c hc i v] at h
    exact h
  · intro p y
    exact congrArg Real.log (heatDensity_permutation_of_law μ p (hperm p) t y)

end ActualHeatRigidity
end GaussianWave.BS
