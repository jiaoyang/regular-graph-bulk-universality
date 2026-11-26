import GaussianWave.BS.ColoredGeometry
import GaussianWave.BS.ColoredScoreRigidity
import GaussianWave.BS.BilinearScoreNormalization

/-! Genuine cross-channel mixed third derivative rigidity. -/
noncomputable section
open scoped BigOperators Topology ContDiff
namespace GaussianWave.BS

section ColoredTensorKernel
variable (d r : ℕ) (hd : 3 ≤ d) (T : TrilinearForm (ColoredSpace d r))
variable (hs : ∀ x y z, T x y z = T y x z)
variable (hm : ∀ i : Fin d, ∀ x y z,
  T (x - coloredPlaneProjection d r i x) (coloredPlaneProjection d r i y) z = 0)

include hd hs hm in
theorem colored_trilinear_root_transverse_zero (x y z : ColoredSpace d r) :
    T (coloredRootPart d r x) (coloredTransversePart d r y) z = 0 := by
  apply trilinear_spectral_separation T (coloredPlaneProjection d r)
    (fun i => trilinear_commute_of_mixed T _ hs (hm i)) _ _ z
    (d : ℝ) ((d : ℝ) / ((d : ℝ) - 1))
  · have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    intro he
    have hh := (eq_div_iff (by linarith : (d : ℝ) - 1 ≠ 0)).mp he
    nlinarith
  · exact coloredPlaneProjection_sum_rootPart d r (by omega) x
  · exact coloredPlaneProjection_sum_transversePart d r (by omega) y

include hd hs hm in
theorem colored_trilinear_block_simplex (a b : Fin r) (i : Fin d)
    (u : Fin d → ℝ) (hu : ∑ j, u j = 0) (z : ColoredSpace d r) :
    T (coloredBlock d r a u) (coloredBlock d r b (starSimplexDirection d i)) z =
      (∑ j, starSimplexDirection d i j * u j) *
        T (coloredBlock d r a (starSimplexDirection d i))
          (coloredBlock d r b (starSimplexDirection d i)) z := by
  have h := trilinear_commute_of_mixed T (coloredPlaneProjection d r i) hs (hm i)
    (coloredBlock d r a u) (coloredBlock d r b (starSimplexDirection d i)) z
  rw [coloredPlaneProjection_block, coloredPlaneProjection_block,
    starPlaneProjection_of_sum_zero _ _ hu, starPlaneProjection_simplex d (by omega),
    if_pos rfl, one_smul] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact h.symm

include hd hs hm in
theorem colored_trilinear_simplex_coefficient_constant (a b : Fin r) (i j : Fin d)
    (z : ColoredSpace d r) :
    T (coloredBlock d r a (starSimplexDirection d i))
      (coloredBlock d r b (starSimplexDirection d i)) z =
    T (coloredBlock d r a (starSimplexDirection d j))
      (coloredBlock d r b (starSimplexDirection d j)) z := by
  by_cases hij : i = j
  · subst j; rfl
  have hi := colored_trilinear_block_simplex d r hd T hs hm a b i (starSimplexDirection d j)
    (sum_starSimplexDirection d (by omega) j) z
  have hj := colored_trilinear_block_simplex d r hd T hs hm b a j (starSimplexDirection d i)
    (sum_starSimplexDirection d (by omega) i) z
  rw [hs] at hj
  rw [starSimplex_inner d (by omega), if_neg hij] at hi
  rw [starSimplex_inner d (by omega), if_neg (Ne.symm hij)] at hj
  have hswap := hs (coloredBlock d r b (starSimplexDirection d j))
    (coloredBlock d r a (starSimplexDirection d j)) z
  rw [hswap] at hj
  have hnonzero : -1 / ((d : ℝ) - 1) ≠ 0 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact div_ne_zero (by norm_num) (by linarith)
  apply mul_left_cancel₀ hnonzero
  exact hi.symm.trans hj

include hd hs hm in
theorem colored_trilinear_centered_factor (a b : Fin r) (i₀ : Fin d)
    (u v : Fin d → ℝ) (hu : ∑ j, u j = 0) (hv : ∑ j, v j = 0)
    (z : ColoredSpace d r) :
    T (coloredBlock d r a u) (coloredBlock d r b v) z =
      (∑ j, u j * v j) * T (coloredBlock d r a (starSimplexDirection d i₀))
        (coloredBlock d r b (starSimplexDirection d i₀)) z := by
  have hframe := starSimplex_reconstruction d (by omega) v hv
  have he := congrArg (fun w : Fin d → ℝ => T (coloredBlock d r a u) (coloredBlock d r b w) z) hframe
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at he
  have hsum : (∑ i : Fin d, (∑ j, starSimplexDirection d i j * v j) *
      T (coloredBlock d r a u) (coloredBlock d r b (starSimplexDirection d i)) z) =
      (∑ i : Fin d, (∑ j, starSimplexDirection d i j * v j) *
        (∑ j, starSimplexDirection d i j * u j)) *
        T (coloredBlock d r a (starSimplexDirection d i₀))
          (coloredBlock d r b (starSimplexDirection d i₀)) z := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [colored_trilinear_block_simplex d r hd T hs hm a b i u hu z,
      colored_trilinear_simplex_coefficient_constant d r hd T hs hm a b i i₀ z]
    ring
  rw [hsum] at he
  have hip : (∑ i, (∑ j, starSimplexDirection d i j * v j) *
      (∑ j, starSimplexDirection d i j * u j)) =
      ((d : ℝ) / ((d : ℝ) - 1)) * ∑ j, u j * v j := by
    calc
      _ = ∑ j, u j * (∑ i, (∑ l, starSimplexDirection d i l * v l) * starSimplexDirection d i j) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        have hp (j : Fin d) :
            (∑ i, (∑ l, starSimplexDirection d i l * v l) * starSimplexDirection d i j) =
              ((d : ℝ) / ((d : ℝ) - 1)) * v j := by
          simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hframe j
        simp_rw [hp]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hip] at he
  have hnonzero : (d : ℝ) / ((d : ℝ) - 1) ≠ 0 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact div_ne_zero (by linarith) (by linarith)
  apply mul_left_cancel₀ hnonzero
  nlinarith only [he]

include hd hs hm in
theorem colored_trilinear_centered_coefficient_zero
    (hsyz : ∀ x y z, T x y z = T x z y)
    (a b c : Fin r) (i₀ l : Fin d) :
    T (coloredBlock d r a (starSimplexDirection d i₀))
      (coloredBlock d r b (starSimplexDirection d i₀))
      (coloredBlock d r c (starSimplexDirection d l)) = 0 := by
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
  let ρ : ℝ := -1 / ((d : ℝ) - 1)
  let v : Fin d → ℝ := starSimplexDirection d j - ρ • starSimplexDirection d l
  have hρ : ρ ^ 2 < 1 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [ρ]
    rw [div_pow]
    norm_num only [neg_one_sq]
    exact (div_lt_one (by nlinarith : (0 : ℝ) < ((d : ℝ) - 1) ^ 2)).2 (by nlinarith)
  have hv : ∑ k, v k = 0 := by
    simp only [v, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_starSimplexDirection d (by omega), mul_zero, sub_zero]
  have hortho : (∑ k, v k * starSimplexDirection d l k) = 0 := by
    change (starSimplexDirection d j - ρ • starSimplexDirection d l) ⬝ᵥ starSimplexDirection d l = 0
    rw [sub_dotProduct, smul_dotProduct]
    simp only [dotProduct, starSimplex_inner d (by omega), if_neg hj, if_pos rfl, smul_eq_mul, mul_one]
    dsimp [ρ]
    ring
  have hvnorm : squareRadius v = 1 - ρ ^ 2 := by
    simp only [squareRadius, pow_two]
    change v ⬝ᵥ v = 1 - ρ * ρ
    dsimp only [v]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    simp only [dotProduct, starSimplex_inner d (by omega), if_neg hj, if_neg (Ne.symm hj),
      if_pos rfl, smul_eq_mul, mul_one]
    dsimp [ρ]
    ring
  have hvpos : 0 < ∑ k, v k * v k := by
    have hp : 0 < squareRadius v := by rw [hvnorm]; linarith
    simpa only [squareRadius, pow_two] using hp
  have h := hsyz (coloredBlock d r a v) (coloredBlock d r b v)
    (coloredBlock d r c (starSimplexDirection d l))
  rw [colored_trilinear_centered_factor d r hd T hs hm a b i₀ v v hv hv,
    colored_trilinear_centered_factor d r hd T hs hm a c i₀ v (starSimplexDirection d l) hv
      (sum_starSimplexDirection d (by omega) l), hortho, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hvpos.ne'

include hd hs hm in
theorem colored_trilinear_centered_blocks_zero
    (hsyz : ∀ x y z, T x y z = T x z y)
    (a b c : Fin r) (u v w : Fin d → ℝ)
    (hu : ∑ j, u j = 0) (hv : ∑ j, v j = 0) (hw : ∑ j, w j = 0) :
    T (coloredBlock d r a u) (coloredBlock d r b v) (coloredBlock d r c w) = 0 := by
  let i₀ : Fin d := ⟨0, by omega⟩
  have hz : T (coloredBlock d r a (starSimplexDirection d i₀))
      (coloredBlock d r b (starSimplexDirection d i₀)) (coloredBlock d r c w) = 0 := by
    have hframe := starSimplex_reconstruction d (by omega) w hw
    have h := congrArg (fun z : Fin d → ℝ =>
      T (coloredBlock d r a (starSimplexDirection d i₀))
        (coloredBlock d r b (starSimplexDirection d i₀)) (coloredBlock d r c z)) hframe
    simp only [map_sum, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    simp_rw [colored_trilinear_centered_coefficient_zero d r hd T hs hm hsyz a b c i₀] at h
    simp only [mul_zero, Finset.sum_const_zero] at h
    have hnonzero : (d : ℝ) / ((d : ℝ) - 1) ≠ 0 := by
      have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
      exact div_ne_zero (by linarith) (by linarith)
    exact (mul_eq_zero.mp h.symm).resolve_left hnonzero
  rw [colored_trilinear_centered_factor d r hd T hs hm a b i₀ u v hu hv, hz, mul_zero]

include hd hs hm in
theorem colored_trilinear_transverse_parts_zero
    (hsyz : ∀ x y z, T x y z = T x z y) (x y z : ColoredSpace d r) :
    T (coloredTransversePart d r x) (coloredTransversePart d r y) (coloredTransversePart d r z) = 0 := by
  rw [coloredTransversePart_eq_sum_blocks d r x, coloredTransversePart_eq_sum_blocks d r y,
    coloredTransversePart_eq_sum_blocks d r z]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro c _
  exact colored_trilinear_centered_blocks_zero d r hd T hs hm hsyz c b a _ _ _
    (sum_coloredTransversePart d r (by omega) x c)
    (sum_coloredTransversePart d r (by omega) y b)
    (sum_coloredTransversePart d r (by omega) z a)

include hd hs hm in
theorem colored_trilinear_transverse_first_zero
    (hsyz : ∀ x y z, T x y z = T x z y) (x y z : ColoredSpace d r) :
    T (coloredTransversePart d r x) y z = 0 := by
  have h1 : T (coloredTransversePart d r x) (coloredRootPart d r y) (coloredRootPart d r z) = 0 := by
    rw [hs]
    exact colored_trilinear_root_transverse_zero d r hd T hs hm y x _
  have h2 : T (coloredTransversePart d r x) (coloredRootPart d r y) (coloredTransversePart d r z) = 0 := by
    rw [hs]
    exact colored_trilinear_root_transverse_zero d r hd T hs hm y x _
  have h3 : T (coloredTransversePart d r x) (coloredTransversePart d r y) (coloredRootPart d r z) = 0 := by
    rw [hsyz, hs]
    exact colored_trilinear_root_transverse_zero d r hd T hs hm z x _
  have h4 := colored_trilinear_transverse_parts_zero d r hd T hs hm hsyz x y z
  calc
    _ = T (coloredTransversePart d r x)
        (coloredRootPart d r y + coloredTransversePart d r y)
        (coloredRootPart d r z + coloredTransversePart d r z) := by
      rw [coloredRootPart_add_transversePart, coloredRootPart_add_transversePart]
    _ = 0 := by simp only [map_add, LinearMap.add_apply, h1, h2, h3, h4, add_zero]

include hd hs hm in
theorem colored_mixed_third_derivative_kernel
    (hsyz : ∀ x y z, T x y z = T x z y) (x y z : ColoredSpace d r) :
    T x y z = T (coloredRootPart d r x) (coloredRootPart d r y) (coloredRootPart d r z) := by
  have hz := colored_trilinear_transverse_first_zero d r hd T hs hm hsyz
  have hx : T x y z = T (coloredRootPart d r x) y z := by
    calc
      _ = T (coloredRootPart d r x + coloredTransversePart d r x) y z := by
        rw [coloredRootPart_add_transversePart]
      _ = _ := by simp only [map_add, LinearMap.add_apply, hz, add_zero]
  have hy : T (coloredRootPart d r x) y z = T (coloredRootPart d r x) (coloredRootPart d r y) z := by
    calc
      _ = T (coloredRootPart d r x) (coloredRootPart d r y + coloredTransversePart d r y) z := by
        rw [coloredRootPart_add_transversePart]
      _ = _ := by
        rw [map_add, LinearMap.add_apply, hs (coloredRootPart d r x) (coloredTransversePart d r y) z, hz]
        simp
  have hw : T (coloredRootPart d r x) (coloredRootPart d r y) z =
      T (coloredRootPart d r x) (coloredRootPart d r y) (coloredRootPart d r z) := by
    calc
      _ = T (coloredRootPart d r x) (coloredRootPart d r y)
          (coloredRootPart d r z + coloredTransversePart d r z) := by rw [coloredRootPart_add_transversePart]
      _ = _ := by
        rw [map_add, hsyz (coloredRootPart d r x) (coloredRootPart d r y) (coloredTransversePart d r z),
          hs (coloredRootPart d r x) (coloredTransversePart d r z) (coloredRootPart d r y), hz]
        simp
  exact hx.trans (hy.trans hw)

end ColoredTensorKernel

def coloredPermutationLinear (d r : ℕ) (p : Equiv.Perm (Fin d)) :
    ColoredSpace d r →L[ℝ] ColoredSpace d r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x q => x (q.1, p q.2)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem coloredPermutationLinear_apply (d r : ℕ) (p : Equiv.Perm (Fin d))
    (x : ColoredSpace d r) (a : Fin r) (j : Fin d) :
    coloredPermutationLinear d r p x (a, j) = x (a, p j) := rfl

theorem coloredPermutationLinear_rootPart (d r : ℕ) (p : Equiv.Perm (Fin d)) (x : ColoredSpace d r) :
    coloredPermutationLinear d r p (coloredRootPart d r x) = coloredRootPart d r x := by
  ext ⟨a, j⟩
  rfl

theorem coloredPermutationLinear_block_coordinate (d r : ℕ) (p : Equiv.Perm (Fin d))
    (a : Fin r) (i : Fin d) :
    coloredPermutationLinear d r p (coloredBlock d r a (starCoordinateVector i)) =
      coloredBlock d r a (starCoordinateVector (p.symm i)) := by
  ext ⟨b, j⟩
  simp only [coloredPermutationLinear_apply, coloredBlock_apply, starCoordinateVector,
    p.apply_eq_iff_eq_symm_apply]

theorem colored_derivative_rootPart_centered_eq_zero (d r : ℕ) (hd : 0 < d)
    (L : ColoredSpace d r → ℝ) (hL : Differentiable ℝ L)
    (hperm : ∀ p : Equiv.Perm (Fin d), ∀ x, L (fun q => x (q.1, p q.2)) = L x)
    (x u : ColoredSpace d r) (hu : ∀ a, ∑ j, u (a, j) = 0) :
    fderiv ℝ L (coloredRootPart d r x) u = 0 := by
  let R := coloredRootPart d r x
  have hD (p : Equiv.Perm (Fin d)) :
      (fderiv ℝ L R).comp (coloredPermutationLinear d r p) = fderiv ℝ L R := by
    have heq : L ∘ coloredPermutationLinear d r p = L := by funext y; exact hperm p y
    have h := (hL (coloredPermutationLinear d r p R)).hasFDerivAt.comp R
      (coloredPermutationLinear d r p).hasFDerivAt
    have hfix : coloredPermutationLinear d r p R = R := coloredPermutationLinear_rootPart d r p x
    rw [heq, hfix] at h
    exact h.unique (hL R).hasFDerivAt
  let i₀ : Fin d := ⟨0, hd⟩
  have hcoef (a : Fin r) (i : Fin d) :
      fderiv ℝ L R (coloredBlock d r a (starCoordinateVector i)) =
        fderiv ℝ L R (coloredBlock d r a (starCoordinateVector i₀)) := by
    have h := congrArg (fun A : ColoredSpace d r →L[ℝ] ℝ =>
      A (coloredBlock d r a (starCoordinateVector i))) (hD (Equiv.swap i i₀))
    simp only [ContinuousLinearMap.comp_apply, coloredPermutationLinear_block_coordinate,
      Equiv.symm_swap, Equiv.swap_apply_left] at h
    exact h.symm
  have hreconstruct : u = ∑ a : Fin r, ∑ i : Fin d, u (a, i) • coloredBlock d r a (starCoordinateVector i) := by
    ext ⟨b, j⟩
    simp [Finset.sum_apply, coloredBlock_apply, starCoordinateVector, mul_ite]
  change fderiv ℝ L R u = 0
  rw [hreconstruct, map_sum]
  simp_rw [map_sum, map_smul, smul_eq_mul, hcoef, ← Finset.sum_mul, hu, zero_mul]
  exact Finset.sum_const_zero

section ColoredSmoothRigidity
variable {d r : ℕ}

set_option maxHeartbeats 1000000 in
theorem colored_third_mixed_zero_of_hessian_mixed_zero
    (L : ColoredSpace d r → ℝ) (hL : ContDiff ℝ 3 L)
    (hH : ∀ x i u v,
      fderiv ℝ (fderiv ℝ L) x (u - coloredPlaneProjection d r i u)
        (coloredPlaneProjection d r i v) = 0)
    (x : ColoredSpace d r) (i : Fin d) (u v w : ColoredSpace d r) :
    thirdFDeriv L x (u - coloredPlaneProjection d r i u) (coloredPlaneProjection d r i v) w = 0 := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ L) := hL.fderiv_right (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ (fderiv ℝ L)) :=
    (h1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  let a := u - coloredPlaneProjection d r i u
  let b := coloredPlaneProjection d r i v
  have heq : (fun y => fderiv ℝ (fderiv ℝ L) y a b) = (fun _ => (0 : ℝ)) := by
    funext y
    exact hH y i u v
  have h : HasFDerivAt (fun y => fderiv ℝ (fderiv ℝ L) y a b)
      (((thirdFDeriv L x).flip a).flip b) x :=
    hasFDerivAt_evaluate_const (hasFDerivAt_evaluate_const (h2 x).hasFDerivAt a) b
  rw [heq] at h
  have hz := congrArg (fun A : ColoredSpace d r →L[ℝ] ℝ => A w)
    (h.unique (hasFDerivAt_const (0 : ℝ) x))
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply] at hz
  change thirdDifferential L x a b w = 0
  rw [← thirdDifferential_swap_last L hL x a w b,
    ← thirdDifferential_swap_first L hL x w a b]
  exact hz

theorem colored_thirdFDeriv_root_only (hd : 3 ≤ d)
    (L : ColoredSpace d r → ℝ) (hL : ContDiff ℝ 3 L)
    (hH : ∀ x i u v,
      fderiv ℝ (fderiv ℝ L) x (u - coloredPlaneProjection d r i u)
        (coloredPlaneProjection d r i v) = 0)
    (x u v w : ColoredSpace d r) :
    thirdFDeriv L x u v w = thirdFDeriv L x
      (coloredRootPart d r u) (coloredRootPart d r v) (coloredRootPart d r w) := by
  apply colored_mixed_third_derivative_kernel d r hd (trilinearOfContinuous (thirdFDeriv L x))
  · exact thirdDifferential_swap_first L hL x
  · exact colored_third_mixed_zero_of_hessian_mixed_zero L hL hH x
  · exact thirdDifferential_swap_last L hL x

theorem colored_transverse_hessian_constant (hd : 3 ≤ d)
    (L : ColoredSpace d r → ℝ) (hL : ContDiff ℝ 3 L)
    (hH : ∀ x i u v,
      fderiv ℝ (fderiv ℝ L) x (u - coloredPlaneProjection d r i u)
        (coloredPlaneProjection d r i v) = 0)
    (u v : ColoredSpace d r) (hu : ∀ a, ∑ j, u (a, j) = 0) (x : ColoredSpace d r) :
    fderiv ℝ (fderiv ℝ L) x u v = fderiv ℝ (fderiv ℝ L) 0 u v := by
  apply hessian_coefficient_constant_of_third_zero L hL u v _ x
  intro y w
  rw [colored_thirdFDeriv_root_only hd L hL hH, coloredRootPart_of_centered d r u hu]
  simp

/-- Genuine colored root-plus-constant-quadratic shape, retaining all
cross-channel Hessian coefficients until the actual covariance/IBP step. -/
theorem colored_logDensity_root_plus_constant_quadratic (hd : 3 ≤ d)
    (L : ColoredSpace d r → ℝ) (hL : ContDiff ℝ 3 L)
    (hH : ∀ x i u v,
      fderiv ℝ (fderiv ℝ L) x (u - coloredPlaneProjection d r i u)
        (coloredPlaneProjection d r i v) = 0)
    (hperm : ∀ p : Equiv.Perm (Fin d), ∀ x, L (fun q => x (q.1, p q.2)) = L x)
    (x : ColoredSpace d r) :
    L x = L (coloredRootPart d r x) +
      fderiv ℝ (fderiv ℝ L) 0 (coloredTransversePart d r x) (coloredTransversePart d r x) / 2 := by
  let R := coloredRootPart d r x
  let U := coloredTransversePart d r x
  have hu (a : Fin r) : ∑ j, U (a, j) = 0 := sum_coloredTransversePart d r (by omega) x a
  have hquad := quadratic_along_of_hessian_constant L (hL.of_le (by decide)) R U
    (fderiv ℝ (fderiv ℝ L) 0 U U)
    (fun y => colored_transverse_hessian_constant hd L hL hH U U hu y)
  have hgrad : fderiv ℝ L R U = 0 :=
    colored_derivative_rootPart_centered_eq_zero d r (by omega) L
      (hL.differentiable (by norm_num)) hperm x U hu
  rw [hgrad, add_zero] at hquad
  simpa only [R, U, coloredRootPart_add_transversePart] using hquad

end ColoredSmoothRigidity

theorem heatKernel_colored_permutation (d r : ℕ) (p : Equiv.Perm (Fin d))
    (t : ℝ) (x : ColoredSpace d r) :
    heatKernel t (fun q : Fin r × Fin d => x (q.1, p q.2)) = heatKernel t x := by
  exact Equiv.prod_comp (Equiv.prodCongr (Equiv.refl (Fin r)) p)
    (fun q => ProbabilityTheory.gaussianPDFReal 0 (heatVariance t) (x q))

theorem heatDensity_colored_permutation_of_law (d r : ℕ)
    (μ : MeasureTheory.Measure (ColoredSpace d r)) (p : Equiv.Perm (Fin d))
    (hperm : MeasureTheory.Measure.map (fun x : ColoredSpace d r => fun q => x (q.1, p q.2)) μ = μ)
    (t : ℝ) (x : ColoredSpace d r) :
    heatDensity μ t (fun q => x (q.1, p q.2)) = heatDensity μ t x := by
  let P : ColoredSpace d r → ColoredSpace d r := fun y q => y (q.1, p q.2)
  have hP : Measurable P := (coloredPermutationLinear d r p).continuous.measurable
  calc
    _ = heatDensity (MeasureTheory.Measure.map P μ) t (P x) := by rw [hperm]
    _ = ∫ y, heatKernel t (P x - P y) ∂μ := by
      have hf : MeasureTheory.AEStronglyMeasurable (fun y : ColoredSpace d r => heatKernel t (P x - y))
          (MeasureTheory.Measure.map P μ) :=
        (((continuous_heatKernel t).comp (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
      exact MeasureTheory.integral_map hP.aemeasurable hf
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with y
      exact heatKernel_colored_permutation d r p t (x - y)

/-- Whole-edge score equality yields the genuine multichannel log shape,
with every cross-channel quadratic entry retained. No shape or mixed-Hessian
condition is an assumption. -/
theorem colored_log_heatDensity_root_plus_constant_quadratic_of_fisherDefect_zero
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : MeasureTheory.Measure (ColoredSpace d r)) [MeasureTheory.IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, MeasureTheory.Measure.map (edgeFlipLinear r)
      (MeasureTheory.Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        MeasureTheory.Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ)
    (hzero : heatFrameFisherDefect μ (coloredStarEdgeProjection d r c) t = 0)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      MeasureTheory.Measure.map (fun x : ColoredSpace d r => fun q => x (q.1, p q.2)) μ = μ)
    (x : ColoredSpace d r) :
    let L := fun y => Real.log (heatDensity μ t y)
    L x = L (coloredRootPart d r x) +
      fderiv ℝ (fderiv ℝ L) 0 (coloredTransversePart d r x) (coloredTransversePart d r x) / 2 := by
  apply colored_logDensity_root_plus_constant_quadratic hd _ (contDiff_three_log_heatDensity μ ht)
  · intro y i u v
    have h := colored_star_log_heatDensity_hessian_mixed_of_fisherDefect_zero d r hd c hbulk μ ht hrev hzero y i u v
    dsimp only at h
    have hc := (bulk_rho_lower d hd c hbulk).1
    rw [← coloredPlaneProjection_eq_transpose_mulVec d r (by omega) c hc i u,
      ← coloredPlaneProjection_eq_transpose_mulVec d r (by omega) c hc i v] at h
    exact h
  · intro p y
    exact congrArg Real.log (heatDensity_colored_permutation_of_law d r μ p (hperm p) t y)

/-- Every genuinely transverse direction, including arbitrary mixtures of
channel and spatial directions, has the Gaussian Stein score. Identity
covariance determines the full constant quadratic operator by actual IBP. -/
theorem colored_heatDirectionalScore_of_fisherDefect_zero
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : MeasureTheory.Measure (ColoredSpace d r)) [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : MeasureTheory.Integrable (squareRadius (I := Fin r × Fin d)) μ)
    (hmom : HasIdentitySecondMoments μ) {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, MeasureTheory.Measure.map (edgeFlipLinear r)
      (MeasureTheory.Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        MeasureTheory.Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ)
    (hzero : heatFrameFisherDefect μ (coloredStarEdgeProjection d r c) t = 0)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      MeasureTheory.Measure.map (fun x : ColoredSpace d r => fun q => x (q.1, p q.2)) μ = μ)
    (w : ColoredSpace d r) (hw : ∀ a, ∑ j, w (a, j) = 0) :
    ∀ x, heatDirectionalScore μ t w x = -(1 / (1 + 2 * t)) * finiteLinearForm w x := by
  let L := fun y : ColoredSpace d r => Real.log (heatDensity μ t y)
  let B := fderiv ℝ (fderiv ℝ L) 0
  have hB : ∀ u v, B u v = B v u :=
    (contDiff_three_log_heatDensity μ ht).contDiffAt.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
  have hshape : ∀ x, Real.log (heatDensity μ t x) =
      Real.log (heatDensity μ t (coloredRootPart d r x)) +
        B (x - coloredRootPart d r x) (x - coloredRootPart d r x) / 2 := by
    intro x
    simpa only [B, L, coloredTransversePart, LinearMap.sub_apply, LinearMap.id_apply] using
      colored_log_heatDensity_root_plus_constant_quadratic_of_fisherDefect_zero
        d r hd c hbulk μ ht hrev hzero hperm x
  exact heatDirectionalScore_gaussian_of_bilinear_quadratic_logshape μ hμ hmom ht
    (coloredRootPart d r) B hB hshape w (coloredRootPart_of_centered d r w hw)

end GaussianWave.BS
