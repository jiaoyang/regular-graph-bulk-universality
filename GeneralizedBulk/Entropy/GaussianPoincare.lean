import GeneralizedBulk.Entropy.GaussianSobolevStein
import GeneralizedBulk.Entropy.HermiteCreationLp

/-! Sharp Gaussian Poincaré for actual bounded C¹ finite-dimensional profiles,
proved from bounded Gaussian integration by parts and true chaos Parseval. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable {I : Type*} [Fintype I] [DecidableEq I]

def boundedGaussianLp (f : (I → ℝ) → ℝ) (hf : Continuous f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    Lp ℝ 2 (standardGaussian I) :=
  MemLp.toLp f (MemLp.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall hM))

theorem boundedGaussianLp_ae (f : (I → ℝ) → ℝ) (hf : Continuous f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    (boundedGaussianLp f hf M hM : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] f :=
  MemLp.coeFn_toLp _

theorem inner_multiLp_of_ae (F : Lp ℝ 2 (standardGaussian I)) (f : (I → ℝ) → ℝ)
    (hf : (F : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] f) (a : I → ℕ) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ F (multiLp I a) =
      ∫ x, f x * multiHermite I a x ∂standardGaussian I := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf, multiLp_ae I a] with x hx ha
  simp only [hx, ha, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Actual weak Gaussian lowering determines the degree components of the
actual derivative vector. -/
theorem component_derivative_of_adjoint (F G : Lp ℝ 2 (standardGaussian I)) (i : I)
    (hadj : ∀ a : I → ℕ, @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ G (multiLp I a) =
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ F (multiLp I (upper a i))) (n : ℕ) :
    chaosDerivativeLp (degreeIndexNat I) (fullChaosCoordinates I (n + 1) (chaosComponent I F (n + 1))) i =
      (chaosComponent I G n : Lp ℝ 2 (standardGaussian I)) := by
  let coeff := fullChaosCoordinates I (n + 1) (chaosComponent I F (n + 1))
  have hmem := chaosDerivativeLp_mem_fullChaos_succ (degreeIndexNat I) coeff n (degreeIndexNat_sum I) i
  have heq := fullChaosCoordinates_spec I (n + 1) (chaosComponent I F (n + 1))
  change chaosLp (degreeIndexNat I) coeff = (chaosComponent I F (n + 1) : Lp ℝ 2 (standardGaussian I)) at heq
  have hEq : (⟨chaosDerivativeLp (degreeIndexNat I) coeff i, hmem⟩ : fullChaosSpace I n) = chaosComponent I G n := by
    apply fullChaos_eq_of_basis_inner_eq n
    intro a
    change @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (chaosDerivativeLp (degreeIndexNat I) coeff i)
      (multiLp I (degreeIndexNat I a)) = _
    rw [chaosDerivativeLp_inner_multiLp, heq]
    have hu : (∑ j, upper (degreeIndexNat I a) i j) = n + 1 := by rw [upper_degree, degreeIndexNat_sum]
    rw [chaosComponent_inner I (n + 1) F ⟨multiLp I (upper (degreeIndexNat I a) i), multiLp_mem_fullChaosSpace I _ _ hu⟩,
      ← hadj]
    exact (chaosComponent_inner I n G ⟨multiLp I (degreeIndexNat I a), multiLp_mem_fullChaosSpace I _ _ (degreeIndexNat_sum I a)⟩).symm
  exact congrArg (fun g : fullChaosSpace I n => (g : Lp ℝ 2 (standardGaussian I))) hEq

/-- The exact spectral Gaussian Poincaré implication. Its coefficient
adjoint condition is subsequently proved for actual bounded C¹ functions. -/
theorem norm_sq_le_sum_derivative_norm_sq (F : Lp ℝ 2 (standardGaussian I))
    (G : I → Lp ℝ 2 (standardGaussian I))
    (hcenter : (∫ x, F x ∂standardGaussian I) = 0)
    (hadj : ∀ i a, @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (G i) (multiLp I a) =
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ F (multiLp I (upper a i))) :
    ‖F‖ ^ 2 ≤ ∑ i, ‖G i‖ ^ 2 := by
  have henergy (n : ℕ) : ((n + 1 : ℕ) : ℝ) * ‖chaosComponent I F (n + 1)‖ ^ 2 =
      ∑ i, ‖chaosComponent I (G i) n‖ ^ 2 := by
    have hh := chaos_derivative_energy (degreeIndexNat I) (degreeIndexNat_injective I (n + 1))
      (fullChaosCoordinates I (n + 1) (chaosComponent I F (n + 1))) (n + 1) (degreeIndexNat_sum I)
    have heq := fullChaosCoordinates_spec I (n + 1) (chaosComponent I F (n + 1))
    change chaosLp (degreeIndexNat I) (fullChaosCoordinates I (n + 1) (chaosComponent I F (n + 1))) =
      (chaosComponent I F (n + 1) : Lp ℝ 2 (standardGaussian I)) at heq
    rw [heq] at hh
    simp_rw [component_derivative_of_adjoint F (G _) _ (hadj _) n] at hh
    exact hh.symm
  have hsG : HasSum (fun n : ℕ => ∑ i, ‖chaosComponent I (G i) n‖ ^ 2) (∑ i, ‖G i‖ ^ 2) :=
    hasSum_sum (fun i _ => hasSum_chaosComponent_norm_sq I (G i))
  have hsWeighted : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖chaosComponent I F (n + 1)‖ ^ 2)
      (∑ i, ‖G i‖ ^ 2) := by
    convert hsG using 1
    funext n
    exact henergy n
  have hsTail : HasSum (fun n : ℕ => ‖chaosComponent I F (n + 1)‖ ^ 2) (‖F‖ ^ 2) := by
    have hh := (hasSum_nat_add_iff' 1).mpr (hasSum_chaosComponent_norm_sq I F)
    simpa only [Finset.sum_range_one, chaosComponent_zero_of_integral_zero I F hcenter, norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using hh
  apply hasSum_le _ hsTail hsWeighted
  intro n
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (sq_nonneg ‖chaosComponent I F (n + 1)‖)

/-- Sharp Poincaré for an actual centered bounded C¹ Gaussian profile. -/
theorem gaussian_poincare_centered (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) (L : I → ℝ)
    (hL : ∀ i x, |coordinateGradient f i x| ≤ L i)
    (hcenter : (∫ x, f x ∂standardGaussian I) = 0) :
    (∫ x, f x ^ 2 ∂standardGaussian I) ≤
      ∫ x, ∑ i, coordinateGradient f i x ^ 2 ∂standardGaussian I := by
  let F := boundedGaussianLp f hf.continuous M hM
  let G := fun i => boundedGaussianLp (coordinateGradient f i) (continuous_coordinateGradient f hf i) (L i) (hL i)
  have hF := boundedGaussianLp_ae f hf.continuous M hM
  have hG (i : I) := boundedGaussianLp_ae (coordinateGradient f i) (continuous_coordinateGradient f hf i) (L i) (hL i)
  have hcent : (∫ x, F x ∂standardGaussian I) = 0 := (integral_congr_ae hF).trans hcenter
  have hadj (i : I) (a : I → ℕ) : @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (G i) (multiLp I a) =
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ F (multiLp I (upper a i)) := by
    rw [inner_multiLp_of_ae _ _ (hG i), inner_multiLp_of_ae _ _ hF]
    exact coordinate_creation_adjoint_bounded f hf i M (L i) hM (hL i) a
  have hbound := norm_sq_le_sum_derivative_norm_sq F G hcent hadj
  have hFnorm : ‖F‖ ^ 2 = ∫ x, f x ^ 2 ∂standardGaussian I := by
    rw [← integral_sq_real_Lp]
    exact integral_congr_ae (hF.mono (fun x hx => congrArg (fun r : ℝ => r ^ 2) hx))
  have hGnorm (i : I) : ‖G i‖ ^ 2 = ∫ x, coordinateGradient f i x ^ 2 ∂standardGaussian I := by
    rw [← integral_sq_real_Lp]
    exact integral_congr_ae ((hG i).mono (fun x hx => congrArg (fun r : ℝ => r ^ 2) hx))
  have hGi (i : I) : Integrable (fun x => coordinateGradient f i x ^ 2) (standardGaussian I) :=
    ((memLp_congr_ae (hG i)).mp (Lp.memLp _)).integrable_sq
  rw [hFnorm] at hbound
  simp_rw [hGnorm] at hbound
  rw [integral_finset_sum _ (fun i _ => hGi i)]
  exact hbound

/-- The actual bounded C¹ Gaussian-profile Poincaré inequality. The gradient
uses literal coordinate Fréchet derivatives in finite Pi coordinates. -/
theorem gaussian_poincare_bounded_C1 (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) (L : I → ℝ)
    (hL : ∀ i x, |coordinateGradient f i x| ≤ L i) :
    (∫ x, (f x - ∫ y, f y ∂standardGaussian I) ^ 2 ∂standardGaussian I) ≤
      ∫ x, ∑ i, coordinateGradient f i x ^ 2 ∂standardGaussian I := by
  let m := ∫ y, f y ∂standardGaussian I
  let g := fun x => f x - m
  have hg : ContDiff ℝ 1 g := hf.sub contDiff_const
  have hgb (x) : |g x| ≤ M + |m| := (abs_sub _ _).trans (add_le_add_right (hM x) _)
  have hgrad (i : I) (x : I → ℝ) : coordinateGradient g i x = coordinateGradient f i x := by
    dsimp only [coordinateGradient, g]
    rw [fderiv_sub_const]
  have hgl (i : I) (x : I → ℝ) : |coordinateGradient g i x| ≤ L i := by rw [hgrad]; exact hL i x
  have hfi : Integrable f (standardGaussian I) :=
    (MemLp.of_bound (p := (2 : ENNReal)) hf.continuous.aestronglyMeasurable M (Filter.Eventually.of_forall hM)).integrable (by norm_num)
  have hcenter : (∫ x, g x ∂standardGaussian I) = 0 := by
    rw [show g = fun x => f x - m from rfl, integral_sub hfi (integrable_const m)]
    simp only [integral_const, measureReal_univ_eq_one, one_smul, m, sub_self]
  have hh := gaussian_poincare_centered g hg (M + |m|) hgb L hgl hcenter
  simpa only [g, hgrad] using hh

end GeneralizedBulk.Entropy.Hermite
