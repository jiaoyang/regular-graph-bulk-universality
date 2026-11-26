import GeneralizedBulk.Entropy.GaussianRefresh

/-! Actual coordinate Gaussian integration by parts for bounded C¹ profiles. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
open GeneralizedBulk.Gaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

def coordinateGradient (f : (I → ℝ) → ℝ) (i : I) (x : I → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

theorem continuous_coordinateGradient (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (i : I) :
    Continuous (coordinateGradient f i) :=
  (hf.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const)

theorem hasDerivAt_update (x : I → ℝ) (i : I) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Function.update x i t) (Pi.single i 1) t := by
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self, Pi.single_eq_same] using hasDerivAt_id t
  · simpa only [Function.update_of_ne hji, Pi.single_eq_of_ne hji] using hasDerivAt_const t (x j)

theorem hasDerivAt_coordinate_profile (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (x : I → ℝ) (i : I) (t : ℝ) :
    HasDerivAt (fun t => f (Function.update x i t)) (coordinateGradient f i (Function.update x i t)) t :=
  ((hf.differentiable le_rfl) (Function.update x i t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x i t)

/-- Literal polynomial factorization of the raised Hermite on a coordinate fiber. -/
theorem multiHermite_upper_update_factor (a : I → ℕ) (i : I) (x : I → ℝ) (t : ℝ) :
    multiHermite I (upper a i) (Function.update x i t) = (hermite (a i + 1)).eval t *
      ∏ j ∈ Finset.univ.erase i, (hermite (a j)).eval (x j) := by
  rw [multiHermite_update_factor]
  simp only [upper, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

/-- The actual coordinate creation-adjoint relation for every bounded C¹
profile with bounded coordinate derivative. -/
theorem coordinate_creation_adjoint_bounded (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (i : I) (M L : ℝ) (hM : ∀ x, |f x| ≤ M) (hL : ∀ x, |coordinateGradient f i x| ≤ L)
    (a : I → ℕ) :
    (∫ x, coordinateGradient f i x * multiHermite I a x ∂standardGaussian I) =
      ∫ x, f x * multiHermite I (upper a i) x ∂standardGaussian I := by
  have hG := continuous_coordinateGradient f hf i
  have hleft : Integrable (fun x => coordinateGradient f i x * multiHermite I a x) (standardGaussian I) :=
    (integrable_multiHermite I a).bdd_mul hG.aestronglyMeasurable ⟨L, hL⟩
  have hright : Integrable (fun x => f x * multiHermite I (upper a i) x) (standardGaussian I) :=
    (integrable_multiHermite I (upper a i)).bdd_mul hf.continuous.aestronglyMeasurable ⟨M, hM⟩
  rw [← integral_refresh i _ (hG.mul (continuous_multiHermite I a)) hleft,
    ← integral_refresh i _ (hf.continuous.mul (continuous_multiHermite I (upper a i))) hright]
  apply integral_congr_ae
  filter_upwards with x
  have hupdate : Continuous (fun t : ℝ => Function.update x i t) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_update x i t).continuousAt)
  have hs := gaussian_creation_adjoint_bounded (hermite (a i))
    (fun t => f (Function.update x i t)) (fun t => coordinateGradient f i (Function.update x i t))
    (hasDerivAt_coordinate_profile f hf x i) (hG.comp hupdate) M L
    (fun t => hM _) (fun t => hL _)
  rw [← hermite_succ] at hs
  simp_rw [multiHermite_upper_update_factor, multiHermite_update_factor, ← mul_assoc]
  rw [integral_mul_const, integral_mul_const, hs]

end GeneralizedBulk.Entropy.Hermite
