import GeneralizedBulk.Entropy.FiltrationLp
import GeneralizedBulk.Entropy.GaussianCondExp

/-! Orthogonal basis changes preserve actual homogeneous Gaussian chaoses. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem standardGaussian_matrixAction_measurePreserving (O : Matrix I I ℝ)
    (hO : O * O.transpose = 1) :
    MeasurePreserving (fun x : I → ℝ => O.mulVec x) (standardGaussian I) (standardGaussian I) := by
  have h := GeneralizedBulk.Gaussian.standardVector_orthogonal_measurePreserving O (by
    convert hO using 1
    ext i j
    by_cases hij : i = j
    · simp only [Matrix.one_apply, hij, ↓reduceIte]
    · simp only [Matrix.one_apply, hij, ↓reduceIte])
  simpa only [standardGaussian, GeneralizedBulk.Gaussian.standardVector] using h

/-- The actual Gaussian unitary pullback under an orthogonal coordinate map. -/
def gaussianPullback (O : Matrix I I ℝ) (hO : O * O.transpose = 1) :
    Lp ℝ 2 (standardGaussian I) →ₗᵢ[ℝ] Lp ℝ 2 (standardGaussian I) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => O.mulVec x)
    (standardGaussian_matrixAction_measurePreserving O hO)

theorem gaussianPullback_ae (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (f : Lp ℝ 2 (standardGaussian I)) :
    (gaussianPullback O hO f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] (fun x => f (O.mulVec x)) :=
  Lp.coeFn_compMeasurePreserving f (standardGaussian_matrixAction_measurePreserving O hO)

/-- Triangular polynomial degree is transported through the actual Gaussian
unitary, using concrete finite coefficient expansions of the composed function. -/
theorem gaussianPullback_mem_lpFiltration (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (degree : ℕ) {f : Lp ℝ 2 (standardGaussian I)} (hf : f ∈ lpFiltration I degree) :
    gaussianPullback O hO f ∈ lpFiltration I degree := by
  have hincl : lpFiltration I degree ≤ (lpFiltration I degree).comap (gaussianPullback O hO).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro g ⟨a, rfl⟩
    change gaussianPullback O hO (multiLp I (atMostIndexNat I a)) ∈ lpFiltration I degree
    have hraw := linearSubstitution_mem
      (multiHermite_mem_functionFiltration (atMostIndexNat I a) degree a.property) O
    obtain ⟨coeff, hc⟩ := exists_functionFiltration_coefficients I hraw
    have heq : gaussianPullback O hO (multiLp I (atMostIndexNat I a)) =
        chaosLp (atMostIndexNat I) coeff := by
      apply Lp.ext
      have hae := (standardGaussian_matrixAction_measurePreserving O hO).quasiMeasurePreserving.ae_eq_comp
        (multiLp_ae I (atMostIndexNat I a))
      filter_upwards [gaussianPullback_ae O hO (multiLp I (atMostIndexNat I a)), hae,
        chaosLp_ae (atMostIndexNat I) coeff] with x hp hr hcoeff
      simp only [Function.comp_apply] at hr
      rw [hp, hr, hcoeff]
      exact (congrFun hc x).symm
    rw [heq]
    exact chaosLp_mem_lpFiltration I _ coeff degree (atMostIndexNat_degree I)
  exact hincl hf

/-- Pullback by the transpose is a genuine inverse, including the chosen L²
representatives. The proof uses only two finite almost-everywhere comparisons. -/
theorem gaussianPullback_transpose_inverse (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (f : Lp ℝ 2 (standardGaussian I)) :
    gaussianPullback O hO
      (gaussianPullback O.transpose (by simpa using Matrix.mul_eq_one_comm.mpr hO) f) = f := by
  apply Lp.ext
  have hOt : O.transpose * O.transpose.transpose = 1 := by simpa using Matrix.mul_eq_one_comm.mpr hO
  have hc := (standardGaussian_matrixAction_measurePreserving O hO).quasiMeasurePreserving.ae_eq_comp
    (gaussianPullback_ae O.transpose hOt f)
  filter_upwards [gaussianPullback_ae O hO (gaussianPullback O.transpose hOt f), hc] with x hp hc
  simp only [Function.comp_apply] at hc
  rw [hp, hc]
  have hi : O.transpose.mulVec (O.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_eq_one_comm.mpr hO, Matrix.one_mulVec]
  rw [hi]

/-- Positive Hermite degree is invariant under every actual Gaussian
orthogonal basis change. No degree-preservation premise is assumed. -/
theorem gaussianPullback_mem_fullChaos_pos (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (degree : ℕ) (hdegree : 0 < degree) {f : Lp ℝ 2 (standardGaussian I)}
    (hf : f ∈ fullChaosSpace I degree) : gaussianPullback O hO f ∈ fullChaosSpace I degree := by
  apply (mem_fullChaos_iff_filtration_orthogonal I degree hdegree _).2
  refine ⟨gaussianPullback_mem_lpFiltration O hO degree (fullChaosSpace_le_lpFiltration I degree hf), ?_⟩
  intro g hg
  have hOt : O.transpose * O.transpose.transpose = 1 := by simpa using Matrix.mul_eq_one_comm.mpr hO
  let g' := gaussianPullback O.transpose hOt g
  have hg' : g' ∈ lpFiltration I (degree - 1) := gaussianPullback_mem_lpFiltration O.transpose hOt _ hg
  have hinv : gaussianPullback O hO g' = g := gaussianPullback_transpose_inverse O hO g
  rw [← hinv, (gaussianPullback O hO).inner_map_map]
  exact fullChaos_inner_lowerFiltration_zero I degree (degree - 1) (by omega) f hf g' hg'

/-- Orthogonal transport preserves every homogeneous degree, with the constant
chaos handled separately rather than through a false degree-zero positivity claim. -/
theorem gaussianPullback_mem_fullChaos (O : Matrix I I ℝ) (hO : O * O.transpose = 1)
    (degree : ℕ) {f : Lp ℝ 2 (standardGaussian I)} (hf : f ∈ fullChaosSpace I degree) :
    gaussianPullback O hO f ∈ fullChaosSpace I degree := by
  cases degree with
  | zero =>
    rw [← lpFiltration_zero_eq_fullChaos] at hf ⊢
    exact gaussianPullback_mem_lpFiltration O hO 0 hf
  | succ degree => exact gaussianPullback_mem_fullChaos_pos O hO _ (by omega) hf

/-- The actual retained-coordinate Gaussian conditional expectation preserves
every full chaos, using the proved Hermite truncation formula. -/
theorem coordinateConditionalL2_mem_fullChaos (observed : Finset I) (degree : ℕ)
    {f : Lp ℝ 2 (standardGaussian I)} (hf : f ∈ fullChaosSpace I degree) :
    coordinateConditionalL2 observed f ∈ fullChaosSpace I degree := by
  classical
  obtain ⟨coeff, rfl⟩ := hf
  change coordinateConditionalL2 observed (chaosLp (degreeIndexNat I) coeff) ∈ _
  rw [coordinateConditionalL2_chaosLp]
  exact chaosLp_mem_fullChaosSpace I degree (degreeIndexNat I)
    (degreeIndexNat_sum I) _

end GeneralizedBulk.Entropy.Hermite
