import GeneralizedBulk.Graph.GaussianSampleLaws
import GeneralizedBulk.Entropy.GaussianMixtureJacobian
import GeneralizedBulk.Entropy.GaussianMixtureCovarianceEntropy

/-! Entropy transport from canonical flattened observations to actual
physical coordinate factors and an equivalent finite sampling law. -/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Covariance GeneralizedBulk.Graph.Configuration

def coloredCoordinateSelection {k L N : ℕ} (v : Fin L → Fin N) : Fin k × Fin L → Fin k × Fin N :=
  fun aj => (aj.1,v aj.2)

theorem coloredCoordinateSelection_injective {k L N : ℕ} (v : Fin L → Fin N) (hv : Function.Injective v) :
    Function.Injective (coloredCoordinateSelection (k := k) v) := by
  intro a b h
  change (a.1,v a.2)=(b.1,v b.2) at h
  have h1 : a.1=b.1 := congrArg (fun z : Fin k × Fin N => z.1) h
  have h2 : v a.2=v b.2 := congrArg (fun z : Fin k × Fin N => z.2) h
  exact Prod.ext h1 (hv h2)

theorem gaussianMixturePDF_uniform_reindex {S : Type*} [Fintype S] {I : Type*} [Fintype I] [DecidableEq I]
    (e : S ≃ S) (mean : S → I → ℝ) (A : S → Matrix I I ℝ) :
    gaussianMixturePDF (uniformSampleWeight S) (mean ∘ e) (A ∘ e)=
      gaussianMixturePDF (uniformSampleWeight S) mean A := by
  funext x
  exact e.sum_comp (fun s => (Fintype.card S : ℝ)⁻¹*affineGaussianPDF (mean s) (A s) x)

theorem selectedGaussian_entropy_physical_coordinates
    {S J : Type*} [Fintype S] [Nonempty S] [Fintype J] {k L N : ℕ}
    (A : Matrix (Fin k × Fin N) J ℝ) (mean : Fin k × Fin N → ℝ)
    (canonical physical : S → Fin L → Fin N) (sampleEquiv : S ≃ S)
    (hselect : ∀ s,canonical s=physical (sampleEquiv s))
    (C : S → Matrix (Fin (k*L)) (Fin (k*L)) ℝ)
    (F : S → Matrix (Fin k × Fin L) (Fin k × Fin L) ℝ)
    (hC : ∀ s,(C s).det ≠ 0) (hF : ∀ s,(F s).det ≠ 0)
    (hCGram : ∀ s,C s*(C s).transpose=(A*A.transpose).submatrix (flatSelection (canonical s)) (flatSelection (canonical s)))
    (hFGram : ∀ s,F s*(F s).transpose=(A*A.transpose).submatrix
      (coloredCoordinateSelection (physical s)) (coloredCoordinateSelection (physical s))) :
    differentialEntropy (gaussianMixturePDF (uniformSampleWeight S)
      (fun s => mean ∘ flatSelection (canonical s)) C)=
      differentialEntropy (gaussianMixturePDF (uniformSampleWeight S)
        (fun s => mean ∘ coloredCoordinateSelection (physical s)) F) := by
  let e : (Fin k × Fin L) ≃ Fin (k*L) := finProdFinEquiv
  let FG := fun s : S => (F (sampleEquiv s)).submatrix e.symm e.symm
  have hFG (s : S) : (FG s).det ≠ 0 := by
    dsimp [FG]
    rw [Matrix.det_submatrix_equiv_self]
    exact hF (sampleEquiv s)
  have hcov (s : S) : C s*(C s).transpose=FG s*(FG s).transpose := by
    dsimp [FG]
    rw [Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv,hFGram,hCGram,hselect s]
    rfl
  rw [gaussianMixture_entropy_eq_of_covariance _ _ C FG (uniformSampleWeight_nonneg S)
    (uniformSampleWeight_sum S) hC hFG hcov]
  have hm : (fun s => mean ∘ flatSelection (canonical s))=
      (fun s j => (mean ∘ coloredCoordinateSelection (physical s)) (e.symm j)) ∘ sampleEquiv := by
    funext s j
    rw [hselect s]
    rfl
  rw [hm]
  change differentialEntropy (gaussianMixturePDF (uniformSampleWeight S)
    ((fun s j => (mean ∘ coloredCoordinateSelection (physical s)) (e.symm j)) ∘ sampleEquiv)
    ((fun s => (F s).submatrix e.symm e.symm) ∘ sampleEquiv))= _
  rw [gaussianMixturePDF_uniform_reindex sampleEquiv]
  exact gaussianMixture_entropy_coordinate e _ _ F

end GeneralizedBulk.Entropy
