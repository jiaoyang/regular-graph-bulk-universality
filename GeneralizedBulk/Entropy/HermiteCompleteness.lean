import GeneralizedBulk.Entropy.HermiteFourier
import GeneralizedBulk.Analysis.FourierDensity

/-! Completeness of actual finite-dimensional Gaussian Hermite chaos. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable (I : Type*) [Fintype I] [DecidableEq I]

/-- Orthogonality to all actual Gaussian Hermites forces a true L² vector to
vanish. Fourier uniqueness and exponential domination supply completeness. -/
theorem eq_zero_of_hermiteOrthogonal (f : Lp ℝ 2 (standardGaussian I)) (hf : HermiteOrthogonal f) : f = 0 := by
  have hfi : Integrable (f : (I → ℝ) → ℝ) (standardGaussian I) :=
    (Lp.memLp f).integrable (by norm_num)
  have hae := GeneralizedBulk.Analysis.ae_zero_of_fourier_density_zero (standardGaussian I)
    (f : (I → ℝ) → ℝ) hfi (hermiteOrthogonal_fourier_zero f hf)
  apply Lp.ext
  filter_upwards [hae, Lp.coeFn_zero ℝ 2 (standardGaussian I)] with x hx h0
  exact hx.trans h0.symm

theorem hermite_span_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range (multiLp I)))ᗮ = ⊥ := by
  apply bot_unique
  intro f hf
  change f = 0
  apply eq_zero_of_hermiteOrthogonal I f
  intro a
  have ha : multiLp I a ∈ Submodule.span ℝ (Set.range (multiLp I)) := Submodule.subset_span ⟨a, rfl⟩
  exact Submodule.inner_left_of_mem_orthogonal ha hf

/-- All actual Hermite polynomials have dense span in Gaussian L². -/
theorem dense_hermite_span :
    (Submodule.span ℝ (Set.range (multiLp I))).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, hermite_span_orthogonal_eq_bot,
    Submodule.bot_orthogonal_eq_top]

/-- The genuine homogeneous Gaussian chaos spaces form an orthogonal family. -/
theorem fullChaos_orthogonalFamily : OrthogonalFamily ℝ (fun n : ℕ => fullChaosSpace I n)
    (fun n => (fullChaosSpace I n).subtypeₗᵢ) := by
  intro n m hnm x y
  change @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (x : Lp ℝ 2 (standardGaussian I)) (y : Lp ℝ 2 (standardGaussian I)) = 0
  rw [real_inner_comm]
  exact fullChaosSpace_orthogonal I n m hnm x.property y y.property

/-- Density is proved from Hermite Fourier completeness, rather than supplied
as an assumption to an abstract chaos decomposition. -/
theorem fullChaos_total : ⊤ ≤ (⨆ n : ℕ, fullChaosSpace I n).topologicalClosure := by
  have hs : Submodule.span ℝ (Set.range (multiLp I)) ≤ ⨆ n : ℕ, fullChaosSpace I n := by
    apply Submodule.span_le.mpr
    rintro f ⟨a, rfl⟩
    exact (le_iSup (fullChaosSpace I) (∑ i, a i))
      (multiLp_mem_fullChaosSpace I _ a rfl)
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_hermite_span I] at hc
  exact hc

/-- The actual full infinite orthogonal chaos decomposition. -/
def fullChaosHilbertSum : IsHilbertSum ℝ (fun n : ℕ => fullChaosSpace I n)
    (fun n => (fullChaosSpace I n).subtypeₗᵢ) :=
  IsHilbertSum.mkInternal (fullChaosSpace I) (fullChaos_orthogonalFamily I) (fullChaos_total I)

def fullChaosRepresentation : Lp ℝ 2 (standardGaussian I) ≃ₗᵢ[ℝ]
    lp (fun n : ℕ => fullChaosSpace I n) 2 :=
  (fullChaosHilbertSum I).linearIsometryEquiv

/-- The actual component in each degree, with its inherited Gaussian L² norm. -/
def chaosComponent (f : Lp ℝ 2 (standardGaussian I)) (n : ℕ) : fullChaosSpace I n :=
  fullChaosRepresentation I f n

theorem hasSum_chaosComponents (f : Lp ℝ 2 (standardGaussian I)) :
    HasSum (fun n : ℕ => (chaosComponent I f n : Lp ℝ 2 (standardGaussian I))) f := by
  have h := (fullChaosHilbertSum I).hasSum_linearIsometryEquiv_symm ((fullChaosRepresentation I) f)
  change HasSum (fun n : ℕ => (chaosComponent I f n : Lp ℝ 2 (standardGaussian I)))
    ((fullChaosRepresentation I).symm (fullChaosRepresentation I f)) at h
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h

/-- Parseval, with convergence of the nonnegative true degree energies. -/
theorem hasSum_chaosComponent_norm_sq (f : Lp ℝ 2 (standardGaussian I)) :
    HasSum (fun n : ℕ => ‖chaosComponent I f n‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (fullChaosRepresentation I f)
  change HasSum (fun n : ℕ => ‖chaosComponent I f n‖ ^ (2 : ℝ)) (‖fullChaosRepresentation I f‖ ^ (2 : ℝ)) at h
  simpa only [Real.rpow_two, (fullChaosRepresentation I).norm_map] using h

end GeneralizedBulk.Entropy.Hermite
