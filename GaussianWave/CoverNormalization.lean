import GaussianWave.CoverProcess
import GaussianWave.StarNormalization
import GaussianWave.GaussianProduct
import GaussianWave.GaussianContinuity
import GaussianWave.WeakTransport

/-!
# Normalized Gaussian waves on arbitrary fixed finite covering windows

The cover sampler and radial tree geometry are explicit adapters. This module
does not claim to construct the infinite covering probability space. Given
those sampling adapters and only the qualitative BS Gaussian classification,
it proves normalization, independent-channel product structure, and genuine
Wasserstein convergence, using exactly scalar empirical root fourth bounds.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace GaussianWave.CoverSampling
variable {d N k : ℕ} {D : RegularEigenData d N k}
variable {T Ω : Type*} {G : RadialTreeGeometry d T}
variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (S : CoverSampling D G P)

/-- The finite cover-window law of all channels of the spectral family. -/
def eigenWindowLaw {m : ℕ} (site : Fin m → T) : Measure ((Fin k × Fin m) → ℝ) :=
  S.windowLaw id site

instance eigenWindowLaw_isProbability {m : ℕ} (site : Fin m → T) :
    IsProbabilityMeasure (S.eigenWindowLaw site) := by
  unfold eigenWindowLaw
  infer_instance

/-- The own-eigenvalue covariance at the selected physical tree sites. -/
def eigenWindowCovariance (_S : CoverSampling D G P) {m : ℕ} (site : Fin m → T) :
    Matrix (Fin k × Fin m) (Fin k × Fin m) ℝ :=
  fun aj bl => (if aj.1 = bl.1 then 1 else 0) *
    sphericalCovariance d (D.eigenvalue aj.1) (G.distance (site aj.2) (site bl.2))

omit [IsProbabilityMeasure P] in
theorem eigenWindowCovariance_diagonal {m : ℕ} (site : Fin m → T) (i : Fin k × Fin m) :
    S.eigenWindowCovariance site i i = 1 := by
  simp [eigenWindowCovariance, G.distance_self]

omit [IsProbabilityMeasure P] in
theorem eigenWindowLaw_norm_fourth_integrable {m : ℕ} (site : Fin m → T) :
    Integrable (fun z => ‖z‖ ^ 4) (S.eigenWindowLaw site) := by
  let C := ∑ a : Fin k, (N : ℝ) * ∑ v, D.eigenvector a v ^ 4
  apply (integral_pi_norm_fourth_le (S.eigenWindowLaw site)
    (fun aj => S.windowLaw_integrable_coordinate_fourth id site aj) C ?_).1
  intro aj
  rw [eigenWindowLaw, S.windowLaw_coordinate_fourth]
  change (N : ℝ) * ∑ v, D.eigenvector aj.1 v ^ 4 ≤
    ∑ a : Fin k, (N : ℝ) * ∑ v, D.eigenvector a v ^ 4
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun a : Fin k => (N : ℝ) * ∑ v, D.eigenvector a v ^ 4)
    (fun a _ => by positivity) (Finset.mem_univ aj.1)

theorem eigenWindowCovariance_posSemidef (hd : 2 ≤ d) {m : ℕ} (site : Fin m → T) :
    (S.eigenWindowCovariance site).PosSemidef := by
  classical
  apply covariance_posSemidef_of_tendsto (fun _ => S.eigenWindowLaw site)
    (fun _ => S.eigenWindowLaw_norm_fourth_integrable site)
  intro aj bl
  have heq : (∫ z, z aj * z bl ∂S.eigenWindowLaw site) =
      S.eigenWindowCovariance site aj bl :=
    S.windowLaw_exact_covariance hd id Function.injective_id site aj bl
  simp_rw [heq]
  exact tendsto_const_nhds

/-- Actual Gaussian comparison at the channels' own eigenvalues. -/
def eigenWindowGaussian (hd : 2 ≤ d) {m : ℕ} (site : Fin m → T) :
    Measure ((Fin k × Fin m) → ℝ) :=
  gaussianCovarianceLaw (S.eigenWindowCovariance site)
    (S.eigenWindowCovariance_posSemidef hd site)

instance eigenWindowGaussian_isProbability (hd : 2 ≤ d) {m : ℕ} (site : Fin m → T) :
    IsProbabilityMeasure (S.eigenWindowGaussian hd site) := by
  unfold eigenWindowGaussian
  infer_instance

theorem eigenWindowGaussian_coordinate_fourth (hd : 2 ≤ d) {m : ℕ}
    (site : Fin m → T) (i : Fin k × Fin m) :
    (∫ z, z i ^ 4 ∂S.eigenWindowGaussian hd site) = 3 := by
  rw [eigenWindowGaussian, gaussianCovarianceLaw_coordinate_fourth,
    S.eigenWindowCovariance_diagonal]
  norm_num

/-- The normalized finite-window comparison is literally a product of
independent variance-one channel waves at their respective energies. -/
theorem eigenWindowGaussian_product (hd : 2 ≤ d) {m : ℕ} (site : Fin m → T) :
    ∃ hC : ∀ a : Fin k,
        (windowCovariance d (fun i j => G.distance (site i) (site j)) (D.eigenvalue a)).PosSemidef,
      S.eigenWindowGaussian hd site = Measure.map flattenChannels
        (Measure.pi (fun a => gaussianCovarianceLaw
          (windowCovariance d (fun i j => G.distance (site i) (site j)) (D.eigenvalue a)) (hC a))) := by
  classical
  let C : Fin k → Matrix (Fin m) (Fin m) ℝ := fun a =>
    windowCovariance d (fun i j => G.distance (site i) (site j)) (D.eigenvalue a)
  have hC (a : Fin k) : (C a).PosSemidef := by
    have h := (S.eigenWindowCovariance_posSemidef hd site).submatrix (fun j => (a, j))
    simpa [C, eigenWindowCovariance, windowCovariance, Matrix.submatrix] using h
  refine ⟨hC, ?_⟩
  apply gaussian_eq_flattened_product _ C hC
  intro t
  have h := gaussianCovarianceLaw_characteristic (S.eigenWindowCovariance site)
    (S.eigenWindowCovariance_posSemidef hd site) t
  have heq : S.eigenWindowCovariance site = channelBlockCovariance C := by
    ext aj bl
    simp only [eigenWindowCovariance, channelBlockCovariance, C, windowCovariance]
    split_ifs <;> simp
  simpa only [eigenWindowGaussian, heq] using h

end GaussianWave.CoverSampling

namespace GaussianWave

/-- Block covariance at a common limiting energy for a fixed finite window. -/
def jointWindowCovariance {d k m : ℕ} {T : Type*}
    (G : RadialTreeGeometry d T) (site : Fin m → T) (E : ℝ) :
    Matrix (Fin k × Fin m) (Fin k × Fin m) ℝ :=
  fun aj bl => (if aj.1 = bl.1 then 1 else 0) *
    sphericalCovariance d E (G.distance (site aj.2) (site bl.2))

/-- Deterministic sequence-of-good-graphs theorem on every fixed finite
covering window. BS classification leaves covariance unspecified; covariance
normalization, product independence, and the genuine W2 conclusion are proved. -/
theorem eigenvectors_normalizedWindow_wasserstein
    {d k m : ℕ} (hd : 2 ≤ d) (N : ℕ → ℕ)
    (D : ∀ n, RegularEigenData d (N n) k)
    {T : Type*} (G : RadialTreeGeometry d T) (site : Fin m → T)
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (S : ∀ n, CoverSampling (D n) G (P n))
    (E : ℝ) (hE : ∀ i, Tendsto (fun n => (D n).eigenvalue i) atTop (𝓝 E))
    (M : ℝ) (hM : ∀ n i, (N n : ℝ) * ∑ v, (D n).eigenvector i v ^ 4 ≤ M)
    (BS : BSJointClassification (fun n => (S n).eigenWindowLaw site)) :
    Tendsto (fun n => wassersteinTwo ((S n).eigenWindowLaw site)
      ((S n).eigenWindowGaussian hd site)) atTop (𝓝 0) := by
  classical
  let μ := fun n => (S n).eigenWindowLaw site
  let C : Matrix (Fin k × Fin m) (Fin k × Fin m) ℝ := jointWindowCovariance G site E
  have h4 (n : ℕ) (aj : Fin k × Fin m) : Integrable (fun z => z aj ^ 4) (μ n) :=
    (S n).windowLaw_integrable_coordinate_fourth id site aj
  have h4bound (n : ℕ) (aj : Fin k × Fin m) : (∫ z, z aj ^ 4 ∂μ n) ≤ M := by
    change (∫ z, z aj ^ 4 ∂(S n).windowLaw id site) ≤ M
    rw [(S n).windowLaw_coordinate_fourth]
    exact hM n aj.1
  have hsecond (aj bl : Fin k × Fin m) :
      Tendsto (fun n => ∫ z, z aj * z bl ∂μ n) atTop (𝓝 (C aj bl)) := by
    have heq (n : ℕ) : (∫ z, z aj * z bl ∂μ n) =
        (if aj.1 = bl.1 then 1 else 0) * sphericalCovariance d
          ((D n).eigenvalue aj.1) (G.distance (site aj.2) (site bl.2)) :=
      (S n).windowLaw_exact_covariance hd id Function.injective_id site aj bl
    simp_rw [heq]
    exact (((continuous_sphericalCovariance d (G.distance (site aj.2) (site bl.2))).tendsto E).comp
      (hE aj.1)).const_mul _
  obtain ⟨hC, hw⟩ := normalizedGaussian_weakConverges μ h4 M h4bound C hsecond BS
  have hg : WeakLawConverges (fun n => (S n).eigenWindowGaussian hd site)
      (gaussianCovarianceLaw C hC) := by
    apply gaussianCovarianceLaw_weakConverges
    intro aj bl
    exact (((continuous_sphericalCovariance d (G.distance (site aj.2) (site bl.2))).tendsto E).comp
      (hE aj.1)).const_mul _
  have hμ (n : ℕ) := integral_squareMass_sq_le (μ n) (h4 n) M (h4bound n)
  have hν (n : ℕ) := integral_squareMass_sq_le ((S n).eigenWindowGaussian hd site)
    (fun aj => gaussianCovarianceLaw_coordinate_integrable_pow _ _ aj 4) 3
    (fun aj => ((S n).eigenWindowGaussian_coordinate_fourth hd site aj).le)
  exact wassersteinTwo_tendsto_zero_of_common_weak_limit μ
    (fun n => (S n).eigenWindowGaussian hd site) (gaussianCovarianceLaw C hC) hw hg
    (fun n => (hμ n).1) (fun n => (hν n).1)
    (M * (Fintype.card (Fin k × Fin m) : ℝ) ^ 2)
    (3 * (Fintype.card (Fin k × Fin m) : ℝ) ^ 2)
    (fun n => (hμ n).2) (fun n => (hν n).2)

end GaussianWave
