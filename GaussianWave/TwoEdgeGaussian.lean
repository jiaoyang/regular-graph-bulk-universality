import GaussianWave.StarComparison
import GaussianWave.StarCovariancePSD
import GaussianWave.StarQuadraticInput

/-!
# Actual two-edge Gaussian marks

Independent products preserve weak convergence by their computed characteristic
functions and proved finite-dimensional tightness. Endpoint restriction is a
continuous linear map. The finite sampler and its independent product are the
actual empirical edge laws used in the bulk argument.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical ENNReal

/-! Independent finite-vector products preserve actual weak convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace GaussianWave

def mergeVectors {α β : Type*} (xy : (α → ℝ) × (β → ℝ)) : Sum α β → ℝ :=
  Sum.elim xy.1 xy.2

theorem continuous_mergeVectors {α β : Type*} : Continuous (mergeVectors (α := α) (β := β)) := by
  apply continuous_pi
  intro i
  cases i with
  | inl a => exact (continuous_apply a).comp continuous_fst
  | inr b => exact (continuous_apply b).comp continuous_snd

theorem finiteLinearForm_merge {α β : Type*} [Fintype α] [Fintype β]
    (t : Sum α β → ℝ) (xy : (α → ℝ) × (β → ℝ)) :
    finiteLinearForm t (mergeVectors xy) =
      finiteLinearForm (t ∘ Sum.inl) xy.1 + finiteLinearForm (t ∘ Sum.inr) xy.2 := by
  simp only [finiteLinearForm, Fintype.sum_sum_type, mergeVectors, Sum.elim_inl,
    Sum.elim_inr, Function.comp_apply]

def vectorProductLaw {α β : Type*} (μ : Measure (α → ℝ)) (ν : Measure (β → ℝ)) :
    Measure (Sum α β → ℝ) := Measure.map mergeVectors (μ.prod ν)

instance {α β : Type*} [Fintype α] [Fintype β] (μ : Measure (α → ℝ)) (ν : Measure (β → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (vectorProductLaw μ ν) :=
  MeasureTheory.isProbabilityMeasure_map continuous_mergeVectors.measurable.aemeasurable

theorem vectorProductLaw_characteristic {α β : Type*} [Fintype α] [Fintype β]
    (μ : Measure (α → ℝ)) (ν : Measure (β → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : Sum α β → ℝ) :
    (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂vectorProductLaw μ ν) =
      (∫ x, Complex.exp ((↑(finiteLinearForm (t ∘ Sum.inl) x) : ℂ) * Complex.I) ∂μ) *
      (∫ y, Complex.exp ((↑(finiteLinearForm (t ∘ Sum.inr) y) : ℂ) * Complex.I) ∂ν) := by
  have hmeas : AEStronglyMeasurable
      (fun x => Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I)) (vectorProductLaw μ ν) :=
    (linearCharacteristic t).continuous.aestronglyMeasurable
  rw [vectorProductLaw, integral_map continuous_mergeVectors.measurable.aemeasurable hmeas]
  simp_rw [finiteLinearForm_merge, Complex.ofReal_add, add_mul, Complex.exp_add]
  exact integral_prod_mul
    (fun x : α → ℝ => Complex.exp ((↑(finiteLinearForm (t ∘ Sum.inl) x) : ℂ) * Complex.I))
    (fun y : β → ℝ => Complex.exp ((↑(finiteLinearForm (t ∘ Sum.inr) y) : ℂ) * Complex.I))

theorem mergeVectors_norm_fourth_le {α β : Type*} [Fintype α] [Fintype β]
    (xy : (α → ℝ) × (β → ℝ)) :
    ‖mergeVectors xy‖ ^ 4 ≤ ‖xy.1‖ ^ 4 + ‖xy.2‖ ^ 4 := by
  have hm : ‖mergeVectors xy‖ ≤ max ‖xy.1‖ ‖xy.2‖ := by
    apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).mpr
    intro i
    cases i with
    | inl a => exact (norm_le_pi_norm xy.1 a).trans (le_max_left _ _)
    | inr b => exact (norm_le_pi_norm xy.2 b).trans (le_max_right _ _)
  calc
    _ ≤ (max ‖xy.1‖ ‖xy.2‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hm _
    _ ≤ _ := by
      rcases le_total ‖xy.1‖ ‖xy.2‖ with h | h
      · rw [max_eq_right h]
        linarith [show 0 ≤ ‖xy.1‖ ^ 4 by positivity]
      · rw [max_eq_left h]
        linarith [show 0 ≤ ‖xy.2‖ ^ 4 by positivity]

theorem vectorProductLaw_integrable_norm_fourth {α β : Type*} [Fintype α] [Fintype β]
    (μ : Measure (α → ℝ)) (ν : Measure (β → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x => ‖x‖ ^ 4) μ) (hν : Integrable (fun x => ‖x‖ ^ 4) ν) :
    Integrable (fun x => ‖x‖ ^ 4) (vectorProductLaw μ ν) := by
  have h1 : Integrable (fun xy : (α → ℝ) × (β → ℝ) => ‖xy.1‖ ^ 4) (μ.prod ν) := by
    simpa only [mul_one] using hμ.mul_prod (integrable_const (1 : ℝ))
  have h2 : Integrable (fun xy : (α → ℝ) × (β → ℝ) => ‖xy.2‖ ^ 4) (μ.prod ν) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hν
  apply (integrable_map_measure (continuous_norm.pow 4).aestronglyMeasurable
    continuous_mergeVectors.measurable.aemeasurable).mpr
  apply (h1.add h2).mono' ((continuous_mergeVectors.norm.pow 4).measurable.aestronglyMeasurable)
  filter_upwards [] with xy
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mergeVectors_norm_fourth_le xy

theorem vectorProductLaw_norm_fourth_bound {α β : Type*} [Fintype α] [Fintype β]
    (μ : Measure (α → ℝ)) (ν : Measure (β → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x => ‖x‖ ^ 4) μ) (hν : Integrable (fun x => ‖x‖ ^ 4) ν) :
    (∫ x, ‖x‖ ^ 4 ∂vectorProductLaw μ ν) ≤ (∫ x, ‖x‖ ^ 4 ∂μ) + ∫ y, ‖y‖ ^ 4 ∂ν := by
  have h1 : Integrable (fun xy : (α → ℝ) × (β → ℝ) => ‖xy.1‖ ^ 4) (μ.prod ν) := by
    simpa only [mul_one] using hμ.mul_prod (integrable_const (1 : ℝ))
  have h2 : Integrable (fun xy : (α → ℝ) × (β → ℝ) => ‖xy.2‖ ^ 4) (μ.prod ν) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hν
  have hm := vectorProductLaw_integrable_norm_fourth μ ν hμ hν
  have hm' := (integrable_map_measure (continuous_norm.pow 4).aestronglyMeasurable
    continuous_mergeVectors.measurable.aemeasurable).mp hm
  rw [vectorProductLaw, integral_map continuous_mergeVectors.measurable.aemeasurable
    (continuous_norm.pow 4).aestronglyMeasurable]
  calc
    _ ≤ ∫ xy : (α → ℝ) × (β → ℝ), ‖xy.1‖ ^ 4 + ‖xy.2‖ ^ 4 ∂μ.prod ν :=
      integral_mono hm' (h1.add h2) mergeVectors_norm_fourth_le
    _ = _ := by
      rw [integral_add h1 h2]
      have he1 := integral_prod_mul (μ := μ) (ν := ν) (fun x : α → ℝ => ‖x‖ ^ 4) (fun _ : β → ℝ => (1 : ℝ))
      have he2 := integral_prod_mul (μ := μ) (ν := ν) (fun _ : α → ℝ => (1 : ℝ)) (fun y : β → ℝ => ‖y‖ ^ 4)
      simpa only [mul_one, one_mul, integral_const, measureReal_univ_eq_one, one_smul] using congrArg₂ (· + ·) he1 he2

theorem vectorProductLaw_weakConverges {α β : Type*} [Fintype α] [Fintype β]
    (μ : ℕ → Measure (α → ℝ)) (ν : Measure (α → ℝ))
    (η : ℕ → Measure (β → ℝ)) (θ : Measure (β → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    [∀ n, IsProbabilityMeasure (η n)] [IsProbabilityMeasure θ]
    (hμ : WeakLawConverges μ ν) (hη : WeakLawConverges η θ)
    (hiμ : ∀ n, Integrable (fun x => ‖x‖ ^ 4) (μ n))
    (hiη : ∀ n, Integrable (fun x => ‖x‖ ^ 4) (η n))
    (M L : ℝ) (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂μ n) ≤ M) (hL : ∀ n, (∫ x, ‖x‖ ^ 4 ∂η n) ≤ L) :
    WeakLawConverges (fun n => vectorProductLaw (μ n) (η n)) (vectorProductLaw ν θ) := by
  apply weakLaw_of_characteristic_of_norm_fourth _ _
    (fun n => vectorProductLaw_integrable_norm_fourth (μ n) (η n) (hiμ n) (hiη n)) (M + L)
    (fun n => (vectorProductLaw_norm_fourth_bound (μ n) (η n) (hiμ n) (hiη n)).trans
      (add_le_add (hM n) (hL n)))
  intro t
  simp_rw [vectorProductLaw_characteristic]
  exact (weakLaw_characteristic μ ν hμ (t ∘ Sum.inl)).mul
    (weakLaw_characteristic η θ hη (t ∘ Sum.inr))

end GaussianWave

namespace GaussianWave
def sumCovariance {α β : Type*} (C : Matrix α α ℝ) (D : Matrix β β ℝ) :
    Matrix (Sum α β) (Sum α β) ℝ :=
  fun i j => match i, j with
    | .inl a, .inl b => C a b
    | .inr a, .inr b => D a b
    | _, _ => 0

theorem finiteCovarianceQuadratic_sum {α β : Type*} [Fintype α] [Fintype β]
    (C : Matrix α α ℝ) (D : Matrix β β ℝ) (t : Sum α β → ℝ) :
    finiteCovarianceQuadratic (sumCovariance C D) t =
      finiteCovarianceQuadratic C (t ∘ Sum.inl) + finiteCovarianceQuadratic D (t ∘ Sum.inr) := by
  simp only [finiteCovarianceQuadratic, Fintype.sum_sum_type, sumCovariance, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Function.comp_apply]

theorem HasGaussianCovariance.vectorProductLaw {α β : Type*} [Fintype α] [Fintype β]
    {μ : Measure (α → ℝ)} {ν : Measure (β → ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C : Matrix α α ℝ} {D : Matrix β β ℝ}
    (hμ : HasGaussianCovariance μ C) (hν : HasGaussianCovariance ν D) :
    HasGaussianCovariance (vectorProductLaw μ ν) (sumCovariance C D) := by
  intro t
  rw [vectorProductLaw_characteristic, hμ, hν, ← Complex.exp_add, finiteCovarianceQuadratic_sum]
  congr 1
  push_cast
  ring

theorem finiteCovarianceQuadratic_eq_dot {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (t : ι → ℝ) :
    finiteCovarianceQuadratic C t = t ⬝ᵥ C.mulVec t := by
  simp only [finiteCovarianceQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem finiteCovarianceQuadratic_conjugate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : Matrix ι ι ℝ) (R : Matrix κ ι ℝ) (t : κ → ℝ) :
    finiteCovarianceQuadratic (R * C * R.transpose) t =
      finiteCovarianceQuadratic C (Matrix.vecMul t R) := by
  rw [finiteCovarianceQuadratic_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, ← finiteCovarianceQuadratic_eq_dot]

theorem HasGaussianCovariance.linearImage {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : Measure (ι → ℝ)} {C : Matrix ι ι ℝ} (hμ : HasGaussianCovariance μ C)
    (R : Matrix κ ι ℝ) :
    HasGaussianCovariance (Measure.map (fun x => R.mulVec x) μ) (R * C * R.transpose) := by
  intro t
  have hm : AEStronglyMeasurable
      (fun x => Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I))
      (Measure.map (fun x => R.mulVec x) μ) := (linearCharacteristic t).continuous.aestronglyMeasurable
  rw [integral_map (measurable_finiteMatrixAction R).aemeasurable hm]
  simp_rw [finiteLinearForm_matrixAction]
  rw [hμ, finiteCovarianceQuadratic_conjugate]


end GaussianWave

namespace GaussianWave

/-- Coordinate-selection matrix for a physical endpoint restriction. -/
def selectionMatrix {ι κ : Type*} (source : κ → ι) : Matrix κ ι ℝ :=
  fun i a => if a = source i then 1 else 0

theorem selectionMatrix_mulVec {ι κ : Type*} [Fintype ι] (source : κ → ι) (x : ι → ℝ) (i : κ) :
    (selectionMatrix source).mulVec x i = x (source i) := by
  simp [selectionMatrix, Matrix.mulVec, dotProduct, ite_mul]

theorem selectionMatrix_conjugate {ι κ : Type*} [Fintype ι]
    (source : κ → ι) (C : Matrix ι ι ℝ) :
    selectionMatrix source * C * (selectionMatrix source).transpose =
      fun i j => C (source i) (source j) := by
  ext i j
  simp [selectionMatrix, Matrix.mul_apply, Matrix.transpose_apply, ite_mul, mul_ite]

def starEndpointSource {d k : ℕ} (leaf : Fin d) (ai : Fin k × Fin 4) :
    Sum (Fin k × Fin (d + 1)) (Fin k × Fin (d + 1)) :=
  ![Sum.inl (ai.1, 0), Sum.inl (ai.1, leaf.succ),
    Sum.inr (ai.1, 0), Sum.inr (ai.1, leaf.succ)] ai.2

def starEndpointRestriction {d k : ℕ} (leaf : Fin d) :
    Matrix (Fin k × Fin 4) (Sum (Fin k × Fin (d + 1)) (Fin k × Fin (d + 1))) ℝ :=
  selectionMatrix (starEndpointSource leaf)

/-- One channel's two independent correlated edge pairs. -/
def fourEndpointCovariance (p : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,p,0,0; p,1,0,0; 0,0,1,p; 0,0,p,1]

def finiteMarkCovariance (p : ℝ) (k : ℕ) : Matrix (Fin k × Fin 4) (Fin k × Fin 4) ℝ :=
  fun ai bj => (if ai.1 = bj.1 then 1 else 0) * fourEndpointCovariance p ai.2 bj.2

theorem starEndpointRestriction_covariance (d k : ℕ) (E : ℝ) (leaf : Fin d) :
    starEndpointRestriction (k := k) leaf *
      sumCovariance (jointStarCovariance d k E) (jointStarCovariance d k E) *
        (starEndpointRestriction leaf).transpose = finiteMarkCovariance (E / d) k := by
  rw [starEndpointRestriction, selectionMatrix_conjugate]
  ext ai bj
  rcases ai with ⟨a, i⟩
  rcases bj with ⟨b, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [starEndpointSource, sumCovariance, jointStarCovariance, finiteMarkCovariance,
      RegularEigenData.starWaveCovariance, fourEndpointCovariance,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem canonicalJointStar_posSemidef (d k : ℕ) (E : ℝ) (hd : 2 ≤ d) (hE : |E| ≤ (d : ℝ)) :
    (jointStarCovariance d k E).PosSemidef := by
  have h := channelBlockCovariance_posSemidef
    (fun _ : Fin k => RegularEigenData.starWaveCovariance d E)
    (fun _ => RegularEigenData.starWaveCovariance_posSemidef d E hd hE)
  convert h using 1
  ext aj bl
  simp only [jointStarCovariance, channelBlockCovariance]
  split_ifs <;> simp

/-- The fixed common-energy comparison, constructed from two independent
actual Gaussian stars followed by the physical endpoint restriction. -/
def twoEdgeGaussian (d k : ℕ) (E : ℝ) (hd : 2 ≤ d) (hE : |E| ≤ (d : ℝ)) (leaf : Fin d) :
    Measure ((Fin k × Fin 4) → ℝ) :=
  let γ := gaussianCovarianceLaw (jointStarCovariance d k E)
    (canonicalJointStar_posSemidef d k E hd hE)
  Measure.map (fun x => (starEndpointRestriction (k := k) leaf).mulVec x) (vectorProductLaw γ γ)

instance twoEdgeGaussian_isProbability (d k : ℕ) (E : ℝ) (hd : 2 ≤ d)
    (hE : |E| ≤ (d : ℝ)) (leaf : Fin d) : IsProbabilityMeasure (twoEdgeGaussian d k E hd hE leaf) := by
  unfold twoEdgeGaussian
  exact MeasureTheory.isProbabilityMeasure_map
    (measurable_finiteMatrixAction (starEndpointRestriction leaf)).aemeasurable

theorem twoEdgeGaussian_characteristic (d k : ℕ) (E : ℝ) (hd : 2 ≤ d)
    (hE : |E| ≤ (d : ℝ)) (leaf : Fin d) :
    HasGaussianCovariance (twoEdgeGaussian d k E hd hE leaf) (finiteMarkCovariance (E / d) k) := by
  have hstar := gaussianCovarianceLaw_characteristic (jointStarCovariance d k E)
    (canonicalJointStar_posSemidef d k E hd hE)
  have he := (hstar.vectorProductLaw hstar).linearImage (starEndpointRestriction (k := k) leaf)
  rw [starEndpointRestriction_covariance] at he
  exact he

theorem continuous_finiteMatrixAction {ι κ : Type*} [Fintype ι]
    (R : Matrix κ ι ℝ) : Continuous (fun x : ι → ℝ => R.mulVec x) := by
  apply continuous_pi
  intro i
  exact continuous_finset_sum _ (fun j hj => continuous_const.mul (continuous_apply j))

theorem weakLaw_linearImage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ℕ → Measure (ι → ℝ)) (ν : Measure (ι → ℝ)) (R : Matrix κ ι ℝ)
    (hweak : WeakLawConverges μ ν) :
    WeakLawConverges (fun n => Measure.map (fun x => R.mulVec x) (μ n))
      (Measure.map (fun x => R.mulVec x) ν) := by
  intro F
  have h := hweak (F.compContinuous ⟨_, continuous_finiteMatrixAction R⟩)
  simp only [integral_map (measurable_finiteMatrixAction R).aemeasurable
    F.continuous.aestronglyMeasurable]
  exact h

end GaussianWave

namespace GaussianWave.RegularEigenData

/-- Actual empirical law of two independent sampled star edges. Its finite
raw-sampler representation is proved below. -/
def twoEdgeLaw {d N k : ℕ} (D : RegularEigenData d N k) (leaf : Fin d) :
    Measure ((Fin k × Fin 4) → ℝ) :=
  Measure.map (fun x => (starEndpointRestriction (k := k) leaf).mulVec x)
    (vectorProductLaw D.eigenStarLaw D.eigenStarLaw)

instance twoEdgeLaw_isProbability {d N k : ℕ} (D : RegularEigenData d N k) (leaf : Fin d) :
    IsProbabilityMeasure (D.twoEdgeLaw leaf) :=
  MeasureTheory.isProbabilityMeasure_map
    (measurable_finiteMatrixAction (starEndpointRestriction leaf)).aemeasurable

end GaussianWave.RegularEigenData

namespace GaussianWave

/-- The actual two-edge empirical mark law converges to its fixed normalized
Gaussian law. The only Gaussianity input is the qualitative BS contract. -/
theorem eigenvectors_twoEdge_weakConverges
    {d k : ℕ} (hd : 2 ≤ d) (N : ℕ → ℕ)
    (D : ∀ n, RegularEigenData d (N n) k)
    (E : ℝ) (hE : ∀ i, Tendsto (fun n => (D n).eigenvalue i) atTop (𝓝 E))
    (hEb : |E| ≤ (d : ℝ))
    (M : ℝ) (hM : ∀ n i, (N n : ℝ) * ∑ v, (D n).eigenvector i v ^ 4 ≤ M)
    (BS : BSJointClassification (fun n => (D n).eigenStarLaw)) (leaf : Fin d) :
    WeakLawConverges (fun n => (D n).twoEdgeLaw leaf) (twoEdgeGaussian d k E hd hEb leaf) := by
  classical
  obtain ⟨hC, hw⟩ := eigenvectors_normalizedStar_weakConverges hd N (fun _ => k)
    D (fun _ => id) (fun _ => Function.injective_id) E hE M hM BS
  let γ := gaussianCovarianceLaw (jointStarCovariance d k E) hC
  have hi (n : ℕ) : Integrable (fun x => ‖x‖ ^ 4) (D n).eigenStarLaw :=
    (D n).integrable_starLaw _ _
  have hb (n : ℕ) : (∫ x, ‖x‖ ^ 4 ∂(D n).eigenStarLaw) ≤
      M * (Fintype.card (Fin k × Fin (d + 1)) : ℝ) ^ 2 := by
    apply (integral_pi_norm_fourth_le (D n).eigenStarLaw (fun _ => (D n).integrable_starLaw _ _)
      M ?_).2
    intro aj
    rw [RegularEigenData.eigenStarLaw, (D n).integral_star_coordinate_fourth]
    exact hM n aj.1
  have hp := vectorProductLaw_weakConverges (fun n => (D n).eigenStarLaw) γ
    (fun n => (D n).eigenStarLaw) γ hw hw hi hi _ _ hb hb
  exact weakLaw_linearImage _ _ (starEndpointRestriction leaf) hp

end GaussianWave

namespace GaussianWave

theorem sumCovariance_posSemidef {α β : Type*} [Fintype α] [Fintype β]
    (C : Matrix α α ℝ) (D : Matrix β β ℝ) (hC : C.PosSemidef) (hD : D.PosSemidef) :
    (sumCovariance C D).PosSemidef := by
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    cases i <;> cases j <;> simp only [sumCovariance]
    · exact congrFun (congrFun hC.1 _ ) _
    · exact congrFun (congrFun hD.1 _ ) _
  · intro t
    have h := add_nonneg (finiteCovarianceQuadratic_nonneg_of_posSemidef C hC (t ∘ Sum.inl))
      (finiteCovarianceQuadratic_nonneg_of_posSemidef D hD (t ∘ Sum.inr))
    rw [← finiteCovarianceQuadratic_sum] at h
    simpa only [finiteCovarianceQuadratic, dotProduct, Matrix.mulVec, star_trivial,
      Finset.mul_sum, mul_assoc] using h

/-- Positivity of the explicit four-endpoint covariance follows from the
canonical star covariance and the literal coordinate restriction. -/
theorem fourEndpointCovariance_posSemidef (d : ℕ) (E : ℝ) (hd : 2 ≤ d)
    (hE : |E| ≤ (d : ℝ)) (leaf : Fin d) : (fourEndpointCovariance (E / d)).PosSemidef := by
  have hs := canonicalJointStar_posSemidef d 1 E hd hE
  have hp := (sumCovariance_posSemidef _ _ hs hs).mul_mul_conjTranspose_same
    (starEndpointRestriction (k := 1) leaf)
  have htranspose : (starEndpointRestriction (k := 1) leaf).conjTranspose =
      (starEndpointRestriction (k := 1) leaf).transpose := by ext i j; simp
  rw [htranspose, starEndpointRestriction_covariance] at hp
  have h := hp.submatrix (fun j : Fin 4 => ((0 : Fin 1), j))
  simpa [finiteMarkCovariance, Matrix.submatrix] using h

/-- The fixed target is literally a product of independent N(0,C4(E))
channels, where C4(E) has the two B(E) root-neighbor blocks. -/
theorem twoEdgeGaussian_product (d k : ℕ) (E : ℝ) (hd : 2 ≤ d)
    (hE : |E| ≤ (d : ℝ)) (leaf : Fin d) :
    twoEdgeGaussian d k E hd hE leaf = Measure.map flattenChannels
      (Measure.pi (fun _ : Fin k => gaussianCovarianceLaw
        (fourEndpointCovariance (E / d)) (fourEndpointCovariance_posSemidef d E hd hE leaf))) := by
  apply gaussian_eq_flattened_product _ (fun _ : Fin k => fourEndpointCovariance (E / d))
    (fun _ => fourEndpointCovariance_posSemidef d E hd hE leaf)
  intro t
  have heq : finiteMarkCovariance (E / d) k =
      channelBlockCovariance (fun _ : Fin k => fourEndpointCovariance (E / d)) := by
    ext i j
    simp only [finiteMarkCovariance, channelBlockCovariance]
    split_ifs <;> simp
  simpa only [heq] using twoEdgeGaussian_characteristic d k E hd hE leaf t

end GaussianWave

namespace GaussianWave.EdgeQuadratics.FiniteProbability
open MeasureTheory
variable {Ω : Type*} [Fintype Ω] (P Q : FiniteProbability Ω)

theorem map_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (mark : Ω → E) (f : E → F) (hf : Measurable f) :
    Measure.map f (P.law mark) = P.law (fun ω => f (mark ω)) := by
  classical
  rw [law, map_finset_sum_measure _ hf]
  simp_rw [Measure.map_smul, Measure.map_dirac hf]
  rfl

/-- Independent finite sampling is an equality of actual product measures. -/
theorem prod_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (mark : Ω → E) (mark' : Ω → F) :
    (P.prod Q).law (fun ω => (mark ω.1, mark' ω.2)) = (P.law mark).prod (Q.law mark') := by
  classical
  symm
  apply Measure.prod_eq
  intro A B hA hB
  simp only [law, prod, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (hA.prod hB), Measure.dirac_apply' _ hA, Measure.dirac_apply' _ hB,
    smul_eq_mul, Fintype.sum_prod_type, ENNReal.ofReal_mul (P.nonneg _)]
  simp only [Set.indicator_apply, Pi.one_apply, Set.mem_prod, Set.mem_setOf_eq]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  split_ifs <;> simp_all

end GaussianWave.EdgeQuadratics.FiniteProbability

namespace GaussianWave.RegularEigenData

/-- Physical endpoint numbering 0,1 from the first edge and 2,3 from the second. -/
def physicalEndpoint (i : Fin 4) : Bool × Fin 2 :=
  ![(false, 0), (false, 1), (true, 0), (true, 1)] i

def rawTwoEdgeMark {d N k : ℕ} (D : RegularEigenData d N k) (leaf : Fin d)
    (ω : (Fin N × Equiv.Perm (Fin d)) × (Fin N × Equiv.Perm (Fin d)))
    (ai : Fin k × Fin 4) : ℝ :=
  D.twoEdgeMark leaf ai.1 (physicalEndpoint ai.2) ω

/-- The continuous endpoint restriction selects exactly the raw physical marks
of the concrete independently sampled finite stars. -/
theorem restrict_two_starSample {d N k : ℕ} (D : RegularEigenData d N k) (leaf : Fin d)
    (ω : (Fin N × Equiv.Perm (Fin d)) × (Fin N × Equiv.Perm (Fin d))) :
    (starEndpointRestriction (k := k) leaf).mulVec
      (mergeVectors (D.starSample D.eigenvector ω.1, D.starSample D.eigenvector ω.2)) =
        D.rawTwoEdgeMark leaf ω := by
  ext ai
  rw [starEndpointRestriction, selectionMatrix_mulVec]
  rcases ai with ⟨a, i⟩
  fin_cases i <;> simp [starEndpointSource, mergeVectors, rawTwoEdgeMark, physicalEndpoint,
    twoEdgeMark, edgeMark, edgePosition] <;> rfl

/-- The weak-limit law is the actual raw finite two-edge sampling law used by
the quantitative quadratic estimates, not merely an unrelated image measure. -/
theorem twoEdgeLaw_eq_rawSampler {d N k : ℕ} (D : RegularEigenData d N k) (leaf : Fin d) :
    D.twoEdgeLaw leaf =
      (D.starProbability.prod D.starProbability).law (D.rawTwoEdgeMark leaf) := by
  rw [twoEdgeLaw, eigenStarLaw, ← D.starProbability_law D.eigenvector,
    vectorProductLaw, ← EdgeQuadratics.FiniteProbability.prod_law]
  rw [EdgeQuadratics.FiniteProbability.map_law _ _ mergeVectors continuous_mergeVectors.measurable,
    EdgeQuadratics.FiniteProbability.map_law _ _ _
      (measurable_finiteMatrixAction (starEndpointRestriction leaf))]
  congr 1
  funext ω
  exact D.restrict_two_starSample leaf ω

end GaussianWave.RegularEigenData
