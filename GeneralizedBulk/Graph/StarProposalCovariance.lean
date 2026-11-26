import GeneralizedBulk.Graph.ProposalFourthCovariance
import GeneralizedBulk.Graph.HYEmpiricalFourthMoments
import GeneralizedBulk.Graph.EigenvalueBound

/-! Actual one-star fourth discrepancies control physical quadratic covariances. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def edgeStarSlot (leaf : Fin d) (i : Fin 2) : Fin (d + 1) :=
  Fin.cases 0 (fun _ => leaf.succ) i

@[simp] theorem edgeStarSlot_zero (leaf : Fin d) : edgeStarSlot leaf 0 = 0 := rfl
@[simp] theorem edgeStarSlot_one (leaf : Fin d) : edgeStarSlot leaf 1 = leaf.succ := rfl

/-- The fourth moment of actual oriented-edge quadratic marks is literally
the root/ordered-leaf restriction of the empirical star law. -/
theorem singleEdgeQuadratic_product_eq_star {k : ℕ}
    (selection : Fin k → Fin (N n)) (a b : Fin k) (leaf : Fin d) (i j : Fin 2) :
    (∫ t, D.singleEdgeQuadratic n ω (selection a) i j t *
      D.singleEdgeQuadratic n ω (selection b) i j t ∂finiteUniform (Fin (N n) × Fin d)) =
    ∫ x, x (a,edgeStarSlot leaf i) * x (a,edgeStarSlot leaf j) *
      x (b,edgeStarSlot leaf i) * x (b,edgeStarSlot leaf j)
      ∂D.starLaw n ω (fun c => D.eigenvector n ω (selection c)) := by
  let q := fun c => D.eigenvector n ω (selection c)
  let F := fun y : (Fin k × Fin 2) → ℝ => y (a,i) * y (a,j) * y (b,i) * y (b,j)
  have hF : Measurable F := (((measurable_pi_apply (a,i)).mul
    (measurable_pi_apply (a,j))).mul (measurable_pi_apply (b,i))).mul (measurable_pi_apply (b,j))
  have hraw : (fun t => D.singleEdgeQuadratic n ω (selection a) i j t *
      D.singleEdgeQuadratic n ω (selection b) i j t) =
      (fun t => F (D.orientedEdgeMark n ω q t)) := by
    funext t
    dsimp [singleEdgeQuadratic,F,orientedEdgeMark,q,proposalEndpoint]
    have hs := Real.sq_sqrt (Nat.cast_nonneg (N n) : (0 : ℝ) ≤ N n)
    calc
      _ = (N n : ℝ) ^ 2 * (D.eigenvector n ω (selection a)
          (![t.1,D.neighbor n ω t.1 t.2] i) *
        D.eigenvector n ω (selection a) (![t.1,D.neighbor n ω t.1 t.2] j) *
        D.eigenvector n ω (selection b) (![t.1,D.neighbor n ω t.1 t.2] i) *
        D.eigenvector n ω (selection b) (![t.1,D.neighbor n ω t.1 t.2] j)) := by ring
      _ = (Real.sqrt (N n : ℝ) ^ 2) ^ 2 * (D.eigenvector n ω (selection a)
          (![t.1,D.neighbor n ω t.1 t.2] i) *
        D.eigenvector n ω (selection a) (![t.1,D.neighbor n ω t.1 t.2] j) *
        D.eigenvector n ω (selection b) (![t.1,D.neighbor n ω t.1 t.2] i) *
        D.eigenvector n ω (selection b) (![t.1,D.neighbor n ω t.1 t.2] j)) := by rw [hs]
      _ = _ := by ring
  rw [hraw,← integral_map (measurable_of_finite _).aemeasurable hF.aestronglyMeasurable]
  change (∫ y, F y ∂D.orientedEdgeLaw n ω q) = _
  rw [← D.starLaw_edge_marginal n ω q leaf,
    integral_map (measurable_starEdgeRestriction leaf).aemeasurable hF.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [F,starEdgeRestriction,edgeStarSlot]
  fin_cases i <;> fin_cases j <;> rfl

/-- Actual centering removes precisely the product of the finite covariances. -/
theorem centeredSingleEdgeQuadratic_product_integral (hd : 0 < d)
    (k l : Fin (N n)) (i j : Fin 2) :
    (∫ t, D.centeredSingleEdgeQuadratic n ω k i j t *
      D.centeredSingleEdgeQuadratic n ω l i j t ∂finiteUniform (Fin (N n) × Fin d)) =
      (∫ t, D.singleEdgeQuadratic n ω k i j t * D.singleEdgeQuadratic n ω l i j t
        ∂finiteUniform (Fin (N n) × Fin d)) -
      edgeCovariance (D.eigenvalue n ω k / d) i j * edgeCovariance (D.eigenvalue n ω l / d) i j := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  letI := finiteUniform_isProbability (Fin (N n) × Fin d)
  let Qk := D.singleEdgeQuadratic n ω k i j
  let Ql := D.singleEdgeQuadratic n ω l i j
  let ck := edgeCovariance (D.eigenvalue n ω k / d) i j
  let cl := edgeCovariance (D.eigenvalue n ω l / d) i j
  have hkmean : (∫ t, Qk t ∂finiteUniform (Fin (N n) × Fin d)) = ck :=
    D.singleQuadraticMean_eq n ω hd k i j
  have hlmean : (∫ t, Ql t ∂finiteUniform (Fin (N n) × Fin d)) = cl :=
    D.singleQuadraticMean_eq n ω hd l i j
  have hi (f : (Fin (N n) × Fin d) → ℝ) : Integrable f (finiteUniform (Fin (N n) × Fin d)) :=
    integrable_finiteUniform_real f
  have heq : (fun t => (Qk t - ck) * (Ql t - cl)) =
      (fun t => Qk t * Ql t - ck * Ql t - cl * Qk t + ck * cl) := by funext t; ring
  change (∫ t, (Qk t - ck) * (Ql t - cl) ∂finiteUniform _) = _
  rw [heq,integral_add (hi _) (hi _),integral_sub (hi _) (hi _),integral_sub (hi _) (hi _),
    integral_const_mul,integral_const_mul,integral_const,measureReal_univ_eq_one,one_smul,
    hkmean,hlmean]
  dsimp [Qk,Ql,ck,cl]
  ring

/-- The raw star fourth discrepancy is the centered physical covariance
minus the two remaining Gaussian contractions. -/
theorem singleEdge_covariance_eq_empiricalWick {k : ℕ} (hd : 0 < d)
    (selection : Fin k → Fin (N n)) (a b : Fin k) (leaf : Fin d) (i j : Fin 2) :
    (∫ t, D.centeredSingleEdgeQuadratic n ω (selection a) i j t *
      D.centeredSingleEdgeQuadratic n ω (selection b) i j t ∂finiteUniform (Fin (N n) × Fin d)) =
      D.empiricalFourthWickDiscrepancy n ω selection
        (a,edgeStarSlot leaf i) (a,edgeStarSlot leaf j)
        (b,edgeStarSlot leaf i) (b,edgeStarSlot leaf j) +
      D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf i) (b,edgeStarSlot leaf i) *
        D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf j) (b,edgeStarSlot leaf j) +
      D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf i) (b,edgeStarSlot leaf j) *
        D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf j) (b,edgeStarSlot leaf i) := by
  rw [D.centeredSingleEdgeQuadratic_product_integral n ω hd,
    D.singleEdgeQuadratic_product_eq_star n ω selection a b leaf i j,
    D.integral_starLaw]
  simp only [empiricalFourthWickDiscrepancy,empiricalStarWeight]
  have hsum : (∑ t : EmpiricalStarSample d (N n),
      (Fintype.card (EmpiricalStarSample d (N n)) : ℝ)⁻¹ *
      D.starSample n ω (fun c => D.eigenvector n ω (selection c)) t (a,edgeStarSlot leaf i) *
      D.starSample n ω (fun c => D.eigenvector n ω (selection c)) t (a,edgeStarSlot leaf j) *
      D.starSample n ω (fun c => D.eigenvector n ω (selection c)) t (b,edgeStarSlot leaf i) *
      D.starSample n ω (fun c => D.eigenvector n ω (selection c)) t (b,edgeStarSlot leaf j)) =
      (Fintype.card (EmpiricalStarSample d (N n)) : ℝ)⁻¹ *
      (∑ t, D.starSample n ω (fun c => D.eigenvector n ω (selection c)) t (a,edgeStarSlot leaf i) *
      D.starSample n ω (fun c => D.eigenvector n ω (selection c)) t (a,edgeStarSlot leaf j) *
      D.starSample n ω (fun c => D.eigenvector n ω (selection c)) t (b,edgeStarSlot leaf i) *
      D.starSample n ω (fun c => D.eigenvector n ω (selection c)) t (b,edgeStarSlot leaf j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hsum]
  simp only [empiricalGaussianCovariance,↓reduceIte,one_mul]
  fin_cases i <;> fin_cases j <;> norm_num [starWaveCovariance,edgeCovariance] <;> ring

/-- Each pair of Gaussian contractions is bounded by the universal
quadratic variance constant two on the diagonal, and vanishes off color. -/
theorem empirical_edge_gaussian_contractions_le {k : ℕ} (hd : 0 < d)
    (selection : Fin k → Fin (N n)) (a b : Fin k) (leaf : Fin d) (i j : Fin 2) :
    |D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf i) (b,edgeStarSlot leaf i) *
        D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf j) (b,edgeStarSlot leaf j) +
      D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf i) (b,edgeStarSlot leaf j) *
        D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf j) (b,edgeStarSlot leaf i)| ≤
      2 * (if a = b then 1 else 0) := by
  by_cases hab : a = b
  · subst b
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    have hp : |D.eigenvalue n ω (selection a) / (d : ℝ)| ≤ 1 := by
      rw [abs_div,abs_of_pos hdR,div_le_one hdR]
      exact D.eigenvalue_abs_le_degree n ω (selection a)
    have hp2 : (D.eigenvalue n ω (selection a) / (d : ℝ)) ^ 2 ≤ 1 := by
      simpa only [sq_abs,one_pow] using
        (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hp
    fin_cases i <;> fin_cases j <;>
      norm_num [empiricalGaussianCovariance,starWaveCovariance] <;>
      rw [abs_of_nonneg (by nlinarith [sq_nonneg (D.eigenvalue n ω (selection a) / (d : ℝ))])] <;> nlinarith only [hp2]
  · simp [empiricalGaussianCovariance,hab]

/-- A literal empirical star Wick error yields the physical one-edge
centered quadratic covariance estimate. -/
theorem centeredSingleEdge_covariance_le_of_empiricalWick {k : ℕ} (hd : 0 < d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (a b : Fin k) (leaf : Fin d) (epsilon : ℝ)
    (hfourth : ∀ j1 j2 j3 j4, |D.empiricalFourthWickDiscrepancy n ω selection j1 j2 j3 j4| ≤ epsilon)
    (i j : Fin 2) :
    |∫ t, D.centeredSingleEdgeQuadratic n ω (selection a) i j t *
      D.centeredSingleEdgeQuadratic n ω (selection b) i j t ∂finiteUniform (Fin (N n) × Fin d)| ≤
      2 * (if selection a = selection b then 1 else 0) + epsilon := by
  have hbound := D.empirical_edge_gaussian_contractions_le n ω hd selection a b leaf i j
  have herr := hfourth (a,edgeStarSlot leaf i) (a,edgeStarSlot leaf j)
    (b,edgeStarSlot leaf i) (b,edgeStarSlot leaf j)
  rw [D.singleEdge_covariance_eq_empiricalWick n ω hd selection a b leaf i j]
  have htri := abs_add
    (D.empiricalFourthWickDiscrepancy n ω selection
      (a,edgeStarSlot leaf i) (a,edgeStarSlot leaf j) (b,edgeStarSlot leaf i) (b,edgeStarSlot leaf j))
    (D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf i) (b,edgeStarSlot leaf i) *
        D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf j) (b,edgeStarSlot leaf j) +
      D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf i) (b,edgeStarSlot leaf j) *
        D.empiricalGaussianCovariance n ω selection (a,edgeStarSlot leaf j) (b,edgeStarSlot leaf i))
  rw [← add_assoc] at htri
  simp only [hinj.eq_iff]
  linarith only [htri,hbound,herr]

/-- Empirical fourth control on a finite color selection gives the actual
unconditioned two-dart quadratic covariance, exactly in the variance API. -/
theorem proposal_covariance_le_of_empiricalWick {k : ℕ} (hd : 0 < d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (a b : Fin k) (ha : selection a ≠ ⟨0,D.size_pos n⟩) (hb : selection b ≠ ⟨0,D.size_pos n⟩)
    (leaf : Fin d) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hfourth : ∀ j1 j2 j3 j4, |D.empiricalFourthWickDiscrepancy n ω selection j1 j2 j3 j4| ≤ epsilon)
    (i j : Fin 4) :
    |∫ t, D.centeredProposalQuadratic n ω (selection a) i j t *
      D.centeredProposalQuadratic n ω (selection b) i j t ∂uniformOrientedProposals (N n) d| ≤
      2 * (if selection a = selection b then 1 else 0) + epsilon := by
  exact D.proposal_covariance_le_of_single_edge_covariances n ω hd
    (selection a) (selection b) ha hb epsilon hepsilon
    (fun i j => D.centeredSingleEdge_covariance_le_of_empiricalWick n ω hd selection hinj
      a b leaf epsilon hfourth i j) i j

end GeneralizedBulk.External.RegularSpectralData
