import GeneralizedBulk.Graph.EndpointUniform

/-!
# Exact means of the physical quadratic endpoint marks

The independent proposal law is used before acceptance. The within-edge
second moments come from literal finite star identities; cross-edge means
vanish for each nonconstant eigenvector by independent uniform endpoints.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def singleQuadraticMean (k : Fin (N n)) (i j : Fin 2) : ℝ :=
  ∫ a : Fin (N n) × Fin d, (N n : ℝ) *
    D.eigenvector n ω k (D.proposalEndpoint n ω a i) *
      D.eigenvector n ω k (D.proposalEndpoint n ω a j) ∂finiteUniform (Fin (N n) × Fin d)

def edgeCovariance (p : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1,p;p,1]

/-- Single-edge quadratic means are exactly the finite covariance at that
eigenvalue, including diagonal and repeated-coordinate cases. -/
theorem singleQuadraticMean_eq (hd : 0 < d) (k : Fin (N n)) (i j : Fin 2) :
    D.singleQuadraticMean n ω k i j = edgeCovariance (D.eigenvalue n ω k / d) i j := by
  let leaf : Fin d := ⟨0,hd⟩
  let q : Fin 1 → Fin (N n) → ℝ := fun _ => D.eigenvector n ω k
  let F : ((Fin 1 × Fin 2) → ℝ) → ℝ := fun y => y (0,i) * y (0,j)
  have hF : Measurable F := (measurable_pi_apply (0,i)).mul (measurable_pi_apply (0,j))
  have hraw : D.singleQuadraticMean n ω k i j =
      ∫ a, F (D.orientedEdgeMark n ω q a) ∂finiteUniform (Fin (N n) × Fin d) := by
    apply integral_congr_ae
    filter_upwards [] with a
    dsimp only [F, q, singleQuadraticMean, orientedEdgeMark, proposalEndpoint]
    have hs : Real.sqrt (N n : ℝ) ^ 2 = N n := Real.sq_sqrt (Nat.cast_nonneg _)
    calc
      _ = Real.sqrt (N n : ℝ) ^ 2 *
        (D.eigenvector n ω k (![a.1,D.neighbor n ω a.1 a.2] i) *
          D.eigenvector n ω k (![a.1,D.neighbor n ω a.1 a.2] j)) := by rw [hs]; ring
      _ = _ := by ring
  rw [hraw]
  rw [← integral_map (measurable_of_finite _).aemeasurable hF.aestronglyMeasurable]
  change (∫ y, F y ∂D.orientedEdgeLaw n ω q) = _
  rw [← D.starLaw_edge_marginal n ω q leaf,
    integral_map (measurable_starEdgeRestriction leaf).aemeasurable hF.aestronglyMeasurable]
  change (∫ x, starEdgeRestriction leaf x (0,i) * starEdgeRestriction leaf x (0,j)
    ∂D.starLaw n ω q) = _
  fin_cases i <;> fin_cases j
  · simp only [starEdgeRestriction, Matrix.cons_val_zero, edgeCovariance]
    simpa only [q, ↓reduceIte] using D.integral_star_eigen_root_pair n ω (fun _ : Fin 1 => k) 0 0
  · simp only [starEdgeRestriction, Matrix.cons_val_zero, Matrix.cons_val_one, edgeCovariance]
    simpa only [q, ↓reduceIte, mul_one] using D.integral_star_eigen_root_neighbor n ω
      (fun _ : Fin 1 => k) 0 0 leaf
  · simp only [starEdgeRestriction, Matrix.cons_val_zero, Matrix.cons_val_one, edgeCovariance]
    have heq : (fun x : (Fin 1 × Fin (d + 1)) → ℝ => x (0,leaf.succ) * x (0,0)) =
        (fun x => x (0,0) * x (0,leaf.succ)) := funext (fun x => mul_comm _ _)
    change (∫ x, x (0,leaf.succ) * x (0,0) ∂D.starLaw n ω q) = D.eigenvalue n ω k / d
    rw [heq]
    simpa only [q, ↓reduceIte, mul_one] using D.integral_star_eigen_root_neighbor n ω
      (fun _ : Fin 1 => k) 0 0 leaf
  · simp only [starEdgeRestriction, Matrix.cons_val_one, edgeCovariance]
    simpa only [q, ↓reduceIte] using D.integral_star_eigen_same_neighbor n ω
      (fun _ : Fin 1 => k) 0 0 leaf

include D in
theorem firstEdge_integral (hd : 0 < d) (f : (Fin (N n) × Fin d) → ℝ) :
    (∫ s : ProposalSample (N n) d, f s.1 ∂uniformOrientedProposals (N n) d) =
      ∫ a, f a ∂finiteUniform (Fin (N n) × Fin d) := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  letI := finiteUniform_isProbability (Fin (N n) × Fin d)
  change (∫ s, f s.1 ∂finiteUniform ((Fin (N n) × Fin d) × (Fin (N n) × Fin d))) = _
  rw [← finiteUniform_prod, integral_fun_fst, measureReal_univ_eq_one, one_smul]

include D in
theorem secondEdge_integral (hd : 0 < d) (f : (Fin (N n) × Fin d) → ℝ) :
    (∫ s : ProposalSample (N n) d, f s.2 ∂uniformOrientedProposals (N n) d) =
      ∫ a, f a ∂finiteUniform (Fin (N n) × Fin d) := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  letI := finiteUniform_isProbability (Fin (N n) × Fin d)
  change (∫ s, f s.2 ∂finiteUniform ((Fin (N n) × Fin d) × (Fin (N n) × Fin d))) = _
  rw [← finiteUniform_prod, integral_fun_snd, measureReal_univ_eq_one, one_smul]

/-- Cross-edge means are exactly zero for every nonconstant eigenchannel. -/
theorem crossQuadraticMean_zero (hd : 0 < d) (k : Fin (N n)) (hk : k ≠ ⟨0,D.size_pos n⟩)
    (i j : Fin 2) :
    (∫ s : ProposalSample (N n) d, (N n : ℝ) *
      D.eigenvector n ω k (D.proposalEndpoint n ω s.1 i) *
        D.eigenvector n ω k (D.proposalEndpoint n ω s.2 j) ∂uniformOrientedProposals (N n) d) = 0 := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  letI := finiteUniform_isProbability (Fin (N n))
  let F (p : Fin (N n) × Fin (N n)) : ℝ := (N n : ℝ) * D.eigenvector n ω k p.1 * D.eigenvector n ω k p.2
  have hmap := D.crossProposalEndpoints_uniform_law n ω hd i j
  have h := congrArg (fun mu : Measure (Fin (N n) × Fin (N n)) => ∫ p, F p ∂mu) hmap
  dsimp only at h
  rw [integral_map (measurable_of_finite _).aemeasurable (measurable_of_finite _).aestronglyMeasurable] at h
  change _ = 0
  rw [h]
  have heq : F = fun p => (N n : ℝ) * (D.eigenvector n ω k p.1 * D.eigenvector n ω k p.2) := by
    funext p; dsimp [F]; ring
  rw [heq, integral_const_mul, integral_prod_mul, integral_finiteUniform,
    D.eigenvector_sum_zero n ω k hk, mul_zero, zero_mul, mul_zero]

/-- The exact proposal quadratic mean is the finite eigenvalue covariance.
The only excluded channel is the distinguished constant eigenvector. -/
theorem proposalQuadratic_mean_nonconstant (hd : 0 < d) (k : Fin (N n))
    (hk : k ≠ ⟨0,D.size_pos n⟩) (i j : Fin 4) :
    (∫ s, D.proposalQuadratic n ω k i j s ∂uniformOrientedProposals (N n) d) =
      covarianceMatrix (D.eigenvalue n ω k / (d : ℝ)) i j := by
  have hfirst (a b : Fin 2) :
      (∫ s : ProposalSample (N n) d, (N n : ℝ) *
        D.eigenvector n ω k (D.proposalEndpoint n ω s.1 a) *
          D.eigenvector n ω k (D.proposalEndpoint n ω s.1 b) ∂uniformOrientedProposals (N n) d) =
        edgeCovariance (D.eigenvalue n ω k / d) a b := by
    rw [D.firstEdge_integral n hd (fun t => (N n : ℝ) *
      D.eigenvector n ω k (D.proposalEndpoint n ω t a) *
        D.eigenvector n ω k (D.proposalEndpoint n ω t b))]
    exact D.singleQuadraticMean_eq n ω hd k a b
  have hsecond (a b : Fin 2) :
      (∫ s : ProposalSample (N n) d, (N n : ℝ) *
        D.eigenvector n ω k (D.proposalEndpoint n ω s.2 a) *
          D.eigenvector n ω k (D.proposalEndpoint n ω s.2 b) ∂uniformOrientedProposals (N n) d) =
        edgeCovariance (D.eigenvalue n ω k / d) a b := by
    rw [D.secondEdge_integral n hd (fun t => (N n : ℝ) *
      D.eigenvector n ω k (D.proposalEndpoint n ω t a) *
        D.eigenvector n ω k (D.proposalEndpoint n ω t b))]
    exact D.singleQuadraticMean_eq n ω hd k a b
  have hcross := D.crossQuadraticMean_zero n ω hd k hk
  have hback (a b : Fin 2) :
      (∫ s : ProposalSample (N n) d, (N n : ℝ) *
        D.eigenvector n ω k (D.proposalEndpoint n ω s.2 a) *
          D.eigenvector n ω k (D.proposalEndpoint n ω s.1 b) ∂uniformOrientedProposals (N n) d) = 0 := by
    convert hcross b a using 1
    apply integral_congr_ae
    filter_upwards [] with s
    ring
  rw [covarianceMatrix_eq]
  fin_cases i <;> fin_cases j <;>
    simp only [proposalQuadratic, proposalEndpoints, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;>
    first | exact hfirst 0 0 | exact hfirst 0 1 | exact hfirst 1 0 | exact hfirst 1 1 |
      exact hsecond 0 0 | exact hsecond 0 1 | exact hsecond 1 0 | exact hsecond 1 1 |
      exact hcross 0 0 | exact hcross 0 1 | exact hcross 1 0 | exact hcross 1 1 |
      exact hback 0 0 | exact hback 0 1 | exact hback 1 0 | exact hback 1 1

/-- The actual finite centered summand is therefore the raw quadratic mark
minus `C(lambda/d)`, without an asymptotic mean substitution. -/
theorem centeredProposalQuadratic_eq_covariance (hd : 0 < d) (k : Fin (N n))
    (hk : k ≠ ⟨0,D.size_pos n⟩) (i j : Fin 4) (s : ProposalSample (N n) d) :
    D.centeredProposalQuadratic n ω k i j s = D.proposalQuadratic n ω k i j s -
      covarianceMatrix (D.eigenvalue n ω k / (d : ℝ)) i j := by
  rw [centeredProposalQuadratic, D.proposalQuadratic_mean_nonconstant n ω hd k hk i j]

/-- The constant eigenvector gives the deterministic rank-one mark, also
on proposals whose endpoints coincide. -/
theorem proposalQuadratic_constant (i j : Fin 4) (s : ProposalSample (N n) d) :
    D.proposalQuadratic n ω ⟨0,D.size_pos n⟩ i j s = 1 := by
  have hN : 0 < (N n : ℝ) := by exact_mod_cast D.size_pos n
  have hs : Real.sqrt (N n : ℝ) ^ 2 = N n := Real.sq_sqrt hN.le
  have hs0 : Real.sqrt (N n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  simp only [proposalQuadratic, D.constant_eigenvector]
  rw [← hs]
  field_simp

/-- Its actual centered quadratic mark is identically zero. -/
theorem centeredProposalQuadratic_constant (hd : 0 < d) (i j : Fin 4) (s : ProposalSample (N n) d) :
    D.centeredProposalQuadratic n ω ⟨0,D.size_pos n⟩ i j s = 0 := by
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  simp only [centeredProposalQuadratic, D.proposalQuadratic_constant n ω,
    integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul, sub_self]

end GeneralizedBulk.External.RegularSpectralData
