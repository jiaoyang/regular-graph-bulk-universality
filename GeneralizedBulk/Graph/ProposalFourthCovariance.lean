import GeneralizedBulk.Graph.ProposalQuadraticMean
import GeneralizedBulk.Graph.EmpiricalFourthMoments

/-!
# Physical proposal covariance from one-edge fourth moments

Two oriented edges are sampled independently before acceptance. Within-edge
covariances inherit the actual star fourth estimate; cross-edge entries have
exact diagonal covariance by eigenvector orthogonality.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def singleEdgeQuadratic (k : Fin (N n)) (i j : Fin 2) (a : Fin (N n) × Fin d) : ℝ :=
  (N n : ℝ) * D.eigenvector n ω k (D.proposalEndpoint n ω a i) *
    D.eigenvector n ω k (D.proposalEndpoint n ω a j)

def centeredSingleEdgeQuadratic (k : Fin (N n)) (i j : Fin 2)
    (a : Fin (N n) × Fin d) : ℝ :=
  D.singleEdgeQuadratic n ω k i j a - edgeCovariance (D.eigenvalue n ω k / d) i j

/-- Independent endpoints make the cross-edge quadratic raw covariance
exactly the eigenchannel Kronecker delta. -/
theorem crossEdgeQuadratic_product_integral (hd : 0 < d)
    (k l : Fin (N n)) (i j : Fin 2) :
    (∫ s : ProposalSample (N n) d,
      ((N n : ℝ) * D.eigenvector n ω k (D.proposalEndpoint n ω s.1 i) *
        D.eigenvector n ω k (D.proposalEndpoint n ω s.2 j)) *
      ((N n : ℝ) * D.eigenvector n ω l (D.proposalEndpoint n ω s.1 i) *
        D.eigenvector n ω l (D.proposalEndpoint n ω s.2 j))
      ∂uniformOrientedProposals (N n) d) = if k = l then 1 else 0 := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  letI := finiteUniform_isProbability (Fin (N n))
  let f : Fin (N n) → ℝ := fun v => (N n : ℝ) *
    (D.eigenvector n ω k v * D.eigenvector n ω l v)
  let F : Fin (N n) × Fin (N n) → ℝ := fun p => f p.1 * f p.2
  have hmap := D.crossProposalEndpoints_uniform_law n ω hd i j
  have h := congrArg (fun mu : Measure (Fin (N n) × Fin (N n)) => ∫ p, F p ∂mu) hmap
  dsimp only at h
  rw [integral_map (measurable_of_finite _).aemeasurable
    (measurable_of_finite _).aestronglyMeasurable] at h
  have heq : (fun s : ProposalSample (N n) d =>
      ((N n : ℝ) * D.eigenvector n ω k (D.proposalEndpoint n ω s.1 i) *
        D.eigenvector n ω k (D.proposalEndpoint n ω s.2 j)) *
      ((N n : ℝ) * D.eigenvector n ω l (D.proposalEndpoint n ω s.1 i) *
        D.eigenvector n ω l (D.proposalEndpoint n ω s.2 j))) =
      (fun s => F (D.proposalEndpoint n ω s.1 i,D.proposalEndpoint n ω s.2 j)) := by
    funext s
    dsimp [F,f]
    ring
  rw [heq,h]
  dsimp [F]
  rw [integral_prod_mul,integral_finiteUniform]
  have hsum : (∑ v, f v) = (N n : ℝ) * (if k = l then 1 else 0) := by
    dsimp [f]
    rw [← Finset.mul_sum,D.orthonormal]
  rw [hsum]
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  split_ifs <;> field_simp <;> ring

/-- A one-edge fourth covariance estimate transfers to every physical
four-endpoint covariance. Cross-edge entries require no fourth estimate. -/
theorem proposal_covariance_le_of_single_edge_covariances (hd : 0 < d)
    (k l : Fin (N n)) (hk : k ≠ ⟨0,D.size_pos n⟩) (hl : l ≠ ⟨0,D.size_pos n⟩)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hsingle : ∀ a b : Fin 2,
      |∫ t, D.centeredSingleEdgeQuadratic n ω k a b t *
        D.centeredSingleEdgeQuadratic n ω l a b t ∂finiteUniform (Fin (N n) × Fin d)| ≤
        2 * (if k = l then 1 else 0) + epsilon)
    (i j : Fin 4) :
    |∫ s, D.centeredProposalQuadratic n ω k i j s *
      D.centeredProposalQuadratic n ω l i j s ∂uniformOrientedProposals (N n) d| ≤
      2 * (if k = l then 1 else 0) + epsilon := by
  have hfirst (a b : Fin 2) :
      |∫ s : ProposalSample (N n) d,
        D.centeredSingleEdgeQuadratic n ω k a b s.1 *
        D.centeredSingleEdgeQuadratic n ω l a b s.1 ∂uniformOrientedProposals (N n) d| ≤
        2 * (if k = l then 1 else 0) + epsilon := by
    rw [D.firstEdge_integral n hd (fun t =>
      D.centeredSingleEdgeQuadratic n ω k a b t * D.centeredSingleEdgeQuadratic n ω l a b t)]
    exact hsingle a b
  have hsecond (a b : Fin 2) :
      |∫ s : ProposalSample (N n) d,
        D.centeredSingleEdgeQuadratic n ω k a b s.2 *
        D.centeredSingleEdgeQuadratic n ω l a b s.2 ∂uniformOrientedProposals (N n) d| ≤
        2 * (if k = l then 1 else 0) + epsilon := by
    rw [D.secondEdge_integral n hd (fun t =>
      D.centeredSingleEdgeQuadratic n ω k a b t * D.centeredSingleEdgeQuadratic n ω l a b t)]
    exact hsingle a b
  have hcross (a b : Fin 2) :
      |∫ s : ProposalSample (N n) d,
        ((N n : ℝ) * D.eigenvector n ω k (D.proposalEndpoint n ω s.1 a) *
          D.eigenvector n ω k (D.proposalEndpoint n ω s.2 b)) *
        ((N n : ℝ) * D.eigenvector n ω l (D.proposalEndpoint n ω s.1 a) *
          D.eigenvector n ω l (D.proposalEndpoint n ω s.2 b))
        ∂uniformOrientedProposals (N n) d| ≤ 2 * (if k = l then 1 else 0) + epsilon := by
    rw [D.crossEdgeQuadratic_product_integral n ω hd k l a b]
    split_ifs <;> simp only [abs_one,abs_zero] <;> linarith
  have hback (a b : Fin 2) :
      |∫ s : ProposalSample (N n) d,
        ((N n : ℝ) * D.eigenvector n ω k (D.proposalEndpoint n ω s.2 a) *
          D.eigenvector n ω k (D.proposalEndpoint n ω s.1 b)) *
        ((N n : ℝ) * D.eigenvector n ω l (D.proposalEndpoint n ω s.2 a) *
          D.eigenvector n ω l (D.proposalEndpoint n ω s.1 b))
        ∂uniformOrientedProposals (N n) d| ≤ 2 * (if k = l then 1 else 0) + epsilon := by
    convert hcross b a using 1
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => by ring)
  simp_rw [D.centeredProposalQuadratic_eq_covariance n ω hd k hk,
    D.centeredProposalQuadratic_eq_covariance n ω hd l hl]
  rw [covarianceMatrix_eq,covarianceMatrix_eq]
  fin_cases i <;> fin_cases j <;>
    norm_num [proposalQuadratic,proposalEndpoints] <;>
    first
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hfirst 0 0
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hfirst 0 1
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hfirst 1 0
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hfirst 1 1
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hsecond 0 0
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hsecond 0 1
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hsecond 1 0
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hsecond 1 1
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hcross 0 0
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hcross 0 1
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hcross 1 0
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hcross 1 1
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hback 0 0
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hback 0 1
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hback 1 0
      | simpa [centeredSingleEdgeQuadratic,singleEdgeQuadratic,proposalEndpoint,edgeCovariance] using hback 1 1

end GeneralizedBulk.External.RegularSpectralData
