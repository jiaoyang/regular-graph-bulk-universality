import GaussianWave.BS.GaussianSamplerMoments
import GaussianWave.BS.GraphGaussianGoodWindow

/-! The actual finite-graph Gaussian block rule has root variance one at
good roots and a fixed-block bound everywhere. Hence its expected empirical
root energy is at most one plus a vanishing bad-root error. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS
open Reused.Graph Lower

/-- A fixed-block bound; it is independent of graph size and root. -/
def radialGraphCollisionBound (d : ℕ) (x : ℝ) (b : ℕ) : ℝ :=
  ((radialGaussianBlockCoefficient d x b none).sum (fun _ c => |c|))^2

theorem graphRadialGaussianCoefficient_norm_le {N m : ℕ}
    (G : RegularGraph N (m+2)) (x : ℝ) (b : ℕ) (v : Fin N) :
    finsuppPairing (graphRadialGaussianCoefficient G.val (m+2) x b v)
      (graphRadialGaussianCoefficient G.val (m+2) x b v) ≤ radialGraphCollisionBound (m+2) x b := by
  let seed : VertexCoverSeed N m 0 := (v,1,fun _ => default)
  have he := graphRadialGaussianCoefficient_cover G 0 seed x b none
  change Finsupp.mapDomain (infiniteVertexGraphCover G 0 seed)
    (radialGaussianBlockCoefficient (m+2) x b none) =
      graphRadialGaussianCoefficient G.val (m+2) x b v at he
  rw [← he]
  exact finsuppPairing_mapDomain_le_l1_sq _ _

/-- The exact tree normalization survives at every actual good root. -/
theorem graphRadialGaussianCoefficient_norm_of_good {N m : ℕ}
    (G : RegularGraph N (m+2)) (x : ℝ) (b : ℕ) (v : Fin N)
    (hgood : GoodVertexCoverRoot G (b+1) v) :
    finsuppPairing (graphRadialGaussianCoefficient G.val (m+2) x b v)
      (graphRadialGaussianCoefficient G.val (m+2) x b v)=1 := by
  let seed : VertexCoverSeed N m (0+b+1) := (v,1,fun _ => default)
  have hlaw := graphRadialGaussianLaw_window_of_good G 0 b seed x
    (fun _ : Unit => (none : RegularTreeVertex (m+2))) (by intro j; simp [regularTreeDepth])
    (by simpa only [Nat.zero_add] using hgood)
  change finiteSupportGaussianLaw (fun _ : Unit => graphRadialGaussianCoefficient G.val (m+2) x b v) =
    finiteSupportGaussianLaw (fun _ : Unit => radialGaussianBlockCoefficient (m+2) x b none) at hlaw
  have hm := congrArg (fun P : Measure (Unit → ℝ) => ∫ z,(z ())^2 ∂P) hlaw
  simp only [finiteSupportGaussianLaw_second] at hm
  exact hm.trans (radialGaussianBlockCoefficient_norm (m+2) (by omega) x b none)

/-- Exact iid-source variance formula and the root good/bad estimate. -/
theorem integral_graphRadialGaussianRootEnergy_le {N m : ℕ}
    (G : RegularGraph N (m+2)) (hN : 0 < N) (x : ℝ) (b : ℕ) :
    (∫ ξ,(N : ℝ)⁻¹*∑ v : Fin N,
      (finiteSupportGaussianSample (graphRadialGaussianCoefficient G.val (m+2) x b) ξ v)^2
      ∂gaussianLabelLaw (Fin N)) ≤
      1+radialGraphCollisionBound (m+2) x b*((N : ℝ)⁻¹*badVertexCoverRootCount G (b+1)) := by
  have hi (v : Fin N) := integrable_finiteSupportGaussianSample_pow
    (graphRadialGaussianCoefficient G.val (m+2) x b) v 2
  rw [integral_const_mul,integral_finset_sum _ (fun v _ => hi v)]
  simp_rw [integral_finiteSupportGaussianSample_sq]
  have hv (v : Fin N) : finsuppPairing (graphRadialGaussianCoefficient G.val (m+2) x b v)
      (graphRadialGaussianCoefficient G.val (m+2) x b v) ≤
      1+radialGraphCollisionBound (m+2) x b*(if GoodVertexCoverRoot G (b+1) v then 0 else 1) := by
    by_cases hg : GoodVertexCoverRoot G (b+1) v
    · simp only [if_pos hg,mul_zero,add_zero,graphRadialGaussianCoefficient_norm_of_good G x b v hg,le_refl]
    · simp only [if_neg hg,mul_one]
      exact (graphRadialGaussianCoefficient_norm_le G x b v).trans (by linarith)
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun v _ => hv v))
    (show 0 ≤ (N : ℝ)⁻¹ by positivity)
  apply hsum.trans_eq
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,← Finset.mul_sum,one_mul,mul_one,badVertexCoverRootCount]
  rw [mul_add,inv_mul_cancel₀ hNr]
  ring

/-- Along genuine locally tree-like graphs the expected added root energy
has limsup at most one, at each fixed block radius. -/
theorem eventually_integral_graphRadialGaussianRootEnergy_lt
    (N : ℕ → ℕ) (m : ℕ) (G : ∀ n,RegularGraph (N n) (m+2)) (hN : ∀ n,0 < N n)
    (x : ℝ) (b : ℕ)
    (hbad : Tendsto (fun n => (N n : ℝ)⁻¹*badVertexCoverRootCount (G n) (b+1))
      atTop (𝓝 0)) {M : ℝ} (hM : 1 < M) :
    ∀ᶠ n in atTop,
      (∫ ξ,(N n : ℝ)⁻¹*∑ v : Fin (N n),
        (finiteSupportGaussianSample (graphRadialGaussianCoefficient (G n).val (m+2) x b) ξ v)^2
        ∂gaussianLabelLaw (Fin (N n))) < M := by
  have ht : Tendsto (fun n => 1+radialGraphCollisionBound (m+2) x b*
      ((N n : ℝ)⁻¹*badVertexCoverRootCount (G n) (b+1))) atTop (𝓝 1) := by
    simpa only [mul_zero,add_zero] using tendsto_const_nhds.add (hbad.const_mul _)
  filter_upwards [ht.eventually (gt_mem_nhds hM)] with n hn
  exact (integral_graphRadialGaussianRootEnergy_le (G n) (hN n) x b).trans_lt hn

end GaussianWave.BS
