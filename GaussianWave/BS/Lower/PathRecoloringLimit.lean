import GaussianWave.BS.Lower.PathRecoloringSampling
import GaussianWave.BS.Lower.CoverRecoloringLimit
import GaussianWave.BS.Lower.LocalRecodingLimit

/-! The actual finite-radius path-code entropy lower bound from a weak
marked graph-cover limit. All counting and recoloring errors vanish; marker
cancellation subsequently recovers the unlabeled finite-window entropies. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 1200000
namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration
open GaussianWave.BS.Reused.Graph.ColorProfiles
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

theorem weak_mean_pathRecoded_starProfile {m q r : ℕ} (N : ℕ → ℕ)
    (G : ∀ n,RegularGraph (N n) (m+2)) (k : ℕ) (x : ∀ n,Fin (N n) → Fin r → ℝ)
    (ν : Measure ((Fin r × VertexBallVertex (m+2) k) → ℝ))
    (hweak : WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (fun a v => x n v a)) ν)
    (hbad : Tendsto (fun n => (N n : ℝ)⁻¹*badVertexCoverRootCount (G n) k) atTop (𝓝 0))
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b=1)
    (hφc : ∀ b,Continuous (fun y => φ y b))
    (s : StarWord (m+2) (pathNeighborhoodPalette q k)) :
    Tendsto (fun n => meanProfile
      (independentColoringLaw (fun v => φ (x n v)) (fun v => hφ0 (x n v)) (fun v => hφ1 (x n v)))
      (fun c => graphStarProfile (G n) (pathNeighborhoodRecoding (G n) k c)) s) atTop
        (𝓝 (pushMass (vertexPathStarCode (m+2) q k) (windowRecolorMass ν φ) s)) := by
  simp_rw [mean_pathRecoded_starProfile]
  unfold pushMass
  exact tendsto_finset_sum _ (fun w _ => weak_actualCover_recolorMass N G k x ν hweak hbad φ hφ0 hφ1 hφc w)

def windowRootEntropyTest {r : ℕ} {S F : Type*} [Fintype F]
    (φ : (Fin r → ℝ) → F → ℝ) (o : S) (y : (Fin r × S) → ℝ) : ℝ :=
  entropy (φ (fun a => y (a,o)))

def windowRootEntropyBCF {r : ℕ} {S F : Type*} [Fintype F]
    (φ : (Fin r → ℝ) → F → ℝ) (o : S)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b=1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) :
    BoundedContinuousFunction ((Fin r × S) → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (windowRootEntropyTest φ o)
    (by
      unfold windowRootEntropyTest entropy
      exact continuous_finset_sum _ (fun b _ => Real.continuous_negMulLog.comp
        ((hφc b).comp (continuous_pi (fun a => continuous_apply (a,o))))))
    (Fintype.card F) (fun y => by
      have hn (b : F) : 0 ≤ Real.negMulLog (φ (fun a => y (a,o)) b) :=
        Real.negMulLog_nonneg (hφ0 _ _) (profile_coordinate_le_one _ (hφ0 _) (hφ1 _) b)
      have h0 : 0 ≤ windowRootEntropyTest φ o y := Finset.sum_nonneg (fun b _ => hn b)
      rw [Real.norm_eq_abs,abs_of_nonneg h0]
      calc
        _ ≤ ∑ _b : F,(1 : ℝ) := Finset.sum_le_sum (fun b _ =>
          (negMulLog_le_one_sub _ (hφ0 _ _)).trans (by linarith [hφ0 (fun a => y (a,o)) b]))
        _ = _ := by simp)

theorem weak_cover_root_entropy {m q r : ℕ} (N : ℕ → ℕ)
    (G : ∀ n,RegularGraph (N n) (m+2)) (k : ℕ) (x : ∀ n,Fin (N n) → Fin r → ℝ)
    (ν : Measure ((Fin r × VertexBallVertex (m+2) k) → ℝ))
    (hweak : WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (fun a v => x n v a)) ν)
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b=1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) :
    Tendsto (fun n => (N n : ℝ)⁻¹*(∑ v,entropy (φ (x n v)))) atTop
      (𝓝 (∫ y,windowRootEntropyTest φ (vertexBallRoot (m+2) k) y ∂ν)) := by
  have h := hweak (windowRootEntropyBCF φ (vertexBallRoot (m+2) k) hφ0 hφ1 hφc)
  change Tendsto (fun n => ∫ y,windowRootEntropyTest φ (vertexBallRoot (m+2) k) y
    ∂finiteVertexCoverLaw (G n) k (fun a v => x n v a)) atTop
      (𝓝 (∫ y,windowRootEntropyTest φ (vertexBallRoot (m+2) k) y ∂ν)) at h
  have he (n : ℕ) : (∫ y,windowRootEntropyTest φ (vertexBallRoot (m+2) k) y
      ∂finiteVertexCoverLaw (G n) k (fun a v => x n v a))=
        (N n : ℝ)⁻¹*(∑ v,entropy (φ (x n v))) :=
    integral_finiteVertexCoverLaw_root (G n) k (fun a v => x n v a) (fun z => entropy (φ z))
  simpa only [he] using h

/-- Source randomized entropy lower bound for the concrete neighborhood
codes at every fixed radius, derived from actual finite graph counting. -/
theorem randomized_path_code_entropy_lower_of_graph_limit {m q r : ℕ} (hq : 0 < q)
    (N E : ℕ → ℕ) (hN : ∀ n,0 < N n) (hNinf : Tendsto N atTop atTop)
    (hNE : ∀ n,N n*(m+2)=2*E n) (G : ∀ n,RegularGraph (N n) (m+2))
    (k : ℕ) (x : ∀ n,Fin (N n) → Fin r → ℝ) (C : ℝ) (M : ℕ)
    (hG : ∀ᶠ n in atTop,GraphProfileGood (q := pathNeighborhoodPalette q k) (m := E n)
      C (Real.sqrt (N n : ℝ)) M (G n))
    (ν : Measure ((Fin r × VertexBallVertex (m+2) k) → ℝ))
    (hweak : WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (fun a v => x n v a)) ν)
    (hbad : Tendsto (fun n => (N n : ℝ)⁻¹*badVertexCoverRootCount (G n) k) atTop (𝓝 0))
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b=1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) :
    (∫ y,windowRootEntropyTest φ (vertexBallRoot (m+2) k) y ∂ν) ≤
      entropy (pushMass (vertexPathStarCode (m+2) q k) (windowRecolorMass ν φ))-
      (((m+2 : ℕ) : ℝ)/2)*entropy (edgeMassOfStar
        (pushMass (vertexPathStarCode (m+2) q k) (windowRecolorMass ν φ))) := by
  apply local_recoding_entropy_lower_of_profile_limits (by omega) hq (pathNeighborhoodPalette_pos q k)
    N E hN hNinf hNE G k (fun n => pathNeighborhoodRecoding (G n) k)
    (fun n => pathNeighborhoodRecoding_local (G n) k) (pathNeighborhoodDecoder q k hq)
    (fun n c v => pathNeighborhoodRecoding_decode (G n) k hq c v)
    (fun n v => φ (x n v)) (fun n v => hφ0 (x n v)) (fun n v => hφ1 (x n v)) C M hG
  · exact fun s => weak_mean_pathRecoded_starProfile N G k x ν hweak hbad φ hφ0 hφ1 hφc s
  · exact weak_cover_root_entropy N G k x ν hweak φ hφ0 hφ1 hφc

end GaussianWave.BS.Lower
