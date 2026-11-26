import GaussianWave.BS.TreeBallDistances
import GaussianWave.BS.EdgeBallEmbedding
import GaussianWave.BS.GaussianEdgeBallKernel
import GaussianWave.BS.GaussianTreeWave

/-! Actual edge-ball distances and identification of the edge marginals
of the constructed whole Gaussian-wave reference. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GaussianWave.BS

theorem treeHalfDecode_cross_dist (q : ℕ) (w z : List (Fin q)) :
    (regularWordTree (q+1)).dist (treeHalfDecode q (false,w.reverse))
      (treeHalfDecode q (true,z.reverse)) = w.length+z.length+1 := by
  cases w with
  | nil =>
    change (regularWordTree (q+1)).dist none (some (0,z.reverse)) = _
    rw [regularTree_dist_root]
    simp [regularTreeDepth]
  | cons a w =>
    change (regularWordTree (q+1)).dist (branchWordEmbedding q (a::w)) (some (0,z.reverse)) = _
    rw [branchWordEmbedding_cons,regularTree_dist_distinct_branches _ _ _ _ _ (Fin.succ_ne_zero a)]
    simp only [List.length_reverse,List.length_cons]
    omega

theorem edgeBallEmbedding_dist (m k : ℕ) (v w : EdgeBallVertex (m+2) k) :
    (regularWordTree (m+2)).dist (edgeBallEmbedding m k v) (edgeBallEmbedding m k w) =
      edgeBallDistance m k v w := by
  rcases v with ⟨b,v⟩
  rcases w with ⟨c,w⟩
  cases b <;> cases c
  · change (regularWordTree (m+2)).dist
      (branchWordEmbedding (m+1) (branchPath (m+1) k v))
      (branchWordEmbedding (m+1) (branchPath (m+1) k w)) = branchDistance (m+1) k v w
    rw [branchWordEmbedding_dist,branchDistance_eq_word]
  · change (regularWordTree (m+2)).dist
      (treeHalfDecode (m+1) (false,(branchPath (m+1) k v).reverse))
      (treeHalfDecode (m+1) (true,(branchPath (m+1) k w).reverse)) =
        branchDepth (m+1) k v+branchDepth (m+1) k w+1
    rw [treeHalfDecode_cross_dist,branchPath_length,branchPath_length]
  · rw [SimpleGraph.dist_comm]
    change (regularWordTree (m+2)).dist
      (treeHalfDecode (m+1) (false,(branchPath (m+1) k w).reverse))
      (treeHalfDecode (m+1) (true,(branchPath (m+1) k v).reverse)) =
        branchDepth (m+1) k v+branchDepth (m+1) k w+1
    rw [treeHalfDecode_cross_dist,branchPath_length,branchPath_length]
    omega
  · change (regularWordTree (m+2)).dist
      (some (0,(branchPath (m+1) k v).reverse))
      (some (0,(branchPath (m+1) k w).reverse)) = branchDistance (m+1) k v w
    rw [regularTree_dist_same_branch (m+1),branchWordEmbedding_dist,branchDistance_eq_word]

theorem gaussianTreeProcessLaw_edge (m k : ℕ) (energy : ℝ) (he : |energy| < (m+2 : ℝ)) :
    Measure.map (fun z : RegularTreeVertex (m+2) → ℝ => fun v => z (edgeBallEmbedding m k v))
      (gaussianTreeProcessLaw m energy : Measure _) = edgeGaussianBallLaw m k energy := by
  letI : IsProbabilityMeasure (Measure.map
      (fun z : RegularTreeVertex (m+2) → ℝ => fun v => z (edgeBallEmbedding m k v))
      (gaussianTreeProcessLaw m energy : Measure _)) :=
    isProbabilityMeasure_map (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).aemeasurable
  have h := gaussianTreeProcessLaw_finite_wave_kernel m energy he (edgeBallEmbedding m k)
  have hC : (fun i j => sphericalCovariance (m+2) energy
      ((regularWordTree (m+2)).dist (edgeBallEmbedding m k i) (edgeBallEmbedding m k j))) =
      (fun i j => sphericalCovariance (m+2) energy (edgeBallDistance m k i j)) := by
    funext i j
    rw [edgeBallEmbedding_dist]
  rw [hC] at h
  apply measure_eq_of_linear_characteristic
  intro t
  exact (h t).trans (edgeGaussianBallLaw_wave_kernel m k energy he t).symm

end GaussianWave.BS
