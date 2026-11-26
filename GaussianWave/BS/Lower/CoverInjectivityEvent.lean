import GaussianWave.BS.Lower.LocalCoverCycles

/-! A genuine uniform-simple-regular-graph event on which almost every root
has injective finite cover images for every choice of the cover ordering.
The estimate is obtained from actual near-cycle counts, not from a local
tree-likeness assumption. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 800000

namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Graph

variable {N d : ℕ}

def NearShortCycle (G : RegularGraph N d) (R L : ℕ) (v : Fin N) : Prop :=
  ∃ n : Fin L,NearPattern (SimpleGraph.cycleGraph (n.val+3)) G R v

def nearShortCycleCount (G : RegularGraph N d) (R L : ℕ) : ℝ :=
  ∑ v : Fin N,if NearShortCycle G R L v then 1 else 0

def shortCycleMassBound (d R L : ℕ) : ℝ :=
  ∑ n : Fin L,((n.val+3)*regularBallBound d R : ℕ)*(2*(d : ℝ))^(n.val+3)

theorem nearShortCycleCount_nonneg (G : RegularGraph N d) (R L : ℕ) :
    0 ≤ nearShortCycleCount G R L :=
  Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem nearShortCycleCount_le (G : RegularGraph N d) (R L : ℕ) :
    nearShortCycleCount G R L ≤
      ∑ n : Fin L,nearPatternCount (SimpleGraph.cycleGraph (n.val+3)) G R := by
  calc
    _ ≤ ∑ v : Fin N,∑ n : Fin L,
        if NearPattern (SimpleGraph.cycleGraph (n.val+3)) G R v then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro v hv
      dsimp only
      split_ifs with h
      · obtain ⟨n,hn⟩ := h
        have hs := Finset.single_le_sum (f := fun j : Fin L =>
          if NearPattern (SimpleGraph.cycleGraph (j.val+3)) G R v then (1 : ℝ) else 0)
          (fun j _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ n)
        simpa only [if_pos hn] using hs
      · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    _ = _ := Finset.sum_comm

theorem integral_nearCycleCount_le [Nonempty (RegularGraph N d)]
    (n R : ℕ) (hN : 0 < N) (hd : 0 < d)
    (hsize : 2*(4*d+2*d^2+2*(n+3)) ≤ N*d) :
    (∫ G,nearPatternCount (SimpleGraph.cycleGraph (n+3)) G R ∂regularGraphLaw N d) ≤
      ((n+3)*regularBallBound d R : ℕ)*(2*(d : ℝ))^(n+3) := by
  letI := regularGraphLaw_isProbability N d
  calc
    _ ≤ ∫ G,((n+3)*regularBallBound d R : ℕ)*patternCount (SimpleGraph.cycleGraph (n+3)) G
        ∂regularGraphLaw N d := integral_mono Integrable.of_finite Integrable.of_finite
          (fun G => nearPatternCount_le _ G R)
    _ = ((n+3)*regularBallBound d R : ℕ)*
        (∫ G,patternCount (SimpleGraph.cycleGraph (n+3)) G ∂regularGraphLaw N d) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_cycleCount_le n hN hd hsize) (by positivity)

theorem integral_nearShortCycleCount_le [Nonempty (RegularGraph N d)]
    (R L : ℕ) (hN : 0 < N) (hd : 0 < d)
    (hsize : 2*(4*d+2*d^2+2*(L+2)) ≤ N*d) :
    (∫ G,nearShortCycleCount G R L ∂regularGraphLaw N d) ≤ shortCycleMassBound d R L := by
  letI := regularGraphLaw_isProbability N d
  calc
    _ ≤ ∫ G,∑ n : Fin L,nearPatternCount (SimpleGraph.cycleGraph (n.val+3)) G R
        ∂regularGraphLaw N d := integral_mono Integrable.of_finite Integrable.of_finite
          (fun G => nearShortCycleCount_le G R L)
    _ = ∑ n : Fin L,∫ G,nearPatternCount (SimpleGraph.cycleGraph (n.val+3)) G R
        ∂regularGraphLaw N d := integral_finset_sum _ (fun _ _ => Integrable.of_finite)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      apply integral_nearCycleCount_le n.val R hN hd
      have hnl := n.isLt
      omega

/-- For fixed radius and cycle cutoff the exceptional root mass is `O(1/N)`
under the actual uniform law on finite simple regular graphs. -/
theorem near_short_cycle_mass_probability [Nonempty (RegularGraph N d)]
    (R L : ℕ) (hN : 0 < N) (hd : 0 < d)
    (hsize : 2*(4*d+2*d^2+2*(L+2)) ≤ N*d) (ε : ℝ) (hε : 0 < ε) :
    (regularGraphLaw N d).real {G | ε*(N : ℝ) ≤ nearShortCycleCount G R L} ≤
      shortCycleMassBound d R L/(ε*(N : ℝ)) := by
  letI := regularGraphLaw_isProbability N d
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun G : RegularGraph N d => nearShortCycleCount_nonneg G R L))
    (Integrable.of_finite : Integrable (fun G => nearShortCycleCount G R L) (regularGraphLaw N d))
    (ε*(N : ℝ))
  apply (le_div_iff₀ (mul_pos hε (by exact_mod_cast hN))).mpr
  simpa only [mul_comm] using hm.trans (integral_nearShortCycleCount_le R L hN hd hsize)

/-- Every finite cover ordering at this root has an injective vertex image. -/
def GoodVertexCoverRoot {m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) (v : Fin N) : Prop :=
  ∀ seed : VertexCoverSeed N m k,seed.1=v → Function.Injective (vertexGraphCover G k seed)

def badVertexCoverRootCount {m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) : ℝ :=
  ∑ v : Fin N,if GoodVertexCoverRoot G k v then 0 else 1

theorem badVertexCoverRootCount_nonneg {m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) :
    0 ≤ badVertexCoverRootCount G k :=
  Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem badVertexCoverRootCount_le {m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) :
    badVertexCoverRootCount G k ≤ nearShortCycleCount G (k+1) (2*(k+1)) := by
  apply Finset.sum_le_sum
  intro v hv
  dsimp only
  by_cases hg : GoodVertexCoverRoot G k v
  · simp only [if_pos hg]
    split_ifs <;> norm_num
  · have hb : NearShortCycle G (k+1) (2*(k+1)) v := by
      unfold GoodVertexCoverRoot at hg
      push_neg at hg
      obtain ⟨seed,hroot,hseed⟩ := hg
      obtain ⟨n,hn,hnear⟩ := finite_vertex_cover_collision_near_short_cycle G k seed hseed
      refine ⟨⟨n,by omega⟩,?_⟩
      simpa only [hroot] using hnear
    simp only [if_neg hg,if_pos hb,le_refl]

/-- A concrete graph event valid simultaneously for every root port ordering
and every internal cover ordering. No union over cover seeds is needed. -/
theorem bad_vertex_cover_mass_probability {m : ℕ} [Nonempty (RegularGraph N (m+2))]
    (k : ℕ) (hN : 0 < N)
    (hsize : 2*(4*(m+2)+2*(m+2)^2+2*(2*(k+1)+2)) ≤ N*(m+2))
    (ε : ℝ) (hε : 0 < ε) :
    (regularGraphLaw N (m+2)).real {G | ε*(N : ℝ) ≤ badVertexCoverRootCount G k} ≤
      shortCycleMassBound (m+2) (k+1) (2*(k+1))/(ε*(N : ℝ)) := by
  letI := regularGraphLaw_isProbability N (m+2)
  calc
    _ ≤ (regularGraphLaw N (m+2)).real {G | ε*(N : ℝ) ≤ nearShortCycleCount G (k+1) (2*(k+1))} :=
      measureReal_mono (fun G hG => hG.trans (badVertexCoverRootCount_le G k))
    _ ≤ _ := near_short_cycle_mass_probability (k+1) (2*(k+1)) hN (by omega) hsize ε hε

/-- Along every admissible size sequence, the proportion of roots admitting
any colliding depth-`k` cover goes to zero in probability. -/
theorem bad_vertex_cover_fraction_tendsto_zero (m k : ℕ) (Ns : ℕ → ℕ)
    (hNinf : Tendsto Ns atTop atTop)
    (hgraphs : ∀ n,Nonempty (RegularGraph (Ns n) (m+2))) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (regularGraphLaw (Ns n) (m+2)).real
      {G | ε*(Ns n : ℝ) ≤ badVertexCoverRootCount G k}) atTop (𝓝 0) := by
  have hNr : Tendsto (fun n => (Ns n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNinf
  have hbound : Tendsto (fun n => shortCycleMassBound (m+2) (k+1) (2*(k+1))/
      (ε*(Ns n : ℝ))) atTop (𝓝 0) :=
    (hNr.const_mul_atTop hε).const_div_atTop _
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => measureReal_nonneg)) _ hbound
  have hevent := hNinf.eventually (eventually_ge_atTop
    (2*(4*(m+2)+2*(m+2)^2+2*(2*(k+1)+2))+1))
  filter_upwards [hevent] with n hn
  letI := hgraphs n
  apply bad_vertex_cover_mass_probability k (by omega) _ ε hε
  calc
    _ ≤ Ns n := by omega
    _ ≤ Ns n*(m+2) := Nat.le_mul_of_pos_right _ (by omega)

end GaussianWave.BS.Lower
