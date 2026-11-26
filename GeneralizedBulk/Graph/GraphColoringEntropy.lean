import GeneralizedBulk.Graph.GraphProfileEntropy
import GeneralizedBulk.Graph.ColoringEntropy

/-! The finite whole-coloring Shannon bound on the actual common good graph
profile event. It applies to every coloring distribution, hence to every
bounded signal and every scalar dilation of that signal. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration
open ColorProfiles Entropy Entropy.Finite

def graphNeighbor {N d : ℕ} (G : RegularGraph N d) (v : Fin N) (j : Fin d) : Fin N :=
  (canonicalPortLabeling G v j).val

theorem graphReferencePairing_word {N d q : ℕ} (G : RegularGraph N d) (c : VertexColoring N q) :
    configurationWord (graphReferencePairing G) c = orderedStarWord (graphNeighbor G) c := by
  funext v i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change c ((labelingPairing G (canonicalPortLabeling G)).val (v,j)).1 = c (graphNeighbor G v j)
    rw [labelingPairing_root]
    rfl

theorem graphSymmetricColoringCount_eq {N d q : ℕ} (G : RegularGraph N d) (S : StarWord d q → ℝ) :
    graphSymmetricColoringCount G S = symmetrizedColoringCount (graphNeighbor G) S := by
  unfold graphSymmetricColoringCount configurationSymmetricColoringCount SymmetricColoringFiber
  rw [Fintype.card_subtype]
  unfold symmetrizedColoringCount
  congr 1

theorem graph_coloring_entropy_profile_bound {N d q : ℕ} (G : RegularGraph N d)
    (p : VertexColoring N q → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1) :
    entropy p ≤ paletteLog N d q +
      ∑ profile : symmetrizedProfiles N d q,
        pushMass (symmetrizedProfileColor (graphNeighbor G)) p profile *
          Real.log (graphSymmetricColoringCount G profile.val) := by
  simp_rw [graphSymmetricColoringCount_eq]
  exact coloring_entropy_profile_bound (graphNeighbor G) p hp hsum

theorem pushMass_eq_zero_of_graphCount_zero {N d q : ℕ} (G : RegularGraph N d)
    (p : VertexColoring N q → ℝ) (profile : symmetrizedProfiles N d q)
    (hz : graphSymmetricColoringCount G profile.val = 0) :
    pushMass (symmetrizedProfileColor (graphNeighbor G)) p profile = 0 := by
  have hc := symmetrizedProfile_fiber_card (graphNeighbor G) profile
  rw [← graphSymmetricColoringCount_eq, hz] at hc
  have he := Finset.card_eq_zero.mp hc
  have hnone := Finset.filter_eq_empty_iff.mp he
  unfold pushMass
  apply Finset.sum_eq_zero
  intro c hc'
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hc'
  exact False.elim (hnone (Finset.mem_univ c) hc')

set_option maxHeartbeats 1000000 in
theorem graph_coloring_entropy_bound {N d q m : ℕ} (G : RegularGraph N d)
    (C t : ℝ) (M : ℕ) (hG : GraphProfileGood (q := q) (m := m) C t M G)
    (p : VertexColoring N q → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1) :
    entropy p ≤
      (∑ profile : symmetrizedProfiles N d q,
        pushMass (symmetrizedProfileColor (graphNeighbor G)) p profile *
          symmetricProfileExponent (N := N) (m := m) C profile.val) +
            3*paletteLog N d q+t+simplicityCost N d M := by
  apply (graph_coloring_entropy_profile_bound G p hp hsum).trans
  have hsumq : (∑ profile : symmetrizedProfiles N d q,
      pushMass (symmetrizedProfileColor (graphNeighbor G)) p profile) = 1 :=
    (pushMass_sum _ p).trans hsum
  calc
    _ ≤ paletteLog N d q +
        ∑ profile : symmetrizedProfiles N d q,
          pushMass (symmetrizedProfileColor (graphNeighbor G)) p profile *
            (symmetricProfileExponent (N := N) (m := m) C profile.val+
              2*paletteLog N d q+t+simplicityCost N d M) := by
      apply add_le_add_left
      apply Finset.sum_le_sum
      intro profile hprofile
      by_cases hz : graphSymmetricColoringCount G profile.val = 0
      · rw [pushMass_eq_zero_of_graphCount_zero G p profile hz]
        simp
      · have hpos : (0 : ℝ) < graphSymmetricColoringCount G profile.val := by
          exact_mod_cast Nat.pos_of_ne_zero hz
        exact mul_le_mul_of_nonneg_left ((Real.log_le_iff_le_exp hpos).mpr (hG profile.val))
          (pushMass_nonneg _ p hp profile)
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hsumq,one_mul]
      ring

end GeneralizedBulk.Graph.Configuration
