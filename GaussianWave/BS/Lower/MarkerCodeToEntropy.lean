import GaussianWave.BS.Lower.BallMarkerCancellation
import GaussianWave.BS.Lower.ProcessBallSymmetry
import GaussianWave.BS.Lower.PathCodeRelabeling

/-! The proved finite-tree marker cancellation converts neighborhood-code
entropy inequalities to the ordinary finite-window randomized lower bound.
The code inequalities are an intermediate input discharged by graph
counting in `AllRadiusEntropyLower`. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 1400000
namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

local instance markerTransferCDecidableEq (m k : ℕ) : DecidableEq (VertexBallVertex (m+2) k) := Classical.decEq _
local instance markerTransferEDecidableEq (m k : ℕ) : DecidableEq (EdgeBallVertex (m+2) k) := Classical.decEq _

theorem marker_code_lower_to_entropy {q r : ℕ} (m k : ℕ) (hq : 0 < q)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure P]
    (hP : ∀ e : regularWordTree (m+2) ≃g regularWordTree (m+2),
      Measure.map (fun z av => z (av.1,e av.2)) P=P)
    (hcodes : ∀ (Q : ℕ),0 < Q → ∀ θ : (Fin r → ℝ) → Fin Q → ℝ,
      (∀ b,Continuous (fun x => θ x b)) → (∀ x b,0 ≤ θ x b) → (∀ x,∑ b,θ x b=1) →
      (∫ x,entropy (θ x) ∂rootProcessWindow m P) ≤
        entropy (pushMass (centerPathCodes (GaussianWave.BS.vertexBallGraph (m+2) k) k (vertexBallStarCenter (m+2) k))
          (windowRecolorMass (vertexProcessWindow m k P) θ))-
        (((m+2 : ℕ) : ℝ)/2)*entropy (pushMass (centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k))
          (windowRecolorMass (edgeProcessWindow m k P) θ)))
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφc : ∀ b,Continuous (fun x => φ x b)) (hφ0 : ∀ x b,0 ≤ φ x b) (hφ1 : ∀ x,∑ b,φ x b=1) :
    (∫ x,entropy (φ x) ∂rootProcessWindow m P) ≤
      entropy (windowRecolorMass (vertexProcessWindow m k P) φ)-
      (((m+2 : ℕ) : ℝ)/2)*entropy (windowRecolorMass (edgeProcessWindow m k P) φ) := by
  let pC := windowRecolorMass (vertexProcessWindow m k P) φ
  let pE := windowRecolorMass (edgeProcessWindow m k P) φ
  let left := ∫ x,entropy (φ x) ∂rootProcessWindow m P
  let fC (n : ℕ) := entropy (pushMass
    (centerPathCodes (GaussianWave.BS.vertexBallGraph (m+2) k) k (vertexBallStarCenter (m+2) k))
    (markerDecoratedMass pC (n+1)))
  let fE (n : ℕ) := entropy (pushMass (centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k))
    (markerDecoratedMass pE (n+1)))
  have hlim := ball_path_codes_marker_entropy_cancellation m k pC pE
    (windowRecolorMass_nonneg (vertexProcessWindow m k P) φ hφ0) (windowRecolorMass_nonneg (edgeProcessWindow m k P) φ hφ0)
    (windowRecolorMass_sum (vertexProcessWindow m k P) φ hφ0 hφ1 hφc)
    (windowRecolorMass_sum (edgeProcessWindow m k P) φ hφ0 hφ1 hφc)
    (process_vertex_recolor_stabilizer_invariant m k P hP φ (fun b => (hφc b).measurable))
    (process_edge_recolor_stabilizer_invariant m k P hP φ (fun b => (hφc b).measurable))
    (fun n : ℕ => n+1) (fun n : ℕ => Nat.succ_pos n) (tendsto_add_atTop_nat 1)
  have hbound (n : ℕ) : left ≤ fC n-(((m+2 : ℕ) : ℝ)/2)*fE n-Real.log (n+1) := by
    let A := Fin q × Fin (n+1)
    let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
    let θ (x : Fin r → ℝ) (b : Fin (Fintype.card A)) := markerKernel φ (n+1) x (e.symm b)
    have hA : 0 < Fintype.card A := by
      letI : Nonempty A := ⟨(⟨0,hq⟩,⟨0,by omega⟩)⟩
      exact Fintype.card_pos
    have hθc (b : Fin (Fintype.card A)) : Continuous (fun x => θ x b) := markerKernel_continuous φ hφc (n+1) _
    have hθ0 (x) (b) : 0 ≤ θ x b := markerKernel_nonneg φ hφ0 (n+1) _ _
    have hθ1 (x) : (∑ b,θ x b)=1 := by
      exact (Equiv.sum_comp e.symm _).trans (markerKernel_sum φ hφ1 (n+1) (by omega) x)
    have hn := hcodes (Fintype.card A) hA θ hθc hθ0 hθ1
    have hmassC : windowRecolorMass (vertexProcessWindow m k P) θ=
        pushMass (coordinatewisePaletteEquiv _ e) (markerDecoratedMass pC (n+1)) := by
      rw [← windowRecolorMass_markerKernel]
      exact (windowRecolorMass_palette_push e _ (markerKernel φ (n+1))).symm
    have hmassE : windowRecolorMass (edgeProcessWindow m k P) θ=
        pushMass (coordinatewisePaletteEquiv _ e) (markerDecoratedMass pE (n+1)) := by
      rw [← windowRecolorMass_markerKernel]
      exact (windowRecolorMass_palette_push e _ (markerKernel φ (n+1))).symm
    have hHC : entropy (pushMass
        (centerPathCodes (GaussianWave.BS.vertexBallGraph (m+2) k) k (vertexBallStarCenter (m+2) k))
        (windowRecolorMass (vertexProcessWindow m k P) θ))=fC n := by
      rw [hmassC]
      exact entropy_centerPathCodes_palette_push _ k _ e _
    have hHE : entropy (pushMass (centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k))
        (windowRecolorMass (edgeProcessWindow m k P) θ))=fE n := by
      rw [hmassE]
      exact entropy_centerPathCodes_palette_push _ k _ e _
    have hroot (x : Fin r → ℝ) : entropy (θ x)=entropy (φ x)+Real.log (n+1) := by
      have hh : entropy (markerKernel φ (n+1) x)=entropy (φ x)+Real.log (n+1) := by
        change entropy (fun b : Fin q × Fin (n+1) => φ x b.1/((n+1 : ℕ) : ℝ))=_
        simpa only [Nat.cast_add,Nat.cast_one] using
          finiteEntropy_marker (φ x) (hφ1 x) (n+1) (Nat.succ_pos n)
      exact (entropy_palette_reindex e (markerKernel φ (n+1) x)).trans hh
    have hleft : (∫ x,entropy (θ x) ∂rootProcessWindow m P)=left+Real.log (n+1) := by
      simp_rw [hroot]
      rw [integral_add (integrable_profile_entropy _ φ (fun b => (hφc b).measurable) hφ0 hφ1) (integrable_const _)]
      simp only [integral_const,measureReal_univ_eq_one,one_smul,left]
    rw [hHC,hHE,hleft] at hn
    linarith
  have hlim' : Tendsto (fun n => fC n-(((m+2 : ℕ) : ℝ)/2)*fE n-Real.log (n+1)) atTop
      (𝓝 (entropy pC-(((m+2 : ℕ) : ℝ)/2)*entropy pE)) := by
    simpa only [fC,fE,Nat.cast_add,Nat.cast_one] using hlim
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim' (Filter.Eventually.of_forall hbound)

end GaussianWave.BS.Lower
