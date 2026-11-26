import GaussianWave.BS.Lower.PathCodeGluing
import GaussianWave.BS.Lower.GoodMarkerCoding

/-! Large-marker entropy asymptotics for the actual path-neighborhood tuple
codes. The recovery and invariance properties are proved from finite graph
geometry rather than supplied as entropy/coding assumptions. -/
noncomputable section
open Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 1000000
namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

variable {G V I F : Type*} [Group G] [Fintype G] [Fintype V] [Fintype I] [Fintype F]
  [MulAction G V] [FaithfulSMul G V]

theorem centerPathCodes_marker_entropy_tendsto
    (H : SimpleGraph V) (R : ℕ) (center : I → V)
    (hvertices : ∀ v,PathCoveredVertex H R center v)
    (hedges : ∀ u v,H.Adj u v → PathCoveredEdge H R center u v)
    (actionIso : G → H ≃g H) (hact : ∀ g v,actionIso g v=g • v)
    (hfixed : ∀ (g : G) (i : I),g • center i=center i)
    (hcomplete : ∀ e : H ≃g H,(∀ i,e (center i)=center i) → ∃ g : G,∀ v,g • v=e v)
    (p : (V → F) → ℝ) (hp : ∀ w,0 ≤ p w) (hs : ∑ w,p w=1)
    (hpinv : ∀ (g : G) c,p (fun v => c (g⁻¹ • v))=p c)
    (m : ℕ → ℕ) (hm : ∀ n,0 < m n) (hminf : Tendsto m atTop atTop) :
    Tendsto (fun n => entropy (pushMass (centerPathCodes H R center)
      (markerDecoratedMass p (m n)))-(Fintype.card V : ℝ)*Real.log (m n)) atTop
        (𝓝 (entropy p-Real.log (Fintype.card G))) := by
  apply good_marker_centered_entropy_tendsto p hp hs hpinv m hm hminf
    (fun n => I → PathNeighborhoodCode (F × Fin (m n)) R) (fun _ => centerPathCodes H R center)
  · intro n g w
    exact centerPathCodes_action_invariant H R center actionIso hact hfixed g w
  · intro n w hw w' hcode
    exact centerPathCodes_recover_of_injective_markers H R center hvertices hedges hcomplete w w' hw hcode

end GaussianWave.BS.Lower
