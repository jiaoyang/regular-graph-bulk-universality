import GaussianWave.BS.Reused.Graph.EmpiricalSymmetry
import GaussianWave.BS.Reused.Graph.SymmetricProfileCount
import GaussianWave.BS.Reused.Graph.ConfigurationConditioning

/-! Symmetric star-coloring counts depend on the simple graph alone. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration
open ColorProfiles

def graphReferencePairing {N d : ℕ} (G : RegularGraph N d) : Pairing (Stub N d) :=
  labelingPairing G (canonicalPortLabeling G)

def graphSymmetricColoringCount {N d q : ℕ} (G : RegularGraph N d)
    (S : StarWord d q → ℝ) : ℕ := configurationSymmetricColoringCount (graphReferencePairing G) S

set_option maxHeartbeats 1000000 in
theorem referencePairing_word_port_permutation {N d q : ℕ} (p : Pairing (Stub N d))
    (hp : SimpleConfiguration p) (c : VertexColoring N q) :
    ∃ τ : Fin N → Equiv.Perm (Fin d),
      configurationWord (graphReferencePairing (configurationGraph p hp)) c =
        fun v => starWordPerm (τ v) (configurationWord p c v) := by
  let G := configurationGraph p hp
  let L := canonicalPortLabeling G
  let P := pairingNeighborEquiv p hp
  let τ : Fin N → Equiv.Perm (Fin d) := fun v => (L v).trans (P v).symm
  refine ⟨τ,?_⟩
  funext v i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change c ((graphReferencePairing G).val (v,j)).1 = c (p.val (v,τ v j)).1
    congr 1
    rw [show graphReferencePairing G = labelingPairing G L from rfl,labelingPairing_root]
    have he := (P v).apply_symm_apply (L v j)
    exact (congrArg Subtype.val he).symm

theorem graphReferencePairing_symmetrizedMass {N d q : ℕ} (p : Pairing (Stub N d))
    (hp : SimpleConfiguration p) (c : VertexColoring N q) :
    symmetrizedMass (histogram N (configurationWord (graphReferencePairing (configurationGraph p hp)) c)) =
      symmetrizedMass (histogram N (configurationWord p c)) := by
  obtain ⟨τ,hτ⟩ := referencePairing_word_port_permutation p hp c
  rw [hτ]
  exact symmetrizedMass_local_port_invariant _ τ

theorem graphSymmetricColoringCount_configuration {N d q : ℕ} (p : Pairing (Stub N d))
    (hp : SimpleConfiguration p) (S : StarWord d q → ℝ) :
    graphSymmetricColoringCount (configurationGraph p hp) S = configurationSymmetricColoringCount p S := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro c
  rw [graphReferencePairing_symmetrizedMass p hp c]

end GaussianWave.BS.Reused.Graph.Configuration
