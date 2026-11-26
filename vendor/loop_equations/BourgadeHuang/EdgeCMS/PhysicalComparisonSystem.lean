import BourgadeHuang.EdgeCMS.PhysicalNormalForm
import BourgadeHuang.EdgeCMS.PhysicalChamber
import BourgadeHuang.EdgeCMS.RadialBlocks

/-! The actual homogeneous edge system on a nonempty physical comparison cone.
This is the physical input to the bounded-solution terminal-map uniqueness
argument; it does not construct the full sectorial basis of Theorem 6.5. -/
noncomputable section
namespace BourgadeHuang.EdgeCMS
open CMS

 theorem physicalChamber_subset_airyCone {d : ℕ} (c : Fin d → ℂ) (upper : Fin d → Bool) :
    (physicalOpenCone c upper).carrier ⊆ (physicalAiryCone d).carrier := by
  intro y hy
  exact ⟨fun i => (hy.1 i).1.1, hy.2⟩

/-- The physical coefficient system on the actual sign comparison cone. -/
def physicalComparisonData {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0)
    (upper : Fin d → Bool) : SectorialData (physicalOpenCone c upper) :=
  (physicalSectorialData β c hβ).restrict (physicalChamber_subset_airyCone c upper)

@[simp] theorem physicalComparisonData_phase {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0) (upper : Fin d → Bool) (i : Fin d) :
    (physicalComparisonData β c hβ upper).phase i = 2*c i := rfl

theorem physicalComparisonData_coordinate_gap {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0) (upper : Fin d → Bool)
    {y : Point d} (hy : y ∈ (physicalOpenCone c upper).carrier) (i : Fin d) :
    0 < (-(y i * (physicalComparisonData β c hβ upper).phase i)).re := by
  have hh := physicalChamber_gap hy i
  simpa only [physicalComparisonData_phase,
    show -(y i * (2*c i)) = -2*c i*y i by ring] using hh

theorem physicalComparisonData_exists_gap {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0) (upper : Fin d → Bool)
    {y : Point d} (hy : y ∈ (physicalOpenCone c upper).carrier) :
    ∃ a : ℝ, 0 < a ∧ ∀ S : NonemptySubset d,
      a ≤ ((physicalComparisonData β c hβ upper).radialLambda y S).re :=
  (physicalComparisonData β c hβ upper).exists_radial_gap y
    (physicalComparisonData_coordinate_gap β c hβ upper hy)

/-- Every actual analytic edge observable becomes a genuine solution of the
constructed physical comparison system. -/
theorem physicalComparisonData_isSolution {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0) (upper : Fin d → Bool)
    {F : Point d → ℂ}
    (hF : ∀ y ∈ (physicalOpenCone c upper).carrier,
      AnalyticAt ℂ F (airyInverseCoordinates y))
    (hop : ∀ y ∈ (physicalOpenCone c upper).carrier, ∀ i,
      edgeOperator β c i F (airyInverseCoordinates y) = 0) :
    (physicalComparisonData β c hβ upper).IsSolution (physicalAiryNormalized β c F) := by
  apply physicalAiryNormalized_isSolution β c hβ (physicalOpenCone c upper)
    (physicalChamber_subset_airyCone c upper)
  · intro y hy i
    exact (hy.1 i).1.2.1
  · exact hF
  · exact hop

end BourgadeHuang.EdgeCMS
