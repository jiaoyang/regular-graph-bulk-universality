import BourgadeHuang.EdgeCMS.RadialSystem
import BourgadeHuang.EdgeCMS.ConstantRadial
import BourgadeHuang.CMS.FullSubsetRadial

/-! The constant matrix blocks of the actual edge scaled-jet equation. -/
noncomputable section
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.EdgeCMS
open CMS
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-- A rectangular complex matrix as its actual continuous linear action. -/
def finiteComplexMatrix {J K : Type*} [Fintype J] [Fintype K]
    (A : J → K → ℂ) : (K → ℂ) →L[ℂ] (J → ℂ) :=
  ContinuousLinearMap.pi (fun i => ∑ j, A i j • ContinuousLinearMap.proj j)

@[simp] theorem finiteComplexMatrix_apply {J K : Type*} [Fintype J] [Fintype K]
    (A : J → K → ℂ) (v : K → ℂ) (i : J) :
    finiteComplexMatrix A v i = ∑ j, A i j * v j := by
  simp [finiteComplexMatrix, ContinuousLinearMap.sum_apply, Finset.sum_apply]

namespace SectorialData
variable {d : ℕ} {C : OpenCone d} (D : SectorialData C)

/-- Actual nonempty-sector diagonal. -/
def radialLambda (z : Point d) (S : NonemptySubset d) : ℂ := D.principalDiagonal z S.val

/-- Actual strictly triangular principal matrix. -/
def radialN (z : Point d) : (NonemptySubset d → ℂ) →L[ℂ] (NonemptySubset d → ℂ) :=
  finiteComplexMatrix (fun S T => D.principalRemainder z z 1 S.val T.val)

/-- Actual empty-row reciprocal coefficient. -/
def radialC01 (z : Point d) : (NonemptySubset d → ℂ) →L[ℂ] (Unit → ℂ) :=
  finiteComplexMatrix (fun _ T => D.radialRemainder z z 1 ∅ T.val)

/-- Actual empty-column reciprocal coefficient. -/
def radialC10 (z : Point d) : (Unit → ℂ) →L[ℂ] (NonemptySubset d → ℂ) :=
  finiteComplexMatrix (fun S _ => D.radialRemainder z z 1 S.val ∅)

/-- Actual nonempty reciprocal block. -/
def radialC11 (z : Point d) : (NonemptySubset d → ℂ) →L[ℂ] (NonemptySubset d → ℂ) :=
  finiteComplexMatrix (fun S T => D.radialRemainder z z 1 S.val T.val)

theorem radialN_strictlyLowerDegree (z : Point d) (R : ℝ) :
    StrictlyLowerDegree (fun S : NonemptySubset d => S.val.card)
      (BoundedContinuousFunction.const (Tail R) (D.radialN z)) := by
  intro t S v hv
  simp only [BoundedContinuousFunction.const_apply, radialN, finiteComplexMatrix_apply]
  apply Finset.sum_eq_zero
  intro T hT
  by_cases hTS : T.val.card < S.val.card
  · rw [hv T hTS, mul_zero]
  · rw [D.principalRemainder_strict_degree z z 1 S.val T.val hTS, zero_mul]

theorem radial_degree_lt (S : NonemptySubset d) : S.val.card < d + 1 := by
  have hh := Finset.card_le_univ S.val
  simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hh

theorem radialRemainder_empty_empty (z : Point d) : D.radialRemainder z z 1 ∅ ∅ = 0 := by
  simp only [radialRemainder,Finset.card_empty,Nat.cast_zero,ite_self,
    highCoordinate,Finset.not_mem_empty,if_false,Finset.insert_empty,zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg (Ne.symm (Finset.singleton_ne_empty i))]

/-- The genuine full matrix action splits into its empty row. -/
theorem radial_action_empty (z : Point d) (t : ℂ) (X : Finset (Fin d) → ℂ) :
    D.principalDiagonal z ∅ * X ∅ +
      (∑ T, D.principalRemainder z z 1 ∅ T * X T) +
      t⁻¹ * (∑ T, D.radialRemainder z z 1 ∅ T * X T) =
    t⁻¹ * D.radialC01 z (fun S => X S.val) () := by
  have hn : ∀ T, D.principalRemainder z z 1 ∅ T = 0 := fun T =>
    D.principalRemainder_strict_degree z z 1 ∅ T (by simp)
  simp only [principalDiagonal,Finset.not_mem_empty,if_false,Finset.sum_const_zero,
    zero_mul,hn,zero_add]
  rw [sum_subsets]
  simp [radialRemainder_empty_empty, radialC01]

/-- The genuine full matrix action splits into its nonempty block. -/
theorem radial_action_nonempty (z : Point d) (t : ℂ) (X : Finset (Fin d) → ℂ)
    (S : NonemptySubset d) :
    D.principalDiagonal z S.val * X S.val +
      (∑ T, D.principalRemainder z z 1 S.val T * X T) +
      t⁻¹ * (∑ T, D.radialRemainder z z 1 S.val T * X T) =
    D.radialLambda z S * X S.val + D.radialN z (fun T => X T.val) S +
      t⁻¹ * (D.radialC10 z (fun _ => X ∅) S + D.radialC11 z (fun T => X T.val) S) := by
  rw [sum_subsets, sum_subsets]
  simp [principalRemainder_empty_column, radialLambda, radialN, radialC10, radialC11]


/-- Every nonempty sector has a positive real spectral gap whenever each
coordinate lies in the selected minimal-growth half-plane. -/
theorem radialLambda_re_pos (z : Point d)
    (hgap : ∀ i, 0 < (-(z i * D.phase i)).re) (S : NonemptySubset d) :
    0 < (D.radialLambda z S).re := by
  classical
  unfold radialLambda principalDiagonal
  rw [Complex.re_sum]
  apply Finset.sum_pos'
  · intro i hi
    split_ifs
    · exact (hgap i).le
    · simp
  · obtain ⟨i, hi⟩ := S.property
    exact ⟨i, Finset.mem_univ i, by simpa only [if_pos hi] using hgap i⟩

/-- Positivity of the finitely many actual principal exponents supplies the
uniform lower bound needed by the Volterra theorem. -/
theorem exists_radial_gap (z : Point d)
    (hgap : ∀ i, 0 < (-(z i * D.phase i)).re) :
    ∃ a : ℝ, 0 < a ∧ ∀ S : NonemptySubset d, a ≤ (D.radialLambda z S).re := by
  classical
  have hall : ∀ s : Finset (NonemptySubset d),
      ∃ a : ℝ, 0 < a ∧ ∀ S ∈ s, a ≤ (D.radialLambda z S).re := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert S s hS ih =>
      obtain ⟨a, ha, hbound⟩ := ih
      refine ⟨min a (D.radialLambda z S).re,
        lt_min ha (D.radialLambda_re_pos z hgap S), ?_⟩
      intro T hT
      rcases Finset.mem_insert.mp hT with rfl | hT
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound T hT)
  obtain ⟨a, ha, hbound⟩ := hall Finset.univ
  exact ⟨a, ha, fun S => hbound S (Finset.mem_univ S)⟩

/-- Empty-component differential equation for actual analytic normalized solutions. -/
theorem hasDerivAt_dilation_empty {z : Point d} (hz : z ∈ C.carrier)
    {f : Point d → ℂ} (hf : D.IsSolution f) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r : ℝ => scaledSquareFree ∅ f ((r : ℂ) • z) r)
      (t⁻¹ • D.radialC01 z
        (fun S => scaledSquareFree S.val f ((t : ℂ) • z) t) ()) t := by
  have hh := D.hasDerivAt_scaled_dilation hz ∅ hf ht
  rw [D.radial_action_empty z (t : ℂ) (fun T => scaledSquareFree T f ((t : ℂ) • z) t)] at hh
  simpa only [Complex.real_smul, Complex.ofReal_inv] using hh

/-- Nonempty-component differential equation for actual analytic normalized solutions. -/
theorem hasDerivAt_dilation_nonempty {z : Point d} (hz : z ∈ C.carrier)
    {f : Point d → ℂ} (hf : D.IsSolution f) {t : ℝ} (ht : 0 < t)
    (S : NonemptySubset d) :
    HasDerivAt (fun r : ℝ => scaledSquareFree S.val f ((r : ℂ) • z) r)
      (D.radialLambda z S * scaledSquareFree S.val f ((t : ℂ) • z) t +
        D.radialN z (fun T => scaledSquareFree T.val f ((t : ℂ) • z) t) S +
        t⁻¹ • (D.radialC10 z (fun _ => scaledSquareFree ∅ f ((t : ℂ) • z) t) S +
          D.radialC11 z (fun T => scaledSquareFree T.val f ((t : ℂ) • z) t) S)) t := by
  have hh := D.hasDerivAt_scaled_dilation hz S.val hf ht
  rw [D.radial_action_nonempty z (t : ℂ) (fun T => scaledSquareFree T f ((t : ℂ) • z) t) S] at hh
  simpa only [Complex.real_smul, Complex.ofReal_inv] using hh

end SectorialData
end BourgadeHuang.EdgeCMS
