import BourgadeHuang.CMS.SectorialComplexOperators
import BourgadeHuang.CMS.ComplexMatrixBounds
import BourgadeHuang.CMS.CoupledVolterraBounds
import BourgadeHuang.CMS.ComplexPrimitiveOperator
import BourgadeHuang.CMS.SectorialVolterraData

/-! The actual radial coefficient blocks have a common holomorphic lift and
uniform bounds; their free-diagonal weighted integral equation has a genuine
holomorphic solution for an explicit sufficiently large radius. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

abbrev RadialVector (d : ℕ) := NonemptySubset d → ℂ
abbrev EmptyVector := Unit → ℂ
abbrev RadialBanach (d : ℕ) (R : ℝ) := Tail R →ᵇ RadialVector d
abbrev EmptyBanach (R : ℝ) := Tail R →ᵇ EmptyVector

/-- The four actual complex operator blocks, as functions of the base point. -/
structure RadialOperatorFamily (d : ℕ) (R : ℝ) where
  N : Point d → (Tail R →ᵇ (RadialVector d →L[ℂ] RadialVector d))
  C01 : Point d → (Tail R →ᵇ (RadialVector d →L[ℂ] EmptyVector))
  C10 : Point d → (Tail R →ᵇ (EmptyVector →L[ℂ] RadialVector d))
  C11 : Point d → (Tail R →ᵇ (RadialVector d →L[ℂ] RadialVector d))

namespace RadialOperatorFamily
variable {d : ℕ} {R : ℝ} (F : RadialOperatorFamily d R)

def AnalyticAt (z : Point d) : Prop :=
  _root_.AnalyticAt ℂ F.N z ∧ _root_.AnalyticAt ℂ F.C01 z ∧
    _root_.AnalyticAt ℂ F.C10 z ∧ _root_.AnalyticAt ℂ F.C11 z

/-- Equality to the actual rational radial matrices, at every time. -/
def Matches (D : SectorialData d) (ω : Point d) (σ : Fin d → Sign) (w : Point d) : Prop :=
  (∀t v i,F.N w t v i=∑j,D.principalRemainder ω (sectorialRay σ w R t) (t:ℝ) i.val j.val*v j) ∧
  (∀t v i,F.C01 w t v i=∑j,D.radialRemainder ω (sectorialRay σ w R t) (t:ℝ) ∅ j.val*v j) ∧
  (∀t v i,F.C10 w t v i=∑j : Unit,D.radialRemainder ω (sectorialRay σ w R t) (t:ℝ) i.val ∅*v j) ∧
  (∀t v i,F.C11 w t v i=∑j,D.radialRemainder ω (sectorialRay σ w R t) (t:ℝ) i.val j.val*v j)

/-- A common block norm, with every finite-dimensional summation included. -/
def blockBound (D : SectorialData d) (ω : Point d) : ℝ :=
  ((Fintype.card (NonemptySubset d):ℝ)+1)*D.matrixBound ω

theorem blockBound_pos (D : SectorialData d) (ω : Point d) : 0<blockBound D ω :=
  mul_pos (by positivity) (D.matrixBound_pos ω)

theorem norm_blocks_le (D : SectorialData d) (ω : Point d) (σ : Fin d → Sign)
    {z : Point d} (hF : F.Matches D ω σ z) (hR : 0<R)
    (hz : z∈OrderedDomain d) (hsep : ∀i j,i≠j→R≤‖z i-z j‖) :
    ‖F.N z‖≤blockBound D ω ∧ ‖F.C01 z‖≤blockBound D ω ∧
      ‖F.C10 z‖≤blockBound D ω ∧ ‖F.C11 z‖≤blockBound D ω := by
  have hp (t : Tail R) (S T : Finset (Fin d)) :
      ‖D.principalRemainder ω (sectorialRay σ z R t) (t:ℝ) S T‖≤D.matrixBound ω :=
    (D.norm_principalRemainder_le ω S T (hR.trans_le t.property)
      (sectorialRay_separation σ hz hsep t.property)).trans (D.principalRowBound_le_matrixBound ω S)
  have hr (t : Tail R) (S T : Finset (Fin d)) :
      ‖D.radialRemainder ω (sectorialRay σ z R t) (t:ℝ) S T‖≤D.matrixBound ω :=
    (D.norm_radialRemainder_le ω S T (hR.trans_le t.property)
      (sectorialRay_separation σ hz hsep t.property)).trans (D.remainderRowBound_le_matrixBound ω S)
  have hcard : (Fintype.card (NonemptySubset d):ℝ)*D.matrixBound ω≤blockBound D ω := by
    unfold blockBound
    nlinarith [D.matrixBound_pos ω]
  have hone : (Fintype.card Unit:ℝ)*D.matrixBound ω≤blockBound D ω := by
    unfold blockBound
    simp only [Fintype.card_unique,Nat.cast_one,one_mul]
    nlinarith [D.matrixBound_pos ω,Nat.cast_nonneg (α:=ℝ) (Fintype.card (NonemptySubset d))]
  exact ⟨(norm_boundedMatrixField_le _ _ hF.1 (D.matrixBound_pos ω).le (fun t i j => hp t i.val j.val)).trans hcard,
    (norm_boundedMatrixField_le _ _ hF.2.1 (D.matrixBound_pos ω).le (fun t _ j => hr t ∅ j.val)).trans hcard,
    (norm_boundedMatrixField_le _ _ hF.2.2.1 (D.matrixBound_pos ω).le (fun t i _ => hr t i.val ∅)).trans hone,
    (norm_boundedMatrixField_le _ _ hF.2.2.2 (D.matrixBound_pos ω).le (fun t i j => hr t i.val j.val)).trans hcard⟩

/-- Nilpotence of the actual principal integral operator follows from the
proved strict lowering of subset cardinality. -/
theorem principal_integral_nilpotent (D : SectorialData d) (ω : Point d) (σ : Fin d → Sign)
    {w : Point d} (hF : F.Matches D ω σ w) {a : ℝ} (hR : 0<R) (ha : 0<a)
    (lam : NonemptySubset d → ℂ) (hlam : ∀i,a≤(lam i).re) :
    ((freeForcingOperator hR ha lam hlam).comp
      (complexBoundedCoefficientOperator (F.N w)))^(d+1)=0 := by
  apply pow_eq_zero_of_raisesDegree (degree := fun S : NonemptySubset d => S.val.card) _
    (fun S => lt_of_le_of_lt (Finset.card_le_univ _) (by simp))
  intro k f hf
  apply freeForcingOperator_vanishesBelow hR ha lam hlam
  apply raisesDegree_boundedMatrixField _ (F.N w) _ hF.1 _ k f hf
  intro t i j hij
  exact D.principalRemainder_strict_degree ω (sectorialRay σ w R t) (t:ℝ) i.val j.val hij

end RadialOperatorFamily

namespace SectorialData
variable {d : ℕ} (D : SectorialData d) (ω : Point d) (σ : Fin d → Sign)
  {R : ℝ} {z : Point d}

/-- All four true radial blocks admit a simultaneous Banach-space holomorphic
lift, on one neighborhood valid for the entire half-line. -/
theorem exists_analytic_radialOperatorFamily (hR : 0<R) (hz : z∈OrderedDomain d)
    (hsep : ∀i j,i≠j→R≤‖z i-z j‖) :
    ∃F : RadialOperatorFamily d R,F.AnalyticAt z ∧ ∀ᶠw in 𝓝 z,F.Matches D ω σ w := by
  obtain ⟨N,hN,hNeq⟩ := D.exists_analytic_principalOperator_family σ hR hz hsep ω
    (fun S : NonemptySubset d => S.val) (fun S : NonemptySubset d => S.val)
  obtain ⟨C01,h01,h01eq⟩ := D.exists_analytic_radialOperator_family σ hR hz hsep ω
    (fun _ : Unit => ∅) (fun S : NonemptySubset d => S.val)
  obtain ⟨C10,h10,h10eq⟩ := D.exists_analytic_radialOperator_family σ hR hz hsep ω
    (fun S : NonemptySubset d => S.val) (fun _ : Unit => ∅)
  obtain ⟨C11,h11,h11eq⟩ := D.exists_analytic_radialOperator_family σ hR hz hsep ω
    (fun S : NonemptySubset d => S.val) (fun S : NonemptySubset d => S.val)
  refine ⟨⟨N,C01,C10,C11⟩,⟨hN,h01,h10,h11⟩,?_⟩
  filter_upwards [hNeq,h01eq,h10eq,h11eq] with w hn h01 h10 h11
  exact ⟨hn,h01,h10,h11⟩

end SectorialData
end BourgadeHuang.CMS
