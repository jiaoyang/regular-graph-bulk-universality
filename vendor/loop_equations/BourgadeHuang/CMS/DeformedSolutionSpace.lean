import BourgadeHuang.CMS.GeneralCouplingJets

/-! The actual analytic solution space for arbitrary deformed CMS coupling,
with restriction and the genuine finite square-free jet as linear maps. -/
noncomputable section
open Set
open scoped BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000

theorem deformedOperator_add_analytic {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {f g : Point d → ℂ} {z : Point d} (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) (i : Fin d) :
    deformedOperator β c i (f+g) z=
      deformedOperator β c i f z+deformedOperator β c i g z := by
  simp only [deformedOperator,secondPartial_add_analytic hf hg,Pi.add_apply,
    coordDeriv_add_analytic hf hg,mul_add,add_sub_add_comm,add_div,Finset.sum_add_distrib]
  ring

theorem deformedOperator_smul_analytic {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {f : Point d → ℂ} {z : Point d} (hf : AnalyticAt ℂ f z) (a : ℂ) (i : Fin d) :
    deformedOperator β c i (a•f) z=a*deformedOperator β c i f z := by
  simp only [deformedOperator,secondPartial_smul_analytic hf,Pi.smul_apply,
    coordDeriv_smul_analytic hf,smul_eq_mul]
  have ht (j : Fin d) :
      (c i*c j*(a*coordDeriv i f z)-c i^2*(a*coordDeriv j f z))/(z i-z j)=
        a*((c i*c j*coordDeriv i f z-c i^2*coordDeriv j f z)/(z i-z j)) := by ring
  simp_rw [ht]
  rw [←Finset.mul_sum]
  ring

/-- Analytic functions satisfying the genuine deformed equations on U. -/
def deformedSolutionSpace {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (U : Set (Point d)) :
    Submodule ℂ (Point d → ℂ) where
  carrier := {f | AnalyticOnNhd ℂ f U ∧ ∀z∈U,∀i,deformedOperator β c i f z=0}
  zero_mem' := by
    refine ⟨analyticOnNhd_const,?_⟩
    intro z hz i
    simp [deformedOperator,secondPartial,coordDeriv]
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1,?_⟩
    intro z hz i
    rw [deformedOperator_add_analytic β c (hf.1 z hz) (hg.1 z hz),
      hf.2 z hz i,hg.2 z hz i,add_zero]
  smul_mem' := by
    intro a f hf
    refine ⟨fun z hz=>(hf.1 z hz).const_smul (c:=a),?_⟩
    intro z hz i
    rw [deformedOperator_smul_analytic β c (hf.1 z hz),hf.2 z hz i,mul_zero]

/-- Representatives are identified only after restricting to their domain. -/
def deformedSolutionRestriction {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (U : Set (Point d)) :
    deformedSolutionSpace β c U →ₗ[ℂ] (U → ℂ) where
  toFun := fun f z=>f.val z.val
  map_add' := by intros;rfl
  map_smul' := by intros;rfl

/-- The actual finite family of square-free Fréchet jets at a domain point. -/
def deformedSolutionJet {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (U : Set (Point d)) (z : U) :
    deformedSolutionSpace β c U →ₗ[ℂ] (Finset (Fin d) → ℂ) where
  toFun := fun f S=>coordinateJet S.card f.val z.val (S.orderEmbOfFin rfl)
  map_add' := by
    intro f g
    funext S
    exact coordinateJet_add (f.property.1 z.val z.property) (g.property.1 z.val z.property) _ _
  map_smul' := by
    intro a f
    funext S
    exact coordinateJet_smul (f.property.1 z.val z.property) a _ _

/-- Vanishing of the actual finite jet implies vanishing on the entire
connected domain, by the proved analytic deformed-PDE uniqueness theorem. -/
theorem deformedSolutionRestriction_eq_zero_of_jet_eq_zero {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (U : Set (Point d)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hfree : ∀z∈U,CollisionFree z) (z : U)
    (f : deformedSolutionSpace β c U) (hjet : deformedSolutionJet β c U z f=0) :
    deformedSolutionRestriction β c U f=0 := by
  have hj : ∀S,subsetJet f.val z.val S=0 := fun S=>congrFun hjet S
  have he := analytic_eqOn_zero_of_subsetJet_deformed β c hU hconn hfree
    f.property.1 f.property.2 z.property hj
  funext w
  exact he w.property

end BourgadeHuang.CMS
