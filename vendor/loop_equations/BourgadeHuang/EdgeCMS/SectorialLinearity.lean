import BourgadeHuang.EdgeCMS.SectorialReduction
import BourgadeHuang.CMS.SolutionSpace

/-! Linearity of the genuine homogeneous sectorial differential system. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang.EdgeCMS
open CMS
namespace SectorialData

variable {d : ℕ} {C : OpenCone d} (D : SectorialData C)

theorem operator_add_analytic {f g : Point d→ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (i : Fin d) :
    D.operator i (f+g) z = D.operator i f z+D.operator i g z := by
  simp only [operator,secondPartial_add_analytic hf hg,coordDeriv_add_analytic hf hg,
    Pi.add_apply,mul_add,Finset.sum_add_distrib]
  ring

theorem operator_smul_analytic {f : Point d→ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (a : ℂ) (i : Fin d) :
    D.operator i (a•f) z = a*D.operator i f z := by
  simp only [operator,secondPartial_smul_analytic hf,coordDeriv_smul_analytic hf,
    Pi.smul_apply,smul_eq_mul]
  simp_rw [←mul_assoc, mul_comm _ a, mul_assoc]
  rw [←Finset.mul_sum]
  ring

theorem IsSolution.add {f g : Point d→ℂ}
    (hf : D.IsSolution f) (hg : D.IsSolution g) : D.IsSolution (f+g) := by
  refine ⟨hf.1.add hg.1,?_⟩
  intro z hz i
  rw [D.operator_add_analytic (hf.1 z hz) (hg.1 z hz),hf.2 z hz i,hg.2 z hz i,add_zero]

theorem IsSolution.smul {f : Point d→ℂ}
    (hf : D.IsSolution f) (a : ℂ) : D.IsSolution (a•f) := by
  refine ⟨fun z hz => (hf.1 z hz).const_smul,?_⟩
  intro z hz i
  rw [D.operator_smul_analytic (hf.1 z hz),hf.2 z hz i,mul_zero]

end SectorialData
end BourgadeHuang.EdgeCMS
