import BourgadeHuang.CMS.SquareFreeJets
import Mathlib.Analysis.Analytic.Constructions

/-! Actual analytic CMS solutions on a specified open domain, and their linear jets.
Global representatives need not satisfy any condition outside that domain. -/

noncomputable section
open scoped BigOperators
open Set

namespace BourgadeHuang.CMS

theorem coordinateJet_add {d : ℕ} {f g : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (n : ℕ) (v : Fin n → Fin d) :
    coordinateJet n (f + g) z v = coordinateJet n f z v + coordinateJet n g z v := by
  unfold coordinateJet
  rw [iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt]
  rfl

theorem coordinateJet_smul {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (c : ℂ) (n : ℕ) (v : Fin n → Fin d) :
    coordinateJet n (c • f) z v = c • coordinateJet n f z v := by
  unfold coordinateJet
  rw [iteratedFDeriv_const_smul_apply hf.contDiffAt]
  rfl

theorem coordDeriv_add_analytic {d : ℕ} {f g : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (i : Fin d) :
    coordDeriv i (f + g) z = coordDeriv i f z + coordDeriv i g z := by
  have h := coordinateJet_add hf hg 1 (fun _ => i)
  rw [coordinateJet_one (hf.add hg).differentiableAt,
    coordinateJet_one hf.differentiableAt, coordinateJet_one hg.differentiableAt] at h
  exact h

theorem coordDeriv_smul_analytic {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (c : ℂ) (i : Fin d) :
    coordDeriv i (c • f) z = c • coordDeriv i f z := by
  have h := coordinateJet_smul hf c 1 (fun _ => i)
  rw [coordinateJet_one (hf.const_smul (c := c)).differentiableAt,
    coordinateJet_one hf.differentiableAt] at h
  exact h

theorem secondPartial_add_analytic {d : ℕ} {f g : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (i : Fin d) :
    secondPartial i (f + g) z = secondPartial i f z + secondPartial i g z := by
  have h := coordinateJet_add hf hg 2 (fun _ => i)
  rw [coordinateJet_two_repeat (hf.add hg), coordinateJet_two_repeat hf,
    coordinateJet_two_repeat hg] at h
  exact h

theorem secondPartial_smul_analytic {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (c : ℂ) (i : Fin d) :
    secondPartial i (c • f) z = c • secondPartial i f z := by
  have h := coordinateJet_smul hf c 2 (fun _ => i)
  rw [coordinateJet_two_repeat (hf.const_smul (c := c)), coordinateJet_two_repeat hf] at h
  exact h

theorem reducedOperator_add_analytic {d : ℕ} {f g : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (i : Fin d) :
    reducedOperator i (f + g) z = reducedOperator i f z + reducedOperator i g z := by
  simp only [reducedOperator, secondPartial_add_analytic hf hg, Pi.add_apply,
    coordDeriv_add_analytic hf hg, add_sub_add_comm, add_div, Finset.sum_add_distrib]
  ring

theorem reducedOperator_smul_analytic {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (c : ℂ) (i : Fin d) :
    reducedOperator i (c • f) z = c • reducedOperator i f z := by
  simp only [reducedOperator, secondPartial_smul_analytic hf, Pi.smul_apply,
    coordDeriv_smul_analytic hf, smul_eq_mul, ← mul_sub, mul_div_assoc,
    ← Finset.mul_sum]
  ring

/-- Functions analytic on U and satisfying the actual CMS PDEs at every point of U. -/
def solutionSpace {d : ℕ} (U : Set (Point d)) : Submodule ℂ (Point d → ℂ) where
  carrier := {f | AnalyticOnNhd ℂ f U ∧ ∀ z ∈ U, ∀ i, reducedOperator i f z = 0}
  zero_mem' := by
    constructor
    · exact analyticOnNhd_const
    · intro z hz i
      simp [reducedOperator, secondPartial, coordDeriv]
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, ?_⟩
    intro z hz i
    rw [reducedOperator_add_analytic (hf.1 z hz) (hg.1 z hz), hf.2 z hz i, hg.2 z hz i,
      add_zero]
  smul_mem' := by
    intro c f hf
    refine ⟨(fun z hz => (hf.1 z hz).const_smul (c := c)), ?_⟩
    intro z hz i
    rw [reducedOperator_smul_analytic (hf.1 z hz), hf.2 z hz i, smul_zero]

/-- Restriction keeps track of equality only on U. -/
def solutionRestriction {d : ℕ} (U : Set (Point d)) :
    solutionSpace U →ₗ[ℂ] (U → ℂ) where
  toFun := fun f z => f.val z.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The actual canonical square-free jets of a solution at a point of its domain. -/
def solutionJet {d : ℕ} (U : Set (Point d)) (z : U) :
    solutionSpace U →ₗ[ℂ] (Finset (Fin d) → ℂ) where
  toFun := fun f s => coordinateJet s.card f.val z.val (s.orderEmbOfFin rfl)
  map_add' := by
    intro f g
    funext s
    exact coordinateJet_add (f.property.1 z.val z.property)
      (g.property.1 z.val z.property) _ _
  map_smul' := by
    intro c f
    funext s
    exact coordinateJet_smul (f.property.1 z.val z.property) c _ _

end BourgadeHuang.CMS
