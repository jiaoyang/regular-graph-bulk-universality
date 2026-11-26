import BourgadeHuang.CMS.SolutionSpace
import BourgadeHuang.CMS.FiniteJetLinearAlgebra
import BourgadeHuang.CMS.ExplicitSolutions
import BourgadeHuang.CMS.RayIndependence
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Powerset

/-!
The genuine beta = 2 CMS basis theorem on an arbitrary nonempty, open,
preconnected collision-free domain.  No condition is imposed outside the domain.

The spanning argument uses the proved analytic square-free-jet uniqueness theorem,
not an assumed classification: the kernel of the actual finite-jet map is contained
in the kernel of restriction.  The actual explicit branches have independent
restrictions, and their number equals the dimension of the finite-jet target.
-/

noncomputable section
open scoped BigOperators
open Set

namespace BourgadeHuang.CMS

/-- An explicit branch as an actual analytic solution on the chosen domain. -/
def explicitSolutionInSpace {d : ℕ} (U : Set (Point d))
    (hfree : ∀ z ∈ U, CollisionFree z) (σ : Fin d → Sign) : solutionSpace U :=
  ⟨explicitSolution σ, fun z hz => analyticAt_explicitSolution σ (hfree z hz),
    fun z hz i => explicitSolution_isReducedSolution σ z (hfree z hz) i⟩

/-- Every finite combination of the explicit branches is itself a genuine
analytic CMS solution on any collision-free domain. -/
theorem explicit_combination_is_solution {d : ℕ}
    (U : Set (Point d)) (hfree : ∀ z ∈ U, CollisionFree z)
    (c : (Fin d → Sign) → ℂ) :
    AnalyticOnNhd ℂ (fun z => ∑ σ, c σ * explicitSolution σ z) U ∧
      ∀ z ∈ U, ∀ i,
        reducedOperator i (fun w => ∑ σ, c σ * explicitSolution σ w) z = 0 := by
  classical
  let v : solutionSpace U := ∑ σ, c σ • explicitSolutionInSpace U hfree σ
  have heq : v.val = (fun z => ∑ σ, c σ * explicitSolution σ z) := by
    ext z
    simp [v, explicitSolutionInSpace, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [heq] using v.property

/-- The square-free jets determine the restriction of a solution to the domain. -/
theorem solutionRestriction_eq_zero_of_jet_eq_zero {d : ℕ}
    (U : Set (Point d)) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hfree : ∀ z ∈ U, CollisionFree z) (z : U) (f : solutionSpace U)
    (hjet : solutionJet U z f = 0) : solutionRestriction U f = 0 := by
  have hsubset : ∀ s, subsetJet f.val z.val s = 0 := by
    intro s
    exact congrFun hjet s
  have hzero := analytic_eqOn_zero_of_subsetJet hU hconn hfree
    f.property.1 f.property.2 z.property hsubset
  funext w
  exact hzero w.property

/-- There are as many sign patterns as independent square-free jet entries. -/
theorem sign_card_eq_jet_finrank (d : ℕ) :
    Fintype.card (Fin d → Sign) = Module.finrank ℂ (Finset (Fin d) → ℂ) := by
  simp [Sign, Module.finrank_fintype_fun_eq_card, Fintype.card_finset]

/-- Every genuine analytic CMS solution on U is a linear combination of the
explicit branches, with coefficients constant on U. -/
theorem exists_explicit_expansion {d : ℕ}
    (U : Set (Point d)) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : U.Nonempty) (hfree : ∀ z ∈ U, CollisionFree z)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀ z ∈ U, ∀ i, reducedOperator i f z = 0) :
    ∃ c : (Fin d → Sign) → ℂ,
      EqOn f (fun z => ∑ σ, c σ * explicitSolution σ z) U := by
  classical
  obtain ⟨z, hz⟩ := hne
  let zU : U := ⟨z, hz⟩
  let v : solutionSpace U := ⟨f, hf, hsolve⟩
  have hind : LinearIndependent ℂ
      (fun σ => solutionRestriction U (explicitSolutionInSpace U hfree σ)) :=
    linearIndependent_explicitSolution_on_open U hU ⟨z, hz⟩ hfree
  obtain ⟨c, hc⟩ := exists_expansion_of_finite_jets
    (solutionJet U zU) (solutionRestriction U)
    (solutionRestriction_eq_zero_of_jet_eq_zero U hU hconn hfree zU)
    (explicitSolutionInSpace U hfree) hind (sign_card_eq_jet_finrank d) v
  refine ⟨c, ?_⟩
  intro w hw
  have he := congrFun hc ⟨w, hw⟩
  simpa only [solutionRestriction, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, explicitSolutionInSpace] using he

/-- The coefficients in an expansion on a nonempty open collision-free domain
are unique, independently of connectedness. -/
theorem explicit_expansion_coefficients_unique {d : ℕ}
    (U : Set (Point d)) (hU : IsOpen U) (hne : U.Nonempty)
    (hfree : ∀ z ∈ U, CollisionFree z)
    {c c' : (Fin d → Sign) → ℂ}
    (heq : EqOn (fun z => ∑ σ, c σ * explicitSolution σ z)
      (fun z => ∑ σ, c' σ * explicitSolution σ z) U) : c = c' := by
  apply (linearIndependent_explicitSolution_on_open U hU hne hfree).fintypeLinearCombination_injective
  funext z
  simpa [Fintype.linearCombination_apply, Pi.smul_apply, smul_eq_mul] using heq z.property

/-- Every actual analytic solution has a unique expansion in the 2^d explicit
CMS branches.  The only hypotheses are the domain and analytic PDE assumptions. -/
theorem existsUnique_explicit_expansion {d : ℕ}
    (U : Set (Point d)) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : U.Nonempty) (hfree : ∀ z ∈ U, CollisionFree z)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀ z ∈ U, ∀ i, reducedOperator i f z = 0) :
    ∃! c : (Fin d → Sign) → ℂ,
      EqOn f (fun z => ∑ σ, c σ * explicitSolution σ z) U := by
  obtain ⟨c, hc⟩ := exists_explicit_expansion U hU hconn hne hfree hf hsolve
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply explicit_expansion_coefficients_unique U hU hne hfree
  intro z hz
  exact (hc' hz).symm.trans (hc hz)

/-- The unique-expansion theorem specialized to the connected ordered chamber. -/
theorem existsUnique_explicit_expansion_ordered {d : ℕ}
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f (OrderedDomain d))
    (hsolve : ∀ z ∈ OrderedDomain d, ∀ i, reducedOperator i f z = 0) :
    ∃! c : (Fin d → Sign) → ℂ,
      EqOn f (fun z => ∑ σ, c σ * explicitSolution σ z) (OrderedDomain d) :=
  existsUnique_explicit_expansion (OrderedDomain d) (orderedDomain_isOpen d)
    (orderedDomain_isConnected d).isPreconnected (orderedDomain_nonempty d)
    (fun _ hz => orderedDomain_collisionFree hz) hf hsolve

/-- Unique expansion on every ordered chamber with prescribed half-planes for
any selected set of coordinates, including the observable domains. -/
theorem existsUnique_explicit_expansion_orderedMixed {d : ℕ}
    (J : Finset (Fin d)) (σ : Fin d → Sign)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f (OrderedMixedDomain d J σ))
    (hsolve : ∀ z ∈ OrderedMixedDomain d J σ, ∀ i, reducedOperator i f z = 0) :
    ∃! c : (Fin d → Sign) → ℂ,
      EqOn f (fun z => ∑ τ, c τ * explicitSolution τ z) (OrderedMixedDomain d J σ) :=
  existsUnique_explicit_expansion (OrderedMixedDomain d J σ)
    (orderedMixedDomain_isOpen d J σ)
    (orderedMixedDomain_isConnected d J σ).isPreconnected
    (orderedMixedDomain_nonempty d J σ)
    (fun _ hz => orderedMixedDomain_collisionFree hz) hf hsolve

end BourgadeHuang.CMS
