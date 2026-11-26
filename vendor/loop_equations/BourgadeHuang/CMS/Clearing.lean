import BourgadeHuang.CMS.ExplicitFunctions
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Analytic.Uniqueness

/-! Clearing all collision denominators gives entire exponential-polynomial
functions. This provides an identity-theorem route from any open domain to
rays in the whole ambient space. It does not assume a CMS basis theorem. -/

noncomputable section
open scoped BigOperators Topology

namespace BourgadeHuang.CMS

def allPairs (d : ℕ) : Finset (Fin d × Fin d) :=
  Finset.univ.filter (fun p => p.1 < p.2)

def samePairs {d : ℕ} (σ : Fin d → Sign) : Finset (Fin d × Fin d) :=
  (allPairs d).filter (fun p => σ p.1 = σ p.2)

def vandermonde {d : ℕ} (z : Point d) : ℂ :=
  ∏ p ∈ allPairs d, (z p.1 - z p.2)

/-- The entire function obtained from `explicitSolution` by clearing all poles. -/
def clearedSolution {d : ℕ} (σ : Fin d → Sign) (z : Point d) : ℂ :=
  Complex.exp (phase σ z) * ∏ p ∈ samePairs σ, (z p.1 - z p.2)

theorem oppositePairs_filter {d : ℕ} (σ : Fin d → Sign) :
    oppositePairs σ = (allPairs d).filter (fun p => σ p.1 ≠ σ p.2) := by
  ext p
  simp [oppositePairs, allPairs, and_assoc]

theorem vandermonde_ne_zero {d : ℕ} {z : Point d} (hz : CollisionFree z) :
    vandermonde z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact hz.sub_ne_zero (ne_of_lt (Finset.mem_filter.mp hp).2)

theorem vandermonde_mul_explicitSolution {d : ℕ} (σ : Fin d → Sign)
    {z : Point d} (hz : CollisionFree z) :
    vandermonde z * explicitSolution σ z = clearedSolution σ z := by
  have hprod : (∏ p ∈ oppositePairs σ, (z p.1 - z p.2)) *
      (∏ p ∈ samePairs σ, (z p.1 - z p.2)) = vandermonde z := by
    rw [oppositePairs_filter]
    simpa only [samePairs, not_not] using
      Finset.prod_filter_mul_prod_filter_not (allPairs d)
        (fun p => σ p.1 ≠ σ p.2) (fun p => z p.1 - z p.2)
  have hn : (∏ p ∈ oppositePairs σ, (z p.1 - z p.2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact hz.sub_ne_zero (ne_of_lt (Finset.mem_filter.mp hp).2.1)
  unfold explicitSolution delta clearedSolution
  rw [Finset.prod_inv_distrib, ← hprod]
  field_simp
  <;> ring

theorem analyticAt_clearedSolution {d : ℕ} (σ : Fin d → Sign) (z : Point d) :
    AnalyticAt ℂ (clearedSolution σ) z := by
  have hphase : AnalyticAt ℂ (phase σ) z := by
    apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_sum
    intro j _
    exact analyticAt_const.mul (analyticAt_coord z j)
  exact hphase.cexp'.mul (analyticAt_finset_prod (samePairs σ)
    (fun p x => x p.1 - x p.2) z
    (fun p _ => (analyticAt_coord z p.1).sub (analyticAt_coord z p.2)))

/-- Pointwise clearing preserves every linear relation on the collision-free domain. -/
theorem clear_linear_relation {d : ℕ} (c : (Fin d → Sign) → ℂ)
    {z : Point d} (hz : CollisionFree z)
    (h : (∑ σ, c σ * explicitSolution σ z) = 0) :
    (∑ σ, c σ * clearedSolution σ z) = 0 := by
  calc
    _ = vandermonde z * ∑ σ, c σ * explicitSolution σ z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [← vandermonde_mul_explicitSolution σ hz]
      ring
    _ = 0 := by rw [h, mul_zero]

/-- A locally vanishing relation of the cleared functions vanishes everywhere.
The ambient complex vector space is preconnected, with no collision domain involved. -/
theorem cleared_relation_global_of_local {d : ℕ} (c : (Fin d → Sign) → ℂ)
    (z₀ : Point d)
    (hlocal : (fun z => ∑ σ, c σ * clearedSolution σ z) =ᶠ[nhds z₀]
      (fun _ => (0 : ℂ))) :
    (fun z => ∑ σ, c σ * clearedSolution σ z) = (fun _ => (0 : ℂ)) := by
  apply AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) _ analyticOnNhd_const hlocal
  intro z _
  apply Finset.analyticAt_sum
  intro σ _
  exact analyticAt_const.mul (analyticAt_clearedSolution σ z)

/-- Every relation on a nonempty open collision-free domain extends, after
clearing, to the whole ambient vector space. This includes fixed half-plane
and ordered domains once their elementary openness/nonemptiness is supplied. -/
theorem cleared_relation_global_of_open {d : ℕ} (c : (Fin d → Sign) → ℂ)
    (U : Set (Point d)) (hU : IsOpen U) (hne : U.Nonempty)
    (hfree : ∀ z ∈ U, CollisionFree z)
    (hrelation : ∀ z ∈ U, (∑ σ, c σ * explicitSolution σ z) = 0) :
    (fun z => ∑ σ, c σ * clearedSolution σ z) = (fun _ => (0 : ℂ)) := by
  obtain ⟨z₀, hz₀⟩ := hne
  apply cleared_relation_global_of_local c z₀
  filter_upwards [hU.mem_nhds hz₀] with z hz
  exact clear_linear_relation c (hfree z hz) (hrelation z hz)

end BourgadeHuang.CMS
