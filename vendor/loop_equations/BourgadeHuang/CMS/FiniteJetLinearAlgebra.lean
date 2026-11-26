import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Linear algebra for the finite-jet spanning argument.

The ambient space may consist of functions defined beyond the domain under study.
For that reason the correct hypothesis is that a vanishing jet implies vanishing
*restriction*, rather than injectivity on the whole ambient function space.
These lemmas do not assume spanning. Their analytic/CMS hypotheses are to be
supplied by the separate jet-uniqueness and explicit-independence arguments.
-/

noncomputable section
open scoped BigOperators
open Module

namespace BourgadeHuang.CMS

variable {K V W J ι : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup J] [Module K J] [Fintype ι]

/-- A finite family independent after restriction is independent in its jets,
provided zero jets imply zero restrictions. -/
theorem linearIndependent_jets_of_restriction
    (jet : V →ₗ[K] J) (restrict : V →ₗ[K] W)
    (hzero : ∀ v, jet v = 0 → restrict v = 0) (family : ι → V)
    (hind : LinearIndependent K (fun i => restrict (family i))) :
    LinearIndependent K (fun i => jet (family i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hj : jet (∑ i, c i • family i) = 0 := by
    simpa only [map_sum, map_smul] using hc
  have hr : restrict (∑ i, c i • family i) = 0 := hzero _ hj
  apply Fintype.linearIndependent_iff.mp hind c
  simpa only [map_sum, map_smul] using hr

/-- Matching the finite jet produces an expansion after restriction.
The number of independent branches is exactly the dimension of the jet target. -/
theorem exists_expansion_of_finite_jets [FiniteDimensional K J]
    (jet : V →ₗ[K] J) (restrict : V →ₗ[K] W)
    (hzero : ∀ v, jet v = 0 → restrict v = 0) (family : ι → V)
    (hind : LinearIndependent K (fun i => restrict (family i)))
    (hcard : Fintype.card ι = Module.finrank K J) (v : V) :
    ∃ c : ι → K, restrict v = ∑ i, c i • restrict (family i) := by
  classical
  have hji := linearIndependent_jets_of_restriction jet restrict hzero family hind
  have hspan := hji.span_eq_top_of_card_eq_finrank' hcard
  let b : Basis ι K J := Basis.mk hji (by rw [hspan])
  let c : ι → K := fun i => b.repr (jet v) i
  have hmatch : (∑ i, c i • jet (family i)) = jet v := by
    simpa [c, b] using b.sum_repr (jet v)
  have hz : jet (v - ∑ i, c i • family i) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul]
    rw [hmatch, sub_self]
  have hr := hzero _ hz
  rw [map_sub, sub_eq_zero] at hr
  refine ⟨c, ?_⟩
  simpa only [map_sum, map_smul] using hr

end BourgadeHuang.CMS
