import BourgadeHuang.CMS.DeformedSolutionSpace
import BourgadeHuang.CMS.FiniteJetLinearAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Powerset

/-! Finite-jet spanning and an actual basis for general-coupling deformed
CMS solutions. Spanning follows from proved analytic jet uniqueness and
independence of the supplied actual solution family, not a classification
hypothesis or a presumed solution-space dimension. -/
noncomputable section
open Set
open scoped BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
variable {d : ℕ} {ι : Type*} [Fintype ι]
  (β : ℂ) (c : Fin d → ℂ) (U : Set (Point d))
  (family : ι → Point d → ℂ)
  (hfamily : ∀a,AnalyticOnNhd ℂ (family a) U ∧
    ∀z∈U,∀i,deformedOperator β c i (family a) z=0)

/-- An actual given branch, as a member of the analytic deformed-PDE space. -/
def deformedFamilyInSpace (a : ι) : deformedSolutionSpace β c U :=
  ⟨family a,hfamily a⟩

include hfamily in
/-- The actual finite linear combination of branches satisfies the same PDE. -/
theorem deformed_combination_is_solution (a : ι → ℂ) :
    AnalyticOnNhd ℂ (fun z=>∑i,a i*family i z) U ∧
      ∀z∈U,∀i,deformedOperator β c i (fun w=>∑j,a j*family j w) z=0 := by
  classical
  let v : deformedSolutionSpace β c U := ∑i,a i•deformedFamilyInSpace β c U family hfamily i
  have he : v.val=(fun z=>∑i,a i*family i z) := by
    ext z
    simp [v,deformedFamilyInSpace,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simpa only [he] using v.property

include hfamily in
/-- A family of 2^d independently restricted genuine deformed solutions
spans every actual analytic solution on a connected collision-free domain. -/
theorem exists_deformed_expansion
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (hfree : ∀z∈U,CollisionFree z)
    (hind : LinearIndependent ℂ (fun a (z : U)=>family a z.val))
    (hcard : Fintype.card ι=2^d)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀z∈U,∀i,deformedOperator β c i f z=0) :
    ∃a : ι → ℂ,EqOn f (fun z=>∑i,a i*family i z) U := by
  classical
  obtain ⟨z,hz⟩ := hne
  let zU : U := ⟨z,hz⟩
  let v : deformedSolutionSpace β c U := ⟨f,hf,hsolve⟩
  have hj : Fintype.card ι=Module.finrank ℂ (Finset (Fin d) → ℂ) := by
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_finset,Fintype.card_fin] using hcard
  obtain ⟨a,ha⟩ := exists_expansion_of_finite_jets
    (deformedSolutionJet β c U zU) (deformedSolutionRestriction β c U)
    (deformedSolutionRestriction_eq_zero_of_jet_eq_zero β c U hU hconn hfree zU)
    (deformedFamilyInSpace β c U family hfamily) hind hj v
  refine ⟨a,?_⟩
  intro w hw
  have he := congrFun ha ⟨w,hw⟩
  simpa only [deformedSolutionRestriction,LinearMap.coe_mk,AddHom.coe_mk,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,deformedFamilyInSpace] using he

/-- Equality of combinations on the domain implies equality of coefficients. -/
theorem deformed_expansion_coefficients_unique
    (hind : LinearIndependent ℂ (fun a (z : U)=>family a z.val))
    {a b : ι → ℂ}
    (heq : EqOn (fun z=>∑i,a i*family i z) (fun z=>∑i,b i*family i z) U) : a=b := by
  apply hind.fintypeLinearCombination_injective
  funext z
  simpa [Fintype.linearCombination_apply,Pi.smul_apply,smul_eq_mul] using heq z.property

include hfamily in
/-- Unique expansion in any independently proved 2^d-element family of
actual deformed CMS solutions. No condition is imposed outside the domain. -/
theorem existsUnique_deformed_expansion
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (hfree : ∀z∈U,CollisionFree z)
    (hind : LinearIndependent ℂ (fun a (z : U)=>family a z.val))
    (hcard : Fintype.card ι=2^d)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀z∈U,∀i,deformedOperator β c i f z=0) :
    ∃!a : ι → ℂ,EqOn f (fun z=>∑i,a i*family i z) U := by
  obtain ⟨a,ha⟩ := exists_deformed_expansion β c U family hfamily hU hconn hne hfree hind hcard hf hsolve
  refine ⟨a,ha,?_⟩
  intro b hb
  apply deformed_expansion_coefficients_unique U family hind
  intro z hz
  exact (hb hz).symm.trans (ha hz)

/-- Each branch in the range of genuine solution restriction. -/
def deformedRestrictedFamily (a : ι) : LinearMap.range (deformedSolutionRestriction β c U) :=
  (deformedSolutionRestriction β c U).rangeRestrict (deformedFamilyInSpace β c U family hfamily a)

omit [Fintype ι] in
@[simp] theorem deformedRestrictedFamily_apply (a : ι) (z : U) :
    (deformedRestrictedFamily β c U family hfamily a).val z=family a z.val := rfl

/-- An actual basis of the restricted solution space, derived from the
finite-jet theorem and a proved independent branch family. -/
def deformedRestrictedBasis
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (hfree : ∀z∈U,CollisionFree z)
    (hind : LinearIndependent ℂ (fun a (z : U)=>family a z.val))
    (hcard : Fintype.card ι=2^d) :
    Basis ι ℂ (LinearMap.range (deformedSolutionRestriction β c U)) := by
  classical
  have hi : LinearIndependent ℂ (deformedRestrictedFamily β c U family hfamily) :=
    LinearIndependent.of_comp (LinearMap.range (deformedSolutionRestriction β c U)).subtype hind
  apply Basis.mk hi
  intro g _
  obtain ⟨f,hf⟩ := g.property
  obtain ⟨a,ha⟩ := exists_deformed_expansion β c U family hfamily hU hconn hne hfree hind hcard
    f.property.1 f.property.2
  have he : g=∑i,a i•deformedRestrictedFamily β c U family hfamily i := by
    apply Subtype.ext
    funext z
    have hfz := congrFun hf z
    simpa only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,
      smul_eq_mul,deformedRestrictedFamily_apply] using hfz.symm.trans (ha z.property)
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

include hfamily in
/-- Exact dimension of the actual restricted deformed solution space. -/
theorem finrank_deformedRestrictedSolutionSpace
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (hfree : ∀z∈U,CollisionFree z)
    (hind : LinearIndependent ℂ (fun a (z : U)=>family a z.val))
    (hcard : Fintype.card ι=2^d) :
    Module.finrank ℂ (LinearMap.range (deformedSolutionRestriction β c U))=2^d := by
  rw [Module.finrank_eq_card_basis
    (deformedRestrictedBasis β c U family hfamily hU hconn hne hfree hind hcard),hcard]

end BourgadeHuang.CMS
