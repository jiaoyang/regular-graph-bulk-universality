import BourgadeHuang.CMS.Basis
import BourgadeHuang.CMS.LiftedSolutions

/-! Unique expansion for the original beta=2 system. The quotient by the mixed
Vandermonde is constructed as an actual analytic function; its reduced PDE is
derived from the original equations and the proved analytic gauge theorem. -/
noncomputable section
open scoped BigOperators Topology
open Set
namespace BourgadeHuang.CMS

/-- Mixed Vandermonde expressed in the combined coordinate space. -/
def combinedGauge (n m : ℕ) : Point (n + m) → ℂ :=
  blockFunction (mixedVandermonde (n := n) (m := m))

/-- Actual gauge quotient of a combined-coordinate function. -/
def gaugeQuotient {n m : ℕ} (F : Point (n + m) → ℂ) (z : Point (n + m)) : ℂ :=
  F z / combinedGauge n m z

/-- The original-system branch, equal to formula (6.1) off collisions. -/
def originalBranch {n m : ℕ} (σ : Fin (n + m) → Sign) (z : Point (n + m)) : ℂ :=
  combinedGauge n m z * explicitSolution σ z

@[simp] theorem combinedGauge_append {n m : ℕ} (t : Point n) (s : Point m) :
    combinedGauge n m (Fin.append t s) = mixedVandermonde t s := by
  simp [combinedGauge]

@[simp] theorem originalBranch_append {n m : ℕ} (σ : Fin (n + m) → Sign)
    (t : Point n) (s : Point m) :
    originalBranch (n := n) (m := m) σ (Fin.append t s) = liftedExplicitSolution σ t s := by
  simp [originalBranch, liftedExplicitSolution]

theorem analyticAt_combinedGauge {n m : ℕ} (z : Point (n + m)) :
    AnalyticAt ℂ (combinedGauge n m) z := by
  unfold combinedGauge blockFunction mixedVandermonde
  apply analyticAt_finset_prod
  intro i _
  apply analyticAt_finset_prod
  intro a _
  exact (analyticAt_coord z (Fin.castAdd m i)).sub (analyticAt_coord z (Fin.natAdd n a))

theorem combinedGauge_ne_zero {n m : ℕ} {z : Point (n + m)} (hz : CollisionFree z) :
    combinedGauge n m z ≠ 0 := by
  let t : Point n := fun i => z (Fin.castAdd m i)
  let s : Point m := fun a => z (Fin.natAdd n a)
  have happ : Fin.append t s = z := Fin.append_castAdd_natAdd
  have hc := ((collisionFree_append t s).mp (happ ▸ hz)).2.2
  have hp := mixedVandermonde_ne_zero hc
  simpa only [combinedGauge, blockFunction, t, s] using hp

theorem analyticAt_gaugeQuotient {n m : ℕ} (F : Point (n + m) → ℂ)
    {z : Point (n + m)} (hz : CollisionFree z) (hf : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (gaugeQuotient (n := n) (m := m) F) z :=
  hf.div (analyticAt_combinedGauge z) (combinedGauge_ne_zero hz)

/-- Original equations expressed at the split coordinates of a combined point. -/
def SolvesOriginalAt {n m : ℕ} (F : Point (n + m) → ℂ) (z : Point (n + m)) : Prop :=
  (∀ i, leftOriginal i (restrictBlocks F)
    (fun j => z (Fin.castAdd m j)) (fun a => z (Fin.natAdd n a)) = 0) ∧
  (∀ a, rightOriginal a (restrictBlocks F)
    (fun j => z (Fin.castAdd m j)) (fun b => z (Fin.natAdd n b)) = 0)

/-- The reduced equations for F/P are consequences, not assumptions. -/
theorem gaugeQuotient_solves {n m : ℕ} (F : Point (n + m) → ℂ)
    {z : Point (n + m)} (hz : CollisionFree z) (hf : AnalyticAt ℂ F z)
    (hsolve : SolvesOriginalAt (n := n) (m := m) F z) :
    ∀ r, reducedOperator r (gaugeQuotient (n := n) (m := m) F) z = 0 := by
  let t : Point n := fun i => z (Fin.castAdd m i)
  let s : Point m := fun a => z (Fin.natAdd n a)
  have happ : Fin.append t s = z := Fin.append_castAdd_natAdd
  have hfree : CollisionFree (Fin.append t s) := happ ▸ hz
  have hc := ((collisionFree_append t s).mp hfree).2.2
  have heq : ∀ t s, CrossDistinct t s →
      mixedVandermonde t s * restrictBlocks (gaugeQuotient (n := n) (m := m) F) t s =
        restrictBlocks F t s := by
    intro t s hc
    simp only [restrictBlocks, gaugeQuotient, combinedGauge_append]
    field_simp [mixedVandermonde_ne_zero hc]
  have hop := originalOperators_congr_crossDistinct
    (fun t s => mixedVandermonde t s * restrictBlocks (gaugeQuotient (n := n) (m := m) F) t s)
    (restrictBlocks F) heq t s hc
  have han : AnalyticAt ℂ (gaugeQuotient (n := n) (m := m) F) (Fin.append t s) :=
    happ ▸ analyticAt_gaugeQuotient F hz hf
  have hg := (analytic_gauge_system_iff t s (gaugeQuotient (n := n) (m := m) F)
    hfree han).mp (by
      constructor
      · intro i
        rw [hop.1 i]
        exact hsolve.1 i
      · intro a
        rw [hop.2 a]
        exact hsolve.2 a)
  simpa only [happ] using hg

/-- Multiplication by P takes reduced expansions to original expansions. -/
theorem sum_originalBranch {n m : ℕ} (c : (Fin (n + m) → Sign) → ℂ)
    (z : Point (n + m)) :
    (∑ σ, c σ * originalBranch (n := n) (m := m) σ z) =
      combinedGauge n m z * ∑ σ, c σ * explicitSolution σ z := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  unfold originalBranch
  ring

/-- Unique expansion in the original beta=2 branches on any nonempty connected
open collision-free domain. The only analytic/PDE hypotheses concern F itself. -/
theorem existsUnique_original_expansion {n m : ℕ}
    (U : Set (Point (n + m))) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : U.Nonempty) (hfree : ∀ z ∈ U, CollisionFree z)
    {F : Point (n + m) → ℂ} (hf : AnalyticOnNhd ℂ F U)
    (hsolve : ∀ z ∈ U, SolvesOriginalAt (n := n) (m := m) F z) :
    ∃! c : (Fin (n + m) → Sign) → ℂ,
      EqOn F (fun z => ∑ σ, c σ * originalBranch (n := n) (m := m) σ z) U := by
  have hg : AnalyticOnNhd ℂ (gaugeQuotient (n := n) (m := m) F) U :=
    fun z hz => analyticAt_gaugeQuotient F (hfree z hz) (hf z hz)
  have hgpde : ∀ z ∈ U, ∀ r,
      reducedOperator r (gaugeQuotient (n := n) (m := m) F) z = 0 :=
    fun z hz => gaugeQuotient_solves F (hfree z hz) (hf z hz) (hsolve z hz)
  obtain ⟨c, hc, _⟩ := existsUnique_explicit_expansion U hU hconn hne hfree hg hgpde
  have hexp : EqOn F (fun z => ∑ σ, c σ * originalBranch (n := n) (m := m) σ z) U := by
    intro z hz
    change F z = ∑ σ, c σ * originalBranch (n := n) (m := m) σ z
    have hcz := hc hz
    dsimp only at hcz
    rw [sum_originalBranch (n := n) (m := m) c z, ← hcz]
    unfold gaugeQuotient
    field_simp [combinedGauge_ne_zero (hfree z hz)]
  refine ⟨c, hexp, ?_⟩
  intro c' hc'
  apply explicit_expansion_coefficients_unique U hU hne hfree
  intro z hz
  apply mul_left_cancel₀ (combinedGauge_ne_zero (hfree z hz))
  rw [← sum_originalBranch, ← sum_originalBranch]
  exact (hc' hz).symm.trans (hexp hz)

/-- Each original branch is analytic on every collision-free neighborhood. -/
theorem analyticAt_originalBranch {n m : ℕ} (σ : Fin (n + m) → Sign)
    {z : Point (n + m)} (hz : CollisionFree z) :
    AnalyticAt ℂ (originalBranch (n := n) (m := m) σ) z :=
  (analyticAt_combinedGauge z).mul (analyticAt_explicitSolution σ hz)

/-- Each branch satisfies the original equations in combined-coordinate notation. -/
theorem originalBranch_solves {n m : ℕ} (σ : Fin (n + m) → Sign)
    {z : Point (n + m)} (hz : CollisionFree z) :
    SolvesOriginalAt (n := n) (m := m) (originalBranch (n := n) (m := m) σ) z := by
  let t : Point n := fun i => z (Fin.castAdd m i)
  let s : Point m := fun a => z (Fin.natAdd n a)
  have happ : Fin.append t s = z := Fin.append_castAdd_natAdd
  have hfun : restrictBlocks (originalBranch (n := n) (m := m) σ) =
      liftedExplicitSolution σ := by
    funext t s
    exact originalBranch_append σ t s
  have h := liftedExplicitSolution_solves σ t s (happ ▸ hz)
  simpa only [SolvesOriginalAt, hfun, t, s] using h

/-- Nonzero multiplication by P preserves independence on the domain. -/
theorem linearIndependent_originalBranch_on_open {n m : ℕ}
    (U : Set (Point (n + m))) (hU : IsOpen U) (hne : U.Nonempty)
    (hfree : ∀ z ∈ U, CollisionFree z) :
    LinearIndependent ℂ (fun σ : Fin (n + m) → Sign =>
      fun z : U => originalBranch (n := n) (m := m) σ z.val) := by
  apply linearIndependent_iff_injective_fintypeLinearCombination.mpr
  intro c c' heq
  apply explicit_expansion_coefficients_unique U hU hne hfree
  intro z hz
  have he := congrFun heq ⟨z, hz⟩
  simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at he
  rw [sum_originalBranch, sum_originalBranch] at he
  exact mul_left_cancel₀ (combinedGauge_ne_zero (hfree z hz)) he

/-- Unique original-system expansion on the ordered mixed half-plane domains
used for the exponential observables. -/
theorem existsUnique_original_expansion_orderedMixed {n m : ℕ}
    (J : Finset (Fin (n + m))) (σ : Fin (n + m) → Sign)
    {F : Point (n + m) → ℂ}
    (hf : AnalyticOnNhd ℂ F (OrderedMixedDomain (n + m) J σ))
    (hsolve : ∀ z ∈ OrderedMixedDomain (n + m) J σ,
      SolvesOriginalAt (n := n) (m := m) F z) :
    ∃! c : (Fin (n + m) → Sign) → ℂ,
      EqOn F (fun z => ∑ τ, c τ * originalBranch (n := n) (m := m) τ z)
        (OrderedMixedDomain (n + m) J σ) :=
  existsUnique_original_expansion (OrderedMixedDomain (n + m) J σ)
    (orderedMixedDomain_isOpen (n + m) J σ)
    (orderedMixedDomain_isConnected (n + m) J σ).isPreconnected
    (orderedMixedDomain_nonempty (n + m) J σ)
    (fun _ hz => orderedMixedDomain_collisionFree hz) hf hsolve


end BourgadeHuang.CMS
