import BourgadeHuang.CMS.Basic

/-! The beta=2 rational-exponential functions of Appendix D.2, and their genuine
coordinate derivatives. All assertions are uniform in the dimension. -/

noncomputable section
open scoped BigOperators

namespace BourgadeHuang.CMS

/-- Opposite-sign pairs are ordered once, exactly as in (D.8). -/
def oppositePairs {d : ℕ} (σ : Fin d → Sign) : Finset (Fin d × Fin d) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ σ p.1 ≠ σ p.2)

/-- The rational factor in (D.8); all exponents are zero or minus one. -/
def delta {d : ℕ} (σ : Fin d → Sign) (z : Point d) : ℂ :=
  ∏ p ∈ oppositePairs σ, (z p.1 - z p.2)⁻¹

def phase {d : ℕ} (σ : Fin d → Sign) (z : Point d) : ℂ :=
  Complex.I * ∑ j, signValue (σ j) * z j

/-- The actual analytic function in (D.9), rather than a formal differential expression. -/
def explicitSolution {d : ℕ} (σ : Fin d → Sign) (z : Point d) : ℂ :=
  Complex.exp (phase σ z) * delta σ z

/-- Each coordinate projection is analytic in the standard complex normed-space sense. -/
theorem analyticAt_coord {d : ℕ} (z : Point d) (i : Fin d) :
    AnalyticAt ℂ (fun x : Point d => x i) z :=
  (ContinuousLinearMap.proj (R := ℂ) i).analyticAt z

theorem analyticAt_finset_prod {ι : Type*} [DecidableEq ι] {d : ℕ}
    (s : Finset ι) (f : ι → Point d → ℂ) (z : Point d)
    (hf : ∀ k ∈ s, AnalyticAt ℂ (f k) z) :
    AnalyticAt ℂ (fun x => ∏ k ∈ s, f k x) z := by
  induction s using Finset.induction_on with
  | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : Point d => (1 : ℂ)) z)
  | @insert k s hks ih =>
    simpa only [Finset.prod_insert hks] using
      (hf k (Finset.mem_insert_self k s)).mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- The explicit functions are holomorphic off every collision hyperplane. -/
theorem analyticAt_explicitSolution {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) : AnalyticAt ℂ (explicitSolution σ) z := by
  have hphase : AnalyticAt ℂ (phase σ) z := by
    apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_sum
    intro j _
    exact analyticAt_const.mul (analyticAt_coord z j)
  have hdelta : AnalyticAt ℂ (delta σ) z := by
    apply analyticAt_finset_prod
    intro p hp
    exact ((analyticAt_coord z p.1).sub (analyticAt_coord z p.2)).inv
      (hz.sub_ne_zero (ne_of_lt (Finset.mem_filter.mp hp).2.1))
  exact hphase.cexp'.mul hdelta

end BourgadeHuang.CMS
