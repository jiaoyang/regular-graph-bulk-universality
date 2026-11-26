import GaussianWave.BS.FiniteTestSelection

/-! Countably many finite observation requirements can be realized by
actual samples on a strict graph-size subsequence. The source probability
space may change with graph size. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS

/-- A genuine diagonal probabilistic-method construction. Row b requests
the first b+1 tests at precision ε_b; no deterministic realization is an
input. The energy budget is uniform across all block rows. -/
theorem exists_diagonal_samples_of_second_error_tendsto
    (Ω : ℕ → Type*) [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (X : ℕ → ∀ n,ℕ → Ω n → ℝ) (target : ℕ → ℕ → ℝ)
    (H : ℕ → ∀ n,Ω n → ℝ)
    (hH : ∀ b n,Integrable (H b n) (P n)) (hH0 : ∀ b n ω,0 ≤ H b n ω)
    (hX : ∀ b n i,Integrable (fun ω => (X b n i ω-target b i)^2) (P n))
    (herror : ∀ b i,Tendsto (fun n => ∫ ω,(X b n i ω-target b i)^2 ∂P n) atTop (𝓝 0))
    (B M : ℝ) (hM : 0 < M) (hbudget : B/M < 1)
    (henergy : ∀ b,∀ᶠ n in atTop,(∫ ω,H b n ω ∂P n) ≤ B)
    (ε : ℕ → ℝ) (hε : ∀ b,0 < ε b) :
    ∃ (n : ℕ → ℕ),StrictMono n ∧ ∃ (ω : ∀ b,Ω (n b)),
      (∀ b,H b (n b) (ω b)<M) ∧
      ∀ b (i : Fin (b+1)),|X b (n b) i (ω b)-target b i|<ε b := by
  let V (b n : ℕ) := ∑ i : Fin (b+1),∫ ω,(X b n i ω-target b i)^2 ∂P n
  have hV (b n : ℕ) (i : Fin (b+1)) :
      (∫ ω,(X b n i ω-target b i)^2 ∂P n) ≤ V b n := by
    dsimp only [V]
    exact Finset.single_le_sum
      (f := fun j : Fin (b+1) => ∫ ω,(X b n j ω-target b j)^2 ∂P n)
      (fun j _ => integral_nonneg (fun _ => sq_nonneg _)) (Finset.mem_univ i)
  have hVlimit (b : ℕ) : Tendsto (V b) atTop (𝓝 0) := by
    simpa only [V,Finset.sum_const_zero] using
      tendsto_finset_sum (Finset.univ : Finset (Fin (b+1)))
        (fun (i : Fin (b+1)) _ => herror b i)
  have hrow (b : ℕ) : ∀ᶠ n in atTop,∃ ω : Ω n,H b n ω<M ∧
      ∀ i : Fin (b+1),|X b n i ω-target b i|<ε b := by
    have ht : Tendsto (fun n => B/M+((b+1 : ℕ) : ℝ)*V b n/(ε b)^2)
        atTop (𝓝 (B/M)) := by
      simpa only [mul_zero,zero_div,add_zero] using
        tendsto_const_nhds.add (((hVlimit b).const_mul ((b+1 : ℕ) : ℝ)).div_const ((ε b)^2))
    filter_upwards [henergy b,ht.eventually (gt_mem_nhds hbudget)] with n hn hbud
    exact exists_sample_of_variance_energy_budget (P n) (fun i : Fin (b+1) => X b n i)
      (fun i => target b i) (H b n) (hH b n) (hH0 b n) (fun i => hX b n i)
      B (V b n) M (ε b) hM (hε b) hn (hV b n) (by simpa only [Fintype.card_fin] using hbud)
  obtain ⟨n,hn,hrealize⟩ := extraction_forall_of_eventually hrow
  choose ω hωH hωX using hrealize
  exact ⟨n,hn,ω,hωH,hωX⟩

end GaussianWave.BS
