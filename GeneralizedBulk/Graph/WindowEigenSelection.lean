import GeneralizedBulk.Counting.RankedWindow
import GeneralizedBulk.Graph.MicroscopicScalarState

/-! Measurable literal eigen-indices of the sorted microscopic window. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem microscopicEigenvalue_antitone (n : ℕ) (ω : Ω) (E sigma : ℝ) (hsigma : 0 < sigma) :
    Antitone (D.microscopicEigenvalue n ω E sigma) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (D.ordered n ω i j hij) E)
    (mul_nonneg (Nat.cast_nonneg _) hsigma.le)

def windowEigenCount (n : ℕ) (ω : Ω) (E sigma a b : ℝ) : ℕ :=
  intervalCount (finiteCountingConfiguration (D.microscopicEigenvalue n ω E sigma)) a b

def windowEigenIndex (n : ℕ) (ω : Ω) (E sigma a b : ℝ) (k : ℕ) : Fin (N n) :=
  rankedWindowIndex (D.size_pos n) (D.microscopicEigenvalue n ω E sigma) a b k

theorem measurable_windowEigenCount (n : ℕ) (E sigma a b : ℝ) :
    Measurable (fun ω => D.windowEigenCount n ω E sigma a b) := by
  exact (measurable_intervalCount a b).comp
    (measurable_fst.comp ((D.measurable_microscopicCountingState n E sigma 0).subtype_val))

theorem measurable_windowEigenIndex (n : ℕ) (E sigma a b : ℝ) (k : ℕ) :
    Measurable (fun ω => D.windowEigenIndex n ω E sigma a b k) := by
  apply measurable_rankedWindowIndex
  intro i
  exact ((D.measurable_eigenvalue n i).sub_const E).const_mul _

theorem windowEigenIndex_injective {m : ℕ} (n : ℕ) (ω : Ω) (E sigma a b : ℝ)
    (hsigma : 0 < sigma) (hm : m ≤ D.windowEigenCount n ω E sigma a b) :
    Function.Injective (fun k : Fin m => D.windowEigenIndex n ω E sigma a b k.val) :=
  rankedWindowIndex_injective (D.size_pos n) _ (D.microscopicEigenvalue_antitone n ω E sigma hsigma) a b hm

theorem windowEigenIndex_matches_occurrence (n : ℕ) (ω : Ω) (E sigma a b : ℝ)
    (hsigma : 0 < sigma) (k : ℕ) (hk : k < D.windowEigenCount n ω E sigma a b) :
    D.microscopicEigenvalue n ω E sigma (D.windowEigenIndex n ω E sigma a b k) =
      windowOccurrence (D.microscopicCountingState n ω E sigma 0).val.1 a b k :=
  rankedWindowIndex_matches_occurrence (D.size_pos n) _
    (D.microscopicEigenvalue_antitone n ω E sigma hsigma) a b k hk

theorem windowEigenIndex_near (n : ℕ) (ω : Ω) (E sigma R : ℝ)
    (hsigma : 0 < sigma) (k : ℕ) (hk : k < D.windowEigenCount n ω E sigma (-R) R) :
    |D.eigenvalue n ω (D.windowEigenIndex n ω E sigma (-R) R k) - E| ≤
      microscopicStep (N n) sigma * R := by
  have hmem := rankedWindowIndex_mem (D.size_pos n) _
    (D.microscopicEigenvalue_antitone n ω E sigma hsigma) (-R) R k hk
  have hb : |D.microscopicEigenvalue n ω E sigma (D.windowEigenIndex n ω E sigma (-R) R k)| ≤ R :=
    abs_le.mpr hmem
  have hc : 0 < (N n : ℝ) * sigma := mul_pos (Nat.cast_pos.mpr (D.size_pos n)) hsigma
  rw [microscopicEigenvalue,abs_mul,abs_of_pos hc] at hb
  have hh : |D.eigenvalue n ω (D.windowEigenIndex n ω E sigma (-R) R k) - E| ≤
      R / ((N n : ℝ) * sigma) := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb)
  simpa only [microscopicStep,div_eq_mul_inv,mul_comm] using hh

theorem windowEigenIndex_nonconstant_eventually (E sigma R : ℝ) (hsigma : 0 < sigma)
    (hE : E ≠ (d : ℝ)) : ∀ᶠ n in atTop, ∀ ω : Ω, ∀ k : ℕ,
      k < D.windowEigenCount n ω E sigma (-R) R →
      D.windowEigenIndex n ω E sigma (-R) R k ≠ ⟨0,D.size_pos n⟩ := by
  filter_upwards [D.microscopic_window_nonconstant_eventually E sigma R hE] with n hn
  intro ω k hk
  apply hn ω
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,D.windowEigenIndex_near n ω E sigma R hsigma k hk⟩

/-- Outside the retained-count stratum an independent nearby bulk selection
can fill the list. It is supplied later by the HY quantile adapter. -/
def paddedWindowSelection {m : ℕ} (n : ℕ) (ω : Ω) (E sigma a b : ℝ)
    (fallback : Ω → Fin m → Fin (N n)) : Fin m → Fin (N n) :=
  if m ≤ D.windowEigenCount n ω E sigma a b then
    fun k => D.windowEigenIndex n ω E sigma a b k.val else fallback ω

theorem measurable_paddedWindowSelection {m : ℕ} (n : ℕ) (E sigma a b : ℝ)
    (fallback : Ω → Fin m → Fin (N n)) (hfallback : ∀ i, Measurable (fun ω => fallback ω i))
    (i : Fin m) : Measurable (fun ω => D.paddedWindowSelection n ω E sigma a b fallback i) := by
  simp only [paddedWindowSelection,ite_apply]
  apply Measurable.ite
    (measurableSet_le measurable_const (D.measurable_windowEigenCount n E sigma a b))
    (D.measurable_windowEigenIndex n E sigma a b i.val) (hfallback i)

theorem paddedWindowSelection_of_count_eq {m : ℕ} (n : ℕ) (ω : Ω) (E sigma a b : ℝ)
    (fallback : Ω → Fin m → Fin (N n)) (hm : D.windowEigenCount n ω E sigma a b = m) :
    D.paddedWindowSelection n ω E sigma a b fallback = fun k => D.windowEigenIndex n ω E sigma a b k.val := by
  simp only [paddedWindowSelection,hm,le_refl,ite_true]

end GeneralizedBulk.External.RegularSpectralData
