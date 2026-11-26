import BourgadeHuang.CMS.Volterra
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Finite Duhamel construction of the principal backward evolution. Strict
lowering of a finite degree makes the expansion terminate exactly. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 600000

/-- Scalar variation of constants with terminal value zero. -/
def backwardIntegral (lam : ℂ) (f : ℝ → ℂ) (t s : ℝ) : ℂ :=
  -Complex.exp (lam*(t:ℂ)) * ∫ u in t..s, Complex.exp (-lam*(u:ℂ))*f u

lemma continuous_intervalIntegral_endpoints {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    {f : X → ℝ → ℂ} (hf : Continuous (Function.uncurry f))
    {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => ∫ u in a x..b x, f x u) := by
  have h1 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ:=volume) (a₀:=0) hf hb
  have h2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ:=volume) (a₀:=0) hf ha
  convert h1.sub h2 using 1
  ext x
  have hc : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 (b x))
    (hc.intervalIntegrable 0 (a x))).symm

lemma continuous_backwardIntegral {lam : ℂ} {f : ℝ → ℝ → ℂ}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p : ℝ×ℝ => backwardIntegral lam (f p.2) p.1 p.2) := by
  unfold backwardIntegral
  apply Continuous.mul
  · fun_prop
  · apply continuous_intervalIntegral_endpoints _ continuous_fst continuous_snd
    apply Continuous.mul
    · fun_prop
    · exact hf.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)

lemma hasDerivAt_backwardIntegral (lam : ℂ) {f : ℝ → ℂ} (hf : Continuous f) (t s : ℝ) :
    HasDerivAt (fun t => backwardIntegral lam f t s)
      (lam*backwardIntegral lam f t s + f t) t := by
  have hg : Continuous (fun u : ℝ => Complex.exp (-lam*(u:ℂ))*f u) := by fun_prop
  have hi : HasDerivAt (fun t => ∫ u in t..s, Complex.exp (-lam*(u:ℂ))*f u)
      (-(Complex.exp (-lam*(t:ℂ))*f t)) t := by
    convert (hg.integral_hasStrictDerivAt s t).hasDerivAt.neg using 1
    funext x
    exact intervalIntegral.integral_symm _ _
  have he := (((hasDerivAt_id t).ofReal_comp).const_mul lam).cexp.neg
  have hexp : Complex.exp (lam*(t:ℂ))*Complex.exp (-lam*(t:ℂ))=1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1 <;> congr 1 <;> ring
  convert he.mul hi using 1
  dsimp [backwardIntegral]
  simp only [Complex.ofReal_one,mul_one]
  linear_combination -(f t)*hexp

@[simp] lemma backwardIntegral_self (lam : ℂ) (f : ℝ → ℂ) (s : ℝ) :
    backwardIntegral lam f s s = 0 := by simp [backwardIntegral]

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The exact finite Duhamel terms. -/
def triangularTerm (lam : J → ℂ) (N : ℝ → J → J → ℂ) :
    ℕ → ℝ → ℝ → J → J → ℂ
  | 0,t,s,i,j => if i=j then Complex.exp (lam i*((t-s:ℝ):ℂ)) else 0
  | n+1,t,s,i,j => backwardIntegral (lam i)
      (fun u => ∑ k, N u i k * triangularTerm lam N n u s k j) t s

lemma continuous_triangularTerm (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (hN : ∀ i j, Continuous (fun t => N t i j)) (n : ℕ) (i j : J) :
    Continuous (fun p : ℝ×ℝ => triangularTerm lam N n p.1 p.2 i j) := by
  induction n generalizing i j with
  | zero => simp only [triangularTerm]; split_ifs <;> fun_prop
  | succ n ih =>
    simp only [triangularTerm]
    apply continuous_backwardIntegral (f:=fun s u =>
      ∑ k, N u i k * triangularTerm lam N n u s k j)
    apply continuous_finset_sum
    intro k hk
    exact ((hN i k).comp continuous_snd).mul ((ih k j).comp continuous_swap)

lemma triangularTerm_degree_vanish (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (degree : J → ℕ) (hN : ∀ t i j, ¬ degree j<degree i → N t i j=0)
    (n : ℕ) (t s : ℝ) (i j : J) (hi : degree i<n) :
    triangularTerm lam N n t s i j=0 := by
  induction n generalizing t s i j with
  | zero => omega
  | succ n ih =>
    have hz : (fun u => ∑ k, N u i k * triangularTerm lam N n u s k j)=0 := by
      funext u
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hki : degree k<degree i
      · rw [ih u s k j (by omega),mul_zero]
      · rw [hN u i k hki,zero_mul]
    change backwardIntegral (lam i) _ t s=0
    rw [hz]
    simp [backwardIntegral]

@[simp] lemma triangularTerm_succ_self (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (n : ℕ) (s : ℝ) (i j : J) : triangularTerm lam N (n+1) s s i j=0 := by
  simp [triangularTerm]

lemma hasDerivAt_triangularTerm_zero (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (t s : ℝ) (i j : J) :
    HasDerivAt (fun t => triangularTerm lam N 0 t s i j)
      (lam i*triangularTerm lam N 0 t s i j) t := by
  by_cases hij : i=j
  · simp only [triangularTerm,if_pos hij]
    convert ((((hasDerivAt_id t).sub_const s).ofReal_comp).const_mul (lam i)).cexp using 1 <;>
      simp [mul_comm]
  · simp only [triangularTerm,if_neg hij,mul_zero]
    exact hasDerivAt_const _ _

lemma hasDerivAt_triangularTerm_succ (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (hN : ∀ i j, Continuous (fun t => N t i j))
    (n : ℕ) (t s : ℝ) (i j : J) :
    HasDerivAt (fun t => triangularTerm lam N (n+1) t s i j)
      (lam i*triangularTerm lam N (n+1) t s i j+
        ∑ k, N t i k*triangularTerm lam N n t s k j) t := by
  apply hasDerivAt_backwardIntegral
  apply continuous_finset_sum
  intro k hk
  exact (hN i k).mul ((continuous_triangularTerm lam N hN n k j).comp
    (continuous_id.prodMk continuous_const))

/-- Finite principal backward evolution before choosing a degree cutoff. -/
def triangularEvolution (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (H : ℕ) (t s : ℝ) (i j : J) : ℂ :=
  ∑ n ∈ Finset.range (H+1), triangularTerm lam N n t s i j

lemma continuous_triangularEvolution (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (hN : ∀ i j, Continuous (fun t => N t i j)) (H : ℕ) (i j : J) :
    Continuous (fun p : ℝ×ℝ => triangularEvolution lam N H p.1 p.2 i j) := by
  apply continuous_finset_sum
  intro n hn
  exact continuous_triangularTerm lam N hN n i j

@[simp] lemma triangularEvolution_self (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (H : ℕ) (s : ℝ) (i j : J) :
    triangularEvolution lam N H s s i j = if i=j then 1 else 0 := by
  induction H with
  | zero => simp [triangularEvolution,triangularTerm]
  | succ H ih => simpa [triangularEvolution,Finset.sum_range_succ] using ih

lemma hasDerivAt_triangularSum (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (hN : ∀ i j, Continuous (fun t => N t i j))
    (n : ℕ) (t s : ℝ) (i j : J) :
    HasDerivAt (fun t => ∑ m ∈ Finset.range (n+1), triangularTerm lam N m t s i j)
      (lam i*(∑ m ∈ Finset.range (n+1), triangularTerm lam N m t s i j)+
        ∑ k, N t i k*(∑ m ∈ Finset.range n, triangularTerm lam N m t s k j)) t := by
  induction n with
  | zero => simpa using hasDerivAt_triangularTerm_zero lam N t s i j
  | succ n ih =>
    convert ih.add (hasDerivAt_triangularTerm_succ lam N hN n t s i j) using 1
    · funext u
      simp only [Finset.sum_range_succ]
    · simp only [Finset.sum_range_succ,mul_add,Finset.sum_add_distrib]
      ring

/-- Once the degree cutoff is exceeded, the finite sum satisfies the complete
triangular differential equation, without any remainder. -/
theorem hasDerivAt_triangularEvolution (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (hNc : ∀ i j, Continuous (fun t => N t i j))
    (degree : J → ℕ) (hN : ∀ t i j, ¬ degree j<degree i → N t i j=0)
    (H : ℕ) (hH : ∀ i, degree i<H) (t s : ℝ) (i j : J) :
    HasDerivAt (fun t => triangularEvolution lam N H t s i j)
      (lam i*triangularEvolution lam N H t s i j+
        ∑ k, N t i k*triangularEvolution lam N H t s k j) t := by
  convert hasDerivAt_triangularSum lam N hNc H t s i j using 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  simp only [triangularEvolution,Finset.sum_range_succ,
    triangularTerm_degree_vanish lam N degree hN H t s k j (hH k),add_zero]

end BourgadeHuang.CMS

