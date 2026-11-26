import BourgadeHuang.CMS.DifferentialCriticalPairs
import Mathlib.Algebra.MvPolynomial.Funext

/-! Faithful symbols for finite analytic differential operators. Exponential
test functions separate every derivative coefficient; no PDE solution or
existence theorem is used in this algebraic step. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
open GapExpression
variable {d : ℕ}

def exponentialTest (a : Fin d → ℂ) (z : Point d) : ℂ := Complex.exp (∑i,a i*z i)

theorem analyticAt_exponentialTest (a : Fin d → ℂ) (z : Point d) :
    AnalyticAt ℂ (exponentialTest a) z :=
  (Finset.analyticAt_sum _ (fun i _=>analyticAt_const.mul ((ContinuousLinearMap.proj (R:=ℂ) i).analyticAt z))).cexp

theorem coordDeriv_exponentialTest (a : Fin d → ℂ) (i : Fin d) (z : Point d) :
    coordDeriv i (exponentialTest a) z=a i*exponentialTest a z := by
  have hlinear : AnalyticAt ℂ (fun w : Point d=>∑j,a j*w j) z :=
    Finset.analyticAt_sum _ (fun j _=>analyticAt_const.mul ((ContinuousLinearMap.proj (R:=ℂ) j).analyticAt z))
  have hproj (j : Fin d) : coordDeriv i (fun w : Point d=>w j) z=if j=i then 1 else 0 := by
    by_cases hji : j=i
    · subst j
      simp [coordDeriv]
    · simp [coordDeriv,Function.update_apply,hji,Ne.symm hji]
  change coordDeriv i (fun w=>Complex.exp (∑j,a j*w j)) z=_
  rw [coordDeriv_cexp hlinear]
  have he : coordDeriv i (fun w : Point d=>∑j,a j*w j) z=a i := by
    rw [coordDeriv_finset_sum_analytic _ (fun j w=>a j*w j)
      (fun j _=>analyticAt_const.mul ((ContinuousLinearMap.proj (R:=ℂ) j).analyticAt z))]
    have hcj (j : Fin d) : coordDeriv i (fun w : Point d=>a j*w j) z=a j*(if j=i then 1 else 0) := by
      rw [coordDeriv_const_mul_analytic (f:=fun w : Point d=>w j)
        ((ContinuousLinearMap.proj (R:=ℂ) j).analyticAt z),hproj]
    simp only [hcj]
    simp
  rw [he]
  rfl

theorem wordDerivative_exponentialTest (u : List (Fin d)) (a : Fin d → ℂ) (z : Point d) :
    wordDerivative u (exponentialTest a) z=(u.map a).prod*exponentialTest a z := by
  induction u generalizing z with
  | nil=>simp [wordDerivative]
  | cons i u ih=>
    change coordDeriv i (wordDerivative u (exponentialTest a)) z=_
    rw [show wordDerivative u (exponentialTest a)=(fun w=>(u.map a).prod*exponentialTest a w) from funext ih]
    rw [coordDeriv_const_mul_analytic (analyticAt_exponentialTest a z),coordDeriv_exponentialTest]
    simp only [List.map_cons,List.prod_cons]
    ring

/-- A derivative word has its commutative polynomial symbol. -/
def wordSymbol (u : List (Fin d)) : MvPolynomial (Fin d) ℂ :=
  (u.map MvPolynomial.X).prod

/-- The full finite symbol, including every lower-order coefficient. -/
def operatorSymbol (ts : List (LeibnizTerm d)) (z : Point d) : MvPolynomial (Fin d) ℂ :=
  (ts.map (fun t=>MvPolynomial.C (t.1.eval z)*wordSymbol t.2)).sum

@[simp] theorem eval_wordSymbol (u : List (Fin d)) (a : Fin d → ℂ) :
    MvPolynomial.eval a (wordSymbol u)=(u.map a).prod := by
  induction u with
  | nil=>simp [wordSymbol]
  | cons i u ih=>simp only [wordSymbol,List.map_cons,List.prod_cons,map_mul,MvPolynomial.eval_X] at ih ⊢;rw [ih]

theorem termSum_exponentialTest (ts : List (LeibnizTerm d)) (a : Fin d → ℂ) (z : Point d) :
    termSum ts (exponentialTest a) z=MvPolynomial.eval a (operatorSymbol ts z)*exponentialTest a z := by
  induction ts with
  | nil=>simp [termSum,operatorSymbol]
  | cons t ts ih=>
    simp only [termSum,operatorSymbol,List.map_cons,List.sum_cons,map_add,map_mul,MvPolynomial.eval_C,
      eval_wordSymbol,wordDerivative_exponentialTest] at ih ⊢
    rw [ih]
    ring

/-- Symbols of equal operators agree pointwise. The identity is tested on
entire exponentials, not on solutions of the PDE under study. -/
theorem operatorSymbol_eq_of_identity (ts us : List (LeibnizTerm d)) {z : Point d}
    (hz : z∈OrderedDomain d)
    (h : ∀f,AnalyticOnNhd ℂ f (OrderedDomain d)→EqOn (termSum ts f) (termSum us f) (OrderedDomain d)) :
    operatorSymbol ts z=operatorSymbol us z := by
  apply MvPolynomial.funext
  intro a
  have hh := h (exponentialTest a) (fun w _=>analyticAt_exponentialTest a w) hz
  rw [termSum_exponentialTest,termSum_exponentialTest] at hh
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) hh

end BourgadeHuang.CMS
