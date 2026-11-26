import BourgadeHuang.RationalBulk.ChargedCoefficientFormula
import BourgadeHuang.RationalBulk.RationalLawDetermination
import BourgadeHuang.RationalBulk.Parameter

/-! Exact bulk hierarchy uniqueness for every positive rational beta.
The expected rational charged observable is constructed from the actual point
configuration, its physical CMS coefficients are determined, and its diagonal
specializations determine the full anchored probability law. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang.RationalBulk

/-- Any two exact hierarchy laws agree at every positive rational coupling,
with the rationality supplied by its positive numerator multiplicity. -/
theorem anchored_law_eq_of_exactHierarchy_of_multiplicities
    {beta : ℝ} (hbeta : 0<beta) {p q : ℕ} (hp : 0<p)
    (hrat : beta*(q:ℝ)=2*(p:ℝ))
    (mu nu : ProbabilityMeasure AnchoredCountingState)
    (hmu : ExactHierarchy (mu : Measure AnchoredCountingState) beta)
    (hnu : ExactHierarchy (nu : Measure AnchoredCountingState) beta)
    {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (hemu : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
      (mu : Measure AnchoredCountingState))
    (henu : Integrable (fun s : AnchoredCountingState=>Real.exp (b*‖s.val.2‖^2))
      (nu : Measure AnchoredCountingState)) : mu=nu := by
  apply anchored_law_eq_of_rational_sectorial_expectations hbeta hp hrat mu nu ha hb hemu henu
  intro k eta
  have hn : ((k*p:ℕ):ℝ)=((k*q:ℕ):ℝ)*beta/2 := by
    push_cast
    linear_combination -(k:ℝ)/2*hrat
  have hbal : beta*(CMS.signCount (repeatedSigns q eta) true:ℝ)=
      2*(CMS.signCount (repeatedSigns p eta) true:ℝ) := by
    rw [signCount_repeated,signCount_repeated]
    push_cast
    linear_combination (CMS.signCount eta true:ℝ)*hrat
  have hcoeff : chargedCoefficients (mu : Measure AnchoredCountingState) beta hbeta hmu ha hemu
      (repeatedSigns p eta) (repeatedSigns q eta) hn hbal =
    chargedCoefficients (nu : Measure AnchoredCountingState) beta hbeta hnu hb henu
      (repeatedSigns p eta) (repeatedSigns q eta) hn hbal := by
    apply coefficients_eq_of_numerator_comparison (repeatedSigns q eta)
    · exact chargedCoefficients_denominator_support (mu : Measure AnchoredCountingState)
        beta hbeta hmu ha hemu (repeatedSigns p eta) (repeatedSigns q eta) hn hbal
    · exact chargedCoefficients_denominator_support (nu : Measure AnchoredCountingState)
        beta hbeta hnu hb henu (repeatedSigns p eta) (repeatedSigns q eta) hn hbal
    · intro epsilon
      rw [chargedCoefficients_formula (mu : Measure AnchoredCountingState) beta hbeta hmu ha hemu
        (repeatedSigns p eta) (repeatedSigns q eta) hn hbal epsilon,
        chargedCoefficients_formula (nu : Measure AnchoredCountingState) beta hbeta hnu hb henu
        (repeatedSigns p eta) (repeatedSigns q eta) hn hbal epsilon]
  intro z hz
  rw [chargedCoefficients_spec (mu : Measure AnchoredCountingState) beta hbeta hmu ha hemu
      (repeatedSigns p eta) (repeatedSigns q eta) hn hbal hz,
    chargedCoefficients_spec (nu : Measure AnchoredCountingState) beta hbeta hnu hb henu
      (repeatedSigns p eta) (repeatedSigns q eta) hn hbal hz,hcoeff]

/-- Bourgade--Huang bulk exact-hierarchy uniqueness at a general rational beta.
No target process, uniqueness principle, growth estimate, or CMS coefficient
formula occurs among the hypotheses. -/
theorem anchored_law_eq_of_exactHierarchy_rational
    (beta : ℚ) (hbeta : 0<beta)
    (mu nu : ProbabilityMeasure AnchoredCountingState)
    (hmu : ExactHierarchy (mu : Measure AnchoredCountingState) (beta:ℝ))
    (hnu : ExactHierarchy (nu : Measure AnchoredCountingState) (beta:ℝ))
    {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (hemu : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
      (mu : Measure AnchoredCountingState))
    (henu : Integrable (fun s : AnchoredCountingState=>Real.exp (b*‖s.val.2‖^2))
      (nu : Measure AnchoredCountingState)) : mu=nu := by
  obtain ⟨p,q,hp,_,hrat⟩ := exists_positive_charge_multiplicities beta hbeta
  exact anchored_law_eq_of_exactHierarchy_of_multiplicities
    (by exact_mod_cast hbeta) hp hrat mu nu hmu hnu ha hb hemu henu

theorem counting_law_eq_of_exactHierarchy_rational
    (beta : ℚ) (hbeta : 0<beta)
    (mu nu : ProbabilityMeasure AnchoredCountingState)
    (hmu : ExactHierarchy (mu : Measure AnchoredCountingState) (beta:ℝ))
    (hnu : ExactHierarchy (nu : Measure AnchoredCountingState) (beta:ℝ))
    {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (hemu : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
      (mu : Measure AnchoredCountingState))
    (henu : Integrable (fun s : AnchoredCountingState=>Real.exp (b*‖s.val.2‖^2))
      (nu : Measure AnchoredCountingState)) : anchoredCountingLaw mu=anchoredCountingLaw nu :=
  congrArg anchoredCountingLaw
    (anchored_law_eq_of_exactHierarchy_rational beta hbeta mu nu hmu hnu ha hb hemu henu)

end BourgadeHuang.RationalBulk
