import GeneralizedBulk.Graph.GraphProfileEntropy
import GeneralizedBulk.Entropy.ChannelRateTools

/-! The internally proved common graph-counting event remains valid for
arbitrarily growing finite palettes, with super-polynomially small failure. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical

namespace GeneralizedBulk.Graph.Configuration
open Entropy Entropy.ChannelRates

theorem growing_palette_good_probability
    (d : ℕ) (hd : 0 < d) (N q m : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hgraphs : ∀ n,Nonempty (RegularGraph (N n) d)) (hNd : ∀ n,N n*d = 2*m n)
    (C : ℝ) (hC : ∀ k : ℕ,|Real.log k.factorial-logFactorialMain k| ≤ C+Real.log (k+1))
    (M : ℕ) (hM : 8*d*(d+1) ≤ M) (η : ℝ) :
    ∀ᶠ n in atTop,(regularGraphLaw (N n) d).real
      {G | ¬ GraphProfileGood (q := q n) (m := m n) C ((N n : ℝ)^η) M G} ≤
        Real.exp (-(N n : ℝ)^η) := by
  filter_upwards [hN.eventually (eventually_ge_atTop (7+4*d*(d+1)+M))] with n hn
  letI := hgraphs n
  have hmul : N n ≤ N n*d := Nat.le_mul_of_pos_right _ hd
  have hnp : 0 < N n := by omega
  have hmp : 0 < m n := by have h := hNd n; omega
  exact regularGraph_uniform_symmetric_profile_probability C hC hnp hd hmp (hNd n) M
    (by omega) hM (by omega) _

theorem growing_palette_good_polynomial_failure
    (d : ℕ) (hd : 0 < d) (N q m : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hgraphs : ∀ n,Nonempty (RegularGraph (N n) d)) (hNd : ∀ n,N n*d = 2*m n)
    (C : ℝ) (hC : ∀ k : ℕ,|Real.log k.factorial-logFactorialMain k| ≤ C+Real.log (k+1))
    (M : ℕ) (hM : 8*d*(d+1) ≤ M) (η : ℝ) (hη : 0 < η) (D : ℝ) :
    ∀ᶠ n in atTop,(regularGraphLaw (N n) d).real
      {G | ¬ GraphProfileGood (q := q n) (m := m n) C ((N n : ℝ)^η) M G} ≤ (N n : ℝ)^(-D) := by
  have he := hN.eventually (stretched_exp_eventually_le_nat_rpow η 1 (-D) hη (by norm_num))
  filter_upwards [growing_palette_good_probability d hd N q m hN hgraphs hNd C hC M hM η,he] with n hn he
  exact hn.trans (by simpa only [neg_one_mul] using he)

end GeneralizedBulk.Graph.Configuration
