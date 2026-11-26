import GeneralizedBulk.Graph.AdmissibleMixedFourth

/-! The article's mixed-fourth theorem at every positive admissible size.
The coefficient absorbs the finitely many sizes before the asymptotic
probability bound, without changing the simultaneous good graph event. -/
noncomputable section
open MeasureTheory Filter
open scoped Classical Topology

namespace GeneralizedBulk.Graph

/-- For fixed degree and compact strict bulk set, one event at every size
has the stated polynomial probability and mixed-fourth bounds. The constants
are chosen before the size, graph, eigenfamily and coordinate slots; there is
no asymptotic qualifier or extra condition on the selected eigenvalues. -/
theorem article_polynomial_mixed_fourth
    (d : ℕ) (hd : 3 ≤ d) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, E ^ 2 < 4 * ((d : ℝ) - 1)) :
    ∃ b χ C : ℝ, 0 < b ∧ 0 < χ ∧ 0 < C ∧
      (∀ M : ℕ, MeasurableSet (mixedFourthGood d hd M K)) ∧
      (∀ M : ℕ, AdmissibleSize d M →
        1 - C * (M : ℝ) ^ (-b) ≤
          (regularGraphLaw M d).real (mixedFourthGood d hd M K)) ∧
      ∀ M : ℕ, 0 < M → ∀ g ∈ mixedFourthGood d hd M K,
        ∀ k : ℕ, 0 < k → k ≤ 4 →
        ∀ A : GraphEigenCandidate d M k g, (∀ a, A.val.eigenvalue a ∈ K) →
        ∀ j1 j2 j3 j4 : Fin k × Fin (d + 1),
          |starFourthDifference A.val (by omega) j1 j2 j3 j4| ≤ C * (M : ℝ) ^ (-χ) := by
  let b : ℝ := 1 / 32
  let χ := mixedFourthUniformExponent d hd
  let C₀ := 4 * mixedFourthFailureConstant d
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    linarith [mixedFourthFailureConstant_ge_ten d hd]
  have hprob : ∀ᶠ M : ℕ in admissibleSizeFilter d,
      1 - C₀ * (M : ℝ) ^ (-b) ≤
        (regularGraphLaw M d).real (mixedFourthGood d hd M K) :=
    (uniform_graph_mixed_fourth_along_admissible_sizes d hd K hK hbulk).2.2.2
  have htail : ∀ᶠ M : ℕ in atTop, AdmissibleSize d M →
      1 - C₀ * (M : ℝ) ^ (-b) ≤
        (regularGraphLaw M d).real (mixedFourthGood d hd M K) := by
    exact eventually_inf_principal.mp hprob
  obtain ⟨T, hT⟩ := eventually_atTop.mp htail
  let C := C₀ + ((T : ℝ) + 1) ^ b
  have hCge : C₀ ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) b)
  refine ⟨b, χ, C, by norm_num [b], mixedFourthUniformExponent_pos d hd,
    hC₀.trans_le hCge, (fun M => measurableSet_mixedFourthGood d hd M K), ?_, ?_⟩
  · intro M hM
    by_cases hMT : T ≤ M
    · have hm := hT M hMT hM
      have hmul := mul_le_mul_of_nonneg_right hCge
        (Real.rpow_nonneg (Nat.cast_nonneg M) (-b))
      linarith
    · have hMR : (0 : ℝ) < M := by exact_mod_cast hM.1
      have hMle : (M : ℝ) ≤ (T : ℝ) + 1 := by
        exact_mod_cast (show M ≤ T + 1 by omega)
      have hpow := Real.rpow_le_rpow (Nat.cast_nonneg M) hMle
        (by norm_num [b] : 0 ≤ b)
      have hCpow : (M : ℝ) ^ b ≤ C := by
        exact hpow.trans (by dsimp [C]; linarith [hC₀])
      have hid : (M : ℝ) ^ b * (M : ℝ) ^ (-b) = 1 := by
        rw [← Real.rpow_add hMR]
        simp
      have hone : 1 ≤ C * (M : ℝ) ^ (-b) := by
        rw [← hid]
        exact mul_le_mul_of_nonneg_right hCpow
          (Real.rpow_nonneg (Nat.cast_nonneg M) (-b))
      linarith [measureReal_nonneg (μ := regularGraphLaw M d) (s := mixedFourthGood d hd M K)]
  · intro M hM g hg k hk hk4 A henergy j1 j2 j3 j4
    exact (mixedFourthGood_moment d hd M hM K g hg k hk hk4 A henergy j1 j2 j3 j4).trans
      (mul_le_mul_of_nonneg_right hCge (Real.rpow_nonneg (Nat.cast_nonneg M) (-χ)))

end GeneralizedBulk.Graph
