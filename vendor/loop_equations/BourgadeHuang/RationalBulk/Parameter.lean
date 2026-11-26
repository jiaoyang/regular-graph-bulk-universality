import BourgadeHuang.RationalChargeGeometry

/-! The rational parameter in Theorems 1.5 and 1.9, with its actual integer
charge multiplicities. No restriction to a finite list of symmetry classes. -/
noncomputable section
namespace BourgadeHuang.RationalBulk

theorem exists_positive_charge_multiplicities (β : ℚ) (hβ : 0 < β) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (β : ℝ) * q = 2 * p := by
  let r : ℚ := β / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hn : 0 < r.num := Rat.num_pos.mpr hr
  refine ⟨r.num.toNat, r.den, Int.pos_iff_toNat_pos.mp hn, r.pos, ?_⟩
  have he : (r.num.toNat : ℤ) = r.num := Int.toNat_of_nonneg hn.le
  have hquot : (r : ℝ) = (r.num.toNat : ℝ) / (r.den : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast he.symm
  have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hm : (r : ℝ) * (r.den : ℝ) = (r.num.toNat : ℝ) :=
    (eq_div_iff hd).mp hquot
  dsimp [r] at hm
  push_cast at hm
  nlinarith

theorem positive_rational_iff_charge_multiplicities (β : ℝ) :
    (0 < β ∧ ∃ b : ℚ, (b : ℝ) = β) ↔
      ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ β * q = 2 * p := by
  constructor
  · rintro ⟨hb, b, rfl⟩
    exact exists_positive_charge_multiplicities b (by exact_mod_cast hb)
  · rintro ⟨p, q, hp, hq, he⟩
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp
    have hβ : β = 2 * (p : ℝ) / q := (eq_div_iff hqr.ne').mpr he
    refine ⟨by rw [hβ]; positivity, 2 * (p : ℚ) / q, ?_⟩
    push_cast
    exact hβ.symm

end BourgadeHuang.RationalBulk
