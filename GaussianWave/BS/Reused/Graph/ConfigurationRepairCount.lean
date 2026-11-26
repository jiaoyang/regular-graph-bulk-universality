import GaussianWave.BS.Reused.Graph.ConfigurationFreshEdge

/-! Recording actual involutive switches makes bounded-defect repair a
finite counting argument with an explicit polynomial multiplicity. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration

variable {N d : ℕ}

abbrev RepairCode (N d M : ℕ) := Fin M → Option (Stub N d × Stub N d)

def decodeRepair : (M : ℕ) → RepairCode N d M → Pairing (Stub N d) → Pairing (Stub N d)
  | 0, _, p => p
  | M+1, code, p =>
    let q := decodeRepair M (fun j => code j.succ) p
    match code 0 with
    | none => q
    | some bc => switchPairing q bc.1 bc.2

theorem decodeRepair_none (M : ℕ) (p : Pairing (Stub N d)) :
    decodeRepair M (fun _ => none) p = p := by
  induction M with
  | zero => rfl
  | succ M ih => simpa only [decodeRepair] using ih

abbrev ZeroDefectPairing (N d : ℕ) := {p : Pairing (Stub N d) // defect p = 0}
abbrev BoundedDefectPairing (N d M : ℕ) := {p : Pairing (Stub N d) // defect p ≤ M}

set_option maxHeartbeats 1000000 in
theorem exists_repair_code (M : ℕ) (hsize : 4 * d * (d+1) + M < N*d)
    (p : Pairing (Stub N d)) (hp : defect p ≤ M) :
    ∃ qc : ZeroDefectPairing N d × RepairCode N d M,
      decodeRepair M qc.2 qc.1.val = p := by
  induction M generalizing p with
  | zero => exact ⟨(⟨p,Nat.eq_zero_of_le_zero hp⟩,fun i => Fin.elim0 i),rfl⟩
  | succ M ih =>
    by_cases hz : defect p = 0
    · exact ⟨(⟨p,hz⟩,fun _ => none),decodeRepair_none _ _⟩
    · obtain ⟨b,c,hbc⟩ := exists_defect_reducing_switch p (Nat.pos_of_ne_zero hz)
        (lt_of_le_of_lt (Nat.add_le_add_left hp _) hsize)
      have hq : defect (switchPairing p b c) ≤ M := by omega
      obtain ⟨⟨q,code⟩,hqcode⟩ := ih (by omega) (switchPairing p b c) hq
      refine ⟨(q,Fin.cases (some (b,c)) code),?_⟩
      simp only [decodeRepair,Fin.cases_zero,Fin.cases_succ]
      rw [hqcode]
      exact switchPairing_involutive b c p

def repairEncoding (M : ℕ) (hsize : 4 * d * (d+1) + M < N*d)
    (p : BoundedDefectPairing N d M) : ZeroDefectPairing N d × RepairCode N d M :=
  Classical.choose (exists_repair_code M hsize p.val p.property)

theorem decode_repairEncoding (M : ℕ) (hsize : 4 * d * (d+1) + M < N*d)
    (p : BoundedDefectPairing N d M) :
    decodeRepair M (repairEncoding M hsize p).2 (repairEncoding M hsize p).1.val = p.val :=
  Classical.choose_spec (exists_repair_code M hsize p.val p.property)

theorem repairEncoding_injective (M : ℕ) (hsize : 4 * d * (d+1) + M < N*d) :
    Function.Injective (repairEncoding (N := N) (d := d) M hsize) := by
  intro p q he
  apply Subtype.ext
  rw [← decode_repairEncoding M hsize p,← decode_repairEncoding M hsize q,he]

theorem repairCode_card (N d M : ℕ) :
    Fintype.card (RepairCode N d M) = (1 + (N*d)^2)^M := by
  simp only [RepairCode,Fintype.card_fun,Fintype.card_option,Fintype.card_prod,Fintype.card_fin]
  ring

theorem boundedDefect_card_le (M : ℕ) (hsize : 4 * d * (d+1) + M < N*d) :
    Fintype.card (BoundedDefectPairing N d M) ≤
      Fintype.card (ZeroDefectPairing N d) * (1 + (N*d)^2)^M := by
  have h := Fintype.card_le_of_injective _ (repairEncoding_injective M hsize)
  simpa only [Fintype.card_prod,repairCode_card] using h

end GaussianWave.BS.Reused.Graph.Configuration
