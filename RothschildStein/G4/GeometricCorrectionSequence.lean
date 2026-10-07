-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.ENNReal.Lemmas
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace RothschildStein.G4

/-- Elementary iteration of a genuine quarter-residual construction.
Every point remains in the same buffer, and step costs decay geometrically. -/
theorem exists_geometric_correction_sequence_of_halving {n s : ℕ}
    {K : Set (Fin n → ℝ)} {y x : Fin n → ℝ}
    (d dstar : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    {C M η ε : ℝ} (hε : 0 < ε) (hεη : ε < η) (hx : x ∈ K)
    (hxy : dstar x y < ENNReal.ofReal ε)
    (hstep : ∀ v ∈ K, ∀ δ : ℝ, 0 < δ → δ < η →
      dstar v y < ENNReal.ofReal δ → ∃ p ∈ K,
        d v p ≤ ENNReal.ofReal (C*δ) ∧
        dstar p y ≤ ENNReal.ofReal (δ/4) ∧ ‖p-y‖ ≤ M*δ^(s+1)) :
    ∃ z : ℕ → (Fin n → ℝ), z 0 = x ∧ (∀ j, z j ∈ K) ∧
      (∀ j, d (z j) (z (j+1)) ≤ ENNReal.ofReal (C*(ε*(1/2:ℝ)^j))) ∧
      (∀ j, ‖z (j+1)-y‖ ≤ M*(ε*(1/2:ℝ)^j)^(s+1)) := by
  classical
  let r : ℕ → ℝ := fun j => ε*(1/2:ℝ)^j
  have hr : ∀ j, 0 < r j := fun j => mul_pos hε (by positivity)
  have hre : ∀ j, r j < η := by
    intro j
    exact (mul_le_mul_of_nonneg_left
      (pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1))
      hε.le |>.trans_eq (mul_one ε)).trans_lt hεη
  have hrs : ∀ j, r (j+1) = r j/2 := by
    intro j
    dsimp [r]
    rw [pow_succ]
    ring
  let State : ℕ → Type := fun j => {v : Fin n → ℝ // v ∈ K ∧ dstar v y < ENNReal.ofReal (r j)}
  have hnext : ∀ j, ∀ v : State j, ∃ p : State (j+1),
      d v.val p.val ≤ ENNReal.ofReal (C*r j) ∧ ‖p.val-y‖ ≤ M*(r j)^(s+1) := by
    intro j v
    obtain ⟨p, hp, hcost, hres, herr⟩ := hstep v.val v.property.1 (r j) (hr j)
      (hre j) v.property.2
    have hh : dstar p y < ENNReal.ofReal (r (j+1)) := by
      rw [hrs]
      exact hres.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < r j/2)).mpr
        (by linarith [hr j]))
    exact ⟨⟨p, hp, hh⟩, hcost, herr⟩
  let next : ∀ j, State j → State (j+1) := fun j v => Classical.choose (hnext j v)
  let states : ∀ j, State j := fun j => Nat.rec
    (motive := State) ⟨x, hx, by simpa [r] using hxy⟩ next j
  refine ⟨fun j => (states j).val, rfl, fun j => (states j).property.1, ?_, ?_⟩
  · intro j
    exact (Classical.choose_spec (hnext j (states j))).1
  · intro j
    exact (Classical.choose_spec (hnext j (states j))).2
end RothschildStein.G4
