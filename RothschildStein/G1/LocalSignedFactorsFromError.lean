-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalFactorFromModelError

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G1

/-- Forward and inverse actual endpoint displacements with
opposite retained models have smooth factors matching on the entire
zero-time slice. No opposite-factor identity is required as an input. -/
theorem exists_local_signed_factors_of_model_errors
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n k s : ℕ} (hks : k ≤ s) {U : Set (E × ℝ)} (hU : IsOpen U)
    (Gp Gm Rp Rm : E × ℝ → (Fin n → ℝ))
    (hGp : ContDiffOn ℝ (⊤ : ℕ∞) Gp U)
    (hGm : ContDiffOn ℝ (⊤ : ℕ∞) Gm U)
    (hRp : ContDiffOn ℝ (⊤ : ℕ∞) Rp U) (hRm : ContDiffOn ℝ (⊤ : ℕ∞) Rm U)
    (hmatch : ∀ x, (x, 0) ∈ U → -Rm (x, 0) = Rp (x, 0))
    (M : ℝ)
    (hp : ∀ q ∈ U, ‖Gp q - q.2 ^ k • Rp q‖ ≤ M * |q.2| ^ (s + 1))
    (hm : ∀ q ∈ U, ‖Gm q - q.2 ^ k • Rm q‖ ≤ M * |q.2| ^ (s + 1))
    (x₀ : E) (hx₀ : (x₀, 0) ∈ U) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ (x₀, 0) ∈ V ∧ V ⊆ U ∧
      ∃ Hp Hm : E × ℝ → (Fin n → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) Hp V ∧ ContDiffOn ℝ (⊤ : ℕ∞) Hm V ∧
        (∀ q ∈ V, Gp q = q.2 ^ k • Hp q ∧ Gm q = q.2 ^ k • Hm q) ∧
        (∀ x, (x, 0) ∈ V → Hp (x, 0) = Rp (x, 0) ∧ -Hm (x, 0) = Hp (x, 0)) := by
  obtain ⟨Vp, hVp, hVp₀, hVpU, Hp, hHp, heHp, hHp₀⟩ :=
    exists_local_factor_of_model_error hks hU Gp Rp hGp hRp M hp x₀ hx₀
  obtain ⟨Vm, hVm, hVm₀, _hVmU, Hm, hHm, heHm, hHm₀⟩ :=
    exists_local_factor_of_model_error hks hU Gm Rm hGm hRm M hm x₀ hx₀
  refine ⟨Vp ∩ Vm, hVp.inter hVm, ⟨hVp₀, hVm₀⟩,
    fun _ hq => hVpU hq.1, Hp, Hm, hHp.mono inter_subset_left,
    hHm.mono inter_subset_right, ?_, ?_⟩
  · intro q hq
    exact ⟨heHp q hq.1, heHm q hq.2⟩
  · intro x hx
    refine ⟨hHp₀ x hx.1, ?_⟩
    rw [hHm₀ x hx.2, hmatch x (hVpU hx.1), hHp₀ x hx.1]

end RothschildStein.G1
