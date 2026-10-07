-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedInjectivityChain
public import RothschildStein.G4.UniformChartTransferShrinkage

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Function

namespace RothschildStein.G4

/-- Instantiate finite-chain injectivity with the proved actual
chart-transfer rule and actual same-family analytic/trajectory packages.
The two frames are suboptimal at the original switching radius; only after
transfer is the injective coordinate domain restricted to the next scale
(BB (9.56)–(9.57), pp. 454–458). -/
theorem actual_zero_shift_chart_injectivity_along_chain {m n s : ℕ}
    (w : Fin m → ℕ+) (hw : ∀ J, (w J : ℕ) ≤ s)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ))
    (hZ : ∀ J, ContinuousOn (Z J) Ω)
    (F : (Fin n → Fin m) → (Fin n → ℝ) → (Fin n → ℝ))
    (Γ : (Fin n → Fin m) → (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (x : Fin n → ℝ) (ρ : (Fin n → Fin m) → ℝ) {a D κ t α : ℝ}
    (ha : 0 < a) (hκ : 0 ≤ κ) (hsmall : (n : ℝ) * κ ≤ 1 / 4)
    (f : ℝ → ℝ)
    (hf : ∀ b : ℝ, 0 < b → b ≤ 1 →
      0 < f b ∧ f b ≤ 1 ∧ ChartTransferRule m n s b a (f b) D)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hdata : ∀ B r, 0 < r → r ≤ 1 → IsSuboptimal Z w B x t r →
      ChartAnalyticBounds Ω w Z B (F B) (weightedBox (w ∘ B) (a * r)) r κ D ∧
      ChartTrajectories Ω Z B (F B) (weightedBox (w ∘ B) (a * r)) x 0 (Γ B) ∧ F B 0 = x)
    (l : List (Fin n → Fin m))
    (hchain : l.IsChain (fun B C => IsSuboptimal Z w B x t (ρ B) ∧
      IsSuboptimal Z w C x t (ρ B) ∧ ρ C ≤ ρ B))
    (hρ : ∀ B ∈ l, 0 < ρ B ∧ ρ B ≤ 1)
    (hstart : ∀ h : 0 < l.length,
      InjOn (F l[0]) (weightedBox (w ∘ l[0]) (α * ρ l[0]))) :
    ∀ j : ℕ, ∀ h : j < l.length,
      InjOn (F l[j]) (weightedBox (w ∘ l[j]) (f^[j] α * ρ l[j])) := by
  let R := fun B C => (IsSuboptimal Z w B x t (ρ B) ∧
    IsSuboptimal Z w C x t (ρ B) ∧ ρ C ≤ ρ B) ∧ B ∈ l ∧ C ∈ l
  have hchain' : l.IsChain R :=
    List.IsChain.imp_of_mem_imp (fun B C hB hC hBC => ⟨hBC, hB, hC⟩) hchain
  apply weighted_chart_injectivity_along_transfers (fun B => w ∘ B) F ρ R f hα hα1
    (fun b hb hb1 => ⟨(hf b hb hb1).1, (hf b hb hb1).2.1⟩) l hchain'
    (fun B hB => (hρ B hB).1) (fun _ _ hBC => hBC.1.2.2) _ hstart
  intro b hb hb1 B C hBC hinj
  have hr := hρ B hBC.2.1
  obtain ⟨hB, hΓB, hBzero⟩ := hdata B (ρ B) hr.1 hr.2 hBC.1.1
  obtain ⟨hC, hΓC, hCzero⟩ := hdata C (ρ B) hr.1 hr.2 hBC.1.2.1
  have hzB : (0 : Fin n → ℝ) ∈ weightedBox (w ∘ B) (a * ρ B) := by
    intro i
    simp only [Pi.zero_apply, abs_zero]
    exact pow_pos (mul_pos ha hr.1) _
  have hzC : (0 : Fin n → ℝ) ∈ weightedBox (w ∘ C) (a * ρ B) := by
    intro i
    simp only [Pi.zero_apply, abs_zero]
    exact pow_pos (mul_pos ha hr.1) _
  have hdetB : frameDet Z B x ≠ 0 := by
    simpa only [hBzero] using hB.2.2.2.1 0 hzB
  have hdetC : frameDet Z C x ≠ 0 := by
    simpa only [hCzero] using hC.2.2.2.1 0 hzC
  have hfb := (hf b hb hb1).1
  have hvzero : (0 : Fin m → ℝ) ∈ weightedBox w (f b * ρ B) := by
    intro J
    simp only [Pi.zero_apply, abs_zero]
    exact pow_pos (mul_pos hfb hr.1) _
  exact (hf b hb hb1).2.2 w B C (frame_index_injective_of_frameDet_ne_zero Z B hdetB)
    (fun i => hw (B i)) (fun i => hw (C i)) Z Ω hZ (F C) (F B) (ρ B) κ
    hr.1 hr.2 hκ hsmall hC hB hinj x hBzero hdetC 0 hvzero (Γ C) (Γ B) hΓC hΓB

end RothschildStein.G4
