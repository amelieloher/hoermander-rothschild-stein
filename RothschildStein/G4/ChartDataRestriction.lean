-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ChartAnalyticData

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Weighted boxes are monotone in nonnegative radius, with
all derivative estimates retained at their original radius. -/
theorem weightedBox_subset_of_radius_le {m : ℕ} (w : Fin m → ℕ+)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : weightedBox w a ⊆ weightedBox w b := by
  intro u hu i
  exact (hu i).trans_le (pow_le_pow_left₀ ha hab _)

/-- Restrict an actual analytic chart package to a smaller
coordinate domain, retaining its radius and constants unchanged. -/
theorem chartAnalyticBounds_mono {m n : ℕ} {Ω : Set (Fin n → ℝ)} {w : Fin m → ℕ+}
    {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {B : Fin n → Fin m}
    {F : (Fin n → ℝ) → (Fin n → ℝ)} {Q S : Set (Fin n → ℝ)} {r κ D : ℝ}
    (h : ChartAnalyticBounds Ω w Z B F Q r κ D) (hSQ : S ⊆ Q) :
    ChartAnalyticBounds Ω w Z B F S r κ D := by
  obtain ⟨hF, hmap, hjac, hdet, herr, hframe⟩ := h
  exact ⟨hF.mono hSQ, hmap.mono_left hSQ, fun u hu => hjac u (hSQ hu),
    fun u hu => hdet u (hSQ hu), fun u hu => herr u (hSQ hu),
    fun u hu => hframe u (hSQ hu)⟩

/-- Actual chart trajectories restrict to a smaller coordinate
domain without changing the trajectory, chart, or initial point. -/
theorem chartTrajectories_mono {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {B : Fin n → Fin m}
    {F : (Fin n → ℝ) → (Fin n → ℝ)} {Q S : Set (Fin n → ℝ)}
    {x : Fin n → ℝ} {v : Fin m → ℝ}
    {Γ : (Fin n → ℝ) → ℝ → (Fin n → ℝ)}
    (h : ChartTrajectories Ω Z B F Q x v Γ) (hSQ : S ⊆ Q) :
    ChartTrajectories Ω Z B F S x v Γ := fun u hu => h u (hSQ hu)

end RothschildStein.G4
