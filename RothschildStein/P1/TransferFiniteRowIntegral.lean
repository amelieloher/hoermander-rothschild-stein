-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiniteRowAssembly
public import RothschildStein.P1.RegularTransferWeakIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- A finite off-diagonal decomposition may be
integrated against an interior test after proving every component row
integrable. Values outside the frame and on the diagonal are immaterial. -/
theorem integral_finiteTransferRows {N : ℕ} [Nonempty (Fin N)] {A : Type*}
    (V : Opens (Fin N → ℝ)) (l : List A)
    (κ : (Fin N → ℝ) → ℝ) (p : A → (Fin N → ℝ) → ℝ)
    (r : (Fin N → ℝ) → ℝ) (ξ : Fin N → ℝ)
    (φ : TestFunction V ℝ (⊤ : ℕ∞))
    (he : ∀ η ∈ (V : Set (Fin N → ℝ)), ξ ≠ η →
      κ η = (l.map (fun a => p a η)).sum + r η)
    (hp : ∀ a ∈ l, Integrable (fun η => p a η * φ η))
    (hr : Integrable (fun η => r η * φ η)) :
    (∫ η, κ η * φ η) =
      (l.map (fun a => ∫ η, p a η * φ η)).sum + ∫ η, r η * φ η := by
  have hae : (fun η => κ η * φ η) =ᵐ[volume]
      (fun η => (l.map (fun a => p a η * φ η)).sum + r η * φ η) := by
    filter_upwards [volume.ae_ne ξ] with η hne
    by_cases hη : η ∈ (V : Set (Fin N → ℝ))
    · rw [he η hη hne.symm, add_mul, List.sum_map_mul_right]
    · have hz : φ η = 0 := by simpa using φ.zero_on_compl hη
      simp [hz]
  rw [integral_congr_ae hae, integral_add
    (f := fun η => (l.map (fun a => p a η * φ η)).sum)
    (g := fun η => r η * φ η) (integrable_listMapSum l _ hp) hr,
    integral_listMapSum l _ hp]

end RothschildStein.P1
