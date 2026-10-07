-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderTransferTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- Finite intrinsic Hölder norm gives Euclidean continuity
on an open output set covered by the projection of a full lifted chart.
The control distance is taken in the ambient coefficient domain. -/
theorem continuousOn_of_holderENorm_liftedChart {n k s m : ℕ}
    {w : Fin k → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : LiftedChart w s Ω hΩ X x₀ m)
    (V : Opens (Fin n → ℝ)) (hV : (V : Set (Fin n → ℝ)) ⊆ basePoint '' C.U)
    {α : ℝ} (hα : 0 < α) {f : (Fin n → ℝ) → ℝ}
    (hf : holderENorm (controlDistance Ω w X) α (V : Set (Fin n → ℝ)) f < ⊤) :
    ContinuousOn f (V : Set (Fin n → ℝ)) := by
  let A : Set (Fin (n + m) → ℝ) := C.U ∩ basePoint ⁻¹' (V : Set (Fin n → ℝ))
  have hA : IsOpen A := C.isOpen_U.inter
    (V.isOpen.preimage (P2.basePointCLM n m).continuous)
  have hAU : A ⊆ C.U := fun _ h => h.1
  have hcover : ∀ y ∈ (V : Set (Fin n → ℝ)), ∃ ζ ∈ A, basePoint ζ = y := by
    intro y hy
    obtain ⟨ζ, hζ, he⟩ := hV hy
    exact ⟨ζ, ⟨hζ, by simpa only [Set.mem_preimage, he] using hy⟩, he⟩
  apply P2.continuousOn_of_lifts C hA hAU hα hcover
  have hsem : holderSeminorm (controlDistance Ω w X) α
      (V : Set (Fin n → ℝ)) f < ⊤ :=
    lt_of_le_of_lt (le_add_left le_rfl) hf
  apply ne_top_of_lt
  apply lt_of_le_of_lt (P2.holderSeminorm_comp_le hα.le
    (fun _ h => h.2) (fun ξ _ ξ' _ => P2.controlDistance_basePoint_le Ω w X C.P ξ ξ') f)
    hsem

end RothschildStein.P1
