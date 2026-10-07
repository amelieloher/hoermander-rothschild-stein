-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SharpTestedRowRepresentative
public import RothschildStein.P1.SymmetricTruncationTranspose
public import RothschildStein.P1.StandardFrame
public import RothschildStein.P1.ChartTranspose
public import RothschildStein.P1.TypeKernelInputTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Actual finite sharp truncations satisfy the
bilinear transpose identity, with Fubini proved by compact pole separation. -/
theorem sharp_tested_bilinearTranspose {lam : ℕ}
    (hF : C.IsStandardFrame F H K hQ)
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) (f g : TestFunction F.V ℝ (⊤ : ℕ∞))
    {ε : ℝ} (hε : 0 < ε) :
    (∫ ξ, g ξ * (∫ η in {η | ε < F.rho ξ η}, κ ξ η * f η)) =
      ∫ η, f η * (∫ ξ in {ξ | ε < F.rho η ξ}, κ ξ η * g ξ) := by
  classical
  let rsSharpTransposeFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.lifted.closure_subset
  let d : TypeDecomposition F lam 1 κ := Classical.choice (hκ 1)
  have ht := C.isTypeKernel_transpose F hF.lifted.Θ_eq hVU (fun u _ => hF.pole_reflection u)
    (hF.lifted.pole_smooth false) (hF.lifted.pole_smooth true) lam κ hκ
  let dt : TypeDecomposition F lam 1 (fun ξ η => κ η ξ) := Classical.choice (ht 1)
  have hi := C.integrable_sharpTruncated_tested_representative hF.lifted hκ d H.norm.gauge f g hε
  have he := integral_symmetricTruncation_bilinearTranspose volume
    (C.localizedInputGauge H.norm) d.measurableKernel
    (C.localizedInputGauge_symm hF.norm_symm) ε f g hi
  have hl : (∫ ξ, g ξ * (∫ η in {η | ε < F.rho ξ η}, κ ξ η * f η)) =
      ∫ ξ, g ξ * (∫ η, (if ε < C.localizedInputGauge H.norm ξ η then d.measurableKernel ξ η else 0) * f η) := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ξ
    dsimp only
    conv_rhs => rw [← integral_const_mul]
    simpa only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq] using
      C.sharp_tested_row_eq_representative hF.lifted d H.norm.gauge.1 f g ε ξ
  rw [hl, he]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro η
  dsimp only
  have hr := C.sharp_tested_row_eq_representative hF.lifted dt H.norm.gauge.1 g f ε η
  simp only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq]
  rw [hr, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne η] with ξ hξη
  rw [d.measurableKernel_eq_off_diagonal ξ η hξη,
    dt.measurableKernel_eq_off_diagonal η ξ hξη.symm]

end RothschildStein.P1.LiftedChart
