-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TopExhaustionEnergyTrace
public import HeatKernel.Moser.WeakSolutionAffineEnergyIdentity

/-! # Open-top traces for affine spatial energies -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace HeatKernel

/-- Square-integrable dual curves pair integrably with affine corrections of
square-integrable tests on finite measure spaces. -/
theorem integrable_affine_dual_pairing {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → (E →L[ℝ] ℝ)} {P : α → E}
    (hF : MemLp F 2 μ) (hP : MemLp P 2 μ) (w : E) (c : ℝ) :
    Integrable (fun t => F t (P t + c • w)) μ := by
  let D := ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)
  have hi : Integrable (fun t => F t (P t)) μ :=
    (D.memLp_of_bilin 1 hF hP).integrable (by norm_num)
  have hw : Integrable (fun t => F t w) μ :=
    ((ContinuousLinearMap.apply ℝ ℝ w).comp_memLp' hF).integrable (by norm_num)
  simp only [map_add, map_smul, smul_eq_mul]
  exact hi.add (hw.const_mul c)

variable {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B : ℝ}

/-- The weak cutoff pair controls the affine test flux on its entire time interval. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.integrable_affine_energy_flux
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (W : WeakSolutionSpatialWeight V X) (T : WeakSolutionScalarTest)
    (w : zeroBoundaryGraph V X) (c : ℝ) :
    IntegrableOn (fun t => F t (W.affineEnergyMap hX T w c (v t))) (Icc A B) volume := by
  let : IsFiniteMeasure (volume.restrict (Icc A B)) :=
    isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hP := W.multiplier.comp_memLp' (T.memLp_energyMap V X hX hp.1)
  exact integrable_affine_dual_pairing hp.2.2.2.2.1 hP w c

end HeatKernel
