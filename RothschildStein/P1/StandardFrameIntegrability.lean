-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.StandardFrame
public import RothschildStein.P1.PositiveTypeRowIntegrability

/-!
# Row and column integrability on the standard frame of a lifted chart

`LiftedChart.positiveType_rowIntegrable` proves `TypeKernelIntegrable F` for a frame `F` that shares the
group and the two-point map of a lifted chart `C`, has its cutoff region inside the chart domain and
poles smooth off zero and homogeneous of degree `2 - Q`. All of this is part of the data of a
standard frame (`LiftedChart.IsStandardFrame`: the lifted-frame fields), for the drift chart
(`C.driftModel`, alphabet `Fin (q + 1)`) and the no-drift chart (`C.noDriftModel`) alike, since
`IsStandardFrame` is stated for an arbitrary lifted chart. Hence `TypeKernelIntegrable` is a theorem on
every standard frame.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)} {q : ℕ}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **Row and column integrability on a standard frame** (BB p. 544, Prop 11.10; p. 297,
Lemma 7.5): `TypeKernelIntegrable F` for the standard frame `F` of a lifted chart (drift or no drift).
The frame's group, two-point map, cutoff region (`V ⊆ closure V ⊆ C.U`) and the smoothness and
homogeneity of its poles `Γ, Γ*` are the fields of `IsLiftedFrame`, and
`LiftedChart.positiveType_rowIntegrable` concludes. -/
theorem IsStandardFrame.typeKernelIntegrable (hF : C.IsStandardFrame F H K hQ) :
    TypeKernelIntegrable F :=
  C.positiveType_rowIntegrable F hF.lifted.G_eq hF.lifted.Θ_eq
    (subset_closure.trans hF.lifted.closure_subset) hF.lifted.pole_smooth
    (fun star r hr u hu => by
      rw [hF.lifted.G_eq]
      exact hF.lifted.pole_homogeneous star r hr u hu)

end LiftedChart

end RothschildStein.P1
