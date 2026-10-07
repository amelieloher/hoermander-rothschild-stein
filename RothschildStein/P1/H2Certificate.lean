-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2CertificateGeometry
public import RothschildStein.P1.H2CertificateTruncation
public import RothschildStein.P1.H2CertificateLocalization
public import RothschildStein.P1.H2CertificateRadius

/-!
# Geometric certificate for a lifted chart

The certificate consists of metric-measure, truncation, and localization and radius data,
chosen in this order: the geometry
`(Ω₀ ⋐ Ω₁ ⋐ Ω₂, κ)` and constants `(v₋, v₊, C_D)`, then the truncation `(θ₁, θ₂, τ)`, then a
common radius `r < κ` with centres, cutoffs and the radial support radius `R'`; all choices are
independent of the function acted on. The Data D1-D3, the transpose certificate and the finite
reconstruction are not part of this module.

* `H2CertificateCarrier`: the carrier `C.Carrier` (chart domain with the ambient lifted control
  metric, Euclidean topology, Lebesgue measure);
* `H2CertificateGeometry`: `exists_metricMeasureCertificate`;
* `H2CertificateTruncation`: `exists_truncDist`;
* `H2CertificateLocalization`: `exists_localization`;
* `H2CertificateRadius`: `exists_admissibleRadius`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric MeasureTheory
namespace RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

namespace LiftedChart

variable (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The geometric certificate. For every
compact `K` of the chart domain (input/output supports with their margins) there are regions
`Ω₀ ⋐ Ω₁ ⋐ Ω₂ ∋ K`, a radius `κ`, the volume constants `v₋ ≤ v₊` and the `H2.LocDoubling`
structure with `C_D = 2^Q v₊ / v₋` (`IsMetricMeasureCertificate`); these depend only on `K` and
the chart. Then, for every symmetric homogeneous gauge `ν` and every `τ`, there is a truncation
distance `d'` equal to `ρ = ν(Θ(y, x))` on `{d < τ}` (`IsRhoTruncation`); then, for every common
radius `0 < r < κ`, an admissible radial support radius `R'` (`IsAdmissibleRadius`,
for `τ > 0`) and, for every compact output support `F ⊆ Ω₀`, a finite cover with
smooth cutoffs (`IsLocalization`) (BB pp. 295-296, 306-309, 325-327, 568-576). -/
theorem exists_h2Certificate {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ (S : H2.LocDoubling C.Carrier) (vLo vHi : ℝ),
      C.IsMetricMeasureCertificate S vLo vHi ∧ K ⊆ Carrier.val '' S.Ω₀ ∧
      ∀ ν : (Fin (n + m) → ℝ) → ℝ, C.G.IsHomogeneousGauge ν → (∀ u, ν (-u) = ν u) →
        ∀ τ : ℝ, 0 < τ → ∃ T : H2.TruncDist S, C.IsRhoTruncation S ν τ T ∧
          ∀ r : ℝ, 0 < r → r < S.κ →
            (∃ R' : ℝ, C.IsAdmissibleRadius S T ν τ r R') ∧
            ∀ F : Set (Fin (n + m) → ℝ), IsCompact F → F ⊆ Carrier.val '' S.Ω₀ →
              ∃ (t : Finset C.Carrier) (χ ψ : C.Carrier → (Fin (n + m) → ℝ) → ℝ),
                C.IsLocalization S F r t χ ψ := by
  obtain ⟨S, vLo, vHi, hcert, hKS⟩ := C.exists_metricMeasureCertificate hK hKU
  refine ⟨S, vLo, vHi, hcert, hKS, fun ν hν hsym τ hτ => ?_⟩
  obtain ⟨T, hT⟩ := C.exists_truncDist S hν hsym τ
  refine ⟨T, hT, fun r hr hrκ => ⟨?_, ?_⟩⟩
  · exact C.exists_admissibleRadius S T hν hτ hr
  · intro F hF hFΩ
    exact C.exists_localization S hF hFΩ hr hrκ

end LiftedChart

end RothschildStein.P1
