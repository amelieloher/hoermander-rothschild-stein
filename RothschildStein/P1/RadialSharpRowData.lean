-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1
variable {N : ℕ}

/-- Finite integrability and a common sharp and
smooth row limit. This records proved analytic data for finite assembly. -/
structure RadialSharpRowData (ρ : (Fin N → ℝ) → ℝ)
    (χ : ℝ → (Fin N → ℝ) → ℝ) (f : (Fin N → ℝ) → ℝ) where
  value : ℝ
  sharp_integrable : ∀ ε : ℝ, 0 < ε → IntegrableOn f {η | ε < ρ η} volume
  radial_integrable : ∀ ε : ℝ, 0 < ε → Integrable (fun η => χ ε η * f η)
  sharp_limit : Tendsto (fun ε : ℝ => ∫ η in {η | ε < ρ η}, f η)
    (𝓝[>] (0 : ℝ)) (𝓝 value)
  radial_limit : Tendsto (fun ε : ℝ => ∫ η, χ ε η * f η)
    (𝓝[>] (0 : ℝ)) (𝓝 value)

namespace RadialSharpRowData
variable {ρ : (Fin N → ℝ) → ℝ} {χ : ℝ → (Fin N → ℝ) → ℝ}
  {f g : (Fin N → ℝ) → ℝ}

/-- The zero row has zero sharp and smooth values. -/
def zero (ρ : (Fin N → ℝ) → ℝ) (χ : ℝ → (Fin N → ℝ) → ℝ) :
    RadialSharpRowData ρ χ (fun _ => 0) where
  value := 0
  sharp_integrable := fun _ _ => integrable_zero _ _ _
  radial_integrable := fun _ _ => by simp only [mul_zero]; exact integrable_zero _ _ _
  sharp_limit := by simp only [integral_zero]; exact tendsto_const_nhds
  radial_limit := by simp only [mul_zero, integral_zero]; exact tendsto_const_nhds

/-- Common row limits add when both finite integrability assertions
have been proved. -/
def add (F : RadialSharpRowData ρ χ f) (G : RadialSharpRowData ρ χ g) :
    RadialSharpRowData ρ χ (fun η => f η + g η) where
  value := F.value + G.value
  sharp_integrable := fun ε hε => (F.sharp_integrable ε hε).add (G.sharp_integrable ε hε)
  radial_integrable := fun ε hε =>
    ((F.radial_integrable ε hε).add (G.radial_integrable ε hε)).congr
      (Eventually.of_forall (fun η => by simp only [Pi.add_apply]; ring))
  sharp_limit := by
    refine (F.sharp_limit.add G.sharp_limit).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integral_add (F.sharp_integrable ε hε) (G.sharp_integrable ε hε)).symm
  radial_limit := by
    refine (F.radial_limit.add G.radial_limit).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← integral_add (F.radial_integrable ε hε) (G.radial_integrable ε hε)]
    exact integral_congr_ae (Eventually.of_forall (fun η => by ring))

/-- Almost everywhere equality transfers all the finite and limit
data, so arbitrary diagonal kernel values do not affect the assembly. -/
def congr_ae (F : RadialSharpRowData ρ χ f) (he : f =ᵐ[volume] g) :
    RadialSharpRowData ρ χ g where
  value := F.value
  sharp_integrable := fun ε hε => (F.sharp_integrable ε hε).congr (ae_restrict_of_ae he)
  radial_integrable := fun ε hε => (F.radial_integrable ε hε).congr
    (he.mono (fun η hη => congrArg (fun r => χ ε η * r) hη))
  sharp_limit := by
    have hi (ε : ℝ) : (∫ η in {η | ε < ρ η}, f η) = ∫ η in {η | ε < ρ η}, g η :=
      integral_congr_ae (ae_restrict_of_ae he)
    simpa only [hi] using F.sharp_limit
  radial_limit := by
    have hi (ε : ℝ) : (∫ η, χ ε η * f η) = ∫ η, χ ε η * g η :=
      integral_congr_ae (he.mono (fun η hη => congrArg (fun r => χ ε η * r) hη))
    simpa only [hi] using F.radial_limit

/-- Finite list assembly uses actual integrability before commuting
limits with sums. -/
def listSum {ι : Type*} (l : List ι) (f : ι → (Fin N → ℝ) → ℝ)
    (F : ∀ i ∈ l, RadialSharpRowData ρ χ (f i)) :
    RadialSharpRowData ρ χ (fun η => (l.map (fun i => f i η)).sum) := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using zero ρ χ
  | cons i l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (F i List.mem_cons_self).add (ih (fun j hj => F j (List.mem_cons_of_mem i hj)))

/-- The smooth integral converges to the prescribed sharp `limUnder`. -/
theorem tendsto_radial_to_sharp (F : RadialSharpRowData ρ χ f) :
    Tendsto (fun ε : ℝ => ∫ η, χ ε η * f η) (𝓝[>] (0 : ℝ))
      (𝓝 (limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ => ∫ η in {η | ε < ρ η}, f η))) := by
  rw [F.sharp_limit.limUnder_eq]
  exact F.radial_limit

end RadialSharpRowData
end RothschildStein.P1
