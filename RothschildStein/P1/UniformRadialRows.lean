-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernel
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1
variable {N : ℕ}

/-- Actual integrability and compact-uniform
convergence data for a family of whole radial cutoff rows. -/
structure UniformRadialRows (L : Set (Fin N → ℝ))
    (χ : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (f : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) : Prop where
  integrable : ∀ ξ ∈ L, Integrable (f ξ)
  cutoff_integrable : ∀ ξ ∈ L, ∀ ε : ℝ, Integrable (fun η => χ ε ξ η * f ξ η)
  limit : TendstoUniformlyOn (fun ε : ℝ => fun ξ => ∫ η, χ ε ξ η * f ξ η)
    (fun ξ => ∫ η, f ξ η) (𝓝[>] (0 : ℝ)) L

namespace UniformRadialRows
variable {L : Set (Fin N → ℝ)} {χ : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
  {f g : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}

/-- Zero rows have zero uniform radial limit. -/
theorem zero (L : Set (Fin N → ℝ)) (χ : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ) :
    UniformRadialRows L χ (fun _ _ => 0) where
  integrable := fun _ _ => integrable_zero _ _ _
  cutoff_integrable := fun _ _ _ => by simp only [mul_zero]; exact integrable_zero _ _ _
  limit := by
    simp only [mul_zero, integral_zero]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0)).tendstoUniformlyOn_const L

/-- Integrable radial row families add before
passing to their actual uniform limits. -/
theorem add (D : UniformRadialRows L χ f) (E : UniformRadialRows L χ g) :
    UniformRadialRows L χ (fun ξ η => f ξ η + g ξ η) where
  integrable := fun ξ hξ => (D.integrable ξ hξ).add (E.integrable ξ hξ)
  cutoff_integrable := by
    intro ξ hξ ε
    apply ((D.cutoff_integrable ξ hξ ε).add (E.cutoff_integrable ξ hξ ε)).congr
    exact Filter.Eventually.of_forall (fun η => by
      change χ ε ξ η * f ξ η + χ ε ξ η * g ξ η = χ ε ξ η * (f ξ η + g ξ η)
      ring)
  limit := by
    have ht := D.limit.add E.limit
    have ht' := ht.congr
      (F' := fun ε ξ => ∫ η, χ ε ξ η * (f ξ η + g ξ η))
      (Filter.Eventually.of_forall (fun ε => by
      intro ξ hξ
      change (∫ η, χ ε ξ η * f ξ η) + (∫ η, χ ε ξ η * g ξ η) = _
      rw [← integral_add (D.cutoff_integrable ξ hξ ε) (E.cutoff_integrable ξ hξ ε)]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun η => by ring))))
    exact ht'.congr_right (fun ξ hξ => by
      change (∫ η, f ξ η) + (∫ η, g ξ η) = _
      exact (integral_add (D.integrable ξ hξ) (E.integrable ξ hξ)).symm)

/-- Almost everywhere row equality preserves
finite integrability and the actual uniform radial limit. -/
theorem congr_ae (D : UniformRadialRows L χ f) (he : ∀ ξ ∈ L, f ξ =ᵐ[volume] g ξ) :
    UniformRadialRows L χ g where
  integrable := fun ξ hξ => (D.integrable ξ hξ).congr (he ξ hξ)
  cutoff_integrable := fun ξ hξ ε => (D.cutoff_integrable ξ hξ ε).congr
    ((he ξ hξ).mono (fun η hη => congrArg (fun z => χ ε ξ η * z) hη))
  limit := by
    have ht := D.limit.congr (Filter.Eventually.of_forall (fun ε ξ hξ =>
      integral_congr_ae ((he ξ hξ).mono (fun η hη => congrArg (fun z => χ ε ξ η * z) hη))))
    exact ht.congr_right (fun ξ hξ => integral_congr_ae (he ξ hξ))

/-- Finite decompositions retain actual
integrability before uniform convergence is assembled. -/
theorem listSum {ι : Type*} (l : List ι) (f : ι → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (D : ∀ a ∈ l, UniformRadialRows L χ (f a)) :
    UniformRadialRows L χ (fun ξ η => (l.map (fun a => f a ξ η)).sum) := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using zero L χ
  | cons a l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (D a List.mem_cons_self).add (ih (fun b hb => D b (List.mem_cons_of_mem a hb)))

end UniformRadialRows
end RothschildStein.P1
