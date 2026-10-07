-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RadialSharpRowData

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1
variable {N : ℕ}

/-- Actual finite sharp integrability and locally uniform first-order
convergence on a set of row parameters. -/
structure UniformSharpRows (L : Set (Fin N → ℝ))
    (ρ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (f : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) where
  value : (Fin N → ℝ) → ℝ
  integrable : ∀ ξ ∈ L, ∀ ε : ℝ, 0 < ε → IntegrableOn (f ξ) {η | ε < ρ ξ η}
  limit : ∀ ξ ∈ L, Tendsto (fun ε : ℝ => ∫ η in {η | ε < ρ ξ η}, f ξ η)
    (𝓝[>] (0 : ℝ)) (𝓝 (value ξ))
  error : ∃ r A : ℝ, 0 < r ∧ 0 ≤ A ∧ ∀ ξ ∈ L, ∀ ε : ℝ, 0 < ε → ε < r →
    ‖(∫ η in {η | ε < ρ ξ η}, f ξ η) - value ξ‖ ≤ A * ε

namespace UniformSharpRows
variable {L : Set (Fin N → ℝ)} {ρ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
  {f g : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}

def zero (L : Set (Fin N → ℝ)) (ρ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) :
    UniformSharpRows L ρ (fun _ _ => 0) where
  value := fun _ => 0
  integrable := fun _ _ _ _ => integrable_zero _ _ _
  limit := fun _ _ => by simp only [integral_zero]; exact tendsto_const_nhds
  error := ⟨1, 0, zero_lt_one, le_rfl, fun _ _ _ _ _ => by simp⟩

def add (D : UniformSharpRows L ρ f) (E : UniformSharpRows L ρ g) :
    UniformSharpRows L ρ (fun ξ η => f ξ η + g ξ η) where
  value := fun ξ => D.value ξ + E.value ξ
  integrable := fun ξ hξ ε hε => (D.integrable ξ hξ ε hε).add (E.integrable ξ hξ ε hε)
  limit := by
    intro ξ hξ
    refine ((D.limit ξ hξ).add (E.limit ξ hξ)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integral_add (D.integrable ξ hξ ε hε) (E.integrable ξ hξ ε hε)).symm
  error := by
    obtain ⟨r, A, hr, hA, hb⟩ := D.error
    obtain ⟨s, B, hs, hB, hc⟩ := E.error
    refine ⟨min r s, A + B, lt_min hr hs, add_nonneg hA hB, ?_⟩
    intro ξ hξ ε hε hεr
    rw [integral_add (D.integrable ξ hξ ε hε) (E.integrable ξ hξ ε hε)]
    have he : (∫ η in {η | ε < ρ ξ η}, f ξ η) + (∫ η in {η | ε < ρ ξ η}, g ξ η) -
        (D.value ξ + E.value ξ) =
        ((∫ η in {η | ε < ρ ξ η}, f ξ η) - D.value ξ) +
        ((∫ η in {η | ε < ρ ξ η}, g ξ η) - E.value ξ) := by ring
    rw [he]
    exact (norm_add_le _ _).trans (by
      simpa only [add_mul] using add_le_add
        (hb ξ hξ ε hε (hεr.trans_le (min_le_left _ _)))
        (hc ξ hξ ε hε (hεr.trans_le (min_le_right _ _))))

def congr_ae (D : UniformSharpRows L ρ f) (he : ∀ ξ ∈ L, f ξ =ᵐ[volume] g ξ) :
    UniformSharpRows L ρ g where
  value := D.value
  integrable := fun ξ hξ ε hε => (D.integrable ξ hξ ε hε).congr (ae_restrict_of_ae (he ξ hξ))
  limit := by
    intro ξ hξ
    exact (D.limit ξ hξ).congr' (Eventually.of_forall (fun ε =>
      integral_congr_ae (ae_restrict_of_ae (he ξ hξ))))
  error := by
    obtain ⟨r, A, hr, hA, hb⟩ := D.error
    refine ⟨r, A, hr, hA, ?_⟩
    intro ξ hξ ε hε hεr
    rw [← integral_congr_ae (ae_restrict_of_ae (he ξ hξ))]
    exact hb ξ hξ ε hε hεr

def listSum {ι : Type*} (l : List ι) (f : ι → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (D : ∀ i ∈ l, UniformSharpRows L ρ (f i)) :
    UniformSharpRows L ρ (fun ξ η => (l.map (fun i => f i ξ η)).sum) := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using zero L ρ
  | cons i l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (D i List.mem_cons_self).add (ih (fun j hj => D j (List.mem_cons_of_mem i hj)))

end UniformSharpRows
end RothschildStein.P1
