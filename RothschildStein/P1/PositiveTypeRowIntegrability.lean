-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalColumnIntegrability
public import RothschildStein.P1.RegularKernelIntegrability
public import RothschildStein.P1.TypeCalculusStatements

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.P1

variable {N : ℕ}

private theorem integrable_list_sum_map {A : Type*} (l : List A)
    (f : A → (Fin N → ℝ) → ℝ) (hf : ∀ a ∈ l, Integrable (f a)) :
    Integrable (fun x => (l.map (fun a => f a x)).sum) := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil, Pi.zero_def] using (integrable_zero _ _ volume : Integrable (0 : (Fin N → ℝ) → ℝ))
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf a (by simp)).add (ih (fun b hb => hf b (List.mem_cons_of_mem a hb)))

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The complete positive-type row/column integrability provider for an
actual lifted chart and poles with the H1 smoothness and homogeneity properties.
Every positive type and every endpoint are covered; diagonal values are unrestricted. -/
theorem LiftedChart.positiveType_rowIntegrable
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hG : F.G = C.G) (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hΓ : ∀ star : Bool, ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ star : Bool, ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u) :
    TypeKernelIntegrable F := by
  let rsPositiveTypeFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  intro lam hlam kern hk ξ
  obtain ⟨D⟩ := hk 0
  have hdegree : ∀ t ∈ D.principal, t.degree ≤ 1 := by
    intro t ht
    have hd := D.principal_degree t ht
    omega
  have hrow : Integrable (fun η => (D.principal.map (fun t => t.kernel ξ η)).sum + D.regular ξ η) :=
    (integrable_list_sum_map D.principal (fun t => t.kernel ξ)
      (fun t ht => C.integrable_principal_row F hG hΘ hVU t (hdegree t ht) (hΓ t.star) (hhom t.star) ξ)).add
      (D.regular_isRegular.integrable_slices ξ).1
  have hcol : Integrable (fun η => (D.principal.map (fun t => t.kernel η ξ)).sum + D.regular η ξ) :=
    (integrable_list_sum_map D.principal (fun t η => t.kernel η ξ)
      (fun t ht => C.integrable_principal_column F hG hΘ hVU t (hdegree t ht) (hΓ t.star) (hhom t.star) ξ)).add
      (D.regular_isRegular.integrable_slices ξ).2
  constructor
  · apply hrow.congr
    filter_upwards [volume.ae_ne ξ] with η hη
    exact (D.eq_off_diagonal ξ η hη.symm).symm
  · apply hcol.congr
    filter_upwards [volume.ae_ne ξ] with η hη
    exact (D.eq_off_diagonal η ξ hη).symm

end RothschildStein.P1
