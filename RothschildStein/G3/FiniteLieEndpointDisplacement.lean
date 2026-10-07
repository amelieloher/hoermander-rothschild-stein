-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.EndpointCoefficientDisplacement
public import RothschildStein.G3.ZeroCoefficientFlow
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

theorem norm_finiteLie_endpoint_displacement_of_ode_and_first_jets {a s N : ℕ}
    {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) {σ C : ℝ} (hσ : 0 < σ)
    (Ψ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ ((ball 0 σ ×ˢ Ω) ×ˢ Ioo (-2) 2))
    (hODE : ∀ f : formalSpan a s p, D.basis.equivFun f ∈ ball 0 σ →
      ∀ x ∈ Ω, Ψ ((D.basis.equivFun f,x),0) = x ∧ ∀ t ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt (fun v => Ψ ((D.basis.equivFun f,x),v))
          (finiteLieField D X f (Ψ ((D.basis.equivFun f,x),t))) t)
    (hjet : ∀ q ∈ ball 0 σ ×ˢ Ω, ‖iteratedFDeriv ℝ 1 (finiteLieTimeOneMap Ψ) q‖ ≤ C)
    {c : Fin (freeDimension a s p) → ℝ} (hc : c ∈ ball 0 σ)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    ‖finiteLieTimeOneMap Ψ (c,x)-x‖ ≤ C*‖c‖ := by
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) (finiteLieTimeOneMap Ψ) (ball 0 σ ×ˢ Ω) := by
    apply hΨ.comp (contDiffOn_id.prodMk contDiffOn_const)
    intro q hq
    exact ⟨hq,by norm_num⟩
  have hz : ∀ y ∈ Ω, finiteLieTimeOneMap Ψ (0,y) = y := by
    intro y hy
    have he := hODE 0 (by simpa only [map_zero] using
      (show (0 : Fin (freeDimension a s p) → ℝ) ∈ ball 0 σ by simp [hσ])) y hy
    exact finiteLieTimeOneMap_zero_of_finiteLie_ode D X Ψ y
      (by simpa only [map_zero] using he.1)
      (fun t ht => by simpa only [map_zero] using he.2 t ht)
  exact norm_endpoint_sub_initial_of_joint_first_jet_bound hΩ hσ
    (finiteLieTimeOneMap Ψ) hH hz hjet hc hx
end RothschildStein.G3
