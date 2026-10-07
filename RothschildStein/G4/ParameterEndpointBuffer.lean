-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.EndpointBuffer

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The actual parameter-flow endpoint has its reverse trajectory
on the original forward segment, with parameters kept fixed
(BB Lemma 9.48, pp. 441–443). -/
theorem parameterFlow_endpoint_reverse {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {N : ℕ}
    {A : Set P} {Ω : Set (Fin N → ℝ)} {U : Set (P × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) (hUA : U ⊆ A ×ˢ Ω)
    {Z : P × (Fin N → ℝ) → (Fin N → ℝ)}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω))
    {τ : ℝ} (hτ : 1 < τ)
    (Φ : ((P × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (Z (p.1, Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    {p : P × (Fin N → ℝ)} (hp : p ∈ U)
    (hend : (p.1, Φ (p, 1)) ∈ U) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Φ ((p.1, Φ (p, 1)), -s) = Φ (p, 1 - s) := by
  let V : Set (Fin N → ℝ) := {x | (p.1, x) ∈ U}
  let F : (Fin N → ℝ) → (Fin N → ℝ) := fun x => Z (p.1, x)
  let Ψ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ) := fun q => Φ ((p.1, q.1), q.2)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F Ω :=
    hZ.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun x hx => ⟨(hUA hp).1, hx⟩)
  have hΨ : ∀ x ∈ V, Ψ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Ψ (x, w)) (F (Ψ (x, v))) v ∧ Ψ (x, v) ∈ Ω := by
    intro x hx
    exact hΦ (p.1, x) hx
  have hh := localFlow_endpoint_reverse hΩ F hF hτ Ψ hΨ
    (x := p.2) (by change (p.1, p.2) ∈ U; simpa only [Prod.mk.eta] using hp)
    (by change (p.1, Φ ((p.1, p.2), 1)) ∈ U; simpa only [Prod.mk.eta] using hend) hs
  simpa only [Ψ, Prod.mk.eta] using hh

/-- A forward segment in the original initial-point domain supplies
all reverse-domain hypotheses at the actual endpoint (BB pp. 441–443). -/
theorem parameterFlow_endpoint_reverse_segment {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {N : ℕ}
    {A : Set P} {Ω : Set (Fin N → ℝ)} {U : Set (P × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) (hUA : U ⊆ A ×ˢ Ω)
    {Z : P × (Fin N → ℝ) → (Fin N → ℝ)}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω))
    {τ : ℝ} (hτ : 1 < τ)
    (Φ : ((P × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (Z (p.1, Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    {p : P × (Fin N → ℝ)} (hp : p ∈ U)
    (hforward : ∀ s ∈ Icc (0 : ℝ) 1, (p.1, Φ (p, s)) ∈ U) :
    ∀ s ∈ Icc (0 : ℝ) 1, (p.1, Φ ((p.1, Φ (p, 1)), -s)) ∈ U := by
  intro s hs
  rw [parameterFlow_endpoint_reverse hΩ hUA hZ hτ Φ hΦ hp
    (hforward 1 (by simp)) hs]
  exact hforward (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩

end RothschildStein.G4
