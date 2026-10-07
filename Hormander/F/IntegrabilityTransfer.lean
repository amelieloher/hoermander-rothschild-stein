-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.AdjointTest
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

noncomputable section

open Function MeasureTheory Set Topology

namespace Hormander.F

/-- A compactly supported adjoint test pairs
integrably with locally integrable data, and its integral over the open domain equals the ambient
integral. The same transfer holds for the localized forcing term. -/
theorem adjoint_pairing_integrable_and_integral_transfer {k N : ℕ}
    {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (c g u : (Fin N → ℝ) → ℝ)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
    (hu : LocallyIntegrableOn u Ω volume)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcompact : HasCompactSupport φ) (hK : tsupport φ ⊆ Ω) :
    Integrable (fun x => u x * Hormander.Interface.hormanderAdjointTest X c φ x) volume ∧
      (∫ x in Ω, u x * Hormander.Interface.hormanderAdjointTest X c φ x) =
        ∫ x, u x * Hormander.Interface.hormanderAdjointTest X c φ x ∧
      Integrable (fun x => g x * φ x) volume ∧
      (∫ x in Ω, g x * φ x) = ∫ x, g x * φ x := by
  let ψ := Hormander.Interface.hormanderAdjointTest X c φ
  have hψSmooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hormanderAdjointTest_smooth hΩ X hX c hc φ hφ hK
  have hψSupport : tsupport ψ ⊆ tsupport φ := hormanderAdjointTest_tsupport_subset X c φ
  have hKcompact : IsCompact (tsupport φ) := hφcompact
  have huK : IntegrableOn u (tsupport φ) volume :=
    hu.integrableOn_compact_subset hK hKcompact
  have huψK : IntegrableOn (fun x => u x * ψ x) (tsupport φ) volume :=
    huK.mul_continuousOn hψSmooth.continuous.continuousOn hKcompact
  have huψSupport : support (fun x => u x * ψ x) ⊆ tsupport φ := by
    exact (support_mul_subset_right _ _).trans
      ((subset_tsupport ψ).trans hψSupport)
  have huψ : Integrable (fun x => u x * ψ x) volume :=
    (integrableOn_iff_integrable_of_support_subset huψSupport).mp huψK
  have huψLocal : ∫ x in Ω, u x * ψ x = ∫ x, u x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hxΩ
    have hxK : x ∉ tsupport φ := fun hxs => hxΩ (hK hxs)
    simp [ψ, hormanderAdjointTest_zero_outside X c φ hxK]
  have hgφSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x * g x) :=
    localized_mul_smooth hΩ φ g hφ hK hg
  have hgφCompact : HasCompactSupport (fun x => φ x * g x) := hφcompact.mul_right
  have hgφLeft : Integrable (fun x => φ x * g x) volume :=
    hgφSmooth.continuous.integrable_of_hasCompactSupport hgφCompact
  have hgφ : Integrable (fun x => g x * φ x) volume := by
    simpa [mul_comm] using hgφLeft
  have hgφLocal : ∫ x in Ω, φ x * g x = ∫ x, φ x * g x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hxΩ
    have hxK : x ∉ tsupport φ := fun hxs => hxΩ (hK hxs)
    have hxS : x ∉ support φ := fun hxs => hxK (subset_closure hxs)
    have hφx : φ x = 0 := by
      simpa only [mem_support, not_not] using hxS
    simp [hφx]
  exact ⟨huψ, huψLocal, hgφ, by simpa [mul_comm] using hgφLocal⟩

end Hormander.F
