-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ReflectedChartTransport
public import RothschildStein.S.WeakDeriv
public import RothschildStein.P1.PrincipalModelKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The open reflected target of the actual endpoint chart. -/
def reflectedModelOpens (ξ : Fin (n + m) → ℝ) : Opens (Fin (n + m) → ℝ) :=
  ⟨{u | -u ∈ (C.e ξ).target}, (C.e ξ).open_target.preimage continuous_neg⟩

/-- The reflected transported test has compact
support strictly inside the actual reflected chart target. -/
def reflectedTransportTest {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    TestFunction (C.reflectedModelOpens ξ) ℝ (⊤ : ℕ∞) := by
  obtain ⟨hc, hs⟩ := C.reflectedTransport_regular hξ ψ
  refine ⟨C.reflectedTransport ξ ψ, hc, hs, ?_⟩
  change tsupport (C.modelTransport ξ ψ ∘ (Homeomorph.neg (Fin (n + m) → ℝ))) ⊆ _
  rw [tsupport_comp_eq_preimage]
  intro u hu
  exact C.tsupport_modelTransport_subset hξ ψ hu

/-- A continuous amplitude on the reflected
target, vanishing near the pole, makes the actual moving-endpoint
principal model integrable against its transported test. -/
theorem integrable_inputModel_cutoffProduct {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (A : (Fin (n + m) → ℝ) → ℝ)
    (hA : ContinuousOn A (C.reflectedModelOpens ξ : Set (Fin (n + m) → ℝ)))
    (h0A : A =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 0)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Integrable (fun u => (Ψ ξ ((C.e ξ).symm (-u)) u * A u) * C.reflectedTransport ξ ψ u) := by
  have hc : ContinuousOn (fun u => Ψ ξ ((C.e ξ).symm (-u)) u * A u)
      (C.reflectedModelOpens ξ : Set (Fin (n + m) → ℝ)) := by
    intro u hu
    apply ContinuousAt.continuousWithinAt
    by_cases hz : u = 0
    · subst u
      exact (continuousAt_const : ContinuousAt
        (fun _ : Fin (n + m) → ℝ => (0 : ℝ)) 0).congr_of_eventuallyEq
        (h0A.mono (fun v hv => by
          change Ψ ξ ((C.e ξ).symm (-v)) v * A v = 0
          change A v = 0 at hv
          rw [hv, mul_zero]))
    · have hI : ContinuousAt (fun v => (C.e ξ).symm (-v)) u :=
        ((C.chart ξ hξ).2.2.2.1.continuousOn.continuousAt
          ((C.e ξ).open_target.mem_nhds hu)).comp continuous_neg.continuousAt
      have hzModel : (ξ, (C.e ξ).symm (-u), u) ∈
          {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) | z.2.2 ≠ 0} := hz
      have hparams : ContinuousAt
          (fun v : Fin (n + m) → ℝ => (ξ, (C.e ξ).symm (-v), v)) u :=
        (continuousAt_const : ContinuousAt (fun _ : Fin (n + m) → ℝ => ξ) u).prodMk
          (hI.prodMk continuousAt_id)
      have hbody : ContinuousAt
          (fun v : Fin (n + m) → ℝ => Ψ ξ ((C.e ξ).symm (-v)) v) u := by
        simpa only [kernelUncurry, Function.comp_def] using
          (hΨ.continuousAt (isOpen_kernelDomain.mem_nhds hzModel)).comp
            (f := fun v : Fin (n + m) → ℝ => (ξ, (C.e ξ).symm (-v), v))
            (g := kernelUncurry Ψ) hparams
      exact hbody.mul (hA.continuousAt ((C.reflectedModelOpens ξ).isOpen.mem_nhds hu))
  exact S.integrable_mul_test (C.reflectedModelOpens ξ)
    (hc.locallyIntegrableOn (μ := volume) (C.reflectedModelOpens ξ).isOpen.measurableSet)
    (C.reflectedTransportTest hξ ψ)

end RothschildStein.P1.LiftedChart
