-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LocalIntervalIntegralJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace RothschildStein.G4

universe u

/-- A locally smooth compact parameter integral is smooth at a
parameter whose entire compact segment lies in its actual open domain
(BB pp. 441–443, common-buffer differentiation step). -/
theorem local_compact_parameter_integral_contDiffAt {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Set (E × ℝ)} (hS : IsOpen S) (G : E × ℝ → F)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G S) (x : E)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ S) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ∫ t in Icc (0 : ℝ) 1, G (y, t)) x := by
  have hK : IsCompact (({x} : Set E) ×ˢ Icc (0 : ℝ) 1) := isCompact_singleton.prod isCompact_Icc
  have hKS : ({x} : Set E) ×ˢ Icc (0 : ℝ) 1 ⊆ S := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    have hy' : y = x := mem_singleton_iff.mp hy
    subst y
    exact hsegment t ht
  obtain ⟨g, hg, V, hV, hKV, heq⟩ := exists_contDiff_extension_near_compact hS hK hKS hG
  have he : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, (y, t) ∈ V :=
    isCompact_Icc.eventually_forall_of_forall_eventually
      (fun t ht => hV.mem_nhds (hKV ⟨mem_singleton x, ht⟩))
  have hI : (fun y => ∫ t in Icc (0 : ℝ) 1, G (y, t)) =ᶠ[𝓝 x]
      (fun y => ∫ t in Icc (0 : ℝ) 1, g (y, t)) := by
    filter_upwards [he] with y hy
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (heq (hy t ht)).symm
  exact ((RothschildStein.G1.compactParameterIntegral_contDiff g hg).contDiffAt).congr_of_eventuallyEq hI

/-- The actual local unit-interval integral is smooth at every
parameter whose compact integration segment stays in the open domain
(BB Lemma 9.48, pp. 441–443). -/
theorem local_interval_parameter_integral_contDiffAt {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Set (E × ℝ)} (hS : IsOpen S) (G : E × ℝ → F)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G S) (x : E)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ S) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ∫ t in (0 : ℝ)..1, G (y, t)) x := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact local_compact_parameter_integral_contDiffAt hS G hG x hsegment

/-- The set of parameters with a whole compact integration
segment in an open joint domain is itself open (BB pp. 441–443). -/
theorem isOpen_parameter_segment_domain {E : Type*} [TopologicalSpace E]
    {S : Set (E × ℝ)} (hS : IsOpen S) :
    IsOpen {x | ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ S} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact isCompact_Icc.eventually_forall_of_forall_eventually
    (fun t ht => hS.mem_nhds (hx t ht))

/-- The actual local interval integral is jointly smooth on the
open domain of parameters with a complete integration segment
(BB Lemma 9.48, pp. 441–443). -/
theorem local_interval_parameter_integral_contDiffOn {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Set (E × ℝ)} (hS : IsOpen S) (G : E × ℝ → F)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G S) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ∫ t in (0 : ℝ)..1, G (y, t))
      {x | ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ S} := by
  apply (isOpen_parameter_segment_domain hS).contDiffOn_iff.mpr
  intro x hx
  exact local_interval_parameter_integral_contDiffAt hS G hG x hx

end RothschildStein.G4
