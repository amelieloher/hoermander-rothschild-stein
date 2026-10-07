-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualInverseNeighborhood
public import Mathlib.Topology.Piecewise

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped Topology

namespace RothschildStein.G4

/-- A continuous partial lift whose endpoint has an actual local
inverse extends to a strictly longer time interval. The extension is
constructed by gluing the inverse of the base path to the old lift
(BB Prop 9.52, continuation step, p. 449). -/
theorem partialLift_extend_of_inverse_patch {n : ℕ}
    (F Ψ : (Fin n → ℝ) → (Fin n → ℝ))
    (γ θ : ℝ → (Fin n → ℝ)) {U V : Set (Fin n → ℝ)}
    (hV : IsOpen V) (hΨ : ContinuousOn Ψ V) (hΨU : MapsTo Ψ V U)
    (hright : EqOn (F ∘ Ψ) id V) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) (hγT : γ T ∈ V)
    (hstart : Ψ (γ T) = θ T)
    (hθ : ContinuousOn θ (Icc (0 : ℝ) T))
    (hθU : MapsTo θ (Icc (0 : ℝ) T) U)
    (hlift : EqOn (F ∘ θ) γ (Icc (0 : ℝ) T)) :
    ∃ T' : ℝ, T < T' ∧ T' ≤ 1 ∧ ∃ θ' : ℝ → (Fin n → ℝ),
      ContinuousOn θ' (Icc (0 : ℝ) T') ∧ EqOn θ' θ (Icc (0 : ℝ) T) ∧
      MapsTo θ' (Icc (0 : ℝ) T') U ∧ EqOn (F ∘ θ') γ (Icc (0 : ℝ) T') := by
  have hpre : γ ⁻¹' V ∈ 𝓝[Icc (0 : ℝ) 1] T :=
    (hγ T ⟨hT0, hT1.le⟩).preimage_mem_nhdsWithin (hV.mem_nhds hγT)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let d := min (ε / 2) ((1 - T) / 2)
  have hd : 0 < d := lt_min (by positivity) (by linarith)
  have hdε : d < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hdT : d ≤ (1 - T) / 2 := min_le_right _ _
  have hT' : T + d ≤ 1 := by linarith
  have hpatch : MapsTo γ (Icc T (T + d)) V := by
    intro t ht
    apply hεsub
    refine ⟨?_, ⟨hT0.trans ht.1, ht.2.trans hT'⟩⟩
    rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hnew : ContinuousOn (Ψ ∘ γ) (Icc T (T + d)) :=
    hΨ.comp (hγ.mono (Icc_subset_Icc hT0 hT')) hpatch
  let θ' : ℝ → (Fin n → ℝ) := fun t => if t ≤ T then θ t else Ψ (γ t)
  refine ⟨T + d, by linarith, hT', θ', ?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.if
    · intro t ht
      have he : t = T := frontier_le_subset_eq continuous_id continuous_const ht.2
      simpa only [he] using hstart.symm
    · apply hθ.mono
      intro t ht
      change t ∈ Icc (0 : ℝ) (T + d) ∩ closure (Iic T) at ht
      rw [isClosed_Iic.closure_eq] at ht
      exact ⟨ht.1.1, ht.2⟩
    · apply hnew.mono
      intro t ht
      simp only [not_le] at ht
      exact ⟨closure_lt_subset_le continuous_const continuous_id ht.2, ht.1.2⟩
  · intro t ht
    exact ite_eq_left ht.2
  · intro t ht
    change (if t ≤ T then θ t else Ψ (γ t)) ∈ U
    split_ifs with hle
    · exact hθU ⟨ht.1, hle⟩
    · exact hΨU (hpatch ⟨(lt_of_not_ge hle).le, ht.2⟩)
  · intro t ht
    change F (if t ≤ T then θ t else Ψ (γ t)) = γ t
    split_ifs with hle
    · exact hlift ⟨ht.1, hle⟩
    · exact hright (hpatch ⟨(lt_of_not_ge hle).le, ht.2⟩)

end RothschildStein.G4
