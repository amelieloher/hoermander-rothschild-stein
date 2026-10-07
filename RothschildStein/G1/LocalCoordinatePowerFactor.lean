-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CoordinatePowerFactor
public import RothschildStein.G1.LocalProductFactorization

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RothschildStein.G1

/-- Scalar-time power factorization is local in the original
smooth flow domain. Vanishing jets are required only on its zero-time
slice; a compactly supported multiplier supplies the global FTC factor
(BB Proposition 1.50, pp. 28–29). -/
theorem exists_local_coordinate_power_factor {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    (k : ℕ) {U : Set (E × ℝ)} (hU : IsOpen U)
    (G : E × ℝ → (Fin N → ℝ)) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hzero : ∀ x, (x, 0) ∈ U → ∀ j < k, ∀ i : Fin N,
      iteratedDeriv j (fun t => G (x, t) i) 0 = 0)
    (x₀ : E) (hx₀ : (x₀, 0) ∈ U) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ (x₀, 0) ∈ V ∧ V ⊆ U ∧
      ∃ H : E × ℝ → (Fin N → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
        ∀ q ∈ V, G q = q.2 ^ k • H q := by
  obtain ⟨φ, hsupp, _hcompact, hφ, _hrange, hφx⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU.mem_nhds hx₀)
  let K : E × ℝ → (Fin N → ℝ) := fun q => φ q • G q
  have hK : ContDiff ℝ (⊤ : ℕ∞) K := cutoff_smul_contDiff hU G hG φ hφ hsupp
  have hflat : ∀ x, ∀ j < k, ∀ i : Fin N,
      iteratedDeriv j (fun t => K (x, t) i) 0 = 0 := by
    intro x j hj i
    by_cases hx : (x, 0) ∈ U
    · have hp : ContDiffAt ℝ j (fun t => φ (x, t)) 0 :=
        ((hφ.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id)).contDiffAt
      have hslice : ContDiffAt ℝ j (fun t => G (x, t)) 0 :=
        ((hG.contDiffAt (hU.mem_nhds hx)).of_le (m := j) (by simp)).comp 0
          (contDiffAt_const.prodMk contDiffAt_id)
      have heval : ContDiffAt ℝ j (fun z : Fin N → ℝ => z i) (G (x, 0)) :=
        contDiffAt_apply ℝ ℝ i (G (x, 0))
      have hg : ContDiffAt ℝ j (fun t => G (x, t) i) 0 := heval.comp (f := fun t : ℝ => G (x, t)) (g := fun z : Fin N → ℝ => z i) 0 hslice
      change iteratedDeriv j (fun t => φ (x, t) * G (x, t) i) 0 = 0
      rw [iteratedDeriv_fun_mul hp hg]
      apply Finset.sum_eq_zero
      intro a _ha
      rw [hzero x hx (j - a) (by omega) i, mul_zero]
    · have hs : (x, 0) ∉ tsupport φ := fun hx' => hx (hsupp hx')
      have hz := (continuous_const.prodMk continuous_id).continuousAt.tendsto.eventually
        (notMem_tsupport_iff_eventuallyEq.mp hs)
      have he : (fun t => K (x, t) i) =ᶠ[𝓝 0] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [hz] with t ht
        simp only [id_eq, Pi.zero_apply] at ht
        simp only [K, ht, zero_smul, Pi.zero_apply]
      rw [he.iteratedDeriv_eq j]
      simp
  obtain ⟨H, hH, he⟩ := exists_smooth_coordinate_power_factor k K hK hflat
  let V := U ∩ {q | φ q ≠ 0}
  have hV : IsOpen V := hU.inter (isOpen_ne.preimage hφ.continuous)
  refine ⟨V, hV, ⟨hx₀, by change φ (x₀, 0) ≠ 0; rw [hφx]; exact one_ne_zero⟩,
    inter_subset_left, fun q => (φ q)⁻¹ • H q, ?_, ?_⟩
  · exact (hφ.contDiffOn.inv (fun q hq => hq.2)).smul hH.contDiffOn
  · intro q hq
    have hh := congrArg (fun z : Fin N → ℝ => (φ q)⁻¹ • z) (he q.1 q.2)
    change (φ q)⁻¹ • (φ q • G q) = _ at hh
    rw [inv_smul_smul₀ hq.2] at hh
    exact hh.trans (smul_comm _ _ _)

end RothschildStein.G1
