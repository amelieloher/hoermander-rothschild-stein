-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.BootstrapBounds
public import Hormander.E.Iteration.Estimate
public import Hormander.E.Iteration.OrderWeakening
public import Hormander.E.LocalRegularity.OneStep
public import Hormander.E.LocalRegularity.LocalizedGain
public import Hormander.D.Assembly.OffDiagonalSmoothing

@[expose] public section

noncomputable section

open Filter Topology SchwartzMap TemperedDistribution
open Hormander.Interface

namespace Hormander.Provider

/-- The all-orders local Sobolev conclusion follows from the one-step estimate at the same frame
data. The hypothesis `hE2` is the one-step estimate with frame data fixed. The proof weakens the negative input
order (`order_weakening`), takes the frame step and gain (`frame_step_spec`), chooses the target
order (`target_order_spec`), and applies the distributional estimate
(`distributional_estimate_of_one_step`). -/
theorem forall_memSobolev_of_localized_of_one_step {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (w : Fin N → LieWord k)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => lieWordEval X (w a) x))
    {ζ ζ' : EuclideanSpace ℝ (Fin N) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζ' : ContDiff ℝ (⊤ : ℕ∞) ζ')
    (hζζ' : ∀ᶠ x in 𝓝ˢ (tsupport ζ), ζ' x = 1) (hζ'K : tsupport ζ' ⊆ K)
    (u : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)) (f : 𝓢(EuclideanSpace ℝ (Fin N), ℂ))
    (hf : TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ))
      (Hormander.hormanderOp X c u) = (f : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)))
    {m : ℝ}
    (hm : TemperedDistribution.MemSobolev (-m) 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ)) u))
    (hE2 : Hormander.E.OneStepAtFixedFrame X c hX hXc hc hcc hK hU hKU
      (Hormander.E.frame_step w) (Hormander.E.frame_step_spec w).1 w
      (Hormander.E.frame_step_spec w).2 hw) :
    ∀ t : ℝ, TemperedDistribution.MemSobolev t 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ x : ℝ) : ℂ)) u) := by
  have hζ'compact : HasCompactSupport ζ' := by
    change IsCompact (tsupport ζ')
    exact IsCompact.of_isClosed_subset hK (isClosed_tsupport ζ') hζ'K
  have hζts : tsupport ζ ⊆ tsupport ζ' := by
    intro x hx
    have hvalue : ζ' x = 1 := subset_of_mem_nhdsSet hζζ' hx
    apply subset_tsupport
    apply Function.mem_support.mpr
    rw [hvalue]
    norm_num
  have hζK : tsupport ζ ⊆ K := hζts.trans hζ'K
  have hζcompact : HasCompactSupport ζ := by
    change IsCompact (tsupport ζ)
    exact IsCompact.of_isClosed_subset hK (isClosed_tsupport ζ) hζK
  have hcut : Hormander.D.cutoffPrecedes ζ ζ' :=
    ⟨hζ, hζcompact, hζ', hζ'compact, hζζ'⟩
  let η : SchwartzMap (EuclideanSpace ℝ (Fin N)) ℝ :=
    Hormander.B.cutoffSchwartz hcut
  let η' : SchwartzMap (EuclideanSpace ℝ (Fin N)) ℝ :=
    Hormander.B.cutoffSchwartzOuter hcut
  have hηeq : ∀ x, η x = ζ x := by
    intro x
    rfl
  have hη'eq : ∀ x, η' x = ζ' x := by
    intro x
    rfl
  have hmOuter : TemperedDistribution.MemSobolev (-m) 2
      (Hormander.B.cutoffDistr η' u) := by
    rw [Hormander.E.cutoffDistr_eq_raw_function η' ζ' hη'eq u]
    exact hm
  obtain ⟨M, hM, _, hmemM⟩ := Hormander.E.order_weakening hmOuter
  let A : Hormander.A.SobolevSpace N (-M) := hmemM.toBesselPotentialSpace
  have hA : A.toDistr = Hormander.B.cutoffDistr η' u :=
    hmemM.toBesselPotentialSpace_toDistr
  have hframe := Hormander.E.frame_step_spec w
  intro t
  let σ : ℝ := Hormander.E.target_order t
  have hσ : 0 < σ := by
    dsimp [σ]
    exact (Hormander.E.target_order_spec w t).1
  let B : Hormander.A.SobolevSpace N σ := Hormander.A.schwartzToSobolev σ f
  have hBf : B.toDistr = (f : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)) :=
    TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr
      (Hormander.A.schwartz_memSobolev σ f)
  have hB : B.toDistr = Hormander.B.cutoffDistr η' (Hormander.hormanderOp X c u) := by
    calc
      B.toDistr = (f : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)) := hBf
      _ = TemperedDistribution.smulLeftCLM ℂ
          (fun x => ((ζ' x : ℝ) : ℂ)) (Hormander.hormanderOp X c u) := hf.symm
      _ = Hormander.B.cutoffDistr η' (Hormander.hormanderOp X c u) :=
        (Hormander.E.cutoffDistr_eq_raw_function η' ζ' hη'eq
          (Hormander.hormanderOp X c u)).symm
  obtain ⟨C, hC⟩ := Hormander.E.distributional_estimate_of_one_step
    X c hX hXc hc hcc hK hU hKU (Hormander.E.frame_step w) hframe.1 w hframe.2 hw hE2
    η η' hcut hζ'K hM hσ
  obtain ⟨V, hV, _⟩ := hC u A B hA hB
  have htarget := Hormander.E.target_order_spec w t
  have horderTarget : t ≤ σ + (2 : ℝ) / 4 ^ Hormander.E.frame_step w := by
    apply le_of_lt
    simpa [σ, Hormander.E.target_order, Hormander.E.frame_gain] using htarget.2
  have hmem : TemperedDistribution.MemSobolev t 2 V.toDistr :=
    (BesselPotentialSpace.memSobolev_toDistr V).mono horderTarget
  rw [hV, Hormander.E.cutoffDistr_eq_raw_function η ζ hηeq u] at hmem
  exact hmem

/-- The all-orders local Sobolev conclusion follows from the localized gain hypothesis
`Hormander.E.D1Hypothesis`: the one-step estimate is
`Hormander.E.one_step_regularization_of_localized_gain`, which instantiates the mollifier
converse. -/
theorem forall_memSobolev_of_localized_of_localized_gain {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (w : Fin N → LieWord k)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => lieWordEval X (w a) x))
    {ζ ζ' : EuclideanSpace ℝ (Fin N) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζ' : ContDiff ℝ (⊤ : ℕ∞) ζ')
    (hζζ' : ∀ᶠ x in 𝓝ˢ (tsupport ζ), ζ' x = 1) (hζ'K : tsupport ζ' ⊆ K)
    (u : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)) (f : 𝓢(EuclideanSpace ℝ (Fin N), ℂ))
    (hf : TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ))
      (Hormander.hormanderOp X c u) = (f : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)))
    {m : ℝ}
    (hm : TemperedDistribution.MemSobolev (-m) 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ)) u))
    (hD1 : Hormander.E.D1Hypothesis) :
    ∀ t : ℝ, TemperedDistribution.MemSobolev t 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ x : ℝ) : ℂ)) u) :=
  forall_memSobolev_of_localized_of_one_step X c hX hXc hc hcc hK hU hKU w hw hζ hζ' hζζ' hζ'K
    u f hf hm
    (Hormander.E.oneStepAtFixedFrame_of_localized_gain hD1 X c hX hXc hc hcc hK hU hKU
      (Hormander.E.frame_step w) (Hormander.E.frame_step_spec w).1 w
      (Hormander.E.frame_step_spec w).2 hw)

/-- The all-orders local Sobolev conclusion follows from
the off-diagonal smoothing statement `Hormander.D.OffDiagonalSmoothing`:
`Hormander.D.localized_gain_of_offDiagonal`, together with the mollifier converse. -/
theorem forall_memSobolev_of_localized_of_offDiagonal {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (w : Fin N → LieWord k)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => lieWordEval X (w a) x))
    {ζ ζ' : EuclideanSpace ℝ (Fin N) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζ' : ContDiff ℝ (⊤ : ℕ∞) ζ')
    (hζζ' : ∀ᶠ x in 𝓝ˢ (tsupport ζ), ζ' x = 1) (hζ'K : tsupport ζ' ⊆ K)
    (u : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)) (f : 𝓢(EuclideanSpace ℝ (Fin N), ℂ))
    (hf : TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ))
      (Hormander.hormanderOp X c u) = (f : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)))
    {m : ℝ}
    (hm : TemperedDistribution.MemSobolev (-m) 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ)) u))
    (hB8 : ∀ N, Hormander.D.OffDiagonalSmoothing N) :
    ∀ t : ℝ, TemperedDistribution.MemSobolev t 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ x : ℝ) : ℂ)) u) :=
  forall_memSobolev_of_localized_of_localized_gain X c hX hXc hc hcc hK hU hKU w hw hζ hζ' hζζ'
    hζ'K u f hf hm (Hormander.E.d1Hypothesis_of_offDiagonal hB8)

/-- Local Sobolev regularity from the Hörmander condition (BB Thm. 5.64, repaired). -/
theorem forall_memSobolev_of_localized {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (w : Fin N → LieWord k)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => lieWordEval X (w a) x))
    {ζ ζ' : EuclideanSpace ℝ (Fin N) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζ' : ContDiff ℝ (⊤ : ℕ∞) ζ')
    (hζζ' : ∀ᶠ x in 𝓝ˢ (tsupport ζ), ζ' x = 1) (hζ'K : tsupport ζ' ⊆ K)
    (u : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)) (f : 𝓢(EuclideanSpace ℝ (Fin N), ℂ))
    (hf : TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ)) (hormanderOp X c u) =
      (f : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)))
    {m : ℝ}
    (hm : TemperedDistribution.MemSobolev (-m) 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ)) u)) :
    ∀ t : ℝ, TemperedDistribution.MemSobolev t 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ x : ℝ) : ℂ)) u) :=
  forall_memSobolev_of_localized_of_offDiagonal X c hX hXc hc hcc hK hU hKU w hw hζ hζ' hζζ'
    hζ'K u f hf hm (fun N => Hormander.D.offDiagonalSmoothing N)

end Hormander.Provider

end
