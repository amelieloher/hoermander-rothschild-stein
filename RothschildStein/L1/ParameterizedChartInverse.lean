-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.SmoothChartInverse
public import RothschildStein.L1.UpperTriangularDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

/-- Retaining the parameter converts fiberwise injectivity
into injectivity of the full horizontal chart. -/
theorem injOn_parameter_retaining_chart {E F : Type*}
    (Ψ : E × F → E) (U : Set (E × F))
    (hinj : ∀ v, InjOn (fun u => Ψ (u, v)) {u | (u, v) ∈ U}) :
    InjOn (fun p : E × F => (Ψ p, p.2)) U := by
  rintro ⟨u, v⟩ hp ⟨u', v'⟩ hq he
  have hv : v = v' := congrArg Prod.snd he
  subst v'
  have hu : u = u' := hinj v hp hq (congrArg Prod.fst he)
  subst u'
  rfl

/-- The shifted horizontal inverse is jointly smooth in its
base point and parameter. The premises are actual chart injectivity,
coverage and invertible horizontal derivatives (BB pp. 520–521). -/
theorem contDiffOn_parameterized_chart_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U V : Set (E × F)} (hU : IsOpen U) (hV : IsOpen V)
    (Ψ : E × F → E) (θ : E × F → E) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ U)
    (hinj : ∀ v, InjOn (fun u => Ψ (u, v)) {u | (u, v) ∈ U})
    (hθ : ∀ p ∈ V, (θ p, p.2) ∈ U)
    (hΨθ : ∀ p ∈ V, Ψ (θ p, p.2) = p.1)
    (hderiv : ∀ p ∈ U, ∃ H : E ≃L[ℝ] E,
      (fderiv ℝ Ψ p).comp (ContinuousLinearMap.inl ℝ E F) = (H : E →L[ℝ] E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) θ V := by
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : E × F => (Ψ p, p.2)) U :=
    hΨ.prodMk contDiffOn_snd
  have hd : ∀ p ∈ U, ∃ L : (E × F) ≃L[ℝ] (E × F),
      HasFDerivAt (fun q : E × F => (Ψ q, q.2)) (L : (E × F) →L[ℝ] (E × F)) p := by
    intro p hp
    obtain ⟨H, hH⟩ := hderiv p hp
    let L := upperTriangularDerivativeEquiv H
      ((fderiv ℝ Ψ p).comp (ContinuousLinearMap.inr ℝ E F))
    refine ⟨L, ?_⟩
    rw [upperTriangularDerivativeEquiv_eq_prod (fderiv ℝ Ψ p) H hH]
    exact ((hΨ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.prodMk
      hasFDerivAt_snd
  have hg := contDiffOn_chart_inverse hU hV (fun p : E × F => (Ψ p, p.2))
    (fun p : E × F => (θ p, p.2)) hf (injOn_parameter_retaining_chart Ψ U hinj) hθ
    (fun p hp => Prod.ext (hΨθ p hp) rfl) hd
  exact hg.fst

end RothschildStein.L1
