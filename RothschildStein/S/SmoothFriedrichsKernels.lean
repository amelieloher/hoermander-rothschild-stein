-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FriedrichsKernelDefs
public import RothschildStein.S.HadamardFirstDerivative
public import RothschildStein.S.ParameterSliceJets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- Preferred joint-parameter encoding for the constructed kernels:
K(x,y,ε) is globally smooth and vanishes when ‖y‖>1. Uniform slice jets on compact x-patches follow by compactness (BB p. 76). Local fields are extended to global fields with matching germs. -/
structure SmoothFriedrichsKernel (n : ℕ) where
  toFun : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  vanish : ∀ p, 1 < ‖p.1.2‖ → toFun p = 0

/-- The unbundled ε-indexed family of a joint smooth kernel
(BB p. 76). -/
def SmoothFriedrichsKernel.family (K : SmoothFriedrichsKernel n)
    (ε : ℝ) (x y : Fin n → ℝ) : ℝ := K.toFun ((x,y),ε)

/-- A joint smooth kernel has support in the closed vertical unit
ball, including at its boundary (BB p. 76). -/
theorem SmoothFriedrichsKernel.tsupport_subset (K : SmoothFriedrichsKernel n) :
    tsupport K.toFun ⊆ {p | ‖p.1.2‖ ≤ 1} := by
  apply closure_minimal _
    (isClosed_le ((continuous_fst.snd).norm) continuous_const)
  intro p hp
  by_contra hn
  exact hp (K.vanish p (lt_of_not_ge hn))

/-- Joint smoothness gives the y-section smoothness used for the
kernel test functions (BB pp. 75–78). -/
theorem SmoothFriedrichsKernel.section_smooth (K : SmoothFriedrichsKernel n)
    (ε : ℝ) (x : Fin n → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (K.family ε x) := by
  exact K.smooth.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)

/-- Joint smooth kernels have compact y-sections (BB p. 76). -/
theorem SmoothFriedrichsKernel.section_compact (K : SmoothFriedrichsKernel n)
    (ε : ℝ) (x : Fin n → ℝ) : HasCompactSupport (K.family ε x) := by
  apply (isCompact_closedBall (0 : Fin n → ℝ) 1).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  change ‖y-0‖ ≤ 1
  rw [sub_zero]
  by_contra hn
  exact hy (K.vanish ((x,y),ε) (lt_of_not_ge hn))

/-- On a compact x-patch, the preferred joint encoding satisfies
all fields of the bounded Friedrichs kernel class (BB p. 76). -/
def SmoothFriedrichsKernel.toBounded (K : SmoothFriedrichsKernel n)
    (U : Set (Fin n → ℝ)) (hU : IsCompact (closure U)) (δ : ℝ) :
    BoundedFriedrichsKernel U δ where
  toFun := K.family
  smooth := fun ε _ => (K.smooth.comp
    ((contDiff_fst.prodMk contDiff_snd).prodMk contDiff_const)).contDiffOn
  support := by
    intro ε hε x hx y hy
    change ‖y-0‖ ≤ 1
    rw [sub_zero]
    by_contra hn
    exact hy (K.vanish ((x,y),ε) (lt_of_not_ge hn))
  jetBound := by
    intro m
    obtain ⟨C,hC,hb⟩ := exists_parameterSlice_jetBound K.smooth
      (hU.prod (isCompact_closedBall (0 : Fin n → ℝ) 1)) 0 δ m
    refine ⟨C,hC,?_⟩
    intro ε hε p hp
    by_cases hy : ‖p.2‖ ≤ 1
    · exact hb ε ⟨hε.1.le,hε.2.le⟩ p
        ⟨subset_closure hp.1,by simpa only [mem_closedBall,dist_zero_right] using hy⟩
    · have hn : p ∉ tsupport (uncurry (K.family ε)) := by
        have hc : tsupport (uncurry (K.family ε)) ⊆ {p | ‖p.2‖ ≤ 1} := by
          apply closure_minimal _ (isClosed_le continuous_snd.norm continuous_const)
          intro z hz
          by_contra hh
          exact hz (K.vanish (z,ε) (lt_of_not_ge hh))
        exact fun ht => hy (hc ht)
      have hz : iteratedFDeriv ℝ m (uncurry (K.family ε)) p = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => hn
          (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) m ht))
      rw [hz,norm_zero]
      exact hC

end RothschildStein.S
