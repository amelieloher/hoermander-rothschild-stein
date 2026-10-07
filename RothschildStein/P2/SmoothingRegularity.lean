-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingDescent
public import RothschildStein.P2.NormTransferLp

/-!
# Distributional smoothing, descent: regularity of the descended function

Consequences of the descent identity `g = ḡ ∘ π` a.e. on the cylinder `A × B`
(`RothschildStein.P2.descent_of_lift`):

* `L^p` (BB p. 609, "Hölder/Fubini"): `‖f ∘ π‖_{L^p(A × B)} = |B|^{1/p} ‖f‖_{L^p(A)}`, so the vertical
  average of an `L^p` representative is an `L^p` representative (`memLp_fiberAvg`);
* Hölder: a continuous function on the cylinder that is a.e. a function of the base variable does
  not depend on the vertical variable (`eq_slice_of_continuousOn`), and its vertical average is any
  fixed slice (`fiberAvg_eq_slice`); the continuous weak word derivatives descend to continuous
  weak word derivatives of the slice (`hasWeakWordDeriv_descent_continuous`).

It also records how the restriction of the chart lift to a cylinder satisfies the hypothesis of
`descent_of_lift` (`FiberIntegration.restrict_lift_ofFun`) and the fiber setting of a cylinder
inside a chart (`liftedChart_cylinderFiberSetting`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2
variable {n m : ℕ}

section Lp

variable {A : Opens (Fin n → ℝ)} {B : Opens (Fin m → ℝ)}

/-- The fiber data of the cylinder `A × B` over `A`: all fibers over `A` have volume `|B|`. -/
theorem cylinder_fiberBounds (hB : volume (B : Set (Fin m → ℝ)) < ⊤) :
    FiberBounds (cylinder A B : Set (Fin (n + m) → ℝ)) (A : Set (Fin n → ℝ))
      (A : Set (Fin n → ℝ)) (volume (B : Set (Fin m → ℝ))).toReal
      (volume (B : Set (Fin m → ℝ))).toReal where
  cup_nonneg := ENNReal.toReal_nonneg
  clow_nonneg := ENNReal.toReal_nonneg
  measurableSet_A := (cylinder A B).isOpen.measurableSet
  measurableSet_V := A.isOpen.measurableSet
  measurableSet_W := A.isOpen.measurableSet
  subset := subset_rfl
  proj := fun _ hξ => (mem_cylinder.1 hξ).1
  upper := fun z => by
    by_cases hz : z ∈ (A : Set (Fin n → ℝ))
    · rw [fiberVolume_cylinder_of_mem hz, ENNReal.ofReal_toReal hB.ne]
    · rw [fiberVolume_cylinder_of_notMem hz]
      exact zero_le
  lower := fun z hz => by
    rw [fiberVolume_cylinder_of_mem hz, ENNReal.ofReal_toReal hB.ne]

/-- `‖f ∘ π‖_{L^p(A × B)} = |B|^{1/p} ‖f‖_{L^p(A)}` for `1 ≤ p < ∞` (Tonelli over the fibers). -/
theorem eLpNorm_comp_cylinder {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hB : volume (B : Set (Fin m → ℝ)) < ⊤) {f : (Fin n → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (A : Set (Fin n → ℝ)))) :
    eLpNorm (fun ξ => f (basePoint ξ)) p (volume.restrict (cylinder A B : Set (Fin (n + m) → ℝ))) =
      ENNReal.ofReal ((volume (B : Set (Fin m → ℝ))).toReal ^ (1 / p.toReal)) *
        eLpNorm f p (volume.restrict (A : Set (Fin n → ℝ))) :=
  le_antisymm ((cylinder_fiberBounds hB).eLpNorm_comp_le hp hpt hf)
    ((cylinder_fiberBounds hB).le_eLpNorm_comp hp hpt hf)

/-- `f ∘ π ∈ L^p(A × B)` iff `f ∈ L^p(A)`, for `0 < |B| < ∞`, `1 ≤ p < ∞`. -/
theorem memLp_comp_cylinder_iff {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hB0 : 0 < volume (B : Set (Fin m → ℝ))) (hB : volume (B : Set (Fin m → ℝ)) < ⊤)
    {f : (Fin n → ℝ) → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (A : Set (Fin n → ℝ)))) :
    MemLp (fun ξ => f (basePoint ξ)) p (volume.restrict (cylinder A B : Set (Fin (n + m) → ℝ))) ↔
      MemLp f p (volume.restrict (A : Set (Fin n → ℝ))) := by
  have hc0 : ENNReal.ofReal ((volume (B : Set (Fin m → ℝ))).toReal ^ (1 / p.toReal)) ≠ 0 := by
    have : 0 < (volume (B : Set (Fin m → ℝ))).toReal := ENNReal.toReal_pos hB0.ne' hB.ne
    simpa using Real.rpow_pos_of_pos this _
  rw [memLp_iff, memLp_iff, eLpNorm_comp_cylinder hp hpt hB hf]
  constructor
  · intro h
    by_contra hnot
    rw [not_lt, top_le_iff] at hnot
    rw [hnot, ENNReal.mul_top hc0] at h
    exact lt_irrefl _ h
  · intro h
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

/-- `L^p` membership descends: if `g ∈ L^p(A × B)` is a.e. the lift of its vertical
average `ḡ`, then `ḡ ∈ L^p(A)` (BB p. 609, "averaging its `L^p` representative against `η`"). -/
theorem memLp_fiberAvg {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hB0 : 0 < volume (B : Set (Fin m → ℝ))) (hB : volume (B : Set (Fin m → ℝ)) < ⊤)
    {η : TestFunction B ℝ (⊤ : ℕ∞)} {g : (Fin (n + m) → ℝ) → ℝ}
    (hgloc : LocallyIntegrableOn g (cylinder A B : Set (Fin (n + m) → ℝ)) volume)
    (hgae : g =ᵐ[volume.restrict (cylinder A B : Set (Fin (n + m) → ℝ))]
      fun ξ => fiberAvg g η (basePoint ξ))
    (hg : MemLp g p (volume.restrict (cylinder A B : Set (Fin (n + m) → ℝ)))) :
    MemLp (fiberAvg g η) p (volume.restrict (A : Set (Fin n → ℝ))) := by
  have hmeas : AEStronglyMeasurable (fiberAvg g η) (volume.restrict (A : Set (Fin n → ℝ))) :=
    (locallyIntegrableOn_fiberAvg hgloc η).aestronglyMeasurable
  exact (memLp_comp_cylinder_iff hp hpt hB0 hB hmeas).1 (hg.ae_eq hgae)

end Lp

section Continuity

variable {A : Opens (Fin n → ℝ)} {B : Opens (Fin m → ℝ)}

/-- A continuous function on the cylinder that is a.e. a function of the base variable does not
depend on the vertical variable: `g(x, t) = g(x, t')` for all `(x, t), (x, t')` in `A × B`.
(`g` is continuous in `t` and a.e. equal to `ḡ(x)`, hence equal to `ḡ(x)` on each good fiber; then
continuity in `x` extends the identity from the dense set of good `x`.) -/
theorem eq_slice_of_continuousOn {g : (Fin (n + m) → ℝ) → ℝ} {gbar : (Fin n → ℝ) → ℝ}
    (hg : ContinuousOn g (cylinder A B : Set (Fin (n + m) → ℝ)))
    (hae : g =ᵐ[volume.restrict (cylinder A B : Set (Fin (n + m) → ℝ))]
      fun ξ => gbar (basePoint ξ)) :
    ∀ x ∈ (A : Set (Fin n → ℝ)), ∀ t ∈ (B : Set (Fin m → ℝ)), ∀ t' ∈ (B : Set (Fin m → ℝ)),
      g (joinPoint x t) = g (joinPoint x t') := by
  have h1 := (ae_restrict_iff' (cylinder A B).isOpen.measurableSet).1 hae
  have h2 := (measurePreserving_joinEquiv (n := n) (m := m)).quasiMeasurePreserving.ae h1
  rw [Measure.volume_eq_prod] at h2
  have h3 := Measure.ae_ae_of_ae_prod h2
  simp only [joinEquiv_apply, basePoint_joinPoint] at h3
  -- for almost every `x ∈ A`, `g(x, ·) = ḡ(x)` on `B`
  have hslice : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), x ∈ (A : Set (Fin n → ℝ)) →
      ∀ t ∈ (B : Set (Fin m → ℝ)), g (joinPoint x t) = gbar x := by
    filter_upwards [h3] with x hx hxA
    have hB : (fun t : Fin m → ℝ => g (joinPoint x t)) =ᵐ[volume.restrict (B : Set (Fin m → ℝ))]
        fun _ => gbar x := by
      rw [Filter.EventuallyEq, ae_restrict_iff' B.isOpen.measurableSet]
      filter_upwards [hx] with t ht htB
      exact ht (joinPoint_mem_cylinder.2 ⟨hxA, htB⟩)
    have hcont : ContinuousOn (fun t : Fin m → ℝ => g (joinPoint x t)) (B : Set (Fin m → ℝ)) :=
      hg.comp (continuous_joinPoint_right x).continuousOn fun t ht =>
        joinPoint_mem_cylinder.2 ⟨hxA, ht⟩
    exact fun t ht => Measure.eqOn_open_of_ae_eq hB B.isOpen hcont continuousOn_const ht
  intro x hx t ht t' ht'
  have hcont : ∀ s ∈ (B : Set (Fin m → ℝ)),
      ContinuousOn (fun y : Fin n → ℝ => g (joinPoint y s)) (A : Set (Fin n → ℝ)) := fun s hs =>
    hg.comp (continuous_joinPoint_left s).continuousOn fun y hy => joinPoint_mem_cylinder.2 ⟨hy, hs⟩
  have hxae : (fun y : Fin n → ℝ => g (joinPoint y t)) =ᵐ[volume.restrict (A : Set (Fin n → ℝ))]
      fun y => g (joinPoint y t') := by
    rw [Filter.EventuallyEq, ae_restrict_iff' A.isOpen.measurableSet]
    filter_upwards [hslice] with y hy hyA
    rw [hy hyA t ht, hy hyA t' ht']
  exact Measure.eqOn_open_of_ae_eq hxae A.isOpen (hcont t ht) (hcont t' ht') hx

/-- For continuous `w` on the cylinder with `w = ū ∘ π` a.e., the vertical average is the value of
any fixed slice: `ū(x) = w(x, t₀)` for every `x ∈ A`, `t₀ ∈ B` (when `∫ η = 1`). -/
theorem fiberAvg_eq_slice {w : (Fin (n + m) → ℝ) → ℝ} {η : TestFunction B ℝ (⊤ : ℕ∞)}
    (hw : ContinuousOn w (cylinder A B : Set (Fin (n + m) → ℝ)))
    (hae : w =ᵐ[volume.restrict (cylinder A B : Set (Fin (n + m) → ℝ))]
      fun ξ => fiberAvg w η (basePoint ξ))
    (hη : ∫ t : Fin m → ℝ, η t = 1)
    {x : Fin n → ℝ} (hx : x ∈ (A : Set (Fin n → ℝ))) {t₀ : Fin m → ℝ}
    (ht₀ : t₀ ∈ (B : Set (Fin m → ℝ))) :
    fiberAvg w η x = w (joinPoint x t₀) := by
  have hconst := eq_slice_of_continuousOn hw hae
  unfold fiberAvg
  have : ∀ t : Fin m → ℝ, w (joinPoint x t) * η t = w (joinPoint x t₀) * η t := by
    intro t
    by_cases ht : t ∈ (B : Set (Fin m → ℝ))
    · rw [hconst x hx t ht t₀ ht₀]
    · have : η t = 0 := η.zero_on_compl ht
      rw [this, mul_zero, mul_zero]
  simp_rw [this]
  rw [integral_const_mul, hη, mul_one]

end Continuity

end RothschildStein.P2
