-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.LocalPatchEquation
public import RothschildStein.Distribution.PulledCutoff
public import RothschildStein.Distribution.PatchedDistributionRegularity
public import RothschildStein.Distribution.LocalizedRepresentativePairing
public import Hormander.F.Assembly.Cutoffs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter Metric SchwartzMap
open scoped Topology
namespace RothschildStein.Distribution

/-- an existing Hörmander frame patch produces
an actual local smooth representative of a real-test distribution.
The equation, scalar extension, forcing and negative Sobolev start
are transferred and proved inside this construction. -/
theorem exists_local_distribution_representative_on_framePatch {k N : ℕ} (hN : 0 < N)
    (Ω : Opens (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (Ω : Set (Fin N → ℝ)))
    (T : Distribution Ω ℂ (⊤ : ℕ∞)) (g : (Fin N → ℝ) → ℂ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin N → ℝ)))
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T (adjointTest Ω X c hX hc ψ) =
      Distribution.ofFun Ω g volume (⊤ : ℕ∞) ψ)
    (x₀ : Fin N → ℝ)
    (P : Hormander.F.LocalPatch hN (Hormander.F.coordinateEquiv N '' (Ω : Set (Fin N → ℝ)))
      (Hormander.F.pushVectorFields X) (fun y => c ((Hormander.F.coordinateEquiv N).symm y))
      (Hormander.F.coordinateEquiv N x₀)) :
    ∃ W : Set (Fin N → ℝ), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ Ω ∧
      ∃ F : (Fin N → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), tsupport ψ ⊆ W → T ψ = ∫ x, ψ x • F x := by
  let e := Hormander.F.coordinateEquiv N
  let B : Opens (Fin N → ℝ) := ⟨e ⁻¹' ball (e x₀) P.radius, isOpen_ball.preimage e.continuous⟩
  have hBΩ : B ≤ Ω := pulledPatch_ball_subset hN (Ω : Set (Fin N → ℝ)) X c x₀ P
  have hBimage : e '' (B : Set (Fin N → ℝ)) = ball (e x₀) P.radius := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e (e.symm y) ∈ ball (e x₀) P.radius
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy
  let Y := fun i x => e.symm (P.extendedX i (e x))
  let d := fun x => P.extendedC (e x)
  have hY : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i) :=
    fun i => contDiff_pulledVectorField (P.extendedX i) (P.extendedX_smooth i)
  have hd : ContDiff ℝ (⊤ : ℕ∞) d := P.extendedC_smooth.comp e.contDiff
  have hpush : Hormander.F.pushVectorFields Y = P.extendedX := push_pulledVectorFields P.extendedX
  have hmult : (fun y => d (e.symm y)) = P.extendedC := by
    funext y
    simp only [d, ContinuousLinearEquiv.apply_symm_apply]
  have hYE : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Hormander.F.pushVectorFields Y i) := by
    rw [hpush]
    exact P.extendedX_smooth
  have hYEc : ∀ i, HasCompactSupport (Hormander.F.pushVectorFields Y i) := by
    rw [hpush]
    exact P.extendedX_compact
  have hdE : ContDiff ℝ (⊤ : ℕ∞) (fun y => d (e.symm y)) := by rw [hmult]; exact P.extendedC_smooth
  have hdEc : HasCompactSupport (fun y => d (e.symm y)) := by rw [hmult]; exact P.extendedC_compact
  let TB := restrictComplexDistribution Ω B T
  have hEq : ∀ ψ : TestFunction B ℝ (⊤ : ℕ∞), TB (adjointTest B Y d
      (fun i => (hY i).contDiffOn) hd.contDiffOn ψ) = Distribution.ofFun B g volume (⊤ : ℕ∞) ψ :=
    localPatch_distributionEquation hN Ω X c hX hc x₀ P B rfl T g hg heq
  obtain ⟨ζ, η, χ, hζ, hη, hχ, hcζ, hcη, hcχ, hζ1, hζη, hχη, hηB, hχB⟩ :=
    Hormander.F.exists_nested_cutoffs (e x₀) P.radius_pos
  have hηImage : tsupport η ⊆ e '' (B : Set (Fin N → ℝ)) := by rw [hBimage]; exact hηB
  have hχImage : tsupport χ ⊆ e '' (B : Set (Fin N → ℝ)) := by rw [hBimage]; exact hχB
  let ηB := pullEuclideanCutoff B η hη hcη hηImage
  let χB := pullEuclideanCutoff B χ hχ hcχ hχImage
  have hχone : ∀ x ∈ tsupport ηB, χB x = 1 := by
    intro x hx
    rw [tsupport_pullEuclideanCutoff] at hx
    exact hχη.self_of_nhdsSet (e x) hx
  have hηpull : (fun y : Hormander.A.Carrier N => ηB (e.symm y)) = η := by
    funext y
    change η (e (e.symm y)) = η y
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hζη' : ∀ᶠ y in 𝓝ˢ (tsupport ζ), ηB (e.symm y) = 1 := by
    filter_upwards [hζη] with y hy
    change η (e (e.symm y)) = 1
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy
  have hηK : tsupport (fun y : Hormander.A.Carrier N => ηB (e.symm y)) ⊆ tsupport η := by
    rw [hηpull]
  have hw : ∀ y ∈ ball (e x₀) P.radius, LinearIndependent ℝ
      (fun a => Hormander.lieWordEval (Hormander.F.pushVectorFields Y) (P.words a) y) := by
    rw [hpush]
    exact P.frame_on_ball
  obtain ⟨F, hF, hrep⟩ := patchedDistribution_smooth_of_equation B Y d (fun i => (hY i).contDiffOn)
    hd.contDiffOn hYE hYEc hdE hdEc χB ηB hχone hcη isOpen_ball hηB P.words hw ζ hζ hζη' hηK TB g
    (hg.mono hBΩ) hEq
  let W := e ⁻¹' ball (e x₀) (P.radius / 8)
  have hWB : W ⊆ B := by
    intro x hx
    exact ball_subset_ball (by linarith [P.radius_pos]) hx
  have hζW : ∀ x ∈ W, ζ (e x) = 1 := fun x hx => hζ1 (e x) hx
  have hχW : ∀ x ∈ W, χB x = 1 := by
    intro x hx
    have hz : e x ∈ tsupport ζ := (subset_tsupport ζ) (by rw [Function.mem_support, hζW x hx]; exact one_ne_zero)
    have he1 := hζη.self_of_nhdsSet (e x) hz
    have heη : e x ∈ tsupport η := (subset_tsupport η) (by rw [Function.mem_support, he1]; exact one_ne_zero)
    exact hχη.self_of_nhdsSet (e x) heη
  have hζg : (fun y => (ζ y : ℂ)).HasTemperateGrowth := by
    convert (SchwartzMap.postcompCLM Complex.ofRealCLM (hcζ.toSchwartzMap hζ)).hasTemperateGrowth using 1
    funext y
    rfl
  refine ⟨W, isOpen_ball.preimage e.continuous, ?_, hWB.trans hBΩ,
    fun x => F (e x), hF.comp e.contDiff, fun ψ hψ => ?_⟩
  · change e x₀ ∈ ball (e x₀) (P.radius / 8)
    exact mem_ball_self (div_pos P.radius_pos (by norm_num))
  · let ψB : TestFunction B ℝ (⊤ : ℕ∞) :=
      ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψ.trans hWB⟩
    have hpair := localizedRepresentative_on_realTest B χB ψB TB ζ hζg
      (fun x hx => hχW x (hψ hx)) (fun x hx => hζW x (hψ hx)) F (fun φ => (hrep φ).2)
    have htest : TB ψB = T ψ := by
      rw [restrictComplexDistribution_apply Ω B hBΩ T]
      congr 1
    rw [htest] at hpair
    exact hpair

end RothschildStein.Distribution
