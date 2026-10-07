-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityPositiveOperator
public import RothschildStein.P1.RestrictedErrorEstimates
public import RothschildStein.P1.TypeKernel
public import RothschildStein.H3.HomogeneousOperators
public import RothschildStein.H1.KernelData

/-!
# Positive homogeneous terms: `L^p` by Schur and `L^∞ → C^α`

A principal term `a(ξ) b(η) (D^{ξ,η} Γ_ε)(Θ(η, ξ))` of a positive-type decomposition into principal terms has `D` of
integer degree at most `2 - λ ≤ 1`, so its kernel is homogeneous of degree `ℓ - Q` with `ℓ = 2 - deg D ≥ 1`
in the group variable (`β = 1`, `ν = ℓ ≥ 1` in the language of BB Def 7.10). On a lifted chart frame
(`LiftedChart.IsLiftedFrame`: the frame's model group and two-point map are the chart's, the cutoff
region `V` has closure in the chart domain `U`, and the poles `Γ, Γ*` are smooth off `0` and
homogeneous of degree `2 - Q`, the H1 properties of the fundamental kernels) its kernel is a
`PatchKernel`: the kernel estimates give the size and difference bounds, multiplied by the `C¹` cutoffs
(`HasKernelBounds.mul`), and the dyadic-shell/Schur machinery of the Schur bound and of the restricted-error estimates gives the bounds
(`ContinuityPositiveOperator`).

The Schur bound gives `L^p`; the kernel estimates, together with the fractional-integral theorem of
H2, give `L^∞ → C^α`, since `β = 1` and `ν = ℓ ≥ 1` (BB pp. 299–301, Prop. 7.11; p. 305, Thm. 7.14;
p. 306, Rem. 7.16). The `L^∞ → C^α` bound follows directly from the first-variable difference
estimate and a dyadic decomposition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The hypotheses of a kernel frame `F` on a lifted chart `C` used by the continuity
theorem: the frame's model group and two-point map are the chart's (`G`, `Θ`), the cutoff region `V`
is relatively compact in the chart domain (`V ⋐ U`), and the poles
`Γ, Γ*` are smooth off `0` and homogeneous of degree `2 - Q` for the model dilations (the H1
fundamental kernel fields `smooth_off_zero`, `homogeneous`; see `IsLiftedFrame.of_fundamentalKernels`).
The gauge of the frame (used only at type 0) is unconstrained. -/
structure IsLiftedFrame (F : KernelFrame (n + m)) : Prop where
  G_eq : F.G = C.G
  Θ_eq : F.Θ = C.Θ
  closure_subset : closure (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U
  Γ_smooth : ContDiffOn ℝ (⊤ : ℕ∞) F.Γ {(0 : Fin (n + m) → ℝ)}ᶜ
  Γ_homogeneous : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
    F.Γ (C.G.dilate t x) = t ^ (2 - (C.G.homogeneousDimension : ℝ)) * F.Γ x
  Γs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) F.Γs {(0 : Fin (n + m) → ℝ)}ᶜ
  Γs_homogeneous : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
    F.Γs (C.G.dilate t x) = t ^ (2 - (C.G.homogeneousDimension : ℝ)) * F.Γs x

variable {C}

/-- The frame hypotheses follow from the H1 fundamental kernels `Γ` and `Γ*` of the chart's
model group (`FundamentalKernel.smooth_off_zero`, `FundamentalKernel.homogeneous`; the standing
hypotheses of `Γ*` are those of the reversed drift). -/
theorem IsLiftedFrame.of_fundamentalKernels {F : KernelFrame (n + m)} {q q' : ℕ}
    {H : H1.StandingHypotheses C.G q} {H' : H1.StandingHypotheses C.G q'}
    (Γ : H1.FundamentalKernel C.G H) (Γs : H1.FundamentalKernel C.G H')
    (hG : F.G = C.G) (hΘ : F.Θ = C.Θ) (hV : closure (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hΓ : F.Γ = ⇑Γ) (hΓs : F.Γs = ⇑Γs) : C.IsLiftedFrame F :=
  ⟨hG, hΘ, hV, by rw [hΓ]; exact Γ.smooth_off_zero,
    fun t ht x hx => by rw [hΓ]; exact Γ.homogeneous t ht x hx,
    by rw [hΓs]; exact Γs.smooth_off_zero,
    fun t ht x hx => by rw [hΓs]; exact Γs.homogeneous t ht x hx⟩

variable {F : KernelFrame (n + m)} (hF : C.IsLiftedFrame F)
include hF

/-- The pole `Γ` or `Γ*` selected by a principal term is smooth off `0`. -/
theorem IsLiftedFrame.pole_smooth (star : Bool) :
    ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ := by
  cases star
  · exact hF.Γ_smooth
  · exact hF.Γs_smooth

/-- The pole `Γ` or `Γ*` selected by a principal term is homogeneous of degree `2 - Q`. -/
theorem IsLiftedFrame.pole_homogeneous (star : Bool) :
    ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F.pole star (C.G.dilate t x) = t ^ (2 - (C.G.homogeneousDimension : ℝ)) * F.pole star x := by
  cases star
  · exact hF.Γ_homogeneous
  · exact hF.Γs_homogeneous

/-- The closure of the cutoff region is compact (a closed subset of the compact
`closure U`). -/
theorem IsLiftedFrame.isCompact_closure : IsCompact (closure (F.V : Set (Fin (n + m) → ℝ))) :=
  IsCompact.of_isClosed_subset C.isCompact_closure_U isClosed_closure
    (closure_mono (subset_closure.trans hF.closure_subset))

end LiftedChart

namespace PrincipalTerm

variable {N : ℕ} {F : KernelFrame N} (t : PrincipalTerm F)

/-- The operator applied to a function is the sum over the common multi-indices. -/
theorem apply_eq_sum (Γ : (Fin N → ℝ) → ℝ) (ξ η u : Fin N → ℝ) :
    (t.D ξ η).apply Γ u =
      ∑ a ∈ t.indices, (t.D ξ η).coefficient a u * euclideanPartial a Γ u := by
  unfold SmoothDifferentialOperator.apply
  rw [t.indices_eq]

/-- Coordinate partial derivatives of a function smooth off `0` are smooth off `0`. -/
theorem contDiffOn_euclideanPartial_off_zero {Γ : (Fin N → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin N → ℝ)}ᶜ) (a : Fin N → ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (euclideanPartial a Γ) {(0 : Fin N → ℝ)}ᶜ := by
  apply contDiffOn_infty.mpr
  intro k
  exact H1.contDiffOn_euclideanPartial_finite ⟨{0}ᶜ, isOpen_compl_singleton⟩ a k Γ
    (hΓ.of_le (by simp))

/-- The kernel family `(ξ, η, u) ↦ (D^{ξ,η} Γ)(u)` of a principal term is jointly smooth off
`u = 0` (jointly smooth coefficients, smooth derivatives of `Γ`). -/
theorem contDiffOn_family {Γ : (Fin N → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin N → ℝ)}ᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry (fun ξ η u => (t.D ξ η).apply Γ u))
      {z | z.2.2 ≠ 0} := by
  have hfun : kernelUncurry (fun ξ η u => (t.D ξ η).apply Γ u) = fun z =>
      ∑ a ∈ t.indices, (t.D z.1 z.2.1).coefficient a z.2.2 * euclideanPartial a Γ z.2.2 := by
    funext z
    exact t.apply_eq_sum Γ z.1 z.2.1 z.2.2
  rw [hfun]
  refine ContDiffOn.sum (fun a ha => ?_)
  exact (t.coefficient_smooth a ha).contDiffOn.mul
    ((contDiffOn_euclideanPartial_off_zero hΓ a).comp contDiff_snd.snd.contDiffOn
      (fun z hz => hz))

/-- The kernel of a principal term vanishes off `V × V`. -/
theorem kernel_eq_zero_of_not_mem {ξ η : Fin N → ℝ}
    (h : ξ ∉ (F.V : Set (Fin N → ℝ)) ∨ η ∉ (F.V : Set (Fin N → ℝ))) : t.kernel ξ η = 0 := by
  unfold PrincipalTerm.kernel
  rcases h with h | h
  · rw [t.a.zero_on_compl h]
    simp
  · rw [t.b.zero_on_compl h]
    simp

end PrincipalTerm

namespace PrincipalTerm

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)} (hF : C.IsLiftedFrame F)
include hF

/-- **Kernel estimates for a principal term**: on a compact `L ⊆ U`, the
kernel `a(ξ) b(η) (D^{ξ,η} Γ_ε)(Θ(η, ξ))` of a principal term with `deg D ≤ 1` (so `λ ≥ 1`, kernel
homogeneous of degree `ℓ - Q` with `ℓ = 2 - deg D ≥ 1`) has the kernel bounds of exponent one:
size `A d̃^(1-Q)` and difference `B d̃(ξ, ξ') / d̃(ξ', η)^Q` for `d̃(ξ', η) > 2 d̃(ξ, ξ')`. -/
theorem hasKernelBounds (t : PrincipalTerm F) (hdeg : t.degree ≤ 1)
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L) (hLU : L ⊆ C.U) :
    C.HasKernelBounds L 1 t.kernel := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, (ℓ : ℤ) = 2 - t.degree :=
    ⟨(2 - t.degree).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hℓ1 : 1 ≤ ℓ := by omega
  have hD : ∀ ξ η, (t.D ξ η).IsHomogeneous C.G t.degree := by
    intro ξ η
    have := t.homogeneous ξ η
    rwa [hF.G_eq] at this
  have hΓ := hF.pole_smooth t.star
  have hΓh := hF.pole_homogeneous t.star
  have hW1 : ContDiffOn ℝ 1
      (kernelUncurry (fun ξ η u => (t.D ξ η).apply (F.pole t.star) u)) {z | z.2.2 ≠ 0} :=
    (t.contDiffOn_family hΓ).of_le (by simp)
  have hhom : ∀ ξ η : Fin (n + m) → ℝ, ∀ s : ℝ, 0 < s → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      (t.D ξ η).apply (F.pole t.star) (C.G.dilate s u) =
        s ^ ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ)) *
          (t.D ξ η).apply (F.pole t.star) u := by
    intro ξ η s hs u hu
    have h := (H3.homogeneousOperator_kernel (t.D ξ η) (hD ξ η) hΓ hΓh).2 s hs u hu
    have e : (2 - (C.G.homogeneousDimension : ℝ)) - (t.degree : ℝ) =
        (((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ) : ℤ) : ℝ) := by
      have : (ℓ : ℝ) = 2 - (t.degree : ℝ) := by exact_mod_cast hℓ
      push_cast
      linarith
    rw [h, e, Real.rpow_intCast]
  obtain ⟨A, B, hA, hB, h1, h2⟩ := C.exists_kernel_estimates (ℓ := ℓ) hW1 hhom hL hLU
  have hκ : C.HasKernelBounds L ℓ
      (fun ξ η => (t.D ξ η).apply (F.pole t.star) (C.Θ η ξ)) := ⟨A, B, hA, hB, h1, h2⟩
  have hg : ContDiffOn ℝ 1 (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => t.a p.1 * t.b p.2)
      (C.U ×ˢ C.U) :=
    (((t.a.contDiff.of_le (by simp)).comp contDiff_fst).mul
      ((t.b.contDiff.of_le (by simp)).comp contDiff_snd)).contDiffOn
  obtain ⟨Gs, hGs0, hGs⟩ := C.exists_bound_prod hg hL hLU
  obtain ⟨M, hM0, hM₁, hM₂⟩ := C.exists_lipschitz hg hL hLU
  have h3 : C.HasKernelBounds L ℓ
      (fun ξ η => t.a ξ * t.b η * (t.D ξ η).apply (F.pole t.star) (C.Θ η ξ)) :=
    LiftedChart.HasKernelBounds.mul (e := 0) hL hLU (Nat.zero_le 1) hκ hGs0 hM0
      (fun ξ hξ η hη _ => by simpa using hGs ξ hξ η hη) hM₁ hM₂
  have h4 : C.HasKernelBounds L ℓ t.kernel := h3.congr (fun ξ _ η _ => by
    simp only [PrincipalTerm.kernel, hF.Θ_eq])
  exact h4.of_le_exponent hL hLU hℓ1

/-- The kernel of a principal term is continuous on `S × S` off the
diagonal, for `S ⊆ U` (hence its cut to `S × S` is measurable). -/
theorem continuousOn_kernel (t : PrincipalTerm F) {S : Set (Fin (n + m) → ℝ)}
    (hSU : S ⊆ C.U) :
    ContinuousOn (Function.uncurry t.kernel) ((S ×ˢ S) \ Set.diagonal (Fin (n + m) → ℝ)) := by
  have hΓ := hF.pole_smooth t.star
  have hW : ContinuousOn
      (kernelUncurry (fun ξ η u => (t.D ξ η).apply (F.pole t.star) u)) {z | z.2.2 ≠ 0} :=
    (t.contDiffOn_family hΓ).continuousOn
  have h1 := C.continuousOn_kernelValue hSU (χ := fun _ => (1 : ℝ)) continuous_const hW
  have h2 : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => t.a z.1 * t.b z.2)
      ((S ×ˢ S) \ Set.diagonal (Fin (n + m) → ℝ)) :=
    ((t.a.continuous.comp continuous_fst).mul (t.b.continuous.comp continuous_snd)).continuousOn
  refine (h2.mul h1).congr (fun z _ => ?_)
  simp [Function.uncurry, PrincipalTerm.kernel, LiftedChart.kernelValue, hF.Θ_eq]

/-- **The kernel of a positive principal term is a patch kernel**
(on `S = cl V`, `V ⋐ U`). -/
theorem patchKernel (t : PrincipalTerm F) (hdeg : t.degree ≤ 1) :
    C.PatchKernel (closure (F.V : Set (Fin (n + m) → ℝ))) (F.V : Set (Fin (n + m) → ℝ))
      t.kernel :=
  ⟨hF.isCompact_closure, hF.closure_subset, subset_closure, F.V.isOpen.measurableSet,
    hasKernelBounds hF t hdeg hF.isCompact_closure hF.closure_subset,
    measurable_sliceKernel_of_continuousOn hF.isCompact_closure.measurableSet
      (continuousOn_kernel hF t hF.closure_subset),
    fun _ _ _ hout => t.kernel_eq_zero_of_not_mem hout⟩

end PrincipalTerm

end RothschildStein.P1
