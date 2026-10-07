-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2Certificate
public import RothschildStein.P1.SingularSplitEstimates

/-!
# The kernels of Data D on the carrier: diagonal convention and measurability

H2's Data D lives on the carrier `C.Carrier` of the lifted chart (the chart domain `U` with the
ambient lifted control metric and Lebesgue measure). The kernels `K₀`, `K₁` of the singular split are
functions on `ℝ^{n+m} × ℝ^{n+m}`; `carrierKernel κ` is `κ` on the carrier with value `0` on the
diagonal. The diagonal value is a free choice for H2 (every size, difference and cancellation
statement is off the diagonal, and the diagonal is a null set); `0` makes the transposed sum kernel
agree with the original on the whole doubled ball, which `H2.TransposeData` requires.

The kernels `K₀`, `K₁` are continuous on the off-diagonal region of `U × U` (the pole `Γ` is smooth
off `0`, `Θ(η, ξ) ≠ 0` off the diagonal, the density correction is positive), hence
`carrierKernel K₀`, `carrierKernel K₁` are Borel measurable on the carrier
(`measurable_carrierKernel_splitK0`, `measurable_carrierKernel_splitK1`), the measurability
hypothesis of the H2 kernel classes (BB Def 7.10, p. 299).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric MeasureTheory
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The kernel `κ(ξ, η)` of the ambient space as a kernel on the carrier of
the lifted chart, with the value `0` on the diagonal (the diagonal is a null set, and every
statement of H2's kernel classes and of Data D is off the diagonal). -/
def carrierKernel (κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) (x y : C.Carrier) : ℝ := by
  classical
  exact if x = y then 0 else κ x.val y.val

variable {C}

/-- Off the diagonal `carrierKernel κ` is `κ` on the underlying points. -/
theorem carrierKernel_of_ne {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    {x y : C.Carrier} (h : x ≠ y) : C.carrierKernel κ x y = κ x.val y.val := by
  unfold carrierKernel
  simp [h]

/-- `carrierKernel κ` vanishes on the diagonal. -/
theorem carrierKernel_self {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} (x : C.Carrier) :
    C.carrierKernel κ x x = 0 := by
  unfold carrierKernel
  simp

variable (C)

/-- The off-diagonal region of `U × U`. -/
def offDiag : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) :=
  {p | p.1 ∈ C.U ∧ p.2 ∈ C.U ∧ p.2 ≠ p.1}

theorem offDiag_subset : C.offDiag ⊆ C.U ×ˢ C.U := fun _ hp => ⟨hp.1, hp.2.1⟩

/-- `(ξ, η) ↦ Θ(η, ξ)` is continuous on `U × U`. -/
theorem continuousOn_theta_swap :
    ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ p.2 p.1) (C.U ×ˢ C.U) :=
  C.theta_smooth.continuousOn.comp continuous_swap.continuousOn (fun _ hp => ⟨hp.2, hp.1⟩)

/-- A kernel family `W^{ξ,η}(u)` smooth off `u = 0`, evaluated at
`u = Θ(η, ξ)` with parameters depending continuously on `(ξ, η)`, is continuous off the
diagonal of `U × U` (`Θ(η, ξ) ≠ 0` there). -/
theorem continuousOn_kernel_at_theta
    {W : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry W) {z | z.2.2 ≠ 0})
    {a b : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)}
    (ha : ContinuousOn a C.offDiag) (hb : ContinuousOn b C.offDiag) :
    ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => W (a p) (b p) (C.Θ p.2 p.1))
      C.offDiag := by
  have hΘ : ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ p.2 p.1)
      C.offDiag := C.continuousOn_theta_swap.mono C.offDiag_subset
  exact hW.continuousOn.comp (ha.prodMk (hb.prodMk hΘ))
    (fun p hp => C.Θ_ne_zero_of_ne hp.1 hp.2.1 hp.2.2)

variable {C}
variable {ν : (Fin (n + m) → ℝ) → ℝ} {φ : ℝ → ℝ}
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
  {Γ : (Fin (n + m) → ℝ) → ℝ}

/-- The cut-off kernel `k^{ξ,ξ}(Θ(η, ξ))`, with parameter evaluated on the diagonal, is continuous off
the diagonal of `U × U`. -/
theorem continuousOn_cutoffKernel_diag (F : SplitFamily C.G D)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hχ : Continuous (fun u => φ (ν u))) :
    ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      cutoffKernel ν D Γ φ p.1 p.1 (C.Θ p.2 p.1)) C.offDiag := by
  have h1 := C.continuousOn_kernel_at_theta (F.contDiffOn_kernelUncurry_diag hΓ)
    (a := fun p => p.1) (b := fun p => p.1) continuousOn_fst continuousOn_fst
  have h2 : ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => φ (ν (C.Θ p.2 p.1)))
      C.offDiag :=
    hχ.comp_continuousOn (C.continuousOn_theta_swap.mono C.offDiag_subset)
  exact h1.mul h2

/-- The cut-off kernel `k^{ξ,η}(Θ(η, ξ))` is continuous off the diagonal of
`U × U`. -/
theorem continuousOn_cutoffKernel (F : SplitFamily C.G D)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hχ : Continuous (fun u => φ (ν u))) :
    ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      cutoffKernel ν D Γ φ p.1 p.2 (C.Θ p.2 p.1)) C.offDiag := by
  have h1 := C.continuousOn_kernel_at_theta (F.contDiffOn_kernelUncurry hΓ)
    (a := fun p => p.1) (b := fun p => p.2) continuousOn_fst continuousOn_snd
  have h2 : ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => φ (ν (C.Θ p.2 p.1)))
      C.offDiag :=
    hχ.comp_continuousOn (C.continuousOn_theta_swap.mono C.offDiag_subset)
  exact h1.mul h2

/-- The denominator `1 + ω₋(ξ, Θ(η, ξ))` in the singular split `K = K₀ + K₁` is continuous on `U × U`
and positive (lifted-chart field `jacobian`). -/
theorem continuousOn_one_add_omega :
    ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      1 + C.ωm p.1 (C.Θ p.2 p.1)) C.offDiag :=
  continuousOn_const.add (C.contDiffOn_omegaMinus_theta.continuousOn.mono C.offDiag_subset)

/-- `K₀` is continuous off the diagonal of `U × U`. -/
theorem continuousOn_splitK0 (F : SplitFamily C.G D)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hχ : Continuous (fun u => φ (ν u))) :
    ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      C.splitK0 ν D Γ φ p.1 p.2) C.offDiag :=
  (continuousOn_cutoffKernel_diag F hΓ hχ).div continuousOn_one_add_omega
    (fun p hp => (C.jacobian p.2 hp.2.1 p.1 hp.1).2.1.ne')

/-- `K₁` is continuous off the diagonal of `U × U`. -/
theorem continuousOn_splitK1 (F : SplitFamily C.G D)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hχ : Continuous (fun u => φ (ν u))) :
    ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      C.splitK1 ν D Γ φ p.1 p.2) C.offDiag := by
  have hd := continuousOn_cutoffKernel_diag (C := C) F hΓ hχ
  have hf := continuousOn_cutoffKernel (C := C) F hΓ hχ
  have hω : ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      C.ωm p.1 (C.Θ p.2 p.1)) C.offDiag :=
    C.contDiffOn_omegaMinus_theta.continuousOn.mono C.offDiag_subset
  exact (((hd.mul hω).div continuousOn_one_add_omega
    (fun p hp => (C.jacobian p.2 hp.2.1 p.1 hp.1).2.1.ne')).add hf).sub hd

/-- A kernel that is continuous off the diagonal of `U × U` is Borel
measurable on the carrier, with the convention `0` on the diagonal. -/
theorem measurable_carrierKernel {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => κ p.1 p.2)
      C.offDiag) :
    Measurable (fun p : C.Carrier × C.Carrier => C.carrierKernel κ p.1 p.2) := by
  classical
  have hopen : IsOpen {p : C.Carrier × C.Carrier | p.1 ≠ p.2} :=
    isOpen_ne_fun continuous_fst continuous_snd
  have hf : ContinuousOn (fun p : C.Carrier × C.Carrier => κ p.1.val p.2.val)
      {p : C.Carrier × C.Carrier | p.1 ≠ p.2} := by
    refine hκ.comp ((Carrier.continuous_val.comp continuous_fst).prodMk
      (Carrier.continuous_val.comp continuous_snd)).continuousOn ?_
    intro p hp
    exact ⟨p.1.val_mem, p.2.val_mem, fun h => hp (Carrier.val_injective h).symm⟩
  have hm := hf.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hopen.measurableSet
  convert hm using 1
  funext p
  by_cases h : p.1 = p.2
  · have hp : p ∉ {p : C.Carrier × C.Carrier | p.1 ≠ p.2} := fun hp => hp h
    rw [Set.piecewise_eq_of_notMem _ _ _ hp]
    show C.carrierKernel κ p.1 p.2 = 0
    rw [h]
    exact carrierKernel_self _
  · have hp : p ∈ {p : C.Carrier × C.Carrier | p.1 ≠ p.2} := h
    rw [Set.piecewise_eq_of_mem _ _ _ hp, carrierKernel_of_ne h]

/-- `K₀` is a Borel measurable kernel on the carrier. -/
theorem measurable_carrierKernel_splitK0 (F : SplitFamily C.G D)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hχ : Continuous (fun u => φ (ν u))) :
    Measurable (fun p : C.Carrier × C.Carrier =>
      C.carrierKernel (C.splitK0 ν D Γ φ) p.1 p.2) :=
  measurable_carrierKernel (continuousOn_splitK0 F hΓ hχ)

/-- `K₁` is a Borel measurable kernel on the carrier. -/
theorem measurable_carrierKernel_splitK1 (F : SplitFamily C.G D)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hχ : Continuous (fun u => φ (ν u))) :
    Measurable (fun p : C.Carrier × C.Carrier =>
      C.carrierKernel (C.splitK1 ν D Γ φ) p.1 p.2) :=
  measurable_carrierKernel (continuousOn_splitK1 F hΓ hχ)

end LiftedChart
end RothschildStein.P1
