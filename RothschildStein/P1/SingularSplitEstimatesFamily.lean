-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SingularSplitEstimatesFactors
public import RothschildStein.P1.SingularSplitTranspose
public import RothschildStein.H3.HomogeneousOperators

/-!
# The operator family `D^{ξ,η}` as a homogeneous kernel family

A *split family* packages the hypotheses of the singular split on the parameter family `D^{ξ,η}`
of degree-2 homogeneous differential operators (BB Prop 11.33, p. 572; as in `PrincipalTerm`):
common multi-indices, coefficients jointly smooth in `(ξ, η, u)`, and every `D^{ξ,η}` homogeneous
of degree 2. For a pole `Γ` that is smooth off `0` and homogeneous of degree `2 - Q`, the kernel
family `W^{ξ,η}(u) = (D^{ξ,η} Γ)(u)` is then jointly smooth off `u = 0` and homogeneous of degree
`-Q` (`ℓ = 0`), so the kernel estimates give its size and difference bounds.

The transposed family `refl(D^{η,ξ})` of `transposeFamily` is again a split family
(`SplitFamily.transpose`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1

/-- The hypotheses of the singular split on the family `D^{ξ,η}` (BB p. 572, Prop 11.33;
as in `PrincipalTerm`): fixed multi-indices, coefficients jointly smooth in `(ξ, η, u)`, and every
`D^{ξ,η}` homogeneous of degree 2. -/
structure SplitFamily {N : ℕ} (G : HomogeneousGroup N)
    (D : (Fin N → ℝ) → (Fin N → ℝ) → SmoothDifferentialOperator N) where
  /-- The common multi-indices of the family. -/
  indices : Finset (Fin N → ℕ)
  indices_eq : ∀ ξ η, (D ξ η).indices = indices
  coefficient_smooth : ∀ α ∈ indices, ContDiff ℝ (⊤ : ℕ∞)
    (fun z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) => (D z.1 z.2.1).coefficient α z.2.2)
  homogeneous : ∀ ξ η, (D ξ η).IsHomogeneous G 2

namespace SplitFamily

variable {N : ℕ} {G : HomogeneousGroup N}
  {D : (Fin N → ℝ) → (Fin N → ℝ) → SmoothDifferentialOperator N} (F : SplitFamily G D)

/-- The transposed family (exchange the parameters and reflect, `transposeFamily`) is again
a split family (BB p. 576, Prop 11.33(d): "exchange parameters and reflect `D`"). -/
def transpose : SplitFamily G (transposeFamily D) where
  indices := F.indices
  indices_eq := transposeFamily_indices_eq F.indices_eq
  coefficient_smooth α hα := transposeFamily_coefficient_smooth α (F.coefficient_smooth α hα)
  homogeneous ξ η := transposeFamily_isHomogeneous (fun ξ η => F.homogeneous ξ η) ξ η

/-- The operator applied to `Γ` is the sum over the common multi-indices. -/
theorem apply_eq_sum (Γ : (Fin N → ℝ) → ℝ) (ξ η u : Fin N → ℝ) :
    (D ξ η).apply Γ u = ∑ a ∈ F.indices, (D ξ η).coefficient a u * euclideanPartial a Γ u := by
  unfold SmoothDifferentialOperator.apply
  rw [F.indices_eq]

variable {Γ : (Fin N → ℝ) → ℝ}

/-- Coordinate partial derivatives of a function smooth off `0` are smooth off `0`. -/
theorem contDiffOn_euclideanPartial (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin N → ℝ)}ᶜ)
    (a : Fin N → ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (euclideanPartial a Γ) {(0 : Fin N → ℝ)}ᶜ := by
  apply contDiffOn_infty.mpr
  intro k
  exact H1.contDiffOn_euclideanPartial_finite ⟨{0}ᶜ, isOpen_compl_singleton⟩ a k Γ
    (hΓ.of_le (by simp))

include F in
/-- The kernel family `(ξ, η, u) ↦ (D^{ξ,η} Γ)(u)` is jointly smooth off `u = 0`. -/
theorem contDiffOn_kernelUncurry (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin N → ℝ)}ᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry (fun ξ η u => (D ξ η).apply Γ u))
      {z | z.2.2 ≠ 0} := by
  have hfun : kernelUncurry (fun ξ η u => (D ξ η).apply Γ u) = fun z =>
      ∑ a ∈ F.indices, (D z.1 z.2.1).coefficient a z.2.2 * euclideanPartial a Γ z.2.2 := by
    funext z
    exact F.apply_eq_sum Γ z.1 z.2.1 z.2.2
  rw [hfun]
  refine ContDiffOn.sum (fun a ha => ?_)
  exact (F.coefficient_smooth a ha).contDiffOn.mul
    ((contDiffOn_euclideanPartial hΓ a).comp contDiff_snd.snd.contDiffOn (fun z hz => hz))

include F in
/-- The kernel family `(ξ, η, u) ↦ (D^{ξ,ξ} Γ)(u)`, with parameter evaluated on the diagonal, is
jointly smooth off `u = 0`. -/
theorem contDiffOn_kernelUncurry_diag (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin N → ℝ)}ᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry (fun ξ _ u => (D ξ ξ).apply Γ u))
      {z | z.2.2 ≠ 0} := by
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) => (z.1, z.1, z.2.2))
      {z | z.2.2 ≠ 0} :=
    (contDiff_fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd)).contDiffOn
  exact (F.contDiffOn_kernelUncurry hΓ).comp hmap (fun z hz => hz)

include F in
/-- Homogeneity of the kernel family: for `Γ` smooth off `0` and homogeneous of degree
`2 - Q`, the operator `D^{ξ,η}` of degree 2 gives `(D^{ξ,η} Γ)(δ_t u) = t^(-Q) (D^{ξ,η} Γ)(u)` off
`u = 0` (`ℓ = 0` in the kernel estimates; H3 `homogeneousOperator_kernel`, BB Prop 3.23, p. 107). -/
theorem apply_dilate (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin N → ℝ)}ᶜ)
    (hΓh : ∀ t : ℝ, 0 < t → ∀ x : Fin N → ℝ, x ≠ 0 →
      Γ (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x)
    (ξ η : Fin N → ℝ) {t : ℝ} (ht : 0 < t) {u : Fin N → ℝ} (hu : u ≠ 0) :
    (D ξ η).apply Γ (G.dilate t u) =
      t ^ (((0 : ℕ) : ℤ) - (G.homogeneousDimension : ℤ)) * (D ξ η).apply Γ u := by
  have h := (H3.homogeneousOperator_kernel (D ξ η) (F.homogeneous ξ η) hΓ hΓh).2 t ht u hu
  rw [h]
  congr 1
  rw [← Real.rpow_intCast]
  congr 1
  push_cast
  ring

end SplitFamily

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}
variable {L : Set (Fin (n + m) → ℝ)}

/-- The kernel estimates with `ℓ = 0`, in the form `HasKernelBounds`: a family `W^{ξ,η}(u)` jointly `C¹`
off `u = 0` and homogeneous of degree `-Q`, cut off by a `C¹` radial profile `χ`, has a kernel
`χ(Θ(η, ξ)) W^{ξ,η}(Θ(η, ξ))` of singular exponent 1 (BB pp. 569–571, Prop 11.32). -/
theorem hasKernelBounds_kernelValue_zero
    {χ : (Fin (n + m) → ℝ) → ℝ} {W : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) →
      (Fin (n + m) → ℝ) → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hW : ContDiffOn ℝ 1 (kernelUncurry W) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η : Fin (n + m) → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      W ξ η (C.G.dilate t u) =
        t ^ (((0 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ)) * W ξ η u)
    (hL : IsCompact L) (hLU : L ⊆ C.U) : C.HasKernelBounds L 0 (C.kernelValue χ W) := by
  obtain ⟨A, B, hA, hB, h1, h2⟩ := C.exists_kernel_estimates_cutoff (ℓ := 0) hχ hW hhom hL hLU
  exact ⟨A, B, hA, hB, h1, h2⟩

end LiftedChart

end RothschildStein.P1
