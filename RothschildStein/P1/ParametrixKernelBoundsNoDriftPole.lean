-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsPole
public import RothschildStein.P1.RightParametrixNoDriftError

/-!
# Weighted bounds without drift for the pole and the error terms of the right parametrix

The no-drift counterpart of the chart part of `ParametrixKernelBoundsPole` (the generic part, the
pole family `kerFam`, its class and the slice calculus `fderiv_slice_u`, is alphabet independent
and is used from there). For the H1 fundamental kernel `Γ` of the no-drift model (smooth off `0`,
homogeneous of degree `2 - Q`) and a chart extension `ex : C.ChartExt L`
(`ParametrixKernelBoundsChart`) of a no-drift chart, this file shows, jointly in the parameters and
near `u = 0` (the right pole computation: "`R_{[i]}` has weight `≥ 0`, so the error terms have types at
least `1, 1, 2`"):

* the error `ex.errFamNoDrift Γ = ∑ᵢ (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ Rᵢ) Γ` (with the extended remainders)
  lies in `WtSym` of degree `1 - Q`;
* `ex.zFamNoDrift i (kerFam Γ) = (Yᵢ + Rᵢ) Γ` lies in `WtSym` of degree `1 - Q`.

Hence each family has the weighted bounds `HasWeightedBounds` of the kernel-estimate machinery. On the chart
(`ξ, η ∈ L`, `ξ ≠ η`) the families agree with the actual pole error `E_η Γ =
rightPoleErrorNoDrift η Γ` and with `Zᵢ Γ = zDeriv η i Γ` evaluated at `Θ(η, ξ)`
(`errFam_eq_rightPoleError_noDrift`, `zFam_eq_zDeriv_noDrift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1
namespace LiftedChart
namespace ChartExt

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}
  {L : Set (Fin (n + m) → ℝ)} (ex : C.ChartExt L)

/-- The operator `Z_i = Y_i + R_{[i]}` (with the extended remainder) on families. -/
def zFamNoDrift (i : Fin q) (A : KZ (n + m) → ℝ) : KZ (n + m) → ℝ :=
  fun z => dY (C := C) i A z + ex.dR i A z

/-- The no-drift error `E Γ = ∑ᵢ (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ Rᵢ) Γ` of `L̃` applied to the right pole, with the
extended remainders, as a family `(ξ, η, u) ↦ (E_η Γ)(u)`. -/
def errFamNoDrift (Γ : (Fin (n + m) → ℝ) → ℝ) : KZ (n + m) → ℝ := fun z =>
  ∑ i : Fin q, (dY (C := C) i (ex.dR i (kerFam Γ)) z +
    ex.dR i (dY (C := C) i (kerFam Γ)) z +
    ex.dR i (ex.dR i (kerFam Γ)) z)

/-- `dY_i` of a family smooth off `u = 0` is smooth off `u = 0`. -/
theorem contDiffOn_dY_noDrift {A : KZ (n + m) → ℝ} (hA : ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0})
    (i : Fin q) : ContDiffOn ℝ (⊤ : ℕ∞) (dY (C := C) i A) {z | z.2.2 ≠ 0} := by
  have hV : ContDiff ℝ (⊤ : ℕ∞) (fun z : KZ (n + m) =>
      (((0 : Fin (n + m) → ℝ), (0 : Fin (n + m) → ℝ), C.Y i z.2.2) : KZ (n + m))) :=
    contDiff_const.prodMk (contDiff_const.prodMk ((C.model_field_smooth i).comp contDiff_snd.snd))
  exact (hA.fderiv_of_isOpen isOpen_kernelDomain (by simp)).clm_apply hV.contDiffOn

/-- `dR_i` of a family smooth off `u = 0` is smooth off `u = 0`. -/
theorem contDiffOn_dR_noDrift {A : KZ (n + m) → ℝ} (hA : ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0})
    (i : Fin q) : ContDiffOn ℝ (⊤ : ℕ∞) (ex.dR i A) {z | z.2.2 ≠ 0} := by
  have hV : ContDiff ℝ (⊤ : ℕ∞) (fun z : KZ (n + m) =>
      (((0 : Fin (n + m) → ℝ), (0 : Fin (n + m) → ℝ), ex.Rt i z.2.1 z.2.2) : KZ (n + m))) :=
    contDiff_const.prodMk (contDiff_const.prodMk
      (contDiff_pi.2 (fun j => (ex.Rt_smooth i j).comp contDiff_snd)))
  exact (hA.fderiv_of_isOpen isOpen_kernelDomain (by simp)).clm_apply hV.contDiffOn

/-- Slice form of `dY`: if `F(ξ, η, ·)` agrees with `f` near `u`, then
`dY_i F (ξ, η, u) = Y_i f (u)`. -/
theorem dY_eq_noDrift {F : KZ (n + m) → ℝ} {f : (Fin (n + m) → ℝ) → ℝ} {ξ η u : Fin (n + m) → ℝ}
    (hF : DifferentiableAt ℝ F (ξ, η, u)) (hev : (fun u' => F (ξ, η, u')) =ᶠ[𝓝 u] f)
    (i : Fin q) : dY (C := C) i F (ξ, η, u) = fieldDerivative (C.Y i) f u := by
  show fderiv ℝ F (ξ, η, u) (0, 0, C.Y i u) = fderiv ℝ f u (C.Y i u)
  rw [fderiv_slice_u hF, hev.fderiv_eq]

/-- Slice form of `dR`: if `F(ξ, η, ·)` agrees with `f` near `u` and `(η, u) ∈ V`
(where `Rt = R`), then `dR_i F (ξ, η, u) = R_{[i], η} f (u)`. -/
theorem dR_eq_noDrift {F : KZ (n + m) → ℝ} {f : (Fin (n + m) → ℝ) → ℝ} {ξ η u : Fin (n + m) → ℝ}
    (hF : DifferentiableAt ℝ F (ξ, η, u)) (hev : (fun u' => F (ξ, η, u')) =ᶠ[𝓝 u] f)
    (hV : (η, u) ∈ ex.V) (i : Fin q) :
    ex.dR i F (ξ, η, u) = fieldDerivative (C.R [i] η) f u := by
  show fderiv ℝ F (ξ, η, u) (0, 0, ex.Rt i η u) = fderiv ℝ f u (C.R [i] η u)
  have hR : ex.Rt i η u = C.R [i] η u := ex.Rt_eq i (η, u) hV
  rw [fderiv_slice_u hF, hev.fderiv_eq, hR]

/-- The slice of `dY_j (kerFam Γ)` is `Y_j Γ` near any `u ≠ 0`. -/
theorem eventually_dY_kerFam_noDrift {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({0}ᶜ)) (j : Fin q) {ξ η u : Fin (n + m) → ℝ}
    (hu : u ≠ 0) :
    (fun u' => dY (C := C) j (kerFam Γ) (ξ, η, u')) =ᶠ[𝓝 u] fieldDerivative (C.Y j) Γ := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hu] with u' hu'
  exact dY_eq_noDrift (differentiableAt_of_kernelDomain (contDiffOn_kerFam hΓ) hu')
    (Filter.Eventually.of_forall (fun _ => rfl)) j

/-- The slice of `dR_j (kerFam Γ)` is `R_{[j], η} Γ` near `u ≠ 0` with `(η, u) ∈ V`. -/
theorem eventually_dR_kerFam_noDrift {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({0}ᶜ)) (j : Fin q) {ξ η u : Fin (n + m) → ℝ}
    (hu : u ≠ 0) (hV : (η, u) ∈ ex.V) :
    (fun u' => ex.dR j (kerFam Γ) (ξ, η, u')) =ᶠ[𝓝 u] fieldDerivative (C.R [j] η) Γ := by
  have h2 : {u' : Fin (n + m) → ℝ | (η, u') ∈ ex.V} ∈ 𝓝 u :=
    (ex.isOpen_V.preimage (continuous_const.prodMk continuous_id)).mem_nhds hV
  filter_upwards [isOpen_compl_singleton.mem_nhds hu, h2] with u' hu' hV'
  exact ex.dR_eq_noDrift (differentiableAt_of_kernelDomain (contDiffOn_kerFam hΓ) hu')
    (Filter.Eventually.of_forall (fun _ => rfl)) hV' j

/-- **The right pole error as a symbol family.** For `u ≠ 0` with `(η, u) ∈ V` (where the
extended remainder agrees with `R`) and `Γ` smooth off the origin, `ex.errFamNoDrift Γ (ξ, η, u)` is the
actual error `E_η Γ (u)` (`rightPoleErrorNoDrift`). -/
theorem errFam_eq_noDrift {Γ : (Fin (n + m) → ℝ) → ℝ} (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({0}ᶜ))
    {ξ η u : Fin (n + m) → ℝ} (hu : u ≠ 0) (hV : (η, u) ∈ ex.V) :
    ex.errFamNoDrift Γ (ξ, η, u) = C.rightPoleErrorNoDrift η Γ u := by
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (kerFam Γ) {z | z.2.2 ≠ 0} := contDiffOn_kerFam hΓ
  have hd : ∀ {F : KZ (n + m) → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) F {z | z.2.2 ≠ 0} →
      DifferentiableAt ℝ F (ξ, η, u) := fun hF =>
    differentiableAt_of_kernelDomain hF (z := (ξ, η, u)) hu
  unfold errFamNoDrift rightPoleErrorNoDrift
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dY_eq_noDrift (hd (ex.contDiffOn_dR_noDrift hA i)) (ex.eventually_dR_kerFam_noDrift hΓ i hu hV) i,
    ex.dR_eq_noDrift (hd (contDiffOn_dY_noDrift hA i)) (eventually_dY_kerFam_noDrift hΓ i hu) hV i,
    ex.dR_eq_noDrift (hd (ex.contDiffOn_dR_noDrift hA i)) (ex.eventually_dR_kerFam_noDrift hΓ i hu hV) hV
      i]

/-- **`Z_i Γ` as a symbol family.** For `u ≠ 0` with `(η, u) ∈ V`:
`(ex.zFamNoDrift i (kerFam Γ))(ξ, η, u) = (Z_{i,η} Γ)(u)` (`zDeriv`). -/
theorem zFam_eq_noDrift {Γ : (Fin (n + m) → ℝ) → ℝ} (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({0}ᶜ))
    (i : Fin q) {ξ η u : Fin (n + m) → ℝ} (hu : u ≠ 0) (hV : (η, u) ∈ ex.V) :
    ex.zFamNoDrift i (kerFam Γ) (ξ, η, u) = C.zDeriv η i Γ u := by
  have hd : DifferentiableAt ℝ (kerFam Γ) (ξ, η, u) :=
    differentiableAt_of_kernelDomain (contDiffOn_kerFam hΓ) (z := (ξ, η, u)) hu
  show dY (C := C) i (kerFam Γ) (ξ, η, u) + ex.dR i (kerFam Γ) (ξ, η, u) =
    fieldDerivative (C.Y i) Γ u + fieldDerivative (C.R [i] η) Γ u
  rw [dY_eq_noDrift (f := Γ) hd (Filter.Eventually.of_forall (fun _ => rfl)) i,
    ex.dR_eq_noDrift (f := Γ) hd (Filter.Eventually.of_forall (fun _ => rfl)) hV i]

section Classes

variable {K : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ))} {R : ℝ}

/-- **`Z_i Γ` has degree `2 - Q - 1`.** If `A` lies in `WtSym` of degree `d` to every
depth then `Z_i A = (Y_i + R_{[i]}) A` lies in `WtSym` of degree `d - 1` (the remainder field has
weight `≥ 0`, one better than needed). -/
theorem zFam_class_noDrift (hK : IsCompact K) (hR : 0 < R) {A : KZ (n + m) → ℝ} {d : ℤ}
    (hA : ∀ k : ℕ, WtSym C.G K R k d A) (i : Fin q) (k : ℕ) :
    WtSym C.G K R k (d - 1) (ex.zFamNoDrift i A) :=
  (WtSym.add (dY_class (C := C) (hA (k + 1)) i)
    (WtSym.mono_d hR (by simp) (ex.dR_class hK hR (hA (k + 1)) i))).degree_congr (by simp)

/-- **The right pole error has degree `1 - Q`** (the right pole computation: the terms
`Yᵢ Rᵢ Γ, Rᵢ Yᵢ Γ` have type `1` and `Rᵢ Rᵢ Γ` type `2`, because `Rᵢ` has weight `≥ 0`). If `kerFam Γ ∈ WtSym` of degree `2 - Q` to every depth, then
`ex.errFamNoDrift Γ ∈ WtSym` of degree `1 - Q`. -/
theorem errFam_class_noDrift (hK : IsCompact K) (hR : 0 < R) {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ∀ k : ℕ, WtSym C.G K R k (2 - (C.G.homogeneousDimension : ℤ)) (kerFam Γ)) (k : ℕ) :
    WtSym C.G K R k (1 - (C.G.homogeneousDimension : ℤ)) (ex.errFamNoDrift Γ) := by
  set Q : ℤ := (C.G.homogeneousDimension : ℤ) with hQ
  have t1 : ∀ i : Fin q, WtSym C.G K R k (1 - Q)
      (dY (C := C) i (ex.dR i (kerFam Γ))) := fun i =>
    (dY_class (C := C) (ex.dR_class hK hR (hΓ (k + 1 + 1)) i) i).degree_congr
      (by simp; ring)
  have t2 : ∀ i : Fin q, WtSym C.G K R k (1 - Q)
      (ex.dR i (dY (C := C) i (kerFam Γ))) := fun i =>
    (ex.dR_class hK hR (dY_class (C := C) (hΓ (k + 1 + 1)) i) i).degree_congr
      (by simp; ring)
  have t3 : ∀ i : Fin q, WtSym C.G K R k (1 - Q)
      (ex.dR i (ex.dR i (kerFam Γ))) := fun i =>
    WtSym.mono_d hR (by simp)
      (ex.dR_class hK hR (ex.dR_class hK hR (hΓ (k + 1 + 1)) i) i)
  exact WtSym.sum Finset.univ _ (fun i _ => WtSym.add (WtSym.add (t1 i) (t2 i)) (t3 i))

end Classes

end ChartExt
end LiftedChart

end RothschildStein.P1
