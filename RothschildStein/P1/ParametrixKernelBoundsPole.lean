-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsSize
public import RothschildStein.P1.RightPoleComputationKernel

/-!
# Weighted bounds for the pole and the error terms of the right parametrix

For the H1 fundamental kernel `Γ` (smooth off `0`, homogeneous of degree `2 - Q`) and a chart
extension `ex : C.ChartExt L` (`ParametrixKernelBoundsChart`) this file shows, jointly in the
parameters and near `u = 0` (the right pole computation: "`R_{[i]}` has weight `≥ 0` and `R_{[0]}` weight
`≥ -1`, so the error terms have types at least `1, 1, 2, 1`"):

* `kerFam Γ` (`(ξ, η, u) ↦ Γ(u)`) lies in `WtSym` of degree `2 - Q`;
* the error `ex.errFam Γ = ∑ᵢ (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ Rᵢ) Γ + R₀ Γ` (with the extended remainders)
  lies in `WtSym` of degree `1 - Q`;
* `ex.zFam i (kerFam Γ) = (Yᵢ + Rᵢ) Γ` lies in `WtSym` of degree `2 - Q - wᵢ` (`1 - Q` for the
  horizontal letters, `-Q` for the drift letter).

Hence each family has the weighted bounds `HasWeightedBounds` of the kernel-estimate machinery. On the chart
(`ξ, η ∈ L`, `ξ ≠ η`) the families agree with the actual pole error `E_η Γ = rightPoleError η Γ`
and with `Zᵢ Γ = zDeriv η i Γ` evaluated at `Θ(η, ξ)` (`errFam_eq_rightPoleError`,
`zFam_eq_zDeriv`), because the extended remainder `Rt` agrees with `R` on a neighborhood of
`{(η, Θ(η, ξ))}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1

section Pole

variable {N : ℕ}

/-- The pole `Γ(u)` as a family `(ξ, η, u) ↦ Γ(u)`. -/
def kerFam (Γ : (Fin N → ℝ) → ℝ) : KZ N → ℝ := fun z => Γ z.2.2

/-- `kerFam Γ` is smooth off `u = 0` when `Γ` is smooth off `0`. -/
theorem contDiffOn_kerFam {Γ : (Fin N → ℝ) → ℝ} (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({0}ᶜ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kerFam Γ) {z : KZ N | z.2.2 ≠ 0} :=
  hΓ.comp (contDiff_snd.snd).contDiffOn (fun _ hz => hz)

/-- A family smooth off `u = 0` is differentiable there. -/
theorem differentiableAt_of_kernelDomain {A : KZ N → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A {z : KZ N | z.2.2 ≠ 0}) {z : KZ N} (hz : z.2.2 ≠ 0) :
    DifferentiableAt ℝ A z :=
  (hA.differentiableOn (by simp)).differentiableAt (isOpen_kernelDomain.mem_nhds hz)

/-- A function homogeneous of integer degree `d`, smooth off `0`, gives the family
`kerFam Γ` in `WtSym G K R k d`. -/
theorem wtSym_kerFam (G : HomogeneousGroup N) (K : Set ((Fin N → ℝ) × (Fin N → ℝ))) (R : ℝ)
    {Γ : (Fin N → ℝ) → ℝ} (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({0}ᶜ)) {d : ℤ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ u : Fin N → ℝ, u ≠ 0 → Γ (G.dilate t u) = t ^ d * Γ u)
    {k : ℕ} : WtSym G K R k d (kerFam Γ) :=
  WtSym.homogeneous G K R Γ hΓ hhom

/-- The H1 fundamental kernel, `kerFam Γ ∈ WtSym` of degree `2 - Q` (smooth off `0`,
homogeneous of degree `2 - Q`). -/
theorem wtSym_kerFam_fundamental {G : HomogeneousGroup N} {q : ℕ} {H : H1.StandingHypotheses G q}
    (K : H1.FundamentalKernel G H) (Kp : Set ((Fin N → ℝ) × (Fin N → ℝ))) (R : ℝ) {k : ℕ} :
    WtSym G Kp R k (2 - (G.homogeneousDimension : ℤ)) (kerFam (K : (Fin N → ℝ) → ℝ)) := by
  refine wtSym_kerFam G Kp R K.smooth_off_zero ?_
  intro t ht u hu
  rw [K.homogeneous t ht u hu, ← Real.rpow_intCast]
  congr 2
  push_cast
  ring

/-- Chain rule along a slice: for `A` differentiable at `(ξ, η, u)`,
`D A (ξ, η, u) (0, 0, v) = D (A(ξ, η, ·)) (u) v`. -/
theorem fderiv_slice_u {A : KZ N → ℝ} {ξ η u : Fin N → ℝ} (hA : DifferentiableAt ℝ A (ξ, η, u))
    (v : Fin N → ℝ) :
    fderiv ℝ A (ξ, η, u) (0, 0, v) = fderiv ℝ (fun u' => A (ξ, η, u')) u v := by
  have hB' : HasFDerivAt (fun y : Fin N → ℝ => ((ξ, η, y) : KZ N))
      ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod
        ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod (ContinuousLinearMap.id ℝ (Fin N → ℝ)))) u :=
    (hasFDerivAt_const ξ u).prodMk ((hasFDerivAt_const η u).prodMk (hasFDerivAt_id u))
  have h1 : HasFDerivAt (fun u' => A (ξ, η, u'))
      ((fderiv ℝ A (ξ, η, u)).comp
        ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod
          ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod (ContinuousLinearMap.id ℝ (Fin N → ℝ))))) u :=
    hA.hasFDerivAt.comp u hB'
  rw [h1.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

end Pole

namespace LiftedChart
namespace ChartExt

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}
  {L : Set (Fin (n + m) → ℝ)} (ex : C.ChartExt L)

/-- The operator `Z_i = Y_i + R_{[i]}` (with the extended remainder) on families. -/
def zFam (i : Fin (q + 1)) (A : KZ (n + m) → ℝ) : KZ (n + m) → ℝ :=
  fun z => dY (C := C) i A z + ex.dR i A z

/-- The error `E Γ = ∑_{i ≥ 1} (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ Rᵢ) Γ + R₀ Γ` of `L̃` applied to the right pole, with the
extended remainders, as a family `(ξ, η, u) ↦ (E_η Γ)(u)`. -/
def errFam (Γ : (Fin (n + m) → ℝ) → ℝ) : KZ (n + m) → ℝ := fun z =>
  (∑ i : Fin q, (dY (C := C) i.succ (ex.dR i.succ (kerFam Γ)) z +
    ex.dR i.succ (dY (C := C) i.succ (kerFam Γ)) z +
    ex.dR i.succ (ex.dR i.succ (kerFam Γ)) z)) + ex.dR 0 (kerFam Γ) z

/-- `dY_i` of a family smooth off `u = 0` is smooth off `u = 0`. -/
theorem contDiffOn_dY {A : KZ (n + m) → ℝ} (hA : ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0})
    (i : Fin (q + 1)) : ContDiffOn ℝ (⊤ : ℕ∞) (dY (C := C) i A) {z | z.2.2 ≠ 0} := by
  have hV : ContDiff ℝ (⊤ : ℕ∞) (fun z : KZ (n + m) =>
      (((0 : Fin (n + m) → ℝ), (0 : Fin (n + m) → ℝ), C.Y i z.2.2) : KZ (n + m))) :=
    contDiff_const.prodMk (contDiff_const.prodMk ((C.model_field_smooth i).comp contDiff_snd.snd))
  exact (hA.fderiv_of_isOpen isOpen_kernelDomain (by simp)).clm_apply hV.contDiffOn

/-- `dR_i` of a family smooth off `u = 0` is smooth off `u = 0`. -/
theorem contDiffOn_dR {A : KZ (n + m) → ℝ} (hA : ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0})
    (i : Fin (q + 1)) : ContDiffOn ℝ (⊤ : ℕ∞) (ex.dR i A) {z | z.2.2 ≠ 0} := by
  have hV : ContDiff ℝ (⊤ : ℕ∞) (fun z : KZ (n + m) =>
      (((0 : Fin (n + m) → ℝ), (0 : Fin (n + m) → ℝ), ex.Rt i z.2.1 z.2.2) : KZ (n + m))) :=
    contDiff_const.prodMk (contDiff_const.prodMk
      (contDiff_pi.2 (fun j => (ex.Rt_smooth i j).comp contDiff_snd)))
  exact (hA.fderiv_of_isOpen isOpen_kernelDomain (by simp)).clm_apply hV.contDiffOn

/-- Slice form of `dY`: if `F(ξ, η, ·)` agrees with `f` near `u`, then
`dY_i F (ξ, η, u) = Y_i f (u)`. -/
theorem dY_eq {F : KZ (n + m) → ℝ} {f : (Fin (n + m) → ℝ) → ℝ} {ξ η u : Fin (n + m) → ℝ}
    (hF : DifferentiableAt ℝ F (ξ, η, u)) (hev : (fun u' => F (ξ, η, u')) =ᶠ[𝓝 u] f)
    (i : Fin (q + 1)) : dY (C := C) i F (ξ, η, u) = fieldDerivative (C.Y i) f u := by
  show fderiv ℝ F (ξ, η, u) (0, 0, C.Y i u) = fderiv ℝ f u (C.Y i u)
  rw [fderiv_slice_u hF, hev.fderiv_eq]

/-- Slice form of `dR`: if `F(ξ, η, ·)` agrees with `f` near `u` and `(η, u) ∈ V`
(where `Rt = R`), then `dR_i F (ξ, η, u) = R_{[i], η} f (u)`. -/
theorem dR_eq {F : KZ (n + m) → ℝ} {f : (Fin (n + m) → ℝ) → ℝ} {ξ η u : Fin (n + m) → ℝ}
    (hF : DifferentiableAt ℝ F (ξ, η, u)) (hev : (fun u' => F (ξ, η, u')) =ᶠ[𝓝 u] f)
    (hV : (η, u) ∈ ex.V) (i : Fin (q + 1)) :
    ex.dR i F (ξ, η, u) = fieldDerivative (C.R [i] η) f u := by
  show fderiv ℝ F (ξ, η, u) (0, 0, ex.Rt i η u) = fderiv ℝ f u (C.R [i] η u)
  have hR : ex.Rt i η u = C.R [i] η u := ex.Rt_eq i (η, u) hV
  rw [fderiv_slice_u hF, hev.fderiv_eq, hR]

/-- The slice of `dY_j (kerFam Γ)` is `Y_j Γ` near any `u ≠ 0`. -/
theorem eventually_dY_kerFam {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({0}ᶜ)) (j : Fin (q + 1)) {ξ η u : Fin (n + m) → ℝ}
    (hu : u ≠ 0) :
    (fun u' => dY (C := C) j (kerFam Γ) (ξ, η, u')) =ᶠ[𝓝 u] fieldDerivative (C.Y j) Γ := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hu] with u' hu'
  exact dY_eq (differentiableAt_of_kernelDomain (contDiffOn_kerFam hΓ) hu')
    (Filter.Eventually.of_forall (fun _ => rfl)) j

/-- The slice of `dR_j (kerFam Γ)` is `R_{[j], η} Γ` near `u ≠ 0` with `(η, u) ∈ V`. -/
theorem eventually_dR_kerFam {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({0}ᶜ)) (j : Fin (q + 1)) {ξ η u : Fin (n + m) → ℝ}
    (hu : u ≠ 0) (hV : (η, u) ∈ ex.V) :
    (fun u' => ex.dR j (kerFam Γ) (ξ, η, u')) =ᶠ[𝓝 u] fieldDerivative (C.R [j] η) Γ := by
  have h2 : {u' : Fin (n + m) → ℝ | (η, u') ∈ ex.V} ∈ 𝓝 u :=
    (ex.isOpen_V.preimage (continuous_const.prodMk continuous_id)).mem_nhds hV
  filter_upwards [isOpen_compl_singleton.mem_nhds hu, h2] with u' hu' hV'
  exact ex.dR_eq (differentiableAt_of_kernelDomain (contDiffOn_kerFam hΓ) hu')
    (Filter.Eventually.of_forall (fun _ => rfl)) hV' j

/-- **The right pole error as a symbol family.** For `u ≠ 0` with `(η, u) ∈ V` (where the
extended remainder agrees with `R`) and `Γ` smooth off the origin, `ex.errFam Γ (ξ, η, u)` is the
actual error `E_η Γ (u)` (`rightPoleError`). -/
theorem errFam_eq {Γ : (Fin (n + m) → ℝ) → ℝ} (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({0}ᶜ))
    {ξ η u : Fin (n + m) → ℝ} (hu : u ≠ 0) (hV : (η, u) ∈ ex.V) :
    ex.errFam Γ (ξ, η, u) = C.rightPoleError η Γ u := by
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (kerFam Γ) {z | z.2.2 ≠ 0} := contDiffOn_kerFam hΓ
  have hd : ∀ {F : KZ (n + m) → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) F {z | z.2.2 ≠ 0} →
      DifferentiableAt ℝ F (ξ, η, u) := fun hF =>
    differentiableAt_of_kernelDomain hF (z := (ξ, η, u)) hu
  unfold errFam rightPoleError
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dY_eq (hd (ex.contDiffOn_dR hA i.succ)) (ex.eventually_dR_kerFam hΓ i.succ hu hV) i.succ,
      ex.dR_eq (hd (contDiffOn_dY hA i.succ)) (eventually_dY_kerFam hΓ i.succ hu) hV i.succ,
      ex.dR_eq (hd (ex.contDiffOn_dR hA i.succ)) (ex.eventually_dR_kerFam hΓ i.succ hu hV) hV
        i.succ]
  · exact ex.dR_eq (hd hA) (Filter.Eventually.of_forall (fun _ => rfl)) hV 0

/-- **`Z_i Γ` as a symbol family.** For `u ≠ 0` with `(η, u) ∈ V`:
`(ex.zFam i (kerFam Γ))(ξ, η, u) = (Z_{i,η} Γ)(u)` (`zDeriv`). -/
theorem zFam_eq {Γ : (Fin (n + m) → ℝ) → ℝ} (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({0}ᶜ))
    (i : Fin (q + 1)) {ξ η u : Fin (n + m) → ℝ} (hu : u ≠ 0) (hV : (η, u) ∈ ex.V) :
    ex.zFam i (kerFam Γ) (ξ, η, u) = C.zDeriv η i Γ u := by
  have hd : DifferentiableAt ℝ (kerFam Γ) (ξ, η, u) :=
    differentiableAt_of_kernelDomain (contDiffOn_kerFam hΓ) (z := (ξ, η, u)) hu
  show dY (C := C) i (kerFam Γ) (ξ, η, u) + ex.dR i (kerFam Γ) (ξ, η, u) =
    fieldDerivative (C.Y i) Γ u + fieldDerivative (C.R [i] η) Γ u
  rw [dY_eq (f := Γ) hd (Filter.Eventually.of_forall (fun _ => rfl)) i,
    ex.dR_eq (f := Γ) hd (Filter.Eventually.of_forall (fun _ => rfl)) hV i]

section Classes

variable {K : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ))} {R : ℝ}

/-- **`Z_i Γ` has degree `2 - Q - w_i`.** If `A` lies in `WtSym` of degree `d` to every
depth then `Z_i A = (Y_i + R_{[i]}) A` lies in `WtSym` of degree `d - w_i` (the remainder field has
weight `≥ 1 - w_i`, one better than needed). -/
theorem zFam_class (hK : IsCompact K) (hR : 0 < R) {A : KZ (n + m) → ℝ} {d : ℤ}
    (hA : ∀ k : ℕ, WtSym C.G K R k d A) (i : Fin (q + 1)) (k : ℕ) :
    WtSym C.G K R k (d - (((if i = 0 then (2 : ℕ+) else 1 : ℕ+) : ℕ) : ℤ))
      (ex.zFam i A) :=
  WtSym.add (dY_class (C := C) (hA (k + 1)) i)
    (WtSym.mono_d hR (by omega) (ex.dR_class hK hR (hA (k + 1)) i))

/-- **The right pole error has degree `1 - Q`** (the right pole computation: the terms
`Yᵢ Rᵢ Γ, Rᵢ Yᵢ Γ, R₀ Γ` have type `1` and `Rᵢ Rᵢ Γ` type `2`, because `Rᵢ` has weight `≥ 0` and
`R₀` weight `≥ -1`). If `kerFam Γ ∈ WtSym` of degree `2 - Q` to every depth, then
`ex.errFam Γ ∈ WtSym` of degree `1 - Q`. -/
theorem errFam_class (hK : IsCompact K) (hR : 0 < R) {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ∀ k : ℕ, WtSym C.G K R k (2 - (C.G.homogeneousDimension : ℤ)) (kerFam Γ)) (k : ℕ) :
    WtSym C.G K R k (1 - (C.G.homogeneousDimension : ℤ)) (ex.errFam Γ) := by
  set Q : ℤ := (C.G.homogeneousDimension : ℤ) with hQ
  have t1 : ∀ i : Fin q, WtSym C.G K R k (1 - Q)
      (dY (C := C) i.succ (ex.dR i.succ (kerFam Γ))) := fun i =>
    (dY_class (C := C) (ex.dR_class hK hR (hΓ (k + 1 + 1)) i.succ) i.succ).degree_congr
      (by simp [Fin.succ_ne_zero]; ring)
  have t2 : ∀ i : Fin q, WtSym C.G K R k (1 - Q)
      (ex.dR i.succ (dY (C := C) i.succ (kerFam Γ))) := fun i =>
    (ex.dR_class hK hR (dY_class (C := C) (hΓ (k + 1 + 1)) i.succ) i.succ).degree_congr
      (by simp [Fin.succ_ne_zero]; ring)
  have t3 : ∀ i : Fin q, WtSym C.G K R k (1 - Q)
      (ex.dR i.succ (ex.dR i.succ (kerFam Γ))) := fun i =>
    WtSym.mono_d hR (by simp [Fin.succ_ne_zero])
      (ex.dR_class hK hR (ex.dR_class hK hR (hΓ (k + 1 + 1)) i.succ) i.succ)
  have t0 : WtSym C.G K R k (1 - Q) (ex.dR 0 (kerFam Γ)) :=
    (ex.dR_class hK hR (hΓ (k + 1)) 0).degree_congr (by simp; ring)
  exact WtSym.add (WtSym.sum Finset.univ _
    (fun i _ => WtSym.add (WtSym.add (t1 i) (t2 i)) (t3 i))) t0

end Classes

end ChartExt
end LiftedChart

end RothschildStein.P1
