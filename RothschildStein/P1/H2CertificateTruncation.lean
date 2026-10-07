-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2CertificateGeometry
public import RothschildStein.P1.TypeKernel

/-!
# Truncation certificate

On the carrier of the lifted chart the symmetric gauge `ρ(x, y) = ν(Θ(y, x))` (`ν` a homogeneous
gauge with `ν(-u) = ν(u)`; `Θ` antisymmetric) satisfies `θ₁ d ≤ ρ ≤ θ₂ d` on all of `U × U` (the
lifted-chart field `gauge_comparison` and the equivalence of homogeneous gauges). Given any
`τ > 0`, the truncation distance `d' = ρ` on `{d < τ}` and `d' = d` elsewhere is measurable,
symmetric and comparable everywhere with `θ₁ := min θ₁ 1`, `θ₂ := max θ₂ 1`; it is an
`H2.TruncDist` (BB Thm 7.12, p. 301; BB p. 516, Prop 10.38; BB p. 568).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

namespace LiftedChart

variable (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The gauge truncation distance `ρ(x, y) = ν(Θ(y, x))` on the
carrier (the convention of `KernelFrame.rho ξ η = gauge (Θ η ξ)`, BB p. 516). -/
def rho (ν : (Fin (n + m) → ℝ) → ℝ) (x y : C.Carrier) : ℝ := ν (C.Θ y.val x.val)

/-- Symmetry of `ρ`: `Θ` is antisymmetric and `ν` is even. -/
theorem rho_symm {ν : (Fin (n + m) → ℝ) → ℝ} (hsym : ∀ u, ν (-u) = ν u) (x y : C.Carrier) :
    C.rho ν x y = C.rho ν y x := by
  unfold rho
  rw [C.theta_antisymm y.val y.val_mem x.val x.val_mem, hsym]

/-- `ρ` is jointly continuous on the carrier. -/
theorem continuous_rho {ν : (Fin (n + m) → ℝ) → ℝ} (hν : Continuous ν) :
    Continuous (fun p : C.Carrier × C.Carrier => C.rho ν p.1 p.2) := by
  have hΘ : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ z.1 z.2)
      (C.U ×ˢ C.U) := C.theta_smooth.continuousOn
  have hmap : Continuous (fun p : C.Carrier × C.Carrier => (p.2.val, p.1.val)) :=
    (Carrier.continuous_val.comp continuous_snd).prodMk
      (Carrier.continuous_val.comp continuous_fst)
  exact hν.comp (hΘ.comp_continuous hmap (fun p => ⟨p.2.val_mem, p.1.val_mem⟩))

/-- Comparability of `ρ` with the control distance on all of
`U × U`: `θ₁ d ≤ ρ ≤ θ₂ d` with `θ₁ ≤ 1 ≤ θ₂` (after replacing `θ₁, θ₂` by `min θ₁ 1`,
`max θ₂ 1`). Lifted-chart field `gauge_comparison` and `G2.gauge_equivalent_max`. -/
theorem exists_rho_comparison {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν) :
    ∃ θ₁ θ₂ : ℝ, 0 < θ₁ ∧ θ₁ ≤ 1 ∧ 1 ≤ θ₂ ∧ ∀ x y : C.Carrier,
      θ₁ * dist x y ≤ C.rho ν x y ∧ C.rho ν x y ≤ θ₂ * dist x y := by
  obtain ⟨Cρ, hC1, hcomp⟩ := C.exists_dist_comparison_U
  obtain ⟨a, b, ha, hb, hab⟩ := G2.gauge_equivalent_max hν
  have hCρ : 0 < Cρ := zero_lt_one.trans_le hC1
  refine ⟨min (a / Cρ) 1, max (b * Cρ) 1, lt_min (div_pos ha hCρ) one_pos, min_le_right _ _,
    le_max_right _ _, fun x y => ?_⟩
  obtain ⟨h1, h2⟩ := hcomp y.val y.val_mem x.val x.val_mem
  have hd : dist x y = (C.dl y.val x.val).toReal := by
    rw [Carrier.dist_def, Carrier.dist_comm_dl]
  have hdn : 0 ≤ dist x y := dist_nonneg
  set g := rsGauge C.G.weight C.G.weight_pos (C.Θ y.val x.val) with hg
  have hg0 : 0 ≤ g := G2.gauge_nonneg C.G _
  have hd1 : dist x y ≤ Cρ * g := by rw [hd]; exact h2
  have hd2 : g ≤ Cρ * dist x y := by
    have := (div_le_iff₀ hCρ).mp h1
    rw [hd, mul_comm]
    exact this
  obtain ⟨hlo, hup⟩ := hab (C.Θ y.val x.val)
  constructor
  · calc min (a / Cρ) 1 * dist x y ≤ (a / Cρ) * dist x y :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hdn
      _ ≤ (a / Cρ) * (Cρ * g) :=
          mul_le_mul_of_nonneg_left hd1 (div_nonneg ha.le hCρ.le)
      _ = a * g := by field_simp
      _ ≤ C.rho ν x y := hlo
  · calc C.rho ν x y ≤ b * g := hup
      _ ≤ b * (Cρ * dist x y) := mul_le_mul_of_nonneg_left hd2 hb.le
      _ = (b * Cρ) * dist x y := by ring
      _ ≤ max (b * Cρ) 1 * dist x y := mul_le_mul_of_nonneg_right (le_max_left _ _) hdn

/-- The truncation function: `ρ` on `{d < τ}` and `d` elsewhere
(BB p. 568: `ρ` near the diagonal; a globally defined `TruncDist`). -/
def truncFun (ν : (Fin (n + m) → ℝ) → ℝ) (τ : ℝ) (x y : C.Carrier) : ℝ :=
  if dist x y < τ then C.rho ν x y else dist x y

theorem truncFun_symm {ν : (Fin (n + m) → ℝ) → ℝ} (hsym : ∀ u, ν (-u) = ν u) (τ : ℝ)
    (x y : C.Carrier) : C.truncFun ν τ x y = C.truncFun ν τ y x := by
  unfold truncFun
  rw [dist_comm y x, C.rho_symm hsym y x]

theorem measurable_truncFun {ν : (Fin (n + m) → ℝ) → ℝ} (hν : Continuous ν) (τ : ℝ) :
    Measurable (fun p : C.Carrier × C.Carrier => C.truncFun ν τ p.1 p.2) := by
  unfold truncFun
  exact Measurable.ite (measurableSet_lt continuous_dist.measurable measurable_const)
    (C.continuous_rho hν).measurable continuous_dist.measurable

/-- The properties of the truncation distance: `d' = ρ` on
`{d < τ}`, `d' = d` on `{d ≥ τ}`, `θ₁ ≤ 1 ≤ θ₂`, and comparability of both `ρ` and `d'` with `d`
on all of the carrier (not only on `Ω₁`). -/
structure IsRhoTruncation (S : H2.LocDoubling C.Carrier) (ν : (Fin (n + m) → ℝ) → ℝ) (τ : ℝ)
    (T : H2.TruncDist S) : Prop where
  θ₁_le_one : T.θ₁ ≤ 1
  one_le_θ₂ : 1 ≤ T.θ₂
  near : ∀ x y : C.Carrier, dist x y < τ → T.d' x y = C.rho ν x y
  far : ∀ x y : C.Carrier, τ ≤ dist x y → T.d' x y = dist x y
  rho_comp : ∀ x y : C.Carrier, T.θ₁ * dist x y ≤ C.rho ν x y ∧ C.rho ν x y ≤ T.θ₂ * dist x y
  comp_all : ∀ x y : C.Carrier, T.θ₁ * dist x y ≤ T.d' x y ∧ T.d' x y ≤ T.θ₂ * dist x y

/-- For every locally doubling structure `S` on the carrier,
every homogeneous gauge `ν` with `ν(-u) = ν(u)` and every `τ`, the truncation distance
`d' = ρ = ν(Θ(y, x))` on `{d < τ}` and `d' = d` elsewhere is an `H2.TruncDist`: measurable,
symmetric, and comparable everywhere with constants `θ₁ ≤ 1 ≤ θ₂` (BB p. 301, Thm 7.12;
BB p. 568). -/
theorem exists_truncDist (S : H2.LocDoubling C.Carrier) {ν : (Fin (n + m) → ℝ) → ℝ}
    (hν : C.G.IsHomogeneousGauge ν) (hsym : ∀ u, ν (-u) = ν u) (τ : ℝ) :
    ∃ T : H2.TruncDist S, C.IsRhoTruncation S ν τ T := by
  obtain ⟨θ₁, θ₂, hθ₁, hθ₁1, hθ₂1, hcomp⟩ := C.exists_rho_comparison hν
  have hcompd : ∀ x y : C.Carrier,
      θ₁ * dist x y ≤ C.truncFun ν τ x y ∧ C.truncFun ν τ x y ≤ θ₂ * dist x y := by
    intro x y
    unfold truncFun
    by_cases h : dist x y < τ
    · rw [ite_eq_left h]
      exact hcomp x y
    · rw [ite_eq_right h]
      have hd : 0 ≤ dist x y := dist_nonneg
      exact ⟨mul_le_of_le_one_left hd hθ₁1, le_mul_of_one_le_left hd hθ₂1⟩
  refine ⟨{ d' := C.truncFun ν τ
            θ₁ := θ₁
            θ₂ := θ₂
            θ₁_pos := hθ₁
            θ₁_le := hθ₁1.trans hθ₂1
            comp := fun x _ y _ => hcompd x y
            meas := C.measurable_truncFun hν.1 τ
            symm := C.truncFun_symm hsym τ }, ?_⟩
  refine ⟨hθ₁1, hθ₂1, ?_, ?_, hcomp, hcompd⟩
  · intro x y h
    show C.truncFun ν τ x y = _
    unfold truncFun
    rw [ite_eq_left h]
  · intro x y h
    show C.truncFun ν τ x y = _
    unfold truncFun
    rw [ite_eq_right (not_lt.mpr h)]

namespace IsRhoTruncation

variable {C} {S : H2.LocDoubling C.Carrier} {ν : (Fin (n + m) → ℝ) → ℝ} {τ : ℝ}
  {T : H2.TruncDist S}

/-- A small `d'`-ball has small control radius:
`d'(x, y) < θ₁ ρ'` implies `d(x, y) < ρ'`. -/
theorem dist_lt_of_d'_lt (h : C.IsRhoTruncation S ν τ T) {x y : C.Carrier} {ρ' : ℝ}
    (hxy : T.d' x y < T.θ₁ * ρ') : dist x y < ρ' := by
  have h1 := (h.comp_all x y).1
  have hθ := T.θ₁_pos
  by_contra hcon
  have : T.θ₁ * ρ' ≤ T.θ₁ * dist x y := mul_le_mul_of_nonneg_left (not_lt.mp hcon) hθ.le
  linarith

/-- Inside the near-diagonal region the truncation distance is
`ρ`, so small truncations are exactly the original `ρ`-truncations: for `R ≤ θ₁ τ`,
`d'(x, y) < R ↔ ρ(x, y) < R`. -/
theorem d'_lt_iff_rho_lt (h : C.IsRhoTruncation S ν τ T) {x y : C.Carrier} {R : ℝ}
    (hR : R ≤ T.θ₁ * τ) : T.d' x y < R ↔ C.rho ν x y < R := by
  constructor
  · intro hxy
    have hd : dist x y < τ := h.dist_lt_of_d'_lt (hxy.trans_le hR)
    rwa [← h.near x y hd]
  · intro hxy
    have hd : dist x y < τ := by
      have h1 := (h.rho_comp x y).1
      have hθ := T.θ₁_pos
      by_contra hcon
      have : T.θ₁ * τ ≤ T.θ₁ * dist x y := mul_le_mul_of_nonneg_left (not_lt.mp hcon) hθ.le
      linarith
    rwa [h.near x y hd]

end IsRhoTruncation

end LiftedChart

end RothschildStein.P1
