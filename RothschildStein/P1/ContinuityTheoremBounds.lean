-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityTheoremHolder
public import RothschildStein.P1.ContinuityReconstructionIntegrable
public import RothschildStein.P1.ContinuityPositiveOperator

/-!
# Continuity: the class of kernels with continuity bounds for the principal value

A kernel `κ` has **principal-value bounds on `V`** (`LiftedChart.PVBounds`) if for every input `f` of
finite Hölder norm `‖f‖_{C^α(V)}`, `0 < α < 1`,

* the `ρ`-principal value `PV κ f (ξ)` exists at **every** point `ξ` (`HasRhoPV`);
* `‖PV κ f‖_{C^α(V)} ≤ C_H ‖f‖_{C^α(V)}`;
* `‖PV κ f‖_{L^p(V)} ≤ Λ ‖f‖_{L^p(V)}` for `1 < p < ∞` (the a priori bound behind the `L^p` continuity; `f` is
  measurable, being continuous on `V`).

The class contains the absolutely integrable positive-type kernels (patch kernels), the singular near
parts of degree-2 principal terms, and is closed under finite sums (the linearity of the principal
value is part of the existence clause) and under changes of the kernel on the diagonal. These closure
properties allow the bounds to be assembled from a type decomposition (BB pp. 566–576,
Thm 11.29); smooth multipliers and finite sums preserve the continuity estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section PVCongr

variable {N : ℕ} {ρ κ κ' : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} {f : (Fin N → ℝ) → ℝ}
  {ξ : Fin N → ℝ} {v : ℝ}

/-- The `ρ`-truncations only see the kernel slice almost everywhere. -/
theorem rhoTruncated_congr_ae (h : ∀ᵐ η ∂(volume : Measure (Fin N → ℝ)), κ ξ η = κ' ξ η)
    (ε : ℝ) : rhoTruncated ρ κ f ε ξ = rhoTruncated ρ κ' f ε ξ := by
  unfold rhoTruncated
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h] with η hη
  rw [hη]

/-- The principal value only sees the kernel slice almost everywhere. -/
theorem HasRhoPV.congr_ae (h : ∀ᵐ η ∂(volume : Measure (Fin N → ℝ)), κ ξ η = κ' ξ η)
    (hpv : HasRhoPV ρ κ f ξ v) : HasRhoPV ρ κ' f ξ v := by
  refine ⟨fun ε hε => (hpv.1 ε hε).congr_fun_ae ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae h] with η hη
    rw [hη]
  · exact hpv.2.congr' (Eventually.of_forall fun ε => rhoTruncated_congr_ae h ε)

/-- The `ρ`-principal value as a function depends only on the kernel almost everywhere in
each slice. -/
theorem rhoPV_congr_ae (h : ∀ ξ, ∀ᵐ η ∂(volume : Measure (Fin N → ℝ)), κ ξ η = κ' ξ η) :
    rhoPV ρ κ f = rhoPV ρ κ' f := by
  funext ξ
  unfold rhoPV
  simp only [rhoTruncated_congr_ae (h ξ)]

/-- The principal value of the zero kernel exists and is zero. -/
theorem hasRhoPV_zero : HasRhoPV ρ (fun _ _ => (0 : ℝ)) f ξ 0 :=
  ⟨fun _ _ => by simp, by simp [rhoTruncated]⟩

end PVCongr

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- **A kernel with principal-value bounds on `V`**: for every `f` of finite Hölder norm the
`ρ`-principal value exists at every point, satisfies the Hölder bound for each
`0 < α < 1` and the a priori `L^p` bound for each `1 < p < ∞` and each such `f`.
The gauge `ν` defines the truncation distance `ρ(ξ, η) = ν(Θ(η, ξ))`. -/
structure PVBounds (ν : (Fin (n + m) → ℝ) → ℝ) (V : Set (Fin (n + m) → ℝ))
    (κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) : Prop where
  holder : ∀ {α : ℝ}, 0 < α → α < 1 → ∃ CH : ℝ, 0 < CH ∧
    ∀ f : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α V f ≠ ⊤ →
      (∀ ξ, HasRhoPV (C.rhoGauge ν) κ f ξ (rhoPV (C.rhoGauge ν) κ f ξ)) ∧
      holderENorm C.dl α V (rhoPV (C.rhoGauge ν) κ f) ≤
        ENNReal.ofReal CH * holderENorm C.dl α V f
  lp : ∀ {p : ℝ}, 1 < p → ∀ {α : ℝ}, 0 < α → α < 1 → ∃ Λ : ℝ, 0 < Λ ∧
    ∀ f : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α V f ≠ ⊤ →
      AEStronglyMeasurable f (volume.restrict V) →
        MemLp (rhoPV (C.rhoGauge ν) κ f) (ENNReal.ofReal p) (volume.restrict V) ∧
        eLpNorm (rhoPV (C.rhoGauge ν) κ f) (ENNReal.ofReal p) (volume.restrict V) ≤
          ENNReal.ofReal Λ * eLpNorm f (ENNReal.ofReal p) (volume.restrict V)

variable {C} {ν : (Fin (n + m) → ℝ) → ℝ} {V : Set (Fin (n + m) → ℝ)}
  {κ κ' : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}

/-- The zero kernel has principal-value bounds. -/
theorem PVBounds.zero : C.PVBounds ν V (fun _ _ => (0 : ℝ)) := by
  have hz : ∀ f : (Fin (n + m) → ℝ) → ℝ,
      rhoPV (C.rhoGauge ν) (fun _ _ => (0 : ℝ)) f = fun _ => 0 := fun f =>
    funext fun ξ => hasRhoPV_zero.rhoPV_eq
  refine ⟨fun {α} hα0 hα1 => ⟨1, one_pos, fun f _ => ⟨fun ξ => ?_, ?_⟩⟩,
    fun {p} hp {α} hα0 hα1 => ⟨1, one_pos, fun f _ _ => ?_⟩⟩
  · rw [hz f]
    exact hasRhoPV_zero
  · rw [hz f, holderENorm_zero]
    exact bot_le
  · rw [hz f]
    exact ⟨MemLp.zero, by simp⟩

/-- **Principal-value bounds are stable under sums** (linearity of the principal value: it
exists for the sum and is the sum of the principal values). -/
theorem PVBounds.add (h₁ : C.PVBounds ν V κ) (h₂ : C.PVBounds ν V κ') :
    C.PVBounds ν V (fun ξ η => κ ξ η + κ' ξ η) := by
  have hs : ∀ (f : (Fin (n + m) → ℝ) → ℝ),
      (∀ ξ, HasRhoPV (C.rhoGauge ν) κ f ξ (rhoPV (C.rhoGauge ν) κ f ξ)) →
      (∀ ξ, HasRhoPV (C.rhoGauge ν) κ' f ξ (rhoPV (C.rhoGauge ν) κ' f ξ)) →
      (∀ ξ, HasRhoPV (C.rhoGauge ν) (fun ξ η => κ ξ η + κ' ξ η) f ξ
        (rhoPV (C.rhoGauge ν) κ f ξ + rhoPV (C.rhoGauge ν) κ' f ξ)) ∧
      rhoPV (C.rhoGauge ν) (fun ξ η => κ ξ η + κ' ξ η) f =
        fun ξ => rhoPV (C.rhoGauge ν) κ f ξ + rhoPV (C.rhoGauge ν) κ' f ξ := by
    intro f hp₁ hp₂
    have hadd : ∀ ξ, HasRhoPV (C.rhoGauge ν) (fun ξ η => κ ξ η + κ' ξ η) f ξ
        (rhoPV (C.rhoGauge ν) κ f ξ + rhoPV (C.rhoGauge ν) κ' f ξ) :=
      fun ξ => (hp₁ ξ).add_kernel (hp₂ ξ)
    exact ⟨hadd, funext fun ξ => (hadd ξ).rhoPV_eq⟩
  refine ⟨fun {α} hα0 hα1 => ?_, fun {p} hp {α} hα0 hα1 => ?_⟩
  · obtain ⟨CH₁, hCH₁, hb₁⟩ := h₁.holder hα0 hα1
    obtain ⟨CH₂, hCH₂, hb₂⟩ := h₂.holder hα0 hα1
    refine ⟨CH₁ + CH₂, by positivity, fun f hf => ?_⟩
    obtain ⟨hp₁, hn₁⟩ := hb₁ f hf
    obtain ⟨hp₂, hn₂⟩ := hb₂ f hf
    obtain ⟨hadd, heq⟩ := hs f hp₁ hp₂
    refine ⟨fun ξ => ?_, ?_⟩
    · rw [heq]
      exact hadd ξ
    · rw [heq]
      calc holderENorm C.dl α V (fun ξ => rhoPV (C.rhoGauge ν) κ f ξ +
              rhoPV (C.rhoGauge ν) κ' f ξ)
          ≤ holderENorm C.dl α V (rhoPV (C.rhoGauge ν) κ f) +
              holderENorm C.dl α V (rhoPV (C.rhoGauge ν) κ' f) := holderENorm_add_le hα0.le _ _
        _ ≤ ENNReal.ofReal CH₁ * holderENorm C.dl α V f +
              ENNReal.ofReal CH₂ * holderENorm C.dl α V f := add_le_add hn₁ hn₂
        _ = ENNReal.ofReal (CH₁ + CH₂) * holderENorm C.dl α V f := by
            rw [ENNReal.ofReal_add hCH₁.le hCH₂.le, add_mul]
  · obtain ⟨Λ₁, hΛ₁, hb₁⟩ := h₁.lp hp hα0 hα1
    obtain ⟨Λ₂, hΛ₂, hb₂⟩ := h₂.lp hp hα0 hα1
    obtain ⟨CH₁, -, hh₁⟩ := h₁.holder hα0 hα1
    obtain ⟨CH₂, -, hh₂⟩ := h₂.holder hα0 hα1
    refine ⟨Λ₁ + Λ₂, by positivity, fun f hf hfm => ?_⟩
    obtain ⟨hm₁, hn₁⟩ := hb₁ f hf hfm
    obtain ⟨hm₂, hn₂⟩ := hb₂ f hf hfm
    obtain ⟨-, heq⟩ := hs f (hh₁ f hf).1 (hh₂ f hf).1
    rw [heq]
    have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp.le
    refine ⟨hm₁.add hm₂, ?_⟩
    calc eLpNorm (fun ξ => rhoPV (C.rhoGauge ν) κ f ξ + rhoPV (C.rhoGauge ν) κ' f ξ)
          (ENNReal.ofReal p) (volume.restrict V)
        ≤ eLpNorm (rhoPV (C.rhoGauge ν) κ f) (ENNReal.ofReal p) (volume.restrict V) +
          eLpNorm (rhoPV (C.rhoGauge ν) κ' f) (ENNReal.ofReal p) (volume.restrict V) :=
          eLpNorm_add_le hp1
      _ ≤ ENNReal.ofReal Λ₁ * eLpNorm f (ENNReal.ofReal p) (volume.restrict V) +
          ENNReal.ofReal Λ₂ * eLpNorm f (ENNReal.ofReal p) (volume.restrict V) := add_le_add hn₁ hn₂
      _ = ENNReal.ofReal (Λ₁ + Λ₂) * eLpNorm f (ENNReal.ofReal p) (volume.restrict V) := by
          rw [ENNReal.ofReal_add hΛ₁.le hΛ₂.le, add_mul]

/-- **Principal-value bounds depend on the kernel off the diagonal only**: the diagonal is
Lebesgue-null and the truncation `ρ > ε` avoids it. -/
theorem PVBounds.congr_off_diagonal (h : C.PVBounds ν V κ)
    (he : ∀ ξ η, ξ ≠ η → κ ξ η = κ' ξ η) : C.PVBounds ν V κ' := by
  have hae : ∀ ξ, ∀ᵐ η ∂(volume : Measure (Fin (n + m) → ℝ)), κ ξ η = κ' ξ η := fun ξ => by
    filter_upwards [C.ae_ne ξ] with η hη
    exact he ξ η hη.symm
  have hpv : ∀ f : (Fin (n + m) → ℝ) → ℝ,
      rhoPV (C.rhoGauge ν) κ' f = rhoPV (C.rhoGauge ν) κ f := fun f =>
    (rhoPV_congr_ae hae).symm
  refine ⟨fun {α} hα0 hα1 => ?_, fun {p} hp {α} hα0 hα1 => ?_⟩
  · obtain ⟨CH, hCH, hb⟩ := h.holder hα0 hα1
    refine ⟨CH, hCH, fun f hf => ?_⟩
    obtain ⟨hp1, hn⟩ := hb f hf
    rw [hpv f]
    exact ⟨fun ξ => (hp1 ξ).congr_ae (hae ξ), hn⟩
  · obtain ⟨Λ, hΛ, hb⟩ := h.lp hp hα0 hα1
    refine ⟨Λ, hΛ, fun f hf hfm => ?_⟩
    rw [hpv f]
    exact hb f hf hfm

end LiftedChart

end RothschildStein.P1
