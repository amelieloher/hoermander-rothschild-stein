-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AuxiliaryControl

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.G4

/-- Constant-control curves retain BB's absolute-continuity and a.e.
ODE requirements on the original ambient domain (BB Definition 9.8, p. 403). -/
def IsConstantControlledCurve {m n : ℕ} (Ω : Set (Fin n → ℝ))
    (w : Fin m → ℕ+) (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (δ : ℝ) (γ : ℝ → (Fin n → ℝ)) : Prop :=
  0 < δ ∧ AbsolutelyContinuousOnInterval γ 0 1 ∧ MapsTo γ (Icc 0 1) Ω ∧
    ∃ a : Fin m → ℝ, (∀ i, |a i| ≤ δ ^ (w i : ℕ)) ∧
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
        HasDerivAt γ (∑ i, a i • Z i (γ t)) t

/-- Constant-control cost `ρ#`, still possibly infinite until the
local endpoint construction (BB Definition 9.8, p. 403). -/
def constantControlDistance {m n : ℕ} (Ω : Set (Fin n → ℝ))
    (w : Fin m → ℕ+) (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (x y : Fin n → ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ δ : ℝ, r = ENNReal.ofReal δ ∧ ∃ γ : ℝ → (Fin n → ℝ),
    IsConstantControlledCurve Ω w Z δ γ ∧ γ 0 = x ∧ γ 1 = y}

/-- Every constant-control curve is a controlled curve,
using measurable constant controls (BB Remark 9.9, p. 403). -/
theorem IsConstantControlledCurve.isControlledCurve {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} {w : Fin m → ℕ+}
    {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {δ : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (h : IsConstantControlledCurve Ω w Z δ γ) : isControlledCurve Ω w Z δ γ := by
  obtain ⟨hδ, hac, hmap, a, ha, hd⟩ := h
  exact ⟨hδ, hac, hmap, fun i _ => a i, fun _ => aemeasurable_const,
    hd.mono (fun t ht => ⟨ha, ht⟩)⟩

/-- The auxiliary distance is bounded by the constant-control cost;
thus `B# ⊆ B*` before any finiteness theorem (BB Remark 9.9, p. 403). -/
theorem controlDistance_le_constantControlDistance {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x y : Fin n → ℝ) :
    controlDistance Ω w Z x y ≤ constantControlDistance Ω w Z x y := by
  unfold controlDistance constantControlDistance
  apply sInf_le_sInf
  rintro r ⟨δ, rfl, γ, hγ, hzero, hone⟩
  exact ⟨δ, rfl, γ, hγ.isControlledCurve, hzero, hone⟩

/-- Infimum strictness produces an actual constant-control curve
with strictly smaller cost (BB Remark 9.10, p. 404). -/
theorem exists_constantCurve_of_distance_lt {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} {w : Fin m → ℕ+}
    {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {x y : Fin n → ℝ} {r : ℝ}
    (h : constantControlDistance Ω w Z x y < ENNReal.ofReal r) :
    ∃ δ, 0 < δ ∧ δ < r ∧ ∃ γ, IsConstantControlledCurve Ω w Z δ γ ∧ γ 0 = x ∧ γ 1 = y := by
  obtain ⟨b, hb, hbr⟩ := sInf_lt_iff.mp h
  obtain ⟨δ, rfl, γ, hγ, hzero, hone⟩ := hb
  exact ⟨δ, hγ.1, (ENNReal.ofReal_lt_ofReal_iff'.mp hbr).1, γ, hγ, hzero, hone⟩

/-- Constant-control balls from the complete short-field family
use the original ambient domain, without recomputing distances on patches. -/
def constantShortDistance {m n s : ℕ} (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x y : Fin n → ℝ) : ℝ≥0∞ :=
  constantControlDistance Ω (fun j => shortWeight w (shortIndex (s := s) w j))
    (fun j => shortField w X (shortIndex (s := s) w j)) x y

/-- The exact short-field distance comparison (BB Remark 9.9, p. 403). -/
theorem auxiliaryDistance_le_constantShortDistance {m n s : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x y : Fin n → ℝ) :
    auxiliaryDistance (s := s) Ω w X x y ≤ constantShortDistance (s := s) Ω w X x y :=
  controlDistance_le_constantControlDistance _ _ _ x y

end RothschildStein.G4
