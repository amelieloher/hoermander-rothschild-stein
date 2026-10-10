-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.GroupCovariance
public import RothschildStein.G2.DilationMeasure

/-! Images of horizontal balls under group translations and dilations. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set RothschildStein
open scoped NNReal
namespace HeatKernel

/-- The open horizontal ball of real radius. -/
def horizontalBall {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (r : ℝ) : Set (Fin N → ℝ) :=
  {y | horizontalL2Distance X x y < ENNReal.ofReal r}

/-- Left translation carries horizontal balls to balls of the same radius. -/
theorem image_horizontalBall_leftTranslation {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (g x : Fin N → ℝ) (r : ℝ) :
    G.mul g '' horizontalBall (G.horizontalFields hq) x r =
      horizontalBall (G.horizontalFields hq) (G.mul g x) r := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change horizontalL2Distance _ (G.mul g x) (G.mul g y) < _
    rw [horizontalL2Distance_leftTranslation]
    exact hy
  · intro hz
    obtain ⟨y, rfl⟩ := (G2.leftTranslation_bijective G g).surjective z
    exact ⟨y, by simpa only [horizontalBall, mem_ofPred_eq,
      horizontalL2Distance_leftTranslation] using hz, rfl⟩

/-- Positive dilations carry horizontal balls to balls with scaled radius. -/
theorem image_horizontalBall_dilate {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r)
    (x : Fin N → ℝ) (ρ : ℝ) :
    G.dilate r '' horizontalBall (G.horizontalFields hq) x ρ =
      horizontalBall (G.horizontalFields hq) (G.dilate r x) (r * ρ) := by
  have hmul := ENNReal.mul_right_strictMono (ne_of_gt (ENNReal.ofReal_pos.mpr hr))
    ENNReal.ofReal_ne_top
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change horizontalL2Distance _ (G.dilate r x) (G.dilate r y) < _
    rw [horizontalL2Distance_dilate G hq hw hr, ENNReal.ofReal_mul hr.le]
    exact hmul hy
  · intro hz
    obtain ⟨y, rfl⟩ := (G2.dilate_bijective G hr.ne').surjective z
    refine ⟨y, ?_, rfl⟩
    change horizontalL2Distance _ x y < _
    change horizontalL2Distance _ (G.dilate r x) (G.dilate r y) < _ at hz
    rw [horizontalL2Distance_dilate G hq hw hr, ENNReal.ofReal_mul hr.le] at hz
    exact hmul.lt_iff_lt.mp hz

/-- Every positive-radius horizontal ball is a translated dilation of the unit ball. -/
theorem horizontalBall_eq_image_unitBall {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r)
    (x : Fin N → ℝ) :
    horizontalBall (G.horizontalFields hq) x r =
      (fun y => G.mul x (G.dilate r y)) '' horizontalBall (G.horizontalFields hq) 0 1 := by
  have hd := image_horizontalBall_dilate G hq hw hr 0 1
  simp only [G2.dilate_zero, mul_one] at hd
  have ht := image_horizontalBall_leftTranslation G hq x 0 r
  simp only [G2.mul_zero] at ht
  rw [← ht, ← hd, image_image]

end HeatKernel
