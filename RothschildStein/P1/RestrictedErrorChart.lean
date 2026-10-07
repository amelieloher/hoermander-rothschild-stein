-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RestrictedErrorHolder
public import RothschildStein.P1.H2CertificateCarrier
public import RothschildStein.G4.ControlTopology
public import RothschildStein.G2.DilationMeasure

/-!
# Restricted-error bounds on a lifted chart: small balls and kernel hypotheses

The abstract small-ball estimates of `RestrictedErrorShell/Slice/Holder` are instantiated on a
`LiftedChart C` with `dr = (C.dl ·  ·).toReal`, `S = U_r = rsBall C.O w C.Xl ξ₀ r`, `ρ = r` and
`q + 1 = Q` the homogeneous dimension of the model group.

* `IsSmallBallRadius K₀ ξ₀ r_*`: `0 < r_* ≤ 1`, the balls `B̃(ξ₀, r)`, `r < r_*`, stay in the
  compact `K₀ ⊆ U`, and the control balls `B̃(η, t)`, `η ∈ K₀`, `t < 2 r_*`, are measurable of
  volume at most `Cv t^Q` (the upper half of `LiftedChart.ball_bounds`). Such `r_*` exists when
  `ξ₀ ∈ interior K₀` (`exists_isSmallBallRadius`), by a first-exit argument for controlled curves.
* `RestrictedKernelBounds K₀ k A B`: the hypotheses on the kernel, exactly the conclusion of the
  lifted kernel estimates at `ℓ = 1` (size `A d̃^(1-Q)`, difference `B d̃(ξ, ξ') / d̃(ξ', η)^Q`
  for `d̃(ξ', η) > 2 d̃(ξ, ξ')`), required only at distances `< 2` (all that matters for
  `r_* ≤ 1`), plus measurability of the kernel cut to `K₀ × K₀` off the diagonal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

namespace LiftedChart

variable (C : LiftedChart w s Ω hΩ X x₀ m)

/-- An admissible small-ball radius `r_*` for the compact
`K₀ ⊆ U` and the centre `ξ₀ ∈ K₀`: `0 < r_* ≤ 1`; the lifted control balls `B̃(ξ₀, r)`, `r < r_*`,
stay in `K₀`; and the control balls `B̃(η, t)`, `η ∈ K₀`, `t < 2 r_*`, are measurable of finite
volume at most `Cv t^Q` (the upper bound of `LiftedChart.ball_bounds`). -/
structure IsSmallBallRadius (K₀ : Set (Fin (n + m) → ℝ)) (ξ₀ : Fin (n + m) → ℝ)
    (rstar : ℝ) : Prop where
  pos : 0 < rstar
  le_one : rstar ≤ 1
  mem : ξ₀ ∈ K₀
  subset_U : K₀ ⊆ C.U
  ball_subset : ∀ r : ℝ, 0 < r → r < rstar → rsBall C.O w C.Xl ξ₀ r ⊆ K₀
  volume_bound : ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ η ∈ K₀, ∀ t : ℝ, 0 < t → t < 2 * rstar →
    MeasurableSet (rsBall C.O w C.Xl η t) ∧ volume (rsBall C.O w C.Xl η t) ≠ ⊤ ∧
      (volume (rsBall C.O w C.Xl η t)).toReal ≤ Cv * t ^ C.G.homogeneousDimension

variable {C}

/-- **Existence of `r_*`**: for a compact `K₀ ⊆ U` and
`ξ₀ ∈ interior K₀` there is an admissible radius. The balls stay in `K₀` by the first-exit lemma
(`G4.exists_controlBall_subset_ball`), the volume bound is `LiftedChart.ball_bounds`. -/
theorem exists_isSmallBallRadius {K₀ : Set (Fin (n + m) → ℝ)} (hK₀ : IsCompact K₀)
    (hK₀U : K₀ ⊆ C.U) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ interior K₀) :
    ∃ rstar : ℝ, C.IsSmallBallRadius K₀ ξ₀ rstar := by
  obtain ⟨rb, cv, Cv, δ, cf, Cf, hrb, hcv, hCv, hδ, hδ1, hcf, hCf, hball⟩ :=
    C.ball_bounds K₀ hK₀ hK₀U
  obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hξ₀)
  have hξK : ξ₀ ∈ K₀ := interior_subset hξ₀
  have hξO : ξ₀ ∈ C.O := C.mem_O_of_mem_U (hK₀U hξK)
  obtain ⟨r₁, hr₁, hr₁sub⟩ := G4.exists_controlBall_subset_ball C.isOpen_O_of_chart
    (fun j => (C.lift_smooth j).continuousOn) w hξO hε
  have hpos : 0 < min 1 (min (rb / 2) r₁) :=
    lt_min one_pos (lt_min (by linarith) hr₁)
  refine ⟨min 1 (min (rb / 2) r₁), hpos, min_le_left _ _, hξK, hK₀U, ?_, Cv, hCv.le, ?_⟩
  · intro r hr hrr
    have hr1 : r < r₁ := hrr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    intro y hy
    apply hεK
    apply hr₁sub
    exact lt_of_lt_of_le hy.2 (ENNReal.ofReal_le_ofReal hr1.le)
  · intro η hη t ht htr
    have htb : t < rb := by
      have : min 1 (min (rb / 2) r₁) ≤ rb / 2 := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    obtain ⟨-, hm, -, hfin, -, -, -, -, hup, -⟩ := hball η hη t ht htb
    exact ⟨hm, hfin, hup⟩

section Bridge

variable {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ} {rstar r : ℝ}

/-- Two points of `U_r` are at lifted control distance
`< 2r`. -/
theorem dl_lt_of_mem_rsBall {x y : Fin (n + m) → ℝ} (hr : 0 < r)
    (hx : x ∈ rsBall C.O w C.Xl ξ₀ r) (hy : y ∈ rsBall C.O w C.Xl ξ₀ r) :
    C.dl x y < ENNReal.ofReal (2 * r) := by
  have h1 : C.dl x ξ₀ < ENNReal.ofReal r := by
    rw [show C.dl x ξ₀ = C.dl ξ₀ x from G1.controlDistance_symm C.O w C.Xl x ξ₀]
    exact hx.2
  have h2 : C.dl ξ₀ y < ENNReal.ofReal r := hy.2
  calc C.dl x y ≤ C.dl x ξ₀ + C.dl ξ₀ y := G1.controlDistance_triangle C.O w C.Xl x ξ₀ y
    _ < ENNReal.ofReal r + ENNReal.ofReal r := ENNReal.add_lt_add h1 h2
    _ = ENNReal.ofReal (2 * r) := by
        rw [← ENNReal.ofReal_add hr.le hr.le]
        congr 1
        ring

/-- **The small-ball data of a lifted chart**: for `r < r_*` the
control ball `U_r = B̃(ξ₀, r)`, the real distance `d̃.toReal`, `ρ = r` and `q + 1 = Q` satisfy the
abstract `ShellData` hypotheses, with a constant `Cv` independent of `r`. -/
theorem IsSmallBallRadius.exists_shellData (h : C.IsSmallBallRadius K₀ ξ₀ rstar) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ r : ℝ, 0 < r → r < rstar →
      ShellData volume (rsBall C.O w C.Xl ξ₀ r) (fun x y => (C.dl x y).toReal)
        (C.G.homogeneousDimension - 1) r Cv := by
  obtain ⟨Cv, hCv, hvol⟩ := h.volume_bound
  refine ⟨Cv, hCv, fun r hr hrr => ?_⟩
  have hQ : 1 ≤ C.G.homogeneousDimension := G2.homogeneousDimension_pos C.G
  have hQ' : C.G.homogeneousDimension - 1 + 1 = C.G.homogeneousDimension := Nat.sub_add_cancel hQ
  set S := rsBall C.O w C.Xl ξ₀ r with hSdef
  have hSK : S ⊆ K₀ := h.ball_subset r hr hrr
  have hSU : ∀ x ∈ S, x ∈ C.U := fun x hx => h.subset_U (hSK hx)
  have hSm : MeasurableSet S :=
    (hvol ξ₀ h.mem r hr (by linarith [h.pos])).1
  have hfin : ∀ x ∈ S, ∀ y ∈ S, C.dl x y ≠ ⊤ := fun x hx y hy =>
    C.dl_finite_on_U (hSU x hx) (hSU y hy)
  have hball : ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ 2 * r →
      S ∩ {y | (C.dl x y).toReal < t} = S ∩ rsBall C.O w C.Xl x t := by
    intro x hx t ht htr
    ext y
    constructor
    · rintro ⟨hy, hyt⟩
      exact ⟨hy, hy.1, (ENNReal.lt_ofReal_iff_toReal_lt (hfin x hx y hy)).mpr hyt⟩
    · rintro ⟨hy, -, hyt⟩
      exact ⟨hy, (ENNReal.lt_ofReal_iff_toReal_lt (hfin x hx y hy)).mp hyt⟩
  refine ⟨hSm, hr, hCv, fun x _ y _ => ENNReal.toReal_nonneg, fun x hx => ?_, fun x hx y hy => ?_,
    fun x hx y hy z hz => ?_, fun x hx y hy => ?_, fun x hx t ht htr => ?_,
    fun x hx t ht htr => ?_⟩
  · show (C.dl x x).toReal = 0
    rw [show C.dl x x = 0 from G1.controlDistance_self w C.Xl hx.1]
    rfl
  · exact congrArg ENNReal.toReal (G1.controlDistance_symm C.O w C.Xl x y)
  · have hxy := hfin x hx y hy
    have hyz := hfin y hy z hz
    have htri : C.dl x z ≤ C.dl x y + C.dl y z := G1.controlDistance_triangle C.O w C.Xl x y z
    show (C.dl x z).toReal ≤ (C.dl x y).toReal + (C.dl y z).toReal
    rw [← ENNReal.toReal_add hxy hyz]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hxy, hyz⟩) htri
  · exact ENNReal.toReal_lt_of_lt_ofReal (C.dl_lt_of_mem_rsBall hr hx hy)
  · rw [hball x hx t ht htr]
    exact hSm.inter (hvol x (hSK hx) t ht (by linarith [h.pos])).1
  · rw [hball x hx t ht htr, hQ']
    obtain ⟨hm, hf, hup⟩ := hvol x (hSK hx) t ht (by linarith [h.pos])
    calc volume (S ∩ rsBall C.O w C.Xl x t) ≤ volume (rsBall C.O w C.Xl x t) :=
          measure_mono inter_subset_right
      _ = ENNReal.ofReal (volume (rsBall C.O w C.Xl x t)).toReal := (ENNReal.ofReal_toReal hf).symm
      _ ≤ ENNReal.ofReal (Cv * t ^ C.G.homogeneousDimension) := ENNReal.ofReal_le_ofReal hup

end Bridge

end LiftedChart

end RothschildStein.P1
