-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LiftedChart
public import RothschildStein.P2.NormTransferWords

/-!
# Lifted norm transfer

For a lifted chart `C` (`RothschildStein.P1.LiftedChart`), a compact set `K` of centers in `C.U`
and the constants `r_*, δ, c_-, c_+` of the fiber bounds `C.ball_bounds`, the fiber volumes
`v_r(y) = |{h : (y, h) ∈ U_r}|` satisfy `v_r ≤ c_+ |U_r|/|V_r|` and `v_r ≥ c_- |U_r|/|V_r|` on
`V_{δ r}`, and for `ũ = u ∘ π`, every `j` and `1 ≤ p < ∞` (BB pp. 584–585, Thms 11.40–11.41,
(11.68)):
`c_-^{1/p} (|U_r|/|V_r|)^{1/p} ‖u‖_{W^{j,p}_X(V_{δ r})} ≤ ‖ũ‖_{W^{j,p}_{X̃}(U_r)}
  ≤ c_+^{1/p} (|U_r|/|V_r|)^{1/p} ‖u‖_{W^{j,p}_X(V_r)}`,
with the radius ratio `|U_r|/|V_r|` displayed (not absorbed into constants).

The Sobolev norms live on `Opens`; the balls `V_r, V_{δ r}, U_r` are therefore passed as
open sets together with the equalities identifying them with the control balls.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2
variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

theorem contDiff_joinPoint_zero :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => joinPoint x (0 : Fin m → ℝ)) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun l => ?_) i
  · simp only [joinPoint, Fin.addCases_left]
    exact contDiff_apply ℝ ℝ j
  · simp only [joinPoint, Fin.addCases_right]
    exact contDiff_const

/-- The base fields of a lifted chart are smooth on `Ω` (they are the base components of the
smooth lifted fields on the slice `t = 0`). -/
theorem liftedChart_contDiffOn_base (C : LiftedChart w s Ω hΩ X x₀ m) (i : Fin k) :
    ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω := by
  have h0 := C.lift_smooth i
  have hmaps : MapsTo (fun x : Fin n → ℝ => joinPoint x (0 : Fin m → ℝ)) Ω C.O := by
    intro x hx
    change basePoint (joinPoint x (0 : Fin m → ℝ)) ∈ Ω
    rw [basePoint_joinPoint]
    exact hx
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ => fun j : Fin n =>
        triangularLift X C.P i (joinPoint x (0 : Fin m → ℝ)) (Fin.castAdd m j)) Ω :=
    contDiffOn_pi.2 fun j =>
      (contDiff_apply ℝ ℝ (Fin.castAdd m j)).comp_contDiffOn
        (h0.comp contDiff_joinPoint_zero.contDiffOn hmaps)
  refine h1.congr fun x _ => ?_
  funext j
  simp [triangularLift, basePoint_joinPoint]

/-- A lifted open set inside the chart neighborhood `U` with a bound on its fiber volumes is a
`FiberSetting` over any open set containing its projection, by the `fiber_average` field. -/
theorem liftedChart_fiberSetting (C : LiftedChart w s Ω hΩ X x₀ m)
    (Uo : Opens (Fin (n + m) → ℝ)) (Vo : Opens (Fin n → ℝ))
    (hU : (Uo : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hproj : ∀ ξ ∈ (Uo : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vo : Set (Fin n → ℝ)))
    (hbdd : ∃ c : ℝ, 0 ≤ c ∧ ∀ z, fiberVolume (Uo : Set (Fin (n + m) → ℝ)) z ≤ ENNReal.ofReal c) :
    FiberSetting Uo Vo := by
  refine ⟨hproj, hbdd, fun φ => ?_⟩
  obtain ⟨F, hF⟩ := C.fiber_average ⟨C.U, C.isOpen_U⟩ rfl
  let φ' : TestFunction (⟨C.U, C.isOpen_U⟩ : Opens (Fin (n + m) → ℝ)) ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hU⟩
  have hfun : (fun x : Fin n → ℝ => ∫ t : Fin m → ℝ, φ (joinPoint x t)) =
      (F φ' : (Fin n → ℝ) → ℝ) := funext fun x => (hF φ' x).symm
  rw [hfun]
  exact (F φ').contDiff

theorem rsBall_mono {a n' : ℕ} (Ω' : Set (Fin n' → ℝ)) (p : Fin a → ℕ+)
    (Y : Fin a → (Fin n' → ℝ) → (Fin n' → ℝ)) (x : Fin n' → ℝ) {r r' : ℝ} (h : r ≤ r') :
    rsBall Ω' p Y x r ⊆ rsBall Ω' p Y x r' := by
  rintro y ⟨hy, hd⟩
  exact ⟨hy, lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal h)⟩

/-- The fiber bounds of `C.ball_bounds`, repackaged for the open sets `V_r, V_{δ r}, U_r`:
`FiberSetting` and `FiberBounds` with `cup = c_+ ρ`, `clow = c_- ρ`, `ρ = |U_r|/|V_r|`. -/
theorem exists_fiberBounds (C : LiftedChart w s Ω hΩ X x₀ m) {K : Set (Fin (n + m) → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ rstar δ cminus cplus : ℝ, 0 < rstar ∧ 0 < δ ∧ δ < 1 ∧ 0 < cminus ∧ 0 < cplus ∧
      ∀ η ∈ K, ∀ r : ℝ, 0 < r → r < rstar →
        ∀ (Vr Vδ : Opens (Fin n → ℝ)) (Ur : Opens (Fin (n + m) → ℝ)),
          (Vr : Set (Fin n → ℝ)) = rsBall Ω w X (basePoint η) r →
          (Vδ : Set (Fin n → ℝ)) = rsBall Ω w X (basePoint η) (δ * r) →
          (Ur : Set (Fin (n + m) → ℝ)) = rsBall C.O w C.Xl η r →
          (Ur : Set (Fin (n + m) → ℝ)) ⊆ C.U ∧
          0 < (volume (Ur : Set (Fin (n + m) → ℝ))).toReal /
              (volume (Vr : Set (Fin n → ℝ))).toReal ∧
          FiberSetting Ur Vr ∧
          FiberBounds (Ur : Set (Fin (n + m) → ℝ)) (Vr : Set (Fin n → ℝ)) (Vδ : Set (Fin n → ℝ))
            (cplus * ((volume (Ur : Set (Fin (n + m) → ℝ))).toReal /
              (volume (Vr : Set (Fin n → ℝ))).toReal))
            (cminus * ((volume (Ur : Set (Fin (n + m) → ℝ))).toReal /
              (volume (Vr : Set (Fin n → ℝ))).toReal)) := by
  obtain ⟨rstar, cv, Cv, δ, cf, Cf, hr, hcv, hCv, hδ0, hδ1, hcf, hCf, hall⟩ :=
    C.ball_bounds K hK hKU
  refine ⟨rstar, δ, cf, Cf, hr, hδ0, hδ1, hcf, hCf, ?_⟩
  intro η hη r hr0 hrr Vr Vδ Ur hVr hVδ hUr
  obtain ⟨hUlU, -, -, -, -, hUlpos, hVbpos, -, -, hdist, hup, hlow⟩ := hall η hη r hr0 hrr
  have hUlU' : (Ur : Set (Fin (n + m) → ℝ)) ⊆ C.U := by rw [hUr]; exact hUlU
  have hUO : (Ur : Set (Fin (n + m) → ℝ)) ⊆ C.O := fun ξ hξ =>
    C.closure_U_subset (subset_closure (hUlU' hξ))
  have hproj : ∀ ξ ∈ (Ur : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vr : Set (Fin n → ℝ)) := by
    intro ξ hξ
    have hξ' : ξ ∈ rsBall C.O w C.Xl η r := hUr ▸ hξ
    rw [hVr]
    exact ⟨hUO hξ, lt_of_le_of_lt (hdist ξ hξ') hξ'.2⟩
  have hVb : (volume (Vr : Set (Fin n → ℝ))).toReal =
      (volume (rsBall Ω w X (basePoint η) r)).toReal := by rw [hVr]
  have hUl : (volume (Ur : Set (Fin (n + m) → ℝ))).toReal =
      (volume (rsBall C.O w C.Xl η r)).toReal := by rw [hUr]
  have hρ : 0 < (volume (Ur : Set (Fin (n + m) → ℝ))).toReal /
      (volume (Vr : Set (Fin n → ℝ))).toReal := by
    rw [hVb, hUl]; exact div_pos hUlpos hVbpos
  have hup' : ∀ z, fiberVolume (Ur : Set (Fin (n + m) → ℝ)) z ≤
      ENNReal.ofReal (Cf * ((volume (Ur : Set (Fin (n + m) → ℝ))).toReal /
        (volume (Vr : Set (Fin n → ℝ))).toReal)) := by
    intro z
    rw [hVb, hUl, ← mul_div_assoc, hUr]
    exact hup z
  have hbdd : ∃ c : ℝ, 0 ≤ c ∧ ∀ z, fiberVolume (Ur : Set (Fin (n + m) → ℝ)) z ≤
      ENNReal.ofReal c := ⟨_, (mul_pos hCf hρ).le, hup'⟩
  have hS := liftedChart_fiberSetting C Ur Vr hUlU' hproj hbdd
  refine ⟨hUlU', hρ, hS, ?_⟩
  refine ⟨(mul_pos hCf hρ).le, (mul_pos hcf hρ).le, Ur.isOpen.measurableSet,
    Vr.isOpen.measurableSet, Vδ.isOpen.measurableSet, ?_, hproj, hup', ?_⟩
  · rw [hVδ, hVr]
    exact rsBall_mono Ω w X (basePoint η) (by nlinarith)
  · intro z hz
    rw [hVb, hUl, ← mul_div_assoc, hUr]
    exact hlow z (hVδ ▸ hz)

/-- The radius ratio `|U_r| / |V_r|` of a lifted open set over a base open set. -/
def ballRatio (Ur : Opens (Fin (n + m) → ℝ)) (Vr : Opens (Fin n → ℝ)) : ℝ :=
  (volume (Ur : Set (Fin (n + m) → ℝ))).toReal / (volume (Vr : Set (Fin n → ℝ))).toReal

/-- `V_r`, `V_{δ r}`, `U_r` are the control balls of radii `r, δ r, r` around `π η`, `π η`,
`η` (`Ur` over the lifted fields `C.Xl` on `C.O`). -/
def BallsAt (C : LiftedChart w s Ω hΩ X x₀ m) (η : Fin (n + m) → ℝ) (r δ : ℝ)
    (Vr Vδ : Opens (Fin n → ℝ)) (Ur : Opens (Fin (n + m) → ℝ)) : Prop :=
  (Vr : Set (Fin n → ℝ)) = rsBall Ω w X (basePoint η) r ∧
  (Vδ : Set (Fin n → ℝ)) = rsBall Ω w X (basePoint η) (δ * r) ∧
  (Ur : Set (Fin (n + m) → ℝ)) = rsBall C.O w C.Xl η r

theorem exists_fiberBounds' (C : LiftedChart w s Ω hΩ X x₀ m) {K : Set (Fin (n + m) → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ rstar δ cminus cplus : ℝ, 0 < rstar ∧ 0 < δ ∧ δ < 1 ∧ 0 < cminus ∧ 0 < cplus ∧
      ∀ η ∈ K, ∀ r : ℝ, 0 < r → r < rstar →
        ∀ (Vr Vδ : Opens (Fin n → ℝ)) (Ur : Opens (Fin (n + m) → ℝ)),
          BallsAt C η r δ Vr Vδ Ur →
          (Ur : Set (Fin (n + m) → ℝ)) ⊆ C.U ∧ 0 < ballRatio Ur Vr ∧ FiberSetting Ur Vr ∧
          FiberBounds (Ur : Set (Fin (n + m) → ℝ)) (Vr : Set (Fin n → ℝ)) (Vδ : Set (Fin n → ℝ))
            (cplus * ballRatio Ur Vr) (cminus * ballRatio Ur Vr) := by
  obtain ⟨rstar, δ, cminus, cplus, h1, h2, h3, h4, h5, h⟩ := exists_fiberBounds C hK hKU
  exact ⟨rstar, δ, cminus, cplus, h1, h2, h3, h4, h5, fun η hη r hr hrr Vr Vδ Ur hb =>
    h η hη r hr hrr Vr Vδ Ur hb.1 hb.2.1 hb.2.2⟩

/-- The control balls `V_r`, `V_{δ r}`, `U_r` give the hypotheses of the abstract transfer:
smoothness of the fields on the balls. -/
theorem liftedChart_hXt (C : LiftedChart w s Ω hΩ X x₀ m) (Ur : Opens (Fin (n + m) → ℝ))
    (hU : (Ur : Set (Fin (n + m) → ℝ)) ⊆ C.U) (i : Fin k) :
    ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X C.P i) (Ur : Set (Fin (n + m) → ℝ)) :=
  (C.lift_smooth i).mono fun _ hξ => C.closure_U_subset (subset_closure (hU hξ))

/-- The radius ratio `H(η, r) = |U_r| / |V_r|` of the lifted
ball `U_r = B̃(η, r)` over the base ball `V_r = B(π η, r)`. -/
def ballRatioAt (C : LiftedChart w s Ω hΩ X x₀ m) (η : Fin (n + m) → ℝ) (r : ℝ) : ℝ :=
  (volume (rsBall C.O w C.Xl η r)).toReal / (volume (rsBall Ω w X (basePoint η) r)).toReal

theorem ballRatio_eq_ballRatioAt {C : LiftedChart w s Ω hΩ X x₀ m} {η : Fin (n + m) → ℝ} {r δ : ℝ}
    {Vr Vδ : Opens (Fin n → ℝ)} {Ur : Opens (Fin (n + m) → ℝ)} (h : BallsAt C η r δ Vr Vδ Ur) :
    ballRatio Ur Vr = ballRatioAt C η r := by
  unfold ballRatio ballRatioAt
  rw [h.1, h.2.2]

/-- Upper comparison: at a fixed multiple
`A ≥ 1` of the radius, `H(η, A r) ≤ C₁ H(η, r)` with `C₁ = (C_v / c_v) A^Q`, by lifted volume
growth `c_v r^Q ≤ |U_r| ≤ C_v r^Q` and monotonicity of `|V_r|`. -/
theorem ballRatioAt_scale_le (C : LiftedChart w s Ω hΩ X x₀ m)
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) {A : ℝ} (hA : 1 ≤ A) :
    ∃ rstar C₁ : ℝ, 0 < rstar ∧ 0 < C₁ ∧ ∀ η ∈ K, ∀ r : ℝ, 0 < r → A * r < rstar →
      ballRatioAt C η (A * r) ≤ C₁ * ballRatioAt C η r := by
  obtain ⟨rstar, cv, Cv, δ, cf, Cf, hr, hcv, hCv, hδ0, hδ1, hcf, hCf, hall⟩ :=
    C.ball_bounds K hK hKU
  refine ⟨rstar, Cv * A ^ C.G.homogeneousDimension / cv, hr,
    div_pos (mul_pos hCv (pow_pos (zero_lt_one.trans_le hA) _)) hcv, ?_⟩
  intro η hη r hr0 hArr
  have hAr0 : 0 < A * r := mul_pos (zero_lt_one.trans_le hA) hr0
  have hrAr : r ≤ A * r := le_mul_of_one_le_left hr0.le hA
  have hrr : r < rstar := lt_of_le_of_lt hrAr hArr
  obtain ⟨-, -, -, -, hVfin, hUpos, hVpos, hUlow, -, -, -, -⟩ := hall η hη r hr0 hrr
  obtain ⟨-, -, -, -, hVfin', hUpos', hVpos', -, hUup', -, -, -⟩ := hall η hη (A * r) hAr0 hArr
  unfold ballRatioAt
  have hVmono : (volume (rsBall Ω w X (basePoint η) r)).toReal ≤
      (volume (rsBall Ω w X (basePoint η) (A * r))).toReal :=
    ENNReal.toReal_mono hVfin' (measure_mono (rsBall_mono Ω w X (basePoint η) hrAr))
  have hUAr_le : (volume (rsBall C.O w C.Xl η (A * r))).toReal ≤
      Cv * A ^ C.G.homogeneousDimension / cv * (volume (rsBall C.O w C.Xl η r)).toReal := by
    have h1 := hUup'
    have h2 := hUlow
    rw [mul_pow] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hcv]
    calc (volume (rsBall C.O w C.Xl η (A * r))).toReal * cv
        ≤ Cv * (A ^ C.G.homogeneousDimension * r ^ C.G.homogeneousDimension) * cv := by gcongr
      _ = Cv * A ^ C.G.homogeneousDimension * (cv * r ^ C.G.homogeneousDimension) := by ring
      _ ≤ _ := by gcongr
  calc (volume (rsBall C.O w C.Xl η (A * r))).toReal /
        (volume (rsBall Ω w X (basePoint η) (A * r))).toReal
      ≤ (volume (rsBall C.O w C.Xl η (A * r))).toReal /
        (volume (rsBall Ω w X (basePoint η) r)).toReal :=
        div_le_div_of_nonneg_left ENNReal.toReal_nonneg hVpos hVmono
    _ ≤ (Cv * A ^ C.G.homogeneousDimension / cv * (volume (rsBall C.O w C.Xl η r)).toReal) /
        (volume (rsBall Ω w X (basePoint η) r)).toReal :=
        div_le_div_of_nonneg_right hUAr_le hVpos.le
    _ = _ := by rw [mul_div_assoc]

end RothschildStein.P2
