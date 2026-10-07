-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderTransferOscillation
public import RothschildStein.P2.HolderTransferCampanato

/-!
# The reverse Hölder inequality

For `0 < t < s < R` in the fixed chart and `x ∈ V_{δ t}` a lift `ξ ∈ Ũ_t` exists (lower fiber
bound), `B̃(ξ, r) ⊆ Ũ_s` for `r ≤ s - t` and the lifted oscillation bound gives the Campanato
bound `inf_c ∫_{B(x, ϱ)} |f - c| ≤ C [f̃]_{α, U_s} ϱ^α |B(x, ϱ)|` (BB p. 598), with the original
local doubling converting `|B(x, ϱ/δ)|` into `|B(x, ϱ)|`. H2's Campanato converse
(`CampanatoData`) then bounds `[f]_{α, V_{δ t}}` and the sup norm is bounded by projection. The
local doubling is taken as the hypothesis `OriginalLocalDoubling` (its exact statement).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2
variable {n k m : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- (centres in `L`, scale `r_vol`, constant `D`): `|B(x, r)| > 0`, `|B(x, 2 r)| < ∞` and
`|B(x, 2 r)| ≤ D |B(x, r)|` for `x ∈ L`, `0 < r`, `2 r ≤ r_vol`. -/
def DoublingAt {n' k' : ℕ} (Ω' : Set (Fin n' → ℝ)) (w' : Fin k' → ℕ+)
    (X' : Fin k' → (Fin n' → ℝ) → (Fin n' → ℝ)) (L : Set (Fin n' → ℝ)) (rv D : ℝ) : Prop :=
  ∀ x ∈ L, ∀ r : ℝ, 0 < r → 2 * r ≤ rv →
    0 < volume (rsBall Ω' w' X' x r) ∧ volume (rsBall Ω' w' X' x (2 * r)) < ⊤ ∧
      volume (rsBall Ω' w' X' x (2 * r)) ≤ ENNReal.ofReal D * volume (rsBall Ω' w' X' x r)

/-- The original compact-centre local doubling (BB pp. 400, 405, Thms 9.1, 9.12) on a
patch `N`: for every compact set `L ⊆ N` of centres (a patch in the sense of local doubling) there are
`r_vol, D > 0` with `|B(x, r)| > 0`, `|B(x, 2 r)| < ∞` and `|B(x, 2 r)| ≤ D |B(x, r)|` for
`x ∈ L` and `0 < r ≤ r_vol / 2`. For the Hölder transfer `N = π(U)` is the projected chart
neighborhood. Used as the hypothesis `hdbl` of the `_of_doubling` results. -/
def OriginalLocalDoubling {n' k' : ℕ} (Ω' : Set (Fin n' → ℝ)) (w' : Fin k' → ℕ+)
    (X' : Fin k' → (Fin n' → ℝ) → (Fin n' → ℝ)) (N : Set (Fin n' → ℝ)) : Prop :=
  ∀ L : Set (Fin n' → ℝ), IsCompact L → L ⊆ N → ∃ rv D : ℝ, 0 < rv ∧ 0 < D ∧
    DoublingAt Ω' w' X' L rv D

/-- The truncated-metric data of a lifted chart: the carrier is `N = π(U)`. -/
def chartBaseData (C : LiftedChart w st Ω hΩ X x₀ m) : BaseData w X where
  Ω := Ω
  isOpen_Ω := hΩ
  cont := fun i => (liftedChart_contDiffOn_base C i).continuousOn
  N := basePoint '' C.U
  isOpen_N := by
    have hsurj : Function.Surjective (basePointCLM n m) :=
      fun y => ⟨joinPoint y (0 : Fin m → ℝ), basePoint_joinPoint y 0⟩
    exact (basePointCLM n m).isOpenMap hsurj C.U C.isOpen_U
  N_subset := by
    rintro _ ⟨ξ, hξ, rfl⟩
    exact holderTransfer_U_subset_O C hξ
  close := fun x hx ε hε => by
    obtain ⟨δ', hδ', h⟩ := exists_controlDistance_lt_of_euclid_close C hx hε
    exact ⟨δ', hδ', fun y hy => (h y hy).2⟩

theorem mem_rsBall_add {n' k' : ℕ} {Ω' : Set (Fin n' → ℝ)} {w' : Fin k' → ℕ+}
    {X' : Fin k' → (Fin n' → ℝ) → (Fin n' → ℝ)} {p z y : Fin n' → ℝ} {r₁ r₂ : ℝ}
    (hz : z ∈ rsBall Ω' w' X' p r₁) (hy : y ∈ Ω')
    (hzy : controlDistance Ω' w' X' z y < ENNReal.ofReal r₂) (h1 : 0 ≤ r₁) (h2 : 0 ≤ r₂) :
    y ∈ rsBall Ω' w' X' p (r₁ + r₂) := by
  refine ⟨hy, ?_⟩
  calc controlDistance Ω' w' X' p y ≤ controlDistance Ω' w' X' p z + controlDistance Ω' w' X' z y :=
        G1.controlDistance_triangle Ω' w' X' p z y
    _ < ENNReal.ofReal r₁ + ENNReal.ofReal r₂ := ENNReal.add_lt_add hz.2 hzy
    _ = ENNReal.ofReal (r₁ + r₂) := (ENNReal.ofReal_add h1 h2).symm

/-- Iterated doubling: `|B(x, 2^j r)| ≤ D^j |B(x, r)|` while `2^j r ≤ r_vol`. -/
theorem iterate_doubling {n' k' : ℕ} {Ω' : Set (Fin n' → ℝ)} {w' : Fin k' → ℕ+}
    {X' : Fin k' → (Fin n' → ℝ) → (Fin n' → ℝ)} {x : Fin n' → ℝ} {rv D : ℝ}
    (hdb : ∀ r : ℝ, 0 < r → 2 * r ≤ rv →
      volume (rsBall Ω' w' X' x (2 * r)) ≤ ENNReal.ofReal D * volume (rsBall Ω' w' X' x r))
    {r : ℝ} (hr : 0 < r) :
    ∀ j : ℕ, 2 ^ j * r ≤ rv →
      volume (rsBall Ω' w' X' x (2 ^ j * r)) ≤
        ENNReal.ofReal D ^ j * volume (rsBall Ω' w' X' x r)
  | 0, _ => by simp
  | j + 1, hj => by
    have hj' : 2 ^ j * r ≤ rv := by
      have : 2 ^ j * r ≤ 2 ^ (j + 1) * r :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ j)) hr.le
      linarith
    have hpos : 0 < 2 ^ j * r := by positivity
    have h2 : 2 * (2 ^ j * r) ≤ rv := by rw [← mul_assoc, ← pow_succ']; exact hj
    have := hdb (2 ^ j * r) hpos h2
    rw [show 2 ^ (j + 1) * r = 2 * (2 ^ j * r) by ring, pow_succ']
    calc volume (rsBall Ω' w' X' x (2 * (2 ^ j * r)))
        ≤ ENNReal.ofReal D * volume (rsBall Ω' w' X' x (2 ^ j * r)) := this
      _ ≤ ENNReal.ofReal D * (ENNReal.ofReal D ^ j * volume (rsBall Ω' w' X' x r)) :=
        mul_le_mul' le_rfl (iterate_doubling hdb hr j hj')
      _ = _ := by rw [mul_assoc]

/-- The Hölder seminorm is bounded by any real constant for which the pointwise bound holds. -/
theorem holderSeminorm_le_of_bound {n' : ℕ} {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ}
    (hα : 0 ≤ α) {V : Set (Fin n' → ℝ)} {f : (Fin n' → ℝ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ V, ∀ y ∈ V, d x y ≠ ⊤ → |f x - f y| ≤ C * (d x y).toReal ^ α) :
    holderSeminorm d α V f ≤ ENNReal.ofReal C := by
  refine sInf_le ⟨ENNReal.ofReal_lt_top, fun x hx y hy hxy => ?_⟩
  have hxy' : d x y ≠ ⊤ := hxy.ne
  have hpow : d x y ^ α = ENNReal.ofReal ((d x y).toReal ^ α) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hxy']
    exact ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα
  rw [hpow, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy hxy')

/-- The Campanato data of a function `f` with `f ∘ π` of finite
`C^α` norm on `U_s = B̃(η, s)`, for the centre set `S₀ = B(π η, δ t)`, the enlarged set
`W₀ = B(π η, δ s)`, `0 < t < s`, `6 ρ = ϖ ≤ min (δ (s - t), 1, r_vol / 2^k)`, `δ 2^k ≥ 1`, the
doubling constant `C_D = max D 2` and `H = (δ^{-α} D^k / c_f) [f̃]_{α, U_s}`; and the sup bound
`|f| ≤ ‖f̃‖_∞` on `W₀`. -/
theorem campanatoData_of_chart (C : LiftedChart w st Ω hΩ X x₀ m) {α : ℝ} (hα : 0 < α)
    {K K₁ : Set (Fin (n + m) → ℝ)} (hK₁c : IsCompact K₁) (hK₁U : K₁ ⊆ C.U) (hKK₁ : K ⊆ K₁)
    {t₁ rstar δ cf rv D : ℝ} {kk : ℕ}
    (ht₁ : ∀ η ∈ K, ∀ ζ, C.dl η ζ < ENNReal.ofReal t₁ → ζ ∈ K₁)
    (hosc : LiftedOscFacts C K₁ rstar δ cf) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hcf : 0 < cf)
    (hD : 0 < D) (hdb : DoublingAt Ω w X (basePoint '' K₁) rv D) (hkk : 1 ≤ δ * 2 ^ kk)
    {t s : ℝ} (ht : 0 < t) (hts : t < s) (hs : s < min rstar t₁)
    {η : Fin (n + m) → ℝ} (hη : η ∈ K) {f : (Fin n → ℝ) → ℝ}
    (hsem : holderSeminorm C.dl α (rsBall C.O w C.Xl η s) (fun ξ => f (basePoint ξ)) ≠ ⊤)
    (hsup : (⨆ x : rsBall C.O w C.Xl η s, ENNReal.ofReal |f (basePoint (x : Fin (n + m) → ℝ))|) ≠ ⊤)
    {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hϖδ : ϖ ≤ δ * (s - t)) (hϖrv : 2 ^ kk * ϖ ≤ rv) :
    CampanatoData (chartBaseData C) f α (rsBall Ω w X (basePoint η) (δ * t))
        (rsBall Ω w X (basePoint η) (δ * s)) (ϖ / 6) (max D 2)
        (δ⁻¹ ^ α * D ^ kk / cf *
          (holderSeminorm C.dl α (rsBall C.O w C.Xl η s) (fun ξ => f (basePoint ξ))).toReal) ∧
      ∀ y ∈ rsBall Ω w X (basePoint η) (δ * s),
        |f y| ≤ (⨆ x : rsBall C.O w C.Xl η s, ENNReal.ofReal |f (basePoint (x : Fin (n + m) → ℝ))|).toReal := by
  classical
  set p := basePoint η with hp
  set Us := rsBall C.O w C.Xl η s with hUs
  set M₀ : ℝ := (holderSeminorm C.dl α Us (fun ξ => f (basePoint ξ))).toReal with hM₀
  have hηK₁ : η ∈ K₁ := hKK₁ hη
  have hs0 : 0 < s := ht.trans hts
  have hsr : s < rstar := lt_of_lt_of_le hs (min_le_left _ _)
  have hst₁ : s < t₁ := lt_of_lt_of_le hs (min_le_right _ _)
  have hδs : δ * s < rstar := lt_of_le_of_lt (mul_le_of_le_one_left hs0.le hδ1.le) hsr
  have hδtδs : δ * t ≤ δ * s := mul_le_mul_of_nonneg_left hts.le hδ0.le
  have hδst : δ * t + ϖ ≤ δ * s := by have := mul_sub δ s t; linarith
  -- facts at the centre η
  obtain ⟨hUsU, hWm, -, -, -, hlift_s, -⟩ := hosc η hηK₁ s hs0 hsr
  obtain ⟨-, -, -, -, hWfin, -, -⟩ := hosc η hηK₁ (δ * s) (mul_pos hδ0 hs0) hδs
  have hUsopen : IsOpen Us := isOpen_rsBall_lifted C hUsU
  have hfcontL : ContinuousOn (fun ξ => f (basePoint ξ)) Us :=
    continuousOn_of_holderSeminorm_ne_top C hUsopen hUsU hα hsem
  have hWN : rsBall Ω w X p (δ * s) ⊆ (chartBaseData C).N := by
    intro x hx
    obtain ⟨ζ, hζ, rfl⟩ := hlift_s x hx
    exact ⟨ζ, hUsU hζ, rfl⟩
  have hfcont : ContinuousOn f (rsBall Ω w X p (δ * s)) :=
    continuousOn_of_lifts C hUsopen hUsU hα hlift_s hsem
  set Sup : ℝ := (⨆ x : Us, ENNReal.ofReal |f (basePoint (x : Fin (n + m) → ℝ))|).toReal with hSup
  have hbdd : ∀ y ∈ rsBall Ω w X p (δ * s), |f y| ≤ Sup := by
    intro y hy
    obtain ⟨ζ, hζ, rfl⟩ := hlift_s y hy
    have h1 : ENNReal.ofReal |f (basePoint ζ)| ≤ ⨆ x : Us, ENNReal.ofReal |f (basePoint (x : Fin (n + m) → ℝ))| :=
      le_iSup (fun x : Us => ENNReal.ofReal |f (basePoint (x : Fin (n + m) → ℝ))|) ⟨ζ, hζ⟩
    have := ENNReal.toReal_mono hsup h1
    rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this
  refine ⟨?_, hbdd⟩
  -- lifts of the centre set
  have hlift_t : ∀ x ∈ rsBall Ω w X p (δ * t), ∃ ζ ∈ K₁, ζ ∈ rsBall C.O w C.Xl η t ∧
      basePoint ζ = x := by
    intro x hx
    have htr : t < rstar := hts.trans hsr
    obtain ⟨-, -, -, -, -, hl, -⟩ := hosc η hηK₁ t ht htr
    obtain ⟨ζ, hζ, hζx⟩ := hl x hx
    exact ⟨ζ, ht₁ η hη ζ (lt_of_lt_of_le hζ.2
      (ENNReal.ofReal_le_ofReal (by linarith))), hζ, hζx⟩
  have hSW : rsBall Ω w X p (δ * t) ⊆ rsBall Ω w X p (δ * s) := rsBall_mono Ω w X p hδtδs
  -- small balls around the centre set stay in `W₀`
  have hballW : ∀ z ∈ rsBall Ω w X p (δ * t), ∀ r : ℝ, 0 < r → r ≤ ϖ →
      rsBall Ω w X z r ⊆ rsBall Ω w X p (δ * s) := by
    intro z hz r hr hrϖ y hy
    have := mem_rsBall_add hz hy.1 hy.2 (mul_pos hδ0 ht).le hr.le
    exact rsBall_mono Ω w X p (by linarith) this
  refine ⟨div_pos hϖ0 (by norm_num), by linarith, lt_max_of_lt_right one_lt_two, ?_, ?_, hSW, hWN,
    hWm, lt_top_iff_ne_top.2 hWfin, ?_, ?_, ?_, ?_, hfcont, ⟨Sup, hbdd⟩, ?_⟩
  · exact mul_nonneg (div_nonneg (mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hδ0.le) _)
      (pow_nonneg hD.le _)) hcf.le) ENNReal.toReal_nonneg
  · exact isOpen_rsBall_of_close (chartBaseData C).N_subset (chartBaseData C).close'
      (hSW.trans hWN)
  · -- incl
    intro z hz y hyN hd
    have h6 : 6 * (ϖ / 6) = ϖ := by ring
    rw [h6] at hd
    have := mem_rsBall_add hz ((chartBaseData C).N_subset hyN) hd (mul_pos hδ0 ht).le hϖ0.le
    exact rsBall_mono Ω w X p hδst this
  · -- ball_sub
    intro z hz r hr hr6
    have h6 : 6 * (ϖ / 6) = ϖ := by ring
    rw [h6] at hr6
    exact (hballW z hz r hr hr6).trans hWN
  · -- doubling
    intro z hz r hr hr6
    have h6 : 6 * (ϖ / 6) = ϖ := by ring
    rw [h6] at hr6
    obtain ⟨ζ, hζK₁, -, hζz⟩ := hlift_t z hz
    have hzL : z ∈ basePoint '' K₁ := ⟨ζ, hζK₁, hζz⟩
    have hrv : 2 * (r / 2) ≤ rv := by
      have : ϖ ≤ 2 ^ kk * ϖ := le_mul_of_one_le_left hϖ0.le (one_le_pow₀ (by norm_num))
      linarith
    obtain ⟨hpos, hfin, hle⟩ := hdb z hzL (r / 2) (half_pos hr) hrv
    rw [show 2 * (r / 2) = r by ring] at hfin hle
    refine ⟨lt_of_lt_of_le hpos (measure_mono (rsBall_mono Ω w X z (half_le_self hr.le))),
      hfin, hle.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)⟩
  · -- compact
    refine ⟨basePoint '' K₁, hK₁c.image continuous_basePoint, ?_, ?_⟩
    · rintro _ ⟨ξ, hξ, rfl⟩
      exact ⟨ξ, hK₁U hξ, rfl⟩
    · intro z hz
      obtain ⟨ζ, hζK₁, -, hζz⟩ := hlift_t z hz
      exact ⟨ζ, hζK₁, hζz⟩
  · -- oscillation
    intro z hz r hr hr6
    have h6 : 6 * (ϖ / 6) = ϖ := by ring
    rw [h6] at hr6
    obtain ⟨ζ, hζK₁, hζt, rfl⟩ := hlift_t z hz
    have hr's : r / δ ≤ s - t := by
      rw [div_le_iff₀ hδ0]
      linarith
    have hr'0 : 0 < r / δ := div_pos hr hδ0
    have hr'r : r / δ < rstar := by linarith
    have hrr : r < rstar := by
      have : r ≤ r / δ := by
        rw [le_div_iff₀ hδ0]
        nlinarith
      linarith
    have hδr' : δ * (r / δ) = r := by field_simp
    obtain ⟨-, -, -, -, hvfin_r, -, -⟩ := hosc ζ hζK₁ r hr hrr
    obtain ⟨-, -, -, -, hvfin, -, hosc'⟩ := hosc ζ hζK₁ (r / δ) hr'0 hr'r
    -- the pointwise Hölder bound on the lifted ball
    have hζUs : ζ ∈ Us := rsBall_mono C.O w C.Xl η (by linarith : t ≤ s) hζt
    have hbound : ∀ ξ ∈ rsBall C.O w C.Xl ζ (r / δ),
        |f (basePoint ξ) - f (basePoint ζ)| ≤ M₀ * (r / δ) ^ α := by
      intro ξ hξ
      have hξUs : ξ ∈ Us :=
        rsBall_mono C.O w C.Xl η (by linarith : t + r / δ ≤ s)
          (mem_rsBall_add hζt hξ.1 hξ.2 ht.le hr'0.le)
      have hd : C.dl ζ ξ < ENNReal.ofReal (r / δ) := hξ.2
      have hdfin : C.dl ξ ζ ≠ ⊤ := by
        rw [show C.dl ξ ζ = C.dl ζ ξ from G1.controlDistance_symm C.O w C.Xl ξ ζ]
        exact ne_top_of_lt (hd.trans ENNReal.ofReal_lt_top)
      have habs := abs_sub_le_of_holderSeminorm hα.le hsem hξUs hζUs hdfin
      have hdt : (C.dl ξ ζ).toReal ≤ r / δ := by
        rw [show C.dl ξ ζ = C.dl ζ ξ from G1.controlDistance_symm C.O w C.Xl ξ ζ]
        exact (ENNReal.toReal_lt_of_lt_ofReal hd).le
      have hpow : (C.dl ξ ζ).toReal ^ α ≤ (r / δ) ^ α :=
        Real.rpow_le_rpow ENNReal.toReal_nonneg hdt hα.le
      calc |f (basePoint ξ) - f (basePoint ζ)|
          ≤ M₀ * (C.dl ξ ζ).toReal ^ α := habs
        _ ≤ M₀ * (r / δ) ^ α := mul_le_mul_of_nonneg_left hpow ENNReal.toReal_nonneg
    have hmeas : AEStronglyMeasurable f
        (volume.restrict (rsBall Ω w X (basePoint ζ) (δ * (r / δ)))) := by
      rw [hδr']
      exact (hfcont.aestronglyMeasurable hWm).mono_measure
        (Measure.restrict_mono (hballW _ hz r hr hr6) le_rfl)
    have key := hosc' f (f (basePoint ζ)) (M₀ * (r / δ) ^ α)
      (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hr'0.le _)) hmeas hbound
    rw [hδr'] at key
    refine ⟨f (basePoint ζ), key.trans ?_⟩
    -- iterated doubling for the volume ratio
    have hzL : basePoint ζ ∈ basePoint '' K₁ := ⟨ζ, hζK₁, rfl⟩
    have hdb' : ∀ r₀ : ℝ, 0 < r₀ → 2 * r₀ ≤ rv →
        volume (rsBall Ω w X (basePoint ζ) (2 * r₀)) ≤
          ENNReal.ofReal D * volume (rsBall Ω w X (basePoint ζ) r₀) :=
      fun r₀ h0 h2 => (hdb _ hzL r₀ h0 h2).2.2
    have hrle : 2 ^ kk * r ≤ rv := by
      have : 2 ^ kk * r ≤ 2 ^ kk * ϖ := mul_le_mul_of_nonneg_left hr6 (by positivity)
      linarith
    have hr'le : r / δ ≤ 2 ^ kk * r := by
      rw [div_le_iff₀ hδ0]
      nlinarith
    have hvol : volume (rsBall Ω w X (basePoint ζ) (r / δ)) ≤
        ENNReal.ofReal D ^ kk * volume (rsBall Ω w X (basePoint ζ) r) :=
      (measure_mono (rsBall_mono Ω w X (basePoint ζ) hr'le)).trans
        (iterate_doubling hdb' hr kk hrle)
    have hvolr : (volume (rsBall Ω w X (basePoint ζ) (r / δ))).toReal ≤
        D ^ kk * (volume (rsBall Ω w X (basePoint ζ) r)).toReal := by
      have hne : ENNReal.ofReal D ^ kk * volume (rsBall Ω w X (basePoint ζ) r) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hvfin_r
      have := ENNReal.toReal_mono hne hvol
      rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hD.le] at this
    have hrpow : (r / δ) ^ α = r ^ α * δ⁻¹ ^ α := by
      rw [div_eq_mul_inv, Real.mul_rpow hr.le (inv_nonneg.2 hδ0.le)]
    have hnn : 0 ≤ M₀ * (r / δ) ^ α / cf :=
      div_nonneg (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hr'0.le _)) hcf.le
    calc M₀ * (r / δ) ^ α / cf * (volume (rsBall Ω w X (basePoint ζ) (r / δ))).toReal
        ≤ M₀ * (r / δ) ^ α / cf * (D ^ kk * (volume (rsBall Ω w X (basePoint ζ) r)).toReal) :=
          mul_le_mul_of_nonneg_left hvolr hnn
      _ = δ⁻¹ ^ α * D ^ kk / cf * M₀ * r ^ α *
            (volume (rsBall Ω w X (basePoint ζ) r)).toReal := by
          rw [hrpow]
          ring

/-- The sup part of the Hölder norm over a set of base points all of which have a lift in `A`. -/
theorem iSup_comp_basePoint_le {A : Set (Fin (n + m) → ℝ)} {S : Set (Fin n → ℝ)}
    (hS : ∀ x ∈ S, ∃ ζ ∈ A, basePoint ζ = x) (f : (Fin n → ℝ) → ℝ) :
    (⨆ x : S, ENNReal.ofReal |f x|) ≤
      ⨆ ζ : A, ENNReal.ofReal |f (basePoint (ζ : Fin (n + m) → ℝ))| := by
  refine iSup_le fun x => ?_
  obtain ⟨ζ, hζ, hζx⟩ := hS x.1 x.2
  have := le_iSup (fun ζ : A => ENNReal.ofReal |f (basePoint (ζ : Fin (n + m) → ℝ))|) ⟨ζ, hζ⟩
  simpa only [hζx] using this

/-- The degenerate case `n = 0` (the base is a point). -/
theorem holderTransfer_reverse_of_zero (C : LiftedChart w st Ω hΩ X x₀ m) (hn : n = 0) {α : ℝ}
    (hα : 0 ≤ α) {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ rstar δ : ℝ, 0 < rstar ∧ 0 < δ ∧ δ < 1 ∧ ∀ t s : ℝ, 0 < t → t < s → s < rstar →
      ∃ Cst : ℝ, 0 < Cst ∧ ∀ η ∈ K, ∀ f : (Fin n → ℝ) → ℝ,
        holderENorm (controlDistance Ω w X) α (rsBall Ω w X (basePoint η) (δ * t)) f ≤
          ENNReal.ofReal Cst *
            holderENorm C.dl α (rsBall C.O w C.Xl η s) (fun ξ => f (basePoint ξ)) := by
  obtain ⟨rstar, δ, cf, hr, hδ0, hδ1, hcf, hosc⟩ := lifted_oscillation C hK hKU
  refine ⟨rstar, δ, hr, hδ0, hδ1, fun t s ht hts hs => ⟨1, one_pos, fun η hη f => ?_⟩⟩
  have hsub : ∀ x y : Fin n → ℝ, x = y := fun x y => by
    funext i
    have := i.2
    exact (by omega : False).elim
  obtain ⟨-, -, -, -, -, hlift, -⟩ := hosc η hη t ht (hts.trans hs)
  have hlift' : ∀ x ∈ rsBall Ω w X (basePoint η) (δ * t),
      ∃ ζ ∈ rsBall C.O w C.Xl η s, basePoint ζ = x := by
    intro x hx
    obtain ⟨ζ, hζ, hζx⟩ := hlift x hx
    exact ⟨ζ, rsBall_mono C.O w C.Xl η hts.le hζ, hζx⟩
  have hsem : holderSeminorm (controlDistance Ω w X) α
      (rsBall Ω w X (basePoint η) (δ * t)) f ≤ ENNReal.ofReal 0 := by
    refine holderSeminorm_le_of_bound hα le_rfl ?_
    intro x _ y _ _
    rw [hsub x y]
    simp
  rw [ENNReal.ofReal_one, one_mul]
  calc holderENorm (controlDistance Ω w X) α (rsBall Ω w X (basePoint η) (δ * t)) f
      = (⨆ x : rsBall Ω w X (basePoint η) (δ * t), ENNReal.ofReal |f x|) +
          holderSeminorm (controlDistance Ω w X) α (rsBall Ω w X (basePoint η) (δ * t)) f := rfl
    _ ≤ (⨆ ζ : rsBall C.O w C.Xl η s, ENNReal.ofReal |f (basePoint (ζ : Fin (n + m) → ℝ))|) + 0 :=
        add_le_add (iSup_comp_basePoint_le hlift' f) (by simpa using hsem)
    _ = ⨆ ζ : rsBall C.O w C.Xl η s, ENNReal.ofReal |f (basePoint (ζ : Fin (n + m) → ℝ))| :=
        add_zero _
    _ ≤ holderENorm C.dl α (rsBall C.O w C.Xl η s) (fun ξ => f (basePoint ξ)) := le_self_add

/-- (Assuming local doubling.) The certificate of H2's patch
hypotheses and the Campanato oscillation bound, uniform in the centres `η ∈ K` and in `f`: for
`0 < t < s < r_*` there are `ρ, C_D, Q` such that for every `f` with `f ∘ π` of finite `C^α` norm on
`U_s = B̃(η, s)`, the data `CampanatoData` (the patch `(S₀, W₀, ρ, C_D)` with `S₀ = B(π η, δ t)`,
`W₀ = B(π η, δ s)`, doubling, compact closure, no atoms, and the oscillation bound
`inf_c ∫_{B(z, r)} |f - c| ≤ Q [f̃]_{α, U_s} r^α |B(z, r)|` for `z ∈ S₀`, `r ≤ 6 ρ`) holds, and
`|f| ≤ ‖f̃‖_∞` on `W₀`. -/
theorem holderTransfer_campanato_of_doubling (C : LiftedChart w st Ω hΩ X x₀ m) {α : ℝ}
    (hα : 0 < α) {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U)
    (hdbl : OriginalLocalDoubling Ω w X (basePoint '' C.U)) :
    ∃ rstar δ : ℝ, 0 < rstar ∧ 0 < δ ∧ δ < 1 ∧ ∀ t s : ℝ, 0 < t → t < s → s < rstar →
      ∃ ρ Cd Q : ℝ, 0 < ρ ∧ 6 * ρ ≤ 1 ∧ 1 < Cd ∧ 0 ≤ Q ∧ ∀ η ∈ K, ∀ f : (Fin n → ℝ) → ℝ,
        holderENorm C.dl α (rsBall C.O w C.Xl η s) (fun ξ => f (basePoint ξ)) ≠ ⊤ →
        CampanatoData (chartBaseData C) f α (rsBall Ω w X (basePoint η) (δ * t))
            (rsBall Ω w X (basePoint η) (δ * s)) ρ Cd
            (Q * (holderSeminorm C.dl α (rsBall C.O w C.Xl η s)
              (fun ξ => f (basePoint ξ))).toReal) ∧
          ∀ y ∈ rsBall Ω w X (basePoint η) (δ * s),
            |f y| ≤ (⨆ x : rsBall C.O w C.Xl η s,
              ENNReal.ofReal |f (basePoint (x : Fin (n + m) → ℝ))|).toReal := by
  obtain ⟨K₁, hK₁, hK₁U, hKK₁, t₁, ht₁0, ht₁⟩ := exists_compact_lifts C hK hKU
  obtain ⟨rstar₁, δ, cf, hr1, hδ0, hδ1, hcf, hosc⟩ := lifted_oscillation C hK₁ hK₁U
  obtain ⟨rv, D, hrv, hD, hdb⟩ :=
    hdbl (basePoint '' K₁) (hK₁.image continuous_basePoint) (image_mono hK₁U)
  obtain ⟨kk, hkk⟩ := pow_unbounded_of_one_lt (δ⁻¹) one_lt_two
  have hkk1 : 1 ≤ δ * 2 ^ kk :=
    calc (1 : ℝ) = δ * δ⁻¹ := (mul_inv_cancel₀ hδ0.ne').symm
      _ ≤ δ * 2 ^ kk := mul_le_mul_of_nonneg_left hkk.le hδ0.le
  refine ⟨min rstar₁ t₁, δ, lt_min hr1 ht₁0, hδ0, hδ1, fun t s ht hts hs => ?_⟩
  set ϖ : ℝ := min (min (δ * (s - t)) 1) (rv / 2 ^ kk) with hϖ
  have h2kk : (0 : ℝ) < 2 ^ kk := by positivity
  have hϖ0 : 0 < ϖ :=
    lt_min (lt_min (mul_pos hδ0 (sub_pos.2 hts)) one_pos) (div_pos hrv h2kk)
  have hϖ1 : ϖ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hϖδ : ϖ ≤ δ * (s - t) := (min_le_left _ _).trans (min_le_left _ _)
  have hϖrv : 2 ^ kk * ϖ ≤ rv := by
    have h1 : ϖ ≤ rv / 2 ^ kk := min_le_right _ _
    rw [le_div_iff₀ h2kk] at h1
    linarith
  have hQc0 : 0 ≤ δ⁻¹ ^ α * D ^ kk / cf :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hδ0.le) _) (pow_nonneg hD.le _)) hcf.le
  refine ⟨ϖ / 6, max D 2, δ⁻¹ ^ α * D ^ kk / cf, div_pos hϖ0 (by norm_num), by linarith,
    lt_max_of_lt_right one_lt_two, hQc0, fun η hη f hf => ?_⟩
  have hne : (⨆ x : rsBall C.O w C.Xl η s,
      ENNReal.ofReal |f (basePoint (x : Fin (n + m) → ℝ))|) +
      holderSeminorm C.dl α (rsBall C.O w C.Xl η s) (fun ξ => f (basePoint ξ)) ≠ ⊤ := hf
  obtain ⟨hsup, hsem⟩ := ENNReal.add_ne_top.mp hne
  exact campanatoData_of_chart C hα hK₁ hK₁U hKK₁ ht₁ hosc hδ0 hδ1 hcf hD hdb
    hkk1 ht hts hs hη hsem hsup hϖ0 hϖ1 hϖδ hϖrv

/-- (Positive dimension, assuming local doubling.) The reverse
inequality `‖f‖_{C^α(V_{δ t})} ≤ C ‖f̃‖_{C^α(U_s)}` for the sup norm and the Hölder seminorm, for
`0 < t < s < r_*`, uniformly over the centres `η ∈ K` and all `f`. -/
theorem holderTransfer_reverse_of_pos (C : LiftedChart w st Ω hΩ X x₀ m) (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U)
    (hdbl : OriginalLocalDoubling Ω w X (basePoint '' C.U)) :
    ∃ rstar δ : ℝ, 0 < rstar ∧ 0 < δ ∧ δ < 1 ∧ ∀ t s : ℝ, 0 < t → t < s → s < rstar →
      ∃ Cst : ℝ, 0 < Cst ∧ ∀ η ∈ K, ∀ f : (Fin n → ℝ) → ℝ,
        holderENorm (controlDistance Ω w X) α (rsBall Ω w X (basePoint η) (δ * t)) f ≤
          ENNReal.ofReal Cst *
            holderENorm C.dl α (rsBall C.O w C.Xl η s) (fun ξ => f (basePoint ξ)) := by
  obtain ⟨rstar, δ, hr, hδ0, hδ1, hP⟩ := holderTransfer_campanato_of_doubling C hα hK hKU hdbl
  refine ⟨rstar, δ, hr, hδ0, hδ1, fun t s ht hts hs => ?_⟩
  obtain ⟨ρ, Cd, Qc, hρ0, hρ6, hCd, hQc0, hdata⟩ := hP t s ht hts hs
  have hCd0 : 0 < Cd := lt_trans zero_lt_one hCd
  have hhalf : (1 / 2 : ℝ) ^ α ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) hα.le
  set KC : ℝ := 4 * ((Cd + 1) / (1 - (1 / 2 : ℝ) ^ α) + Cd) with hKC
  have hKC0 : 0 ≤ KC := by
    have : 0 ≤ (Cd + 1) / (1 - (1 / 2 : ℝ) ^ α) :=
      div_nonneg (by linarith) (by linarith)
    rw [hKC]
    positivity
  set Kfar : ℝ := 2 * (3 * ρ)⁻¹ ^ α with hKfar
  have hKfar0 : 0 ≤ Kfar := by rw [hKfar]; positivity
  have hCst : 0 < 1 + KC * Qc + Kfar := by
    have := mul_nonneg hKC0 hQc0
    linarith
  refine ⟨1 + KC * Qc + Kfar, hCst, fun η hη f => ?_⟩
  set Us := rsBall C.O w C.Xl η s with hUs
  by_cases htop : holderENorm C.dl α Us (fun ξ => f (basePoint ξ)) = ⊤
  · rw [htop, ENNReal.mul_top (by simpa using hCst)]
    exact le_top
  have hne : (⨆ x : Us, ENNReal.ofReal |f (basePoint (x : Fin (n + m) → ℝ))|) +
      holderSeminorm C.dl α Us (fun ξ => f (basePoint ξ)) ≠ ⊤ := htop
  obtain ⟨hsup, hsem⟩ := ENNReal.add_ne_top.mp hne
  obtain ⟨hcd, hbdd⟩ := hdata η hη f htop
  have hbd := hcd.holder_bound hn hα hα1
  set M₀ : ℝ := (holderSeminorm C.dl α Us (fun ξ => f (basePoint ξ))).toReal with hM₀
  set Sup : ℝ := (⨆ x : Us, ENNReal.ofReal |f (basePoint (x : Fin (n + m) → ℝ))|).toReal
    with hSup
  have hM₀0 : 0 ≤ M₀ := ENNReal.toReal_nonneg
  have hSup0 : 0 ≤ Sup := ENNReal.toReal_nonneg
  set S₀ := rsBall Ω w X (basePoint η) (δ * t) with hS₀
  have hS₀W : S₀ ⊆ rsBall Ω w X (basePoint η) (δ * s) :=
    rsBall_mono Ω w X _ (mul_le_mul_of_nonneg_left hts.le hδ0.le)
  have hKCQ0 : 0 ≤ KC * Qc := mul_nonneg hKC0 hQc0
  have hsemS : holderSeminorm (controlDistance Ω w X) α S₀ f ≤
      ENNReal.ofReal (max (KC * (Qc * M₀)) (Kfar * Sup)) := by
    refine holderSeminorm_le_of_bound hα.le (le_max_of_le_left
      (mul_nonneg hKC0 (mul_nonneg hQc0 hM₀0))) ?_
    intro x hx y hy hxy
    by_cases hnear : controlDistance Ω w X x y ≤ ENNReal.ofReal (3 * ρ)
    · have h1 := hbd x hx y hy hnear
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      exact le_max_left _ _
    · have hnear' := not_le.mp hnear
      have hd3 : 3 * ρ < (controlDistance Ω w X x y).toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hxy).mp hnear'
      have hxS := hbdd x (hS₀W hx)
      have hyS := hbdd y (hS₀W hy)
      have hdpow : (0 : ℝ) ≤ (controlDistance Ω w X x y).toReal ^ α :=
        Real.rpow_nonneg ENNReal.toReal_nonneg _
      have h3ρ : 0 < 3 * ρ := by positivity
      have hone : 1 ≤ ((controlDistance Ω w X x y).toReal / (3 * ρ)) ^ α :=
        Real.one_le_rpow ((one_le_div h3ρ).2 hd3.le) hα.le
      calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ 2 * Sup := by linarith
        _ ≤ 2 * Sup * ((controlDistance Ω w X x y).toReal / (3 * ρ)) ^ α :=
            le_mul_of_one_le_right (by positivity) hone
        _ = Kfar * Sup * (controlDistance Ω w X x y).toReal ^ α := by
            rw [div_eq_mul_inv, Real.mul_rpow ENNReal.toReal_nonneg (inv_nonneg.2 h3ρ.le), hKfar]
            ring
        _ ≤ max (KC * (Qc * M₀)) (Kfar * Sup) * (controlDistance Ω w X x y).toReal ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hdpow
  have hsupS : (⨆ x : S₀, ENNReal.ofReal |f x|) ≤ ENNReal.ofReal Sup :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal (hbdd x.1 (hS₀W x.2))
  have hmax0 : 0 ≤ max (KC * (Qc * M₀)) (Kfar * Sup) :=
    le_max_of_le_left (mul_nonneg hKC0 (mul_nonneg hQc0 hM₀0))
  have hreal : Sup + max (KC * (Qc * M₀)) (Kfar * Sup) ≤ (1 + KC * Qc + Kfar) * (Sup + M₀) := by
    have hb : 0 ≤ Kfar * Sup := mul_nonneg hKfar0 hSup0
    have ha : 0 ≤ KC * (Qc * M₀) := mul_nonneg hKC0 (mul_nonneg hQc0 hM₀0)
    have hmax : max (KC * (Qc * M₀)) (Kfar * Sup) ≤ KC * (Qc * M₀) + Kfar * Sup :=
      max_le (le_add_of_nonneg_right hb) (le_add_of_nonneg_left ha)
    nlinarith [mul_nonneg hKCQ0 hSup0, mul_nonneg hKfar0 hM₀0, hM₀0]
  calc holderENorm (controlDistance Ω w X) α S₀ f
      = (⨆ x : S₀, ENNReal.ofReal |f x|) +
          holderSeminorm (controlDistance Ω w X) α S₀ f := rfl
    _ ≤ ENNReal.ofReal Sup + ENNReal.ofReal (max (KC * (Qc * M₀)) (Kfar * Sup)) :=
        add_le_add hsupS hsemS
    _ = ENNReal.ofReal (Sup + max (KC * (Qc * M₀)) (Kfar * Sup)) :=
        (ENNReal.ofReal_add hSup0 hmax0).symm
    _ ≤ ENNReal.ofReal ((1 + KC * Qc + Kfar) * (Sup + M₀)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (1 + KC * Qc + Kfar) * (ENNReal.ofReal Sup + ENNReal.ofReal M₀) := by
        rw [ENNReal.ofReal_mul hCst.le, ENNReal.ofReal_add hSup0 hM₀0]
    _ = ENNReal.ofReal (1 + KC * Qc + Kfar) *
          holderENorm C.dl α Us (fun ξ => f (basePoint ξ)) := by
        congr 1
        unfold holderENorm
        rw [hSup, hM₀, ENNReal.ofReal_toReal hsup, ENNReal.ofReal_toReal hsem]

/-- (Assuming local doubling, `OriginalLocalDoubling`.) The reverse
Hölder inequality of BB Prop 11.56: for `0 < t < s < r_*` in the fixed chart, with `δ` the fiber
constant, every `η ∈ K` and every `f`,
`‖f‖_{C^α(V_{δ t})} ≤ C ‖f̃‖_{C^α(U_s)}` where `V_{δ t} = B(π η, δ t)`, `U_s = B̃(η, s)`,
`f̃ = f ∘ π` and `‖·‖_{C^α(V)} = sup_V |·| + [·]_{α, V}`. -/
theorem holderTransfer_reverse_of_doubling (C : LiftedChart w st Ω hΩ X x₀ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U)
    (hdbl : OriginalLocalDoubling Ω w X (basePoint '' C.U)) :
    ∃ rstar δ : ℝ, 0 < rstar ∧ 0 < δ ∧ δ < 1 ∧ ∀ t s : ℝ, 0 < t → t < s → s < rstar →
      ∃ Cst : ℝ, 0 < Cst ∧ ∀ η ∈ K, ∀ f : (Fin n → ℝ) → ℝ,
        holderENorm (controlDistance Ω w X) α (rsBall Ω w X (basePoint η) (δ * t)) f ≤
          ENNReal.ofReal Cst *
            holderENorm C.dl α (rsBall C.O w C.Xl η s) (fun ξ => f (basePoint ξ)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact holderTransfer_reverse_of_zero C hn hα.le hK hKU
  · exact holderTransfer_reverse_of_pos C hn hα hα1 hK hKU hdbl

end RothschildStein.P2
