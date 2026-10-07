-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.CutoffsHolder
public import RothschildStein.Definitions.driftWeight
public import RothschildStein.Definitions.noDriftWeight
public import RothschildStein.G2.NormConstruction

/-!
# Smooth cutoffs in the lifted chart

The radial cutoff construction (BB Rem 11.35, Lem 11.36, Cor 11.37, pp. 578–580; Lem 11.52, (11.84)–(11.86), pp. 595–596).
For a compact set `Kc` of centres in the chart domain and a smooth homogeneous gauge `ν`
(`G2.HomogeneousNorm` with `.Smooth`, e.g. `G2.smoothNorm`) there is `r_* ∈ (0, 1]` such that for
`0 < s < r < r_*` the radial cutoff
`φ = χ((ν(Θ(ξ₀, ·)) - s)/(r - s))`, `χ(x) = smoothTransition(3 - 6x)`, is smooth with compact
support in the closed `ρ`-ball of radius `(s + r)/2` (so inside `U^ρ_r`), `0 ≤ φ ≤ 1`, `φ = 1` on
`U^ρ_s`, and for every word `I` of weighted length `j`
`‖X̃_I φ‖_∞ ≤ C(j) (r - s)^{-j}`, `‖X̃_I φ‖_{C^α} ≤ C(j) (r - s)^{-(j+1)}`,
with `C(j)` independent of the centre `ξ₀ ∈ Kc`, of `s, r` and of `α ∈ (0, 1)`.
The transition ends at `(s + r)/2`; for `s = σ r` this is `(1 + σ) r / 2`, which gives the
first/second derivative bounds of (11.63) (`smooth_cutoffs_sigma`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1

theorem sqrt_sum_sq_le {q : ℕ} {g : Fin q → ℝ} {b : ℝ} (hb : 0 ≤ b) (hg : ∀ i, |g i| ≤ b) :
    Real.sqrt (∑ i, g i ^ 2) ≤ Real.sqrt q * b := by
  have h1 : ∑ i, g i ^ 2 ≤ (q : ℝ) * b ^ 2 := by
    calc ∑ i, g i ^ 2 ≤ ∑ _i : Fin q, b ^ 2 :=
          Finset.sum_le_sum (fun i _ => sq_le_sq' (abs_le.1 (hg i)).1 (abs_le.1 (hg i)).2)
      _ = (q : ℝ) * b ^ 2 := by simp
  calc Real.sqrt (∑ i, g i ^ 2) ≤ Real.sqrt ((q : ℝ) * b ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt q * b := by rw [Real.sqrt_mul (Nat.cast_nonneg q), Real.sqrt_sq hb]

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- A smooth homogeneous norm exists on every homogeneous group:
the corrected common-multiple polynomial norm `N(u) = (∑ u_j^{2M/ω_j})^{1/(2M)}` of
the homogeneous group (BB Rem 11.35, p. 578, with `M` a common multiple of the weights instead of
BB's choice `M = Q`). Every cutoff theorem
below holds for it (and for any other smooth homogeneous norm). -/
theorem exists_smooth_homogeneous_norm {N : ℕ} (G : HomogeneousGroup N) :
    ∃ ν : G2.HomogeneousNorm G, ν.Smooth :=
  ⟨G2.smoothNorm G, G2.smoothNorm_smooth G⟩

/-- The weighted variation inequality for a drift chart (alphabet `Fin (q + 1)`, drift
at `0` of weight two), with constant `q + 1` (BB Thm 1.56, p. 37). -/
theorem liftedVariation_drift {q : ℕ} {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (C : LiftedChart driftWeight st Ω hΩ X x₀ m) : LiftedVariation C ((q : ℝ) + 1) := by
  intro v b1 b2 hv hb1 hb2 h1 h2 x y hxy
  have hH : ∀ z ∈ C.O, Real.sqrt (∑ i : Fin q, (fderiv ℝ v z (C.Xl i.succ z)) ^ 2) ≤
      Real.sqrt q * b1 := fun z hz =>
    sqrt_sum_sq_le hb1 (fun i => h1 z hz i.succ (by simp [driftWeight, Fin.succ_ne_zero]))
  have hD : ∀ z ∈ C.O, |fderiv ℝ v z (C.Xl 0 z)| ≤ b2 :=
    fun z hz => h2 z hz 0 (by simp [driftWeight])
  have hG := G1.global_drift_variation_of_finite_distance (isOpen_liftedDomain C) hv
    (mul_nonneg (Real.sqrt_nonneg _) hb1) hb2 hH hD hxy.ne
  have hd : 0 ≤ (C.dl x y).toReal := ENNReal.toReal_nonneg
  rw [abs_sub_comm]
  refine hG.trans ?_
  have hq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (Nat.cast_nonneg q)
  have e : Real.sqrt q * (C.dl x y).toReal * (Real.sqrt q * b1) =
      (q : ℝ) * (C.dl x y).toReal * b1 := by
    calc Real.sqrt q * (C.dl x y).toReal * (Real.sqrt q * b1)
        = (Real.sqrt q * Real.sqrt q) * (C.dl x y).toReal * b1 := by ring
      _ = (q : ℝ) * (C.dl x y).toReal * b1 := by rw [hq]
  rw [e]
  have h0 : 0 ≤ (C.dl x y).toReal * b1 + (q : ℝ) * ((C.dl x y).toReal ^ 2 * b2) := by positivity
  nlinarith [h0]

/-- The weighted variation inequality for a drift-free chart (alphabet `Fin q`, all
weights one), with constant `q + 1` (BB Thm 1.54, pp. 36–37). -/
theorem liftedVariation_noDrift {q : ℕ} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m) : LiftedVariation C ((q : ℝ) + 1) := by
  intro v b1 b2 hv hb1 hb2 h1 _ x y hxy
  have hH : ∀ z ∈ C.O, Real.sqrt (∑ i : Fin q, (fderiv ℝ v z (C.Xl i z)) ^ 2) ≤
      Real.sqrt q * b1 := fun z hz =>
    sqrt_sum_sq_le hb1 (fun i => h1 z hz i rfl)
  have hG := G1.global_noDrift_variation_of_finite_distance (isOpen_liftedDomain C) hv
    (mul_nonneg (Real.sqrt_nonneg _) hb1) hH hxy.ne
  have hd : 0 ≤ (C.dl x y).toReal := ENNReal.toReal_nonneg
  rw [abs_sub_comm]
  refine hG.trans ?_
  have hq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (Nat.cast_nonneg q)
  have e : Real.sqrt q * (C.dl x y).toReal * (Real.sqrt q * b1) =
      (q : ℝ) * (C.dl x y).toReal * b1 := by
    calc Real.sqrt q * (C.dl x y).toReal * (Real.sqrt q * b1)
        = (Real.sqrt q * Real.sqrt q) * (C.dl x y).toReal * b1 := by ring
      _ = (q : ℝ) * (C.dl x y).toReal * b1 := by rw [hq]
  rw [e]
  have h0 : 0 ≤ (C.dl x y).toReal * b1 + (q : ℝ) * ((C.dl x y).toReal ^ 2 * b2) +
      (C.dl x y).toReal ^ 2 * b2 := by positivity
  nlinarith [h0]

/-- The qualitative and sup-norm part, for any weights: there is `r_* ∈ (0, 1]` such that
for every centre `ξ₀ ∈ Kc` and `0 < s < r < r_*` the radial cutoff `φ` is smooth with compact
support in the closed `ρ`-ball of radius `(s + r)/2 ⊂ U^ρ_r`, `0 ≤ φ ≤ 1`, `φ = 1` on `U^ρ_s`, and
for every word `I` of weighted length `j`, `‖X̃_I φ‖_∞ ≤ C(j) (r - s)^{-j}` with `C(j)`
independent of `ξ₀, s, r` (BB pp. 578–579, Rem 11.35 and Lem 11.36). -/
theorem exists_radialCutoff (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U) :
    ∃ rstar : ℝ, 0 < rstar ∧ rstar ≤ 1 ∧
      (∀ ξ₀ ∈ Kc, ∀ s r : ℝ, 0 < s → s < r → r < rstar →
        ContDiff ℝ (⊤ : ℕ∞) (radialCutoff C ν ξ₀ s r) ∧
        HasCompactSupport (radialCutoff C ν ξ₀ s r) ∧
        (∀ ξ, 0 ≤ radialCutoff C ν ξ₀ s r ξ ∧ radialCutoff C ν ξ₀ s r ξ ≤ 1) ∧
        EqOn (radialCutoff C ν ξ₀ s r) (fun _ => 1) (rhoBall C ν ξ₀ s) ∧
        tsupport (radialCutoff C ν ξ₀ s r) ⊆ closedRhoBall C ν ξ₀ ((s + r) / 2) ∧
        closedRhoBall C ν ξ₀ ((s + r) / 2) ⊆ rhoBall C ν ξ₀ r) ∧
      ∀ I : List (Fin k), ∃ CI : ℝ, 0 ≤ CI ∧ ∀ ξ₀ ∈ Kc, ∀ s r : ℝ, 0 < s → s < r → r < rstar →
        ∀ ξ, |wordDerivative C.Xl I (radialCutoff C ν ξ₀ s r) ξ| ≤
          CI * (r - s) ^ (-(wordWeight w I : ℤ)) := by
  obtain ⟨ρ, hρ0, hρ1, hT⟩ := exists_chart_radius C ν hKc hKU
  refine ⟨ρ / 2, by linarith, by linarith, ?_, ?_⟩
  · intro ξ₀ hξ₀ s r hs hsr hrρ
    have hξ₀U : ξ₀ ∈ C.U := hKU hξ₀
    have hTξ : ∀ u, ν u ≤ ρ → (ξ₀, u) ∈ C.T := fun u hu => hT ξ₀ hξ₀ u hu
    have hmid : (s + r) / 2 ≤ ρ := by linarith
    have hsub := radialCutoff_tsupport_subset C ν hξ₀U hsr hmid hTξ
    refine ⟨radialCutoff_contDiff C ν hν hξ₀U hs hsr hmid hTξ, ?_,
      radialCutoff_range C ν ξ₀ s r, fun ξ hξ => radialCutoff_eq_one C ν ξ₀ hsr hξ, hsub,
      closedRhoBall_subset_rhoBall C ν ξ₀ (by linarith)⟩
    exact (isCompact_closedRhoBall C ν hξ₀U (ρ := (s + r) / 2)
      (fun u hu => hTξ u (hu.trans hmid))).of_isClosed_subset (isClosed_tsupport _) hsub
  · intro I
    exact radialCutoff_sup_bound C ν hν hKc hKU hρ0 hρ1 hT I

/-- The full cutoff statement for a **drift** chart (alphabet `Fin (q + 1)`, drift letter
`0` of weight two): the qualitative properties and sup bounds of `exists_radialCutoff` together
with `‖X̃_I φ‖_{C^α} ≤ C(j) (r - s)^{-(j+1)}` in the Hölder vocabulary
(`holderENorm` with the lifted control distance `C.dl` on `C.O`), for every `0 < α < 1`
(BB pp. 579–580, Cor 11.37). -/
theorem smooth_cutoffs_drift {q : ℕ} {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (C : LiftedChart driftWeight st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U) :
    ∃ rstar : ℝ, 0 < rstar ∧ rstar ≤ 1 ∧
      (∀ ξ₀ ∈ Kc, ∀ s r : ℝ, 0 < s → s < r → r < rstar →
        ContDiff ℝ (⊤ : ℕ∞) (radialCutoff C ν ξ₀ s r) ∧
        HasCompactSupport (radialCutoff C ν ξ₀ s r) ∧
        (∀ ξ, 0 ≤ radialCutoff C ν ξ₀ s r ξ ∧ radialCutoff C ν ξ₀ s r ξ ≤ 1) ∧
        EqOn (radialCutoff C ν ξ₀ s r) (fun _ => 1) (rhoBall C ν ξ₀ s) ∧
        tsupport (radialCutoff C ν ξ₀ s r) ⊆ closedRhoBall C ν ξ₀ ((s + r) / 2) ∧
        closedRhoBall C ν ξ₀ ((s + r) / 2) ⊆ rhoBall C ν ξ₀ r) ∧
      (∀ I : List (Fin (q + 1)), ∃ CI : ℝ, 0 ≤ CI ∧ ∀ ξ₀ ∈ Kc, ∀ s r : ℝ, 0 < s → s < r →
        r < rstar → ∀ ξ, |wordDerivative C.Xl I (radialCutoff C ν ξ₀ s r) ξ| ≤
          CI * (r - s) ^ (-(wordWeight driftWeight I : ℤ))) ∧
      ∀ I : List (Fin (q + 1)), ∃ CI : ℝ, 0 ≤ CI ∧ ∀ ξ₀ ∈ Kc, ∀ s r : ℝ, 0 < s → s < r →
        r < rstar → ∀ α : ℝ, 0 < α → α < 1 →
          holderENorm C.dl α C.O (wordDerivative C.Xl I (radialCutoff C ν ξ₀ s r)) ≤
            ENNReal.ofReal (CI * (r - s) ^ (-((wordWeight driftWeight I : ℤ) + 1))) := by
  obtain ⟨ρ, hρ0, hρ1, hT⟩ := exists_chart_radius C ν hKc hKU
  obtain ⟨rstar, hr0, hr1, hq, hsup⟩ := exists_radialCutoff C ν hν hKc hKU
  refine ⟨min rstar (ρ / 2), lt_min hr0 (by linarith), (min_le_left _ _).trans hr1, ?_, ?_, ?_⟩
  · intro ξ₀ hξ₀ s r hs hsr hrr
    exact hq ξ₀ hξ₀ s r hs hsr (hrr.trans_le (min_le_left _ _))
  · intro I
    obtain ⟨CI, hCI0, hCI⟩ := hsup I
    exact ⟨CI, hCI0, fun ξ₀ hξ₀ s r hs hsr hrr =>
      hCI ξ₀ hξ₀ s r hs hsr (hrr.trans_le (min_le_left _ _))⟩
  · intro I
    obtain ⟨CI, hCI0, hCI⟩ := radialCutoff_holder_of_variation C ν hν hKc hKU hρ0 hρ1 hT
      (Cg := (q : ℝ) + 1) (by positivity) (liftedVariation_drift C) I
    exact ⟨CI, hCI0, fun ξ₀ hξ₀ s r hs hsr hrr α hα0 hα1 =>
      hCI ξ₀ hξ₀ s r hs hsr (hrr.trans_le (min_le_right _ _)) α hα0 hα1.le⟩

/-- The full cutoff statement for a **drift-free** chart (alphabet `Fin q`, all weights
one); see `smooth_cutoffs_drift`. -/
theorem smooth_cutoffs_noDrift {q : ℕ} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U) :
    ∃ rstar : ℝ, 0 < rstar ∧ rstar ≤ 1 ∧
      (∀ ξ₀ ∈ Kc, ∀ s r : ℝ, 0 < s → s < r → r < rstar →
        ContDiff ℝ (⊤ : ℕ∞) (radialCutoff C ν ξ₀ s r) ∧
        HasCompactSupport (radialCutoff C ν ξ₀ s r) ∧
        (∀ ξ, 0 ≤ radialCutoff C ν ξ₀ s r ξ ∧ radialCutoff C ν ξ₀ s r ξ ≤ 1) ∧
        EqOn (radialCutoff C ν ξ₀ s r) (fun _ => 1) (rhoBall C ν ξ₀ s) ∧
        tsupport (radialCutoff C ν ξ₀ s r) ⊆ closedRhoBall C ν ξ₀ ((s + r) / 2) ∧
        closedRhoBall C ν ξ₀ ((s + r) / 2) ⊆ rhoBall C ν ξ₀ r) ∧
      (∀ I : List (Fin q), ∃ CI : ℝ, 0 ≤ CI ∧ ∀ ξ₀ ∈ Kc, ∀ s r : ℝ, 0 < s → s < r →
        r < rstar → ∀ ξ, |wordDerivative C.Xl I (radialCutoff C ν ξ₀ s r) ξ| ≤
          CI * (r - s) ^ (-(wordWeight noDriftWeight I : ℤ))) ∧
      ∀ I : List (Fin q), ∃ CI : ℝ, 0 ≤ CI ∧ ∀ ξ₀ ∈ Kc, ∀ s r : ℝ, 0 < s → s < r →
        r < rstar → ∀ α : ℝ, 0 < α → α < 1 →
          holderENorm C.dl α C.O (wordDerivative C.Xl I (radialCutoff C ν ξ₀ s r)) ≤
            ENNReal.ofReal (CI * (r - s) ^ (-((wordWeight noDriftWeight I : ℤ) + 1))) := by
  obtain ⟨ρ, hρ0, hρ1, hT⟩ := exists_chart_radius C ν hKc hKU
  obtain ⟨rstar, hr0, hr1, hq, hsup⟩ := exists_radialCutoff C ν hν hKc hKU
  refine ⟨min rstar (ρ / 2), lt_min hr0 (by linarith), (min_le_left _ _).trans hr1, ?_, ?_, ?_⟩
  · intro ξ₀ hξ₀ s r hs hsr hrr
    exact hq ξ₀ hξ₀ s r hs hsr (hrr.trans_le (min_le_left _ _))
  · intro I
    obtain ⟨CI, hCI0, hCI⟩ := hsup I
    exact ⟨CI, hCI0, fun ξ₀ hξ₀ s r hs hsr hrr =>
      hCI ξ₀ hξ₀ s r hs hsr (hrr.trans_le (min_le_left _ _))⟩
  · intro I
    obtain ⟨CI, hCI0, hCI⟩ := radialCutoff_holder_of_variation C ν hν hKc hKU hρ0 hρ1 hT
      (Cg := (q : ℝ) + 1) (by positivity) (liftedVariation_noDrift C) I
    exact ⟨CI, hCI0, fun ξ₀ hξ₀ s r hs hsr hrr α hα0 hα1 =>
      hCI ξ₀ hξ₀ s r hs hsr (hrr.trans_le (min_le_right _ _)) α hα0 hα1.le⟩

end RothschildStein.P2
