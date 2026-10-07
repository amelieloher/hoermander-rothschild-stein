-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityPositive
public import RothschildStein.P2.FractionalInterpolationCutoff

/-!
# Hölder interpolation: the far family of a principal term

For a principal term `t` (kernel `a(ξ) b(η) E(ξ, η, Θ(η, ξ))` with `E(ξ, η, u) = (D^{ξ,η} Γ)(u)`
homogeneous of degree `d = ℓ - Q` in `u`), the far family at scale `h` is
`far_h(ξ, η, u) = farProfile ν h (u) E(ξ, η, u)`, a globally smooth function of `(ξ, η, u)`
(`contDiff_farFamily`). Its iterated derivatives of order `j` at `(ξ, η, u)`, `(ξ, η)` in a compact set
and `ν u ≤ R`, are bounded by `C (1/h)^M` (`exists_farFamily_iteratedFDeriv_bound`): Leibniz with
the dilated cutoff (`FractionalInterpolationCutoff`) and the scaling bound of the homogeneous
family (`FractionalInterpolationScaling`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The family `E(ξ, η, u) = (D^{ξ,η} Γ)(u)` of a principal term. -/
def principalFamily (t : PrincipalTerm F) (z : Z3 (n + m)) : ℝ :=
  (t.D z.1 z.2.1).apply (F.pole t.star) z.2.2

theorem principalFamily_contDiffOn (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (principalFamily t) {z : Z3 (n + m) | z.2.2 ≠ 0} :=
  t.contDiffOn_family (hF.pole_smooth t.star)

/-- The family of a principal term of degree `≤ 1` is homogeneous in `u` of degree
`d = 2 - deg D - Q` (BB p. 543, Def 11.7; the kernel is homogeneous of degree `ℓ - Q`). -/
theorem principalFamily_homogeneous (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) :
    ∃ d : ℤ, ∀ ξ η : Fin (n + m) → ℝ, ∀ s : ℝ, 0 < s → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      principalFamily t (ξ, η, C.G.dilate s u) = s ^ d * principalFamily t (ξ, η, u) := by
  refine ⟨2 - t.degree - (C.G.homogeneousDimension : ℤ), fun ξ η s hs u hu => ?_⟩
  have hD : (t.D ξ η).IsHomogeneous C.G t.degree := by
    have := t.homogeneous ξ η
    rwa [hF.G_eq] at this
  have hΓ := hF.pole_smooth t.star
  have hΓh := hF.pole_homogeneous t.star
  have h := (H3.homogeneousOperator_kernel (t.D ξ η) hD hΓ hΓh).2 s hs u hu
  have e : (2 - (C.G.homogeneousDimension : ℝ)) - (t.degree : ℝ) =
      (((2 - t.degree - (C.G.homogeneousDimension : ℤ) : ℤ)) : ℝ) := by push_cast; ring
  show (t.D ξ η).apply (F.pole t.star) (C.G.dilate s u) = _ * (t.D ξ η).apply (F.pole t.star) u
  rw [h, e, Real.rpow_intCast]

/-- The far family `far_h(ξ, η, u) = farProfile ν h (u) E(ξ, η, u)` of a principal term. -/
def farFamily (ν : G2.HomogeneousNorm C.G) (t : PrincipalTerm F) (h : ℝ) (z : Z3 (n + m)) : ℝ :=
  farProfile ν h z.2.2 * principalFamily t z

theorem farFamily_eq_zero_of_le (ν : G2.HomogeneousNorm C.G) (t : PrincipalTerm F) {h : ℝ}
    (hh : 0 < h) {z : Z3 (n + m)} (hz : ν z.2.2 ≤ 4 * h / 3) : farFamily ν t h z = 0 := by
  unfold farFamily; rw [farProfile_eq_zero ν hh hz, zero_mul]

/-- The far family is globally smooth: it vanishes near `u = 0`. -/
theorem contDiff_farFamily (hF : C.IsLiftedFrame F) (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth)
    (t : PrincipalTerm F) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ (⊤ : ℕ∞) (farFamily ν t h) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : ν z.2.2 < 4 * h / 3
  · have hopen : IsOpen {y : Z3 (n + m) | ν y.2.2 < 4 * h / 3} :=
      isOpen_lt (ν.gauge.1.comp (continuous_snd.comp continuous_snd)) continuous_const
    have hev : farFamily ν t h =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hz] with y hy
      exact farFamily_eq_zero_of_le ν t hh (le_of_lt hy)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hz0 : z.2.2 ≠ 0 := by
      intro h0
      apply hz
      have : ν z.2.2 = 0 := by rw [h0]; exact (ν.gauge.2.2.1 0).mpr rfl
      rw [this]; linarith
    have hU : IsOpen {y : Z3 (n + m) | y.2.2 ≠ 0} :=
      (isOpen_compl_singleton (x := (0 : Fin (n + m) → ℝ))).preimage
        (continuous_snd.comp continuous_snd)
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Z3 (n + m) => farProfile ν h y.2.2) z :=
      ((contDiff_farProfile ν hν hh).comp (contDiff_snd.comp contDiff_snd)).contDiffAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (principalFamily t) z :=
      (principalFamily_contDiffOn hF t).contDiffAt (hU.mem_nhds hz0)
    exact h1.mul h2

theorem dilNorm_mono {N : ℕ} (G : HomogeneousGroup N) {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) :
    dilNorm G a ≤ dilNorm G b := by
  unfold dilNorm
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans hab)]
  exact pow_le_pow_left₀ h0 hab _

theorem zpow_le_natAbs_mul {h ρ c : ℝ} (hh : 0 < h) (hhρ : h ≤ ρ) (hρc : ρ ≤ c) (hc : 1 ≤ c)
    (hh1 : h ≤ 1) (d : ℤ) : ρ ^ d ≤ c ^ d.natAbs * (h⁻¹) ^ d.natAbs := by
  have hρ : 0 < ρ := hh.trans_le hhρ
  have hx : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
  rcases le_or_gt 0 d with hd | hd
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [Int.natAbs_natCast, zpow_natCast]
    calc ρ ^ k ≤ c ^ k := pow_le_pow_left₀ hρ.le hρc k
      _ = c ^ k * 1 := (mul_one _).symm
      _ ≤ c ^ k * (h⁻¹) ^ k :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hx) (pow_nonneg (by linarith) _)
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = -(k : ℤ) := ⟨(-d).toNat, by omega⟩
    rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast, ← inv_pow]
    calc (ρ⁻¹) ^ k ≤ (h⁻¹) ^ k := pow_le_pow_left₀ (inv_nonneg.mpr hρ.le) (inv_anti₀ hh hhρ) k
      _ = 1 * (h⁻¹) ^ k := (one_mul _).symm
      _ ≤ c ^ k * (h⁻¹) ^ k :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hc) (pow_nonneg (by linarith) _)

/-- **Polynomial growth of the iterated derivatives of the far family**: for `(ξ, η)` in a
compact set `L` and `ν u ≤ R`, `‖D^j far_h (ξ, η, u)‖ ≤ C (1/h)^M`, uniformly in `h ∈ (0, 1]`. -/
theorem exists_farFamily_iteratedFDeriv_bound (hF : C.IsLiftedFrame F) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) (t : PrincipalTerm F) {L : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ))}
    (hL : IsCompact L) (R : ℝ) (j : ℕ) :
    ∃ (Cb : ℝ) (M : ℕ), 0 ≤ Cb ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ z : Z3 (n + m),
      (z.1, z.2.1) ∈ L → ν z.2.2 ≤ R →
        ‖iteratedFDeriv ℝ j (farFamily ν t h) z‖ ≤ Cb * (h⁻¹) ^ M := by
  obtain ⟨d, hhom⟩ := principalFamily_homogeneous hF t
  have hW := principalFamily_contDiffOn hF t
  choose S hS0 hS using fun i : ℕ =>
    exists_iteratedFDeriv_scaling_bound C.G ν.gauge hW hhom hL i
  choose D hD0 hD using fun i : ℕ => exists_iteratedFDeriv_farProfileZ_le ν hν i
  set c : ℝ := max 1 R with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  set Bx : ℝ → ℝ := fun x => ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    (D i * dilNorm C.G x ^ i) * (S (j - i) * (c ^ d.natAbs * x ^ d.natAbs) *
      (1 + dilNorm C.G x) ^ (j - i)) with hBx
  have hpoly : PolyBdd Bx := by
    refine PolyBdd.sum _ fun i _ => ?_
    have h1 := polyBdd_dilNorm C.G
    exact ((PolyBdd.const _).mul ((PolyBdd.const _).mul (h1.pow i))).mul
      (((PolyBdd.const _).mul ((PolyBdd.const _).mul PolyBdd.zpow_nat)).mul
        (((PolyBdd.const 1).add h1).pow _))
  obtain ⟨Cb, M, hCb, hB⟩ := hpoly
  refine ⟨Cb, M, hCb, fun h hh hh1 z hzL hzR => ?_⟩
  have hx : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
  have hxM : 0 ≤ Cb * (h⁻¹) ^ M := mul_nonneg hCb (pow_nonneg (by linarith) _)
  by_cases hz : ν z.2.2 < 4 * h / 3
  · have hopen : IsOpen {y : Z3 (n + m) | ν y.2.2 < 4 * h / 3} :=
      isOpen_lt (ν.gauge.1.comp (continuous_snd.comp continuous_snd)) continuous_const
    have hev : farFamily ν t h =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hz] with y hy
      exact farFamily_eq_zero_of_le ν t hh (le_of_lt hy)
    rw [(hev.iteratedFDeriv ℝ j).self_of_nhds, iteratedFDeriv_fun_zero]
    simpa using hxM
  · have hz' : 4 * h / 3 ≤ ν z.2.2 := not_lt.mp hz
    set ρ : ℝ := ν z.2.2 with hρ
    have hρpos : 0 < ρ := by linarith
    have hz0 : z.2.2 ≠ 0 := by
      intro h0
      have : ν z.2.2 = 0 := by rw [h0]; exact (ν.gauge.2.2.1 0).mpr rfl
      linarith
    have hρh : h ≤ ρ := by linarith
    have hρc : ρ ≤ c := hzR.trans (le_max_right _ _)
    have hU : IsOpen {y : Z3 (n + m) | y.2.2 ≠ 0} :=
      (isOpen_compl_singleton (x := (0 : Fin (n + m) → ℝ))).preimage
        (continuous_snd.comp continuous_snd)
    have hzU : z ∈ {y : Z3 (n + m) | y.2.2 ≠ 0} := hz0
    have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Z3 (n + m) => farProfile ν h y.2.2)
        {y : Z3 (n + m) | y.2.2 ≠ 0} :=
      ((contDiff_farProfile ν hν hh).comp (contDiff_snd.comp contDiff_snd)).contDiffOn
    have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ)
      (f := fun y : Z3 (n + m) => farProfile ν h y.2.2) (g := principalFamily t)
      (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) hf hW hU.uniqueDiffOn hzU (n := j) (by exact_mod_cast le_top)
    have e : ∀ (g : Z3 (n + m) → ℝ) (i : ℕ),
        iteratedFDerivWithin ℝ i g {y : Z3 (n + m) | y.2.2 ≠ 0} z = iteratedFDeriv ℝ i g z :=
      fun g i => iteratedFDerivWithin_of_isOpen i hU hzU
    simp only [e] at hmul
    have hdn : dilNorm C.G ρ⁻¹ ≤ dilNorm C.G h⁻¹ :=
      dilNorm_mono C.G (inv_nonneg.mpr hρpos.le) (inv_anti₀ hh hρh)
    have hρd : ρ ^ d ≤ c ^ d.natAbs * (h⁻¹) ^ d.natAbs :=
      zpow_le_natAbs_mul hh hρh hρc hc1 hh1 d
    have hterm : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : Z3 (n + m) => farProfile ν h y.2.2) z‖ *
          ‖iteratedFDeriv ℝ (j - i) (principalFamily t) z‖ ≤
        (j.choose i : ℝ) * (D i * dilNorm C.G h⁻¹ ^ i) * (S (j - i) *
          (c ^ d.natAbs * (h⁻¹) ^ d.natAbs) * (1 + dilNorm C.G h⁻¹) ^ (j - i)) := by
      intro i _
      have h1 := hD i h hh z
      have h2 := hS (j - i) z hzL hz0
      have hdn0 := dilNorm_nonneg C.G h⁻¹
      have hdn1 := dilNorm_nonneg C.G ρ⁻¹
      have h3 : S (j - i) * ρ ^ d * (1 + dilNorm C.G ρ⁻¹) ^ (j - i) ≤
          S (j - i) * (c ^ d.natAbs * (h⁻¹) ^ d.natAbs) * (1 + dilNorm C.G h⁻¹) ^ (j - i) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hρd (hS0 _)) ?_ (by positivity)
          (mul_nonneg (hS0 _) (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)))
        exact pow_le_pow_left₀ (by linarith) (by linarith) _
      refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) (h2.trans h3)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hD0 i) (by positivity)))
    calc ‖iteratedFDeriv ℝ j (farFamily ν t h) z‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : Z3 (n + m) => farProfile ν h y.2.2) z‖ *
            ‖iteratedFDeriv ℝ (j - i) (principalFamily t) z‖ := hmul
      _ ≤ Bx h⁻¹ := Finset.sum_le_sum hterm
      _ ≤ |Bx h⁻¹| := le_abs_self _
      _ ≤ Cb * (h⁻¹) ^ M := hB _ hx

end RothschildStein.P2
