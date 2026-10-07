-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FractionalInterpolationNearAbstract
public import RothschildStein.P2.FractionalInterpolationCutoff
public import RothschildStein.P2.FractionalInterpolationFarKernel
public import RothschildStein.P2.Cutoffs
public import RothschildStein.P1.ContinuityPositive

/-!
# Hölder interpolation: the near part

The near kernel of a principal term at scale `h` is `k(ξ, η) nearProfile ν h (Θ(η, ξ))`
(`nearKernel`): supported at lifted distance `d̃(ξ, η) ≤ r₀ = (3/2) C h`, with the kernel size bound
and a first-variable difference bound with constants **independent of `h`**: the kernel constants of
`k` plus the cutoff term, controlled by the weighted variation inequality and the bounds
`‖X̃_i nearProfile‖ ≤ C h^{-w_i}` of the radial cutoff. Feeding this into the dyadic Hölder bound
for kernels of bounded support (`holder_bound_of_support`) gives
`‖T_h f‖_{C^α(V)} ≤ C h^{1-α} ‖f‖_∞` (BB pp. 594-595, Lem 11.51: "the near kernel is a fractional
kernel with constant `C h^η`, whose `C^α` bound is `C h^η ‖L̃ v‖_∞`").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The near kernel `k(ξ, η) nearProfile ν h (Θ(η, ξ))` of a principal term at scale `h`. -/
def nearKernel (ν : G2.HomogeneousNorm C.G) (t : PrincipalTerm F) (h : ℝ)
    (ξ η : Fin (n + m) → ℝ) : ℝ :=
  t.kernel ξ η * nearProfile ν h (C.Θ η ξ)

theorem nearKernel_add_farKernel (ν : G2.HomogeneousNorm C.G) (t : PrincipalTerm F) (h : ℝ)
    (ξ η : Fin (n + m) → ℝ) :
    nearKernel ν t h ξ η + farKernel ν t h (ξ, η) = t.kernel ξ η := by
  unfold nearKernel farKernel farProfile
  ring

/-- The lifted control distance is dominated by `C ν(Θ(η, ξ))` for any homogeneous norm. -/
theorem exists_dl_le_mul_nu (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G) :
    ∃ Cdn : ℝ, 0 < Cdn ∧ ∀ η ∈ C.U, ∀ ξ ∈ C.U,
      (C.dl η ξ).toReal ≤ Cdn * ν (C.Θ η ξ) := by
  obtain ⟨a, b, ha, hb, hab⟩ := G2.gauge_equivalent_max ν.gauge
  refine ⟨C.gaugeConst / a, div_pos C.gaugeConst_pos ha, fun η hη ξ hξ => ?_⟩
  have h1 := C.dl_toReal_le hη hξ
  have h2 : kgauge C.G (C.Θ η ξ) ≤ ν (C.Θ η ξ) / a := by
    rw [le_div_iff₀ ha]
    have := (hab (C.Θ η ξ)).1
    linarith
  calc _ ≤ C.gaugeConst * kgauge C.G (C.Θ η ξ) := h1
    _ ≤ C.gaugeConst * (ν (C.Θ η ξ) / a) := mul_le_mul_of_nonneg_left h2 C.gaugeConst_pos.le
    _ = C.gaugeConst / a * ν (C.Θ η ξ) := by ring

/-- The radial cutoff at `(s, r) = (h, 2h)` is the near profile of `Θ(η, ·)`. -/
theorem radialCutoff_eq_nearProfile (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (η : Fin (n + m) → ℝ) {h : ℝ} (hh : 0 < h) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    radialCutoff C ν η h (2 * h) ξ = nearProfile ν h (C.Θ η ξ) := by
  rw [radialCutoff_eq_gaugeProfile_comp C ν η (by linarith : h < 2 * h) hξ]
  unfold gaugeProfile nearProfile
  have e1 : h + (2 * h - h) / 3 = 4 * h / 3 := by ring
  have e2 : h + 2 * (2 * h - h) / 3 = 5 * h / 3 := by ring
  rw [e1, e2]

/-- **The near cutoff is `C/h`-Lipschitz for `d̃` at scale `h`** (weighted variation
inequality with the radial cutoff bounds `|X̃_i φ| ≤ C h^{-w_i}`): for `R₁ ≥ 0` there are `hmax, Cl`
with `|φ_h(Θ(η, x)) - φ_h(Θ(η, y))| ≤ Cl d̃(x, y)/h` for `η ∈ Kc`, `x, y ∈ U` with
`d̃(x, y) ≤ R₁ h`, `0 < h < hmax`. -/
theorem exists_nearProfile_lipschitz (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hvar : LiftedVariation C Cg) {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc)
    (hKU : Kc ⊆ C.U) (R₁ : ℝ) (hR₁ : 0 ≤ R₁) :
    ∃ hmax Cl : ℝ, 0 < hmax ∧ 0 ≤ Cl ∧ ∀ h : ℝ, 0 < h → h < hmax → ∀ η ∈ Kc,
      ∀ x y : Fin (n + m) → ℝ, x ∈ C.U → y ∈ C.U → (C.dl x y).toReal ≤ R₁ * h →
        |nearProfile ν h (C.Θ η x) - nearProfile ν h (C.Θ η y)| ≤ Cl * (C.dl x y).toReal / h := by
  obtain ⟨rstar, hr0, hr1, hq, hsup⟩ := exists_radialCutoff C ν hν hKc hKU
  choose CI hCI0 hCI using fun i : Fin k => hsup [i]
  set Csum : ℝ := ∑ i, CI i with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun i _ => hCI0 i
  refine ⟨rstar / 2, Cg * Csum * (1 + R₁), by linarith, by positivity, ?_⟩
  intro h hh hhr η hη x y hx hy hd
  have hr : 2 * h < rstar := by linarith
  obtain ⟨hsm, -, -, -, -, -⟩ := hq η hη h (2 * h) hh (by linarith) hr
  set v := radialCutoff C ν η h (2 * h) with hv
  have hb : ∀ i : Fin k, ∀ z : Fin (n + m) → ℝ,
      |fderiv ℝ v z (C.Xl i z)| ≤ Csum * (h⁻¹) ^ (w i : ℕ) := by
    intro i z
    have h1 := hCI i η hη h (2 * h) hh (by linarith) hr z
    have e : (2 * h - h) = h := by ring
    rw [e] at h1
    have h2 : |wordDerivative C.Xl [i] v z| = |fderiv ℝ v z (C.Xl i z)| := rfl
    rw [h2] at h1
    have hw : wordWeight w [i] = (w i : ℕ) := by simp [wordWeight]
    rw [hw, zpow_neg, zpow_natCast, ← inv_pow] at h1
    refine h1.trans ?_
    have : CI i ≤ Csum := Finset.single_le_sum (f := CI) (fun j _ => hCI0 j) (Finset.mem_univ i)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hvC : ContDiffOn ℝ 1 v C.O := (hsm.of_le (by simp)).contDiffOn
  have hinvh : 0 < h⁻¹ := inv_pos.mpr hh
  have key := hvar v (Csum * h⁻¹) (Csum * (h⁻¹) ^ 2) hvC (by positivity) (by positivity)
    (fun z _ i hi => by
      have := hb i z
      rw [hi, pow_one] at this
      exact this)
    (fun z _ i hi => by
      have := hb i z
      rw [hi] at this
      simpa using this) x y
    (lt_of_le_of_ne le_top (C.dl_ne_top hx hy))
  have hxy : |nearProfile ν h (C.Θ η x) - nearProfile ν h (C.Θ η y)| = |v x - v y| := by
    rw [hv, radialCutoff_eq_nearProfile C ν η hh hx, radialCutoff_eq_nearProfile C ν η hh hy]
  rw [hxy]
  refine key.trans ?_
  set d := (C.dl x y).toReal with hddef
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hdh : d * h⁻¹ ≤ R₁ := by
    rw [mul_inv_le_iff₀ hh]; linarith
  calc Cg * (d * (Csum * h⁻¹) + d ^ 2 * (Csum * (h⁻¹) ^ 2))
      = Cg * Csum * (d * h⁻¹) * (1 + d * h⁻¹) := by ring
    _ ≤ Cg * Csum * (d * h⁻¹) * (1 + R₁) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = Cg * Csum * (1 + R₁) * d / h := by
        rw [div_eq_mul_inv]; ring

/-- The slice bounds of the restricted-error estimates from explicit size and first-variable difference estimates. -/
theorem sliceBounds_of_estimates (C : LiftedChart w st Ω hΩ X x₀ m) {S : Set (Fin (n + m) → ℝ)}
    (hSU : S ⊆ C.U) {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hmeas : Measurable (Function.uncurry (sliceKernel S κ)))
    (hsz : ∀ ξ ∈ S, ∀ η ∈ S, ξ ≠ η →
      |κ ξ η| ≤ A * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ)))
    (hdf : ∀ ξ ∈ S, ∀ ξ' ∈ S, ∀ η ∈ S, 2 * (C.dl ξ ξ').toReal < (C.dl ξ' η).toReal →
      |κ ξ' η - κ ξ η| ≤
        B * (C.dl ξ ξ').toReal / (C.dl ξ' η).toReal ^ C.G.homogeneousDimension) :
    SliceBounds S (fun x y => (C.dl x y).toReal) (C.G.homogeneousDimension - 1)
      (sliceKernel S κ) A B := by
  have hQ : 1 ≤ C.G.homogeneousDimension := G2.homogeneousDimension_pos C.G
  refine ⟨hA, hB, hmeas, fun x y hx => sliceKernel_of_not_mem (Or.inl hx),
    fun x y hy => sliceKernel_of_not_mem (Or.inr (Or.inl hy)), ?_, ?_⟩
  · intro x hx y hy
    show |sliceKernel S κ x y| ≤ A / (C.dl x y).toReal ^ (C.G.homogeneousDimension - 1)
    by_cases hxy : x = y
    · rw [sliceKernel_of_not_mem (Or.inr (Or.inr hxy))]
      simp only [abs_zero]
      exact div_nonneg hA (pow_nonneg ENNReal.toReal_nonneg _)
    · rw [sliceKernel_of_mem hx hy hxy]
      have := hsz x hx y hy hxy
      have e : (1 : ℤ) - (C.G.homogeneousDimension : ℤ) =
          -((C.G.homogeneousDimension - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hQ]
        push_cast
        ring
      rwa [e, zpow_neg, zpow_natCast, ← div_eq_mul_inv] at this
  · intro x hx x' hx' y hy hsep
    have hsep' : 2 * (C.dl x x').toReal < (C.dl x' y).toReal := hsep
    have hh0 : 0 ≤ (C.dl x x').toReal := ENNReal.toReal_nonneg
    have hne1 : x' ≠ y := by
      intro h
      rw [← h] at hsep'
      have : (C.dl x' x').toReal = 0 := by
        rw [(C.dl_eq_zero_iff (hSU hx') (hSU hx')).mpr rfl]
        rfl
      linarith
    have hne2 : x ≠ y := by
      intro h
      rw [← h] at hsep'
      have : (C.dl x' x).toReal = (C.dl x x').toReal := congrArg ENNReal.toReal (C.dl_symm x' x)
      linarith
    show |sliceKernel S κ x' y - sliceKernel S κ x y| ≤
      B * (C.dl x x').toReal / (C.dl x' y).toReal ^ (C.G.homogeneousDimension - 1 + 1)
    rw [sliceKernel_of_mem hx' hy hne1, sliceKernel_of_mem hx hy hne2, Nat.sub_add_cancel hQ]
    exact hdf x hx x' hx' y hy hsep'

/-- **Uniform estimates of the near kernel** on the compact patch `S = cl V`: for
`0 < h < hmax`, size `|κ_h| ≤ A d̃^{1-Q}`, first-variable difference `B d̃(ξ, ξ')/d̃(ξ', η)^Q` and
support `κ_h(ξ, η) = 0` for `d̃(ξ, η) ≥ (3/2) Cdn h`, with `A, B, Cdn, hmax` independent of `h`. -/
theorem nearKernel_estimates (hF : C.IsLiftedFrame F) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) (t : PrincipalTerm F) (hdeg : t.degree ≤ 1) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hvar : LiftedVariation C Cg) :
    ∃ A B Cdn hmax : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < Cdn ∧ 0 < hmax ∧ ∀ h : ℝ, 0 < h → h < hmax →
      (∀ ξ ∈ closure (F.V : Set (Fin (n + m) → ℝ)), ∀ η ∈ closure (F.V : Set (Fin (n + m) → ℝ)),
        ξ ≠ η → |nearKernel ν t h ξ η| ≤
          A * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ))) ∧
      (∀ ξ ∈ closure (F.V : Set (Fin (n + m) → ℝ)), ∀ ξ' ∈ closure (F.V : Set (Fin (n + m) → ℝ)),
        ∀ η ∈ closure (F.V : Set (Fin (n + m) → ℝ)),
        2 * (C.dl ξ ξ').toReal < (C.dl ξ' η).toReal →
        |nearKernel ν t h ξ' η - nearKernel ν t h ξ η| ≤
          B * (C.dl ξ ξ').toReal / (C.dl ξ' η).toReal ^ C.G.homogeneousDimension) ∧
      (∀ ξ ∈ closure (F.V : Set (Fin (n + m) → ℝ)), ∀ η ∈ closure (F.V : Set (Fin (n + m) → ℝ)),
        3 / 2 * Cdn * h ≤ (C.dl ξ η).toReal → nearKernel ν t h ξ η = 0) := by
  set S : Set (Fin (n + m) → ℝ) := closure (F.V : Set (Fin (n + m) → ℝ)) with hS
  have hSc : IsCompact S := hF.isCompact_closure
  have hSU : S ⊆ C.U := hF.closure_subset
  have hQ : 1 ≤ C.G.homogeneousDimension := G2.homogeneousDimension_pos C.G
  obtain ⟨A₀, B₀, hA₀, hB₀, hsz₀, hdf₀⟩ := PrincipalTerm.hasKernelBounds hF t hdeg hSc hSU
  obtain ⟨Cdn, hCdn, hdn⟩ := exists_dl_le_mul_nu C ν
  obtain ⟨hmax, Cl, hhmax, hCl, hlip⟩ :=
    exists_nearProfile_lipschitz C ν hν hCg hvar hSc hSU (3 / 2 * Cdn) (by positivity)
  set p : ℕ := C.G.homogeneousDimension - 1 with hp
  have hpQ : p + 1 = C.G.homogeneousDimension := Nat.sub_add_cancel hQ
  refine ⟨A₀, B₀ + 3 * Cdn * Cl * A₀ * 2 ^ p, Cdn, hmax, hA₀, by positivity, hCdn, hhmax,
    fun h hh hhm => ⟨?_, ?_, ?_⟩⟩
  · -- size
    intro ξ hξ η hη hne
    have h1 := hsz₀ ξ hξ η hη hne
    have hP := nearProfile_range ν h (C.Θ η ξ)
    unfold nearKernel
    rw [abs_mul, abs_of_nonneg hP.1]
    calc |t.kernel ξ η| * nearProfile ν h (C.Θ η ξ) ≤ |t.kernel ξ η| * 1 :=
          mul_le_mul_of_nonneg_left hP.2 (abs_nonneg _)
      _ = |t.kernel ξ η| := mul_one _
      _ ≤ _ := by simpa using h1
  · -- difference
    intro ξ hξ ξ' hξ' η hη hsep
    have hd0 : 0 ≤ (C.dl ξ ξ').toReal := ENNReal.toReal_nonneg
    set d : ℝ := (C.dl ξ ξ').toReal with hd
    set d' : ℝ := (C.dl ξ' η).toReal with hd'
    have hd'pos : 0 < d' := by linarith
    have hd₀ := hdf₀ ξ hξ ξ' hξ' η hη hsep
    have hd₁ : |t.kernel ξ' η - t.kernel ξ η| ≤ B₀ * d / d' ^ C.G.homogeneousDimension := by
      have e : ((C.G.homogeneousDimension : ℤ) + 1 - ((1 : ℕ) : ℤ)) =
          (C.G.homogeneousDimension : ℤ) := by push_cast; ring
      rw [e, zpow_natCast] at hd₀
      exact (le_add_of_nonneg_right (abs_nonneg _)).trans hd₀
    have hPP := nearProfile_range ν h (C.Θ η ξ')
    have hPP' := nearProfile_range ν h (C.Θ η ξ)
    -- split the difference
    have hsplit : nearKernel ν t h ξ' η - nearKernel ν t h ξ η =
        nearProfile ν h (C.Θ η ξ') * (t.kernel ξ' η - t.kernel ξ η) +
          t.kernel ξ η * (nearProfile ν h (C.Θ η ξ') - nearProfile ν h (C.Θ η ξ)) := by
      unfold nearKernel; ring
    have hfirst : |nearProfile ν h (C.Θ η ξ') * (t.kernel ξ' η - t.kernel ξ η)| ≤
        B₀ * d / d' ^ C.G.homogeneousDimension := by
      rw [abs_mul, abs_of_nonneg hPP.1]
      calc nearProfile ν h (C.Θ η ξ') * |t.kernel ξ' η - t.kernel ξ η|
          ≤ 1 * |t.kernel ξ' η - t.kernel ξ η| :=
            mul_le_mul_of_nonneg_right hPP.2 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hd₁
    have hsecond : |t.kernel ξ η * (nearProfile ν h (C.Θ η ξ') - nearProfile ν h (C.Θ η ξ))| ≤
        3 * Cdn * Cl * A₀ * 2 ^ p * d / d' ^ C.G.homogeneousDimension := by
      by_cases hz : nearProfile ν h (C.Θ η ξ') - nearProfile ν h (C.Θ η ξ) = 0
      · rw [hz, mul_zero, abs_zero]; positivity
      · -- one of the two profiles is nonzero: the points are at distance `O(h)` from `η`
        have hnz : nearProfile ν h (C.Θ η ξ') ≠ 0 ∨ nearProfile ν h (C.Θ η ξ) ≠ 0 := by
          by_contra hcon
          rw [not_or, not_not, not_not] at hcon
          exact hz (by rw [hcon.1, hcon.2]; ring)
        have hsymm1 : (C.dl ξ' ξ).toReal = d := by rw [hd, C.dl_symm ξ' ξ]
        have hsymm2 : (C.dl η ξ').toReal = d' := by rw [hd', C.dl_symm η ξ']
        have htri := C.dl_toReal_triangle (hSU hξ') (hSU hξ) (hSU hη)
        have hlow : d' - d ≤ (C.dl ξ η).toReal := by rw [hsymm1] at htri; linarith
        have hdη : d' / 2 < (C.dl ξ η).toReal := by linarith
        have hξη : ξ ≠ η := C.ne_of_dl_toReal_pos (hSU hξ) (by linarith)
        have hd'lt : d' < 3 * Cdn * h := by
          rcases hnz with h1 | h1
          · have h2 : ν (C.Θ η ξ') < 3 * h / 2 := by
              by_contra hc
              exact h1 (nearProfile_eq_zero ν hh (not_lt.mp hc))
            have h3 := hdn η (hSU hη) ξ' (hSU hξ')
            rw [hsymm2] at h3
            nlinarith
          · have h2 : ν (C.Θ η ξ) < 3 * h / 2 := by
              by_contra hc
              exact h1 (nearProfile_eq_zero ν hh (not_lt.mp hc))
            have h3 := hdn η (hSU hη) ξ (hSU hξ)
            have hs3 : (C.dl η ξ).toReal = (C.dl ξ η).toReal := by rw [C.dl_symm η ξ]
            rw [hs3] at h3
            have h4 : (C.dl ξ η).toReal < 3 / 2 * Cdn * h := by nlinarith
            linarith
        have hdlt : d ≤ 3 / 2 * Cdn * h := by linarith
        have hlipk := hlip h hh hhm η hη ξ' ξ (hSU hξ') (hSU hξ)
          (by rw [hsymm1]; exact hdlt)
        rw [hsymm1] at hlipk
        -- the size bound of the kernel at `(ξ, η)`
        have hsz := hsz₀ ξ hξ η hη hξη
        have e1 : (1 : ℤ) - (C.G.homogeneousDimension : ℤ) = -(p : ℤ) := by
          rw [hp, Nat.cast_sub hQ]; push_cast; ring
        have e1' : ((1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ) = -(p : ℤ) := by
          rw [Nat.cast_one]; exact e1
        rw [e1', zpow_neg, zpow_natCast] at hsz
        have hdη_pos : 0 < (C.dl ξ η).toReal := by linarith
        have hpow : ((C.dl ξ η).toReal ^ p)⁻¹ ≤ 2 ^ p * (d' ^ p)⁻¹ := by
          have h1 : (d' / 2) ^ p ≤ (C.dl ξ η).toReal ^ p :=
            pow_le_pow_left₀ (by positivity) hdη.le p
          calc ((C.dl ξ η).toReal ^ p)⁻¹ ≤ ((d' / 2) ^ p)⁻¹ :=
                inv_anti₀ (by positivity) h1
            _ = 2 ^ p * (d' ^ p)⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]
        have hinvh : h⁻¹ ≤ 3 * Cdn / d' := by
          rw [inv_eq_one_div, div_le_div_iff₀ hh hd'pos]; nlinarith
        have hPdiff := hlipk
        rw [abs_mul]
        calc |t.kernel ξ η| * |nearProfile ν h (C.Θ η ξ') - nearProfile ν h (C.Θ η ξ)|
            ≤ (A₀ * ((C.dl ξ η).toReal ^ p)⁻¹) * (Cl * d / h) :=
              mul_le_mul hsz hPdiff (abs_nonneg _) (by positivity)
          _ ≤ (A₀ * (2 ^ p * (d' ^ p)⁻¹)) * (Cl * d * (3 * Cdn / d')) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hA₀) ?_ (by positivity)
                (by positivity)
              rw [div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_left hinvh (by positivity)
          _ = 3 * Cdn * Cl * A₀ * 2 ^ p * d / d' ^ C.G.homogeneousDimension := by
              rw [← hpQ, pow_succ]
              field_simp
    rw [hsplit]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ B₀ * d / d' ^ C.G.homogeneousDimension +
          3 * Cdn * Cl * A₀ * 2 ^ p * d / d' ^ C.G.homogeneousDimension :=
          add_le_add hfirst hsecond
      _ = _ := by ring
  · -- support
    intro ξ hξ η hη hge
    unfold nearKernel
    have h1 := hdn η (hSU hη) ξ (hSU hξ)
    have hs3 : (C.dl η ξ).toReal = (C.dl ξ η).toReal := by rw [C.dl_symm η ξ]
    rw [hs3] at h1
    have hν3 : 3 * h / 2 ≤ ν (C.Θ η ξ) := by
      by_contra hc
      have := not_le.mp hc
      nlinarith
    rw [nearProfile_eq_zero ν hh hν3, mul_zero]

/-- The operator of a kernel supported (off the diagonal) in `V × V` is the slice integral
over the patch `S ⊇ V`: for `x ∈ V`, `∫ κ(x, η) f(η) dη = ∫_S κ_S(x, η) (1_V f)(η) dη`. -/
theorem integral_eq_slice_indicator (C : LiftedChart w st Ω hΩ X x₀ m)
    {S V : Set (Fin (n + m) → ℝ)} (hVS : V ⊆ S) {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hsupp : ∀ ξ η, ξ ≠ η → (ξ ∉ V ∨ η ∉ V) → κ ξ η = 0) (f : (Fin (n + m) → ℝ) → ℝ)
    {x : Fin (n + m) → ℝ} (hx : x ∈ V) :
    ∫ η, κ x η * f η = ∫ η in S, sliceKernel S κ x η * V.indicator f η := by
  have e1 : ∀ η, κ x η * f η = κ x η * V.indicator f η := by
    intro η
    by_cases hη : η ∈ V
    · rw [Set.indicator_of_mem hη]
    · have hne : x ≠ η := fun h => hη (h ▸ hx)
      rw [hsupp x η hne (Or.inr hη), zero_mul, zero_mul]
  simp_rw [e1]
  have e2 : ∀ η, η ∉ S → κ x η * V.indicator f η = 0 := fun η hη => by
    rw [Set.indicator_of_notMem (fun h => hη (hVS h)), mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero e2]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (C.ae_ne x)] with η hηx
  by_cases hη : η ∈ S
  · by_cases hxS : x ∈ S
    · rw [sliceKernel_of_mem hxS hη hηx.symm]
    · exact absurd (hVS hx) hxS
  · rw [e2 η hη, sliceKernel_of_not_mem (Or.inr (Or.inl hη)), zero_mul]

/-- **The near part** (BB pp. 594-595, Lem 11.51: "the near kernel is a fractional kernel
with constant `C h^η`, whose `C^α` bound is `C h^η ‖L̃ v‖_∞`"): there are `Cn > 0` and `h₀ ∈ (0, 1]`
such that for `0 < h ≤ h₀`, every `f` measurable on `V` with `|f| ≤ M` on `V` and `x, y ∈ V`,
`|∫ κ_h(x, η) f(η) dη| ≤ Cn h^{1-α} M` and
`|∫ κ_h(x, ·) f - ∫ κ_h(y, ·) f| ≤ Cn h^{1-α} M d̃(x, y)^α`. -/
theorem exists_near_bound (hF : C.IsLiftedFrame F) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) (t : PrincipalTerm F) (hdeg : t.degree ≤ 1) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hvar : LiftedVariation C Cg) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ Cn h₀ : ℝ, 0 < Cn ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ f : (Fin (n + m) → ℝ) → ℝ,
        AEStronglyMeasurable f (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →
        ∀ M : ℝ, 0 ≤ M → (∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |f y| ≤ M) →
        (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)),
          |∫ η, nearKernel ν t h x η * f η| ≤ Cn * h ^ (1 - α) * M) ∧
        (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)),
          |(∫ η, nearKernel ν t h x η * f η) - ∫ η, nearKernel ν t h y η * f η| ≤
            Cn * h ^ (1 - α) * M * (C.dl x y).toReal ^ α) := by
  set S : Set (Fin (n + m) → ℝ) := closure (F.V : Set (Fin (n + m) → ℝ)) with hS
  have hSc : IsCompact S := hF.isCompact_closure
  have hSU : S ⊆ C.U := hF.closure_subset
  have hVS : (F.V : Set (Fin (n + m) → ℝ)) ⊆ S := subset_closure
  have hVm : MeasurableSet (F.V : Set (Fin (n + m) → ℝ)) := F.V.isOpen.measurableSet
  obtain ⟨A, B, Cdn, hmax, hA, hB, hCdn, hhmax, hest⟩ :=
    nearKernel_estimates hF ν hν t hdeg hCg hvar
  obtain ⟨ρ, Cv, hSh⟩ := C.exists_shellData_patch hSc hSU
  set q : ℕ := C.G.homogeneousDimension - 1 with hq
  have hC₁ : 0 ≤ Cv * 2 ^ (q + 1) := by have := hSh.Cv_nonneg; positivity
  have hCα0' : 0 ≤ holderConst A B Cv q α := by
    have hα' : 0 < 1 - α := by linarith
    have := hSh.Cv_nonneg
    unfold holderConst; positivity
  set Cα : ℝ := holderConst A B Cv q α with hCα
  have hCα0 : 0 ≤ Cα := hCα0'
  set r₁ : ℝ := 3 / 2 * Cdn with hr₁
  have hr₁0 : 0 < r₁ := by positivity
  refine ⟨A * (Cv * 2 ^ (q + 1)) * r₁ + (3 * Cα + 2 * A * (Cv * 2 ^ (q + 1))) * r₁ ^ (1 - α) + 1,
    min (hmax / 2) 1, by positivity, lt_min (by linarith) one_pos, min_le_right _ _, ?_⟩
  intro h hh hh₀ f hf M hM0 hM
  have hhm : h < hmax := lt_of_le_of_lt (hh₀.trans (min_le_left _ _)) (by linarith)
  have hh1 : h ≤ 1 := hh₀.trans (min_le_right _ _)
  obtain ⟨hsz, hdf, hsupp⟩ := hest h hh hhm
  -- measurability of the sliced near kernel
  have hmeas : Measurable (Function.uncurry (sliceKernel S (nearKernel ν t h))) := by
    refine measurable_sliceKernel_of_continuousOn hSc.measurableSet ?_
    have hΘ : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ z.2 z.1)
        ((S ×ˢ S) \ Set.diagonal (Fin (n + m) → ℝ)) :=
      (C.theta_continuousOn.comp (continuous_snd.prodMk continuous_fst).continuousOn
        (fun z hz => ⟨hSU hz.1.2, hSU hz.1.1⟩))
    have hφ : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        nearProfile ν h (C.Θ z.2 z.1)) ((S ×ˢ S) \ Set.diagonal (Fin (n + m) → ℝ)) :=
      (contDiff_nearProfile ν hν hh).continuous.comp_continuousOn hΘ
    exact (PrincipalTerm.continuousOn_kernel hF t hSU).mul hφ
  have hK := sliceBounds_of_estimates C hSU hA hB hmeas hsz hdf
  set r₀ : ℝ := 3 / 2 * Cdn * h with hr₀
  have hr₀0 : 0 < r₀ := by positivity
  have hsupp' : ∀ x ∈ S, ∀ y ∈ S, r₀ ≤ (fun x y => (C.dl x y).toReal) x y →
      sliceKernel S (nearKernel ν t h) x y = 0 := by
    intro x hx y hy hge
    by_cases hxy : x = y
    · exact sliceKernel_of_not_mem (Or.inr (Or.inr hxy))
    · rw [sliceKernel_of_mem hx hy hxy]
      exact hsupp x hx y hy hge
  -- the function `1_V f`
  set g : (Fin (n + m) → ℝ) → ℝ := (F.V : Set (Fin (n + m) → ℝ)).indicator f with hg
  have hgm : AEStronglyMeasurable g (volume.restrict S) := by
    refine (aestronglyMeasurable_indicator_iff hVm).mpr ?_
    rw [Measure.restrict_restrict hVm, inter_eq_left.mpr hVS]
    exact hf
  have hgM : ∀ y ∈ S, |g y| ≤ M := by
    intro y _
    by_cases hy : y ∈ (F.V : Set (Fin (n + m) → ℝ))
    · rw [hg, Set.indicator_of_mem hy]; exact hM y hy
    · rw [hg, Set.indicator_of_notMem hy, abs_zero]; exact hM0
  have hsupport : ∀ ξ η, ξ ≠ η → (ξ ∉ (F.V : Set (Fin (n + m) → ℝ)) ∨
      η ∉ (F.V : Set (Fin (n + m) → ℝ))) → nearKernel ν t h ξ η = 0 := by
    intro ξ η _ hout
    unfold nearKernel
    rw [t.kernel_eq_zero_of_not_mem hout, zero_mul]
  have hrep : ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), ∫ η, nearKernel ν t h x η * f η =
      ∫ η in S, sliceKernel S (nearKernel ν t h) x η * g η :=
    fun x hx => integral_eq_slice_indicator C hVS hsupport f hx
  have hrh : r₀ ^ (1 - α) = r₁ ^ (1 - α) * h ^ (1 - α) := by
    rw [hr₀, Real.mul_rpow (by positivity) hh.le]
  have hhα : h ≤ h ^ (1 - α) := by
    calc h = h ^ (1 : ℝ) := (Real.rpow_one h).symm
      _ ≤ h ^ (1 - α) := Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)
  have hhpos : 0 < h ^ (1 - α) := Real.rpow_pos_of_pos hh _
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [hrep x hx]
    refine (sup_bound_of_support hSh hK hr₀0 hsupp' hM0 hgM (hVS hx)).trans ?_
    have h1 : A * M * (Cv * 2 ^ (q + 1)) * r₀ ≤
        A * (Cv * 2 ^ (q + 1)) * r₁ * h ^ (1 - α) * M := by
      calc A * M * (Cv * 2 ^ (q + 1)) * r₀
          = A * (Cv * 2 ^ (q + 1)) * r₁ * h * M := by rw [hr₀, hr₁]; ring
        _ ≤ A * (Cv * 2 ^ (q + 1)) * r₁ * h ^ (1 - α) * M := by
            gcongr
    refine h1.trans ?_
    have h2 : 0 ≤ (3 * Cα + 2 * A * (Cv * 2 ^ (q + 1))) * r₁ ^ (1 - α) := by positivity
    nlinarith [mul_nonneg hhpos.le hM0, mul_nonneg (mul_nonneg h2 hhpos.le) hM0]
  · rw [hrep x hx, hrep y hy]
    refine (holder_bound_of_support hSh hK hr₀0 hsupp' hα0 hα1 hgm hM0 hgM (hVS hx) (hVS hy)).trans ?_
    rw [hrh]
    have hd : 0 ≤ (C.dl x y).toReal ^ α := Real.rpow_nonneg ENNReal.toReal_nonneg _
    have h2 : 0 ≤ (3 * Cα + 2 * A * (Cv * 2 ^ (q + 1))) * r₁ ^ (1 - α) := by positivity
    have h3 : 0 ≤ h ^ (1 - α) * M * (C.dl x y).toReal ^ α := by positivity
    have h4 := mul_nonneg (by positivity : (0 : ℝ) ≤ A * (Cv * 2 ^ (q + 1)) * r₁ + 1) h3
    nlinarith [mul_nonneg h2 h3, h4]

end RothschildStein.P2
