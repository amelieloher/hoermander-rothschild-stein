-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FractionalInterpolationScaling
public import RothschildStein.H3.SmoothGaugeCutoff
public import RothschildStein.G2.Gauge

/-!
# Hölder interpolation: the near/far cutoff at scale `h`

The kernel of the fixed type-`λ` operator is split at the scale `h` by the smooth radial profile
`nearProfile ν h (u) = quasiballProfile (4h/3) (5h/3) (ν u)` of the smooth homogeneous norm `ν`
(equal to `1` for `ν u ≤ 4h/3`, `0` for `ν u ≥ 3h/2`). It is a dilation of one fixed profile:
`nearProfile ν h = nearProfile ν 1 ∘ δ_{1/h}`, so its iterated derivatives are `O(‖δ_{1/h}‖^j)`
(`iteratedFDeriv_profZ_le`). A **polynomial bound** predicate `PolyBdd` in `x = 1/h` keeps track of
the growth of the constants as `h → 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P2

section Poly

/-- `f` is bounded by a polynomial in `x ≥ 1` (`x = 1/h`, `h ∈ (0, 1]`). -/
def PolyBdd (f : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |f x| ≤ C * x ^ M

theorem PolyBdd.const (c : ℝ) : PolyBdd (fun _ => c) :=
  ⟨|c|, 0, abs_nonneg _, fun x _ => by simp⟩

theorem PolyBdd.id : PolyBdd (fun x => x) :=
  ⟨1, 1, zero_le_one, fun x hx => by
    simp [abs_of_nonneg (zero_le_one.trans hx)]⟩

theorem PolyBdd.mono {f g : ℝ → ℝ} (hg : PolyBdd g) (h : ∀ x : ℝ, 1 ≤ x → |f x| ≤ |g x|) :
    PolyBdd f := by
  obtain ⟨C, M, hC, hg⟩ := hg
  exact ⟨C, M, hC, fun x hx => (h x hx).trans (hg x hx)⟩

theorem PolyBdd.add {f g : ℝ → ℝ} (hf : PolyBdd f) (hg : PolyBdd g) :
    PolyBdd (fun x => f x + g x) := by
  obtain ⟨C₁, M₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, M₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, max M₁ M₂, add_nonneg hC₁ hC₂, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have e1 : x ^ M₁ ≤ x ^ max M₁ M₂ := pow_le_pow_right₀ hx (le_max_left _ _)
  have e2 : x ^ M₂ ≤ x ^ max M₁ M₂ := pow_le_pow_right₀ hx (le_max_right _ _)
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ C₁ * x ^ M₁ + C₂ * x ^ M₂ := add_le_add (h₁ x hx) (h₂ x hx)
    _ ≤ C₁ * x ^ max M₁ M₂ + C₂ * x ^ max M₁ M₂ :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hC₁) (mul_le_mul_of_nonneg_left e2 hC₂)
    _ = (C₁ + C₂) * x ^ max M₁ M₂ := by ring

theorem PolyBdd.mul {f g : ℝ → ℝ} (hf : PolyBdd f) (hg : PolyBdd g) :
    PolyBdd (fun x => f x * g x) := by
  obtain ⟨C₁, M₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, M₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, M₁ + M₂, mul_nonneg hC₁ hC₂, fun x hx => ?_⟩
  rw [abs_mul, pow_add]
  calc |f x| * |g x| ≤ (C₁ * x ^ M₁) * (C₂ * x ^ M₂) :=
        mul_le_mul (h₁ x hx) (h₂ x hx) (abs_nonneg _) (mul_nonneg hC₁ (by positivity))
    _ = C₁ * C₂ * (x ^ M₁ * x ^ M₂) := by ring

theorem PolyBdd.pow {f : ℝ → ℝ} (hf : PolyBdd f) (n : ℕ) : PolyBdd (fun x => f x ^ n) := by
  induction n with
  | zero => simpa using PolyBdd.const 1
  | succ n ih => simpa [pow_succ] using ih.mul hf

theorem PolyBdd.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, PolyBdd (f i)) :
    PolyBdd (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyBdd.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem PolyBdd.zpow_nat {n : ℕ} : PolyBdd (fun x : ℝ => x ^ n) := PolyBdd.id.pow n

theorem polyBdd_dilNorm {N : ℕ} (G : HomogeneousGroup N) : PolyBdd (fun x => dilNorm G x) := by
  refine PolyBdd.sum _ fun j _ => ?_
  refine PolyBdd.mono (g := fun x => x ^ G.weight j) PolyBdd.zpow_nat fun x hx => ?_
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  simp [abs_of_nonneg hx0]

end Poly

variable {N : ℕ} {G : HomogeneousGroup N}

/-- The smooth near cutoff at scale `h`: `1` for `ν u ≤ 4h/3`, `0` for `ν u ≥ 3h/2`. -/
def nearProfile (ν : G2.HomogeneousNorm G) (h : ℝ) (u : Fin N → ℝ) : ℝ :=
  H3.quasiballProfile (4 * h / 3) (5 * h / 3) (ν u)

/-- The smooth far cutoff `1 - nearProfile`. -/
def farProfile (ν : G2.HomogeneousNorm G) (h : ℝ) (u : Fin N → ℝ) : ℝ := 1 - nearProfile ν h u

theorem nearProfile_range (ν : G2.HomogeneousNorm G) (h : ℝ) (u : Fin N → ℝ) :
    0 ≤ nearProfile ν h u ∧ nearProfile ν h u ≤ 1 :=
  H3.quasiballProfile_range _ _ _

theorem farProfile_range (ν : G2.HomogeneousNorm G) (h : ℝ) (u : Fin N → ℝ) :
    0 ≤ farProfile ν h u ∧ farProfile ν h u ≤ 1 := by
  have := nearProfile_range ν h u
  unfold farProfile; constructor <;> linarith [this.1, this.2]

theorem nearProfile_eq_one (ν : G2.HomogeneousNorm G) {h : ℝ} (hh : 0 < h) {u : Fin N → ℝ}
    (hu : ν u ≤ 4 * h / 3) : nearProfile ν h u = 1 :=
  H3.quasiballProfile_one (by linarith) hu

theorem nearProfile_eq_zero (ν : G2.HomogeneousNorm G) {h : ℝ} (hh : 0 < h) {u : Fin N → ℝ}
    (hu : 3 * h / 2 ≤ ν u) : nearProfile ν h u = 0 :=
  H3.quasiballProfile_zero (by linarith) (by linarith)

theorem farProfile_eq_zero (ν : G2.HomogeneousNorm G) {h : ℝ} (hh : 0 < h) {u : Fin N → ℝ}
    (hu : ν u ≤ 4 * h / 3) : farProfile ν h u = 0 := by
  unfold farProfile; rw [nearProfile_eq_one ν hh hu]; norm_num

theorem contDiff_nearProfile (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ (⊤ : ℕ∞) (nearProfile ν h) :=
  H3.contDiff_radial_quasiballProfile ν hν (by linarith) (by linarith)

theorem contDiff_farProfile (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ (⊤ : ℕ∞) (farProfile ν h) :=
  contDiff_const.sub (contDiff_nearProfile ν hν hh)

/-- **The profile is a dilation of the fixed profile**: `nearProfile ν h = nearProfile ν 1 ∘ δ_{1/h}`. -/
theorem nearProfile_eq_dilate (ν : G2.HomogeneousNorm G) {h : ℝ} (hh : 0 < h)
    (u : Fin N → ℝ) : nearProfile ν h u = nearProfile ν 1 (G.dilate h⁻¹ u) := by
  unfold nearProfile H3.quasiballProfile
  rw [ν.gauge.2.2.2 h⁻¹ (inv_pos.mpr hh) u]
  congr 1
  field_simp

theorem farProfile_eq_dilate (ν : G2.HomogeneousNorm G) {h : ℝ} (hh : 0 < h) (u : Fin N → ℝ) :
    farProfile ν h u = farProfile ν 1 (G.dilate h⁻¹ u) := by
  unfold farProfile; rw [nearProfile_eq_dilate ν hh u]

theorem hasCompactSupport_nearProfile (ν : G2.HomogeneousNorm G) :
    HasCompactSupport (nearProfile ν 1) := by
  refine HasCompactSupport.intro (K := {u | ν u ≤ 3 / 2}) (G2.isCompact_gauge_le ν.gauge _)
    fun u hu => ?_
  refine nearProfile_eq_zero ν one_pos ?_
  have : 3 / 2 < ν u := not_le.mp hu
  linarith

/-- The iterated derivatives of the fixed profile `nearProfile ν 1` are bounded. -/
theorem exists_bound_iteratedFDeriv_nearProfile (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (j : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ u, ‖iteratedFDeriv ℝ j (nearProfile ν 1) u‖ ≤ D := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (nearProfile ν 1) := contDiff_nearProfile ν hν one_pos
  have hcont : Continuous (iteratedFDeriv ℝ j (nearProfile ν 1)) :=
    hc.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨D, hD⟩ := hcont.bounded_above_of_compact_support
    ((hasCompactSupport_nearProfile ν).iteratedFDeriv j)
  exact ⟨max D 0, le_max_right _ _, fun u => (hD u).trans (le_max_left _ _)⟩

/-- The iterated derivatives of the fixed far profile `farProfile ν 1` are bounded. -/
theorem exists_bound_iteratedFDeriv_farProfile (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (j : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ u, ‖iteratedFDeriv ℝ j (farProfile ν 1) u‖ ≤ D := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_iteratedFDeriv_nearProfile ν hν j
  have hc : ContDiff ℝ (⊤ : ℕ∞) (nearProfile ν 1) := contDiff_nearProfile ν hν one_pos
  refine ⟨max D 1, le_max_of_le_left hD0, fun u => ?_⟩
  by_cases hj : j = 0
  · subst hj
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have := farProfile_range ν 1 u
    rw [abs_of_nonneg this.1]
    exact this.2.trans (le_max_right _ _)
  · have h1 : iteratedFDeriv ℝ j (farProfile ν 1) u = - iteratedFDeriv ℝ j (nearProfile ν 1) u := by
      have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) (x := u) (f := fun _ : Fin N → ℝ => (1 : ℝ))
        (g := nearProfile ν 1) (contDiffAt_const.of_le (by exact_mod_cast le_top))
        (hc.contDiffAt.of_le (by exact_mod_cast le_top))
      rw [iteratedFDeriv_const_of_ne hj] at this
      simp only [Pi.zero_apply, zero_sub] at this
      exact this
    rw [h1, norm_neg]
    exact (hD u).trans (le_max_left _ _)

/-- The coordinate projection `(ξ, η, u) ↦ u`. -/
def pr3 (N : ℕ) : Z3 N →L[ℝ] (Fin N → ℝ) :=
  (ContinuousLinearMap.snd ℝ (Fin N → ℝ) (Fin N → ℝ)).comp
    (ContinuousLinearMap.snd ℝ (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ)))

theorem norm_pr3_le (N : ℕ) : ‖pr3 N‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  have : ‖z.2.2‖ ≤ ‖z‖ := (norm_snd_le z.2).trans (norm_snd_le z)
  simpa [pr3] using this

theorem pr3_apply (z : Z3 N) : pr3 N z = z.2.2 := rfl

/-- **Derivative bounds of the far profile at scale `h`**: for every `j` there is `D` with
`‖D^j (z ↦ farProfile ν h z.2.2)‖ ≤ D ‖δ_{1/h}‖^j`-bound `D (dilNorm (1/h))^j`, for all `h > 0`. -/
theorem exists_iteratedFDeriv_farProfileZ_le (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) (j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ h : ℝ, 0 < h → ∀ z : Z3 N,
      ‖iteratedFDeriv ℝ j (fun z : Z3 N => farProfile ν h z.2.2) z‖ ≤
        D * (dilNorm G h⁻¹) ^ j := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_iteratedFDeriv_farProfile ν hν j
  refine ⟨D, hD0, fun h hh z => ?_⟩
  have hc : ContDiff ℝ (⊤ : ℕ∞) (farProfile ν 1) := contDiff_farProfile ν hν one_pos
  set g : Z3 N →L[ℝ] (Fin N → ℝ) := (dilCLM G h⁻¹).comp (pr3 N) with hg
  have e : (fun z : Z3 N => farProfile ν h z.2.2) = (farProfile ν 1) ∘ g := by
    funext z
    simp [hg, dilCLM_apply, pr3_apply, farProfile_eq_dilate ν hh z.2.2]
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right g hc z (by exact_mod_cast le_top)]
  have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j (farProfile ν 1) (g z)) (fun _ : Fin j => g)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  have hgn : ‖g‖ ≤ dilNorm G h⁻¹ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_dilCLM_le G _) (norm_pr3_le N) (norm_nonneg _) (dilNorm_nonneg G _)).trans
        (by simp))
  calc _ ≤ ‖iteratedFDeriv ℝ j (farProfile ν 1) (g z)‖ * ‖g‖ ^ j := hb
    _ ≤ D * dilNorm G h⁻¹ ^ j :=
        mul_le_mul (hD _) (pow_le_pow_left₀ (norm_nonneg _) hgn j) (by positivity) hD0

end RothschildStein.P2
