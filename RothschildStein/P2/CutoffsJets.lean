-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.CutoffsHomogeneous
public import RothschildStein.G2.Gauge
public import RothschildStein.Definitions.rsPartial
public import RothschildStein.Definitions.WeightedJet

/-!
# Weighted Taylor bound and symbols from vanishing jets

A parameter family `F η u`, jointly smooth on an open set `T` containing `Kc × {ν ≤ ρ}`, all
of whose weighted Taylor coefficients of weight `< D` vanish at `u = 0` for every `η ∈ Kc`,
satisfies `|F η u| ≤ C ν(u)^D` uniformly (the finite weighted Taylor remainder bound,
BB pp. 547–548), and lies in every symbol class `Sym c k D`.
The proof is by induction on `D`: along the dilation path `s ↦ F η (δ_s u)` the derivative is
`∑ ω_i s^{ω_i - 1} u_i (∂_i F)(δ_s u)` and `∂_i F` has vanishing jets below `D - ω_i`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P2

variable {N : ℕ}

/-- All weighted Taylor coefficients of weight `< D` vanish at the origin. -/
def JetVanish (ω : Fin N → ℕ) (D : ℤ) (f : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ J : List (Fin N), (((J.map ω).sum : ℕ) : ℤ) < D → rsPartial J f 0 = 0

theorem weightedJet_iff {ω : Fin N → ℕ} {a : ℤ} {R : (Fin N → ℝ) → (Fin N → ℝ)} :
    WeightedJet ω a R ↔ ∀ j, JetVanish ω (a + (ω j : ℤ)) (fun u => R u j) := by
  unfold WeightedJet JetVanish
  constructor <;> intro h j J hJ <;> exact h j J hJ

theorem JetVanish.of_nonpos {ω : Fin N → ℕ} {D : ℤ} (hD : D ≤ 0) (f : (Fin N → ℝ) → ℝ) :
    JetVanish ω D f := by
  intro J hJ
  have : (0 : ℤ) ≤ (((J.map ω).sum : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

theorem rsPartial_germ (J : List (Fin N)) {f g : (Fin N → ℝ) → ℝ} {u : Fin N → ℝ}
    (h : f =ᶠ[𝓝 u] g) : rsPartial J f =ᶠ[𝓝 u] rsPartial J g := by
  induction J with
  | nil => exact h
  | cons j J ih =>
    filter_upwards [ih.eventuallyEq_nhds] with y hy
    simp only [rsPartial, hy.fderiv_eq]

theorem rsPartial_append (J : List (Fin N)) (j : Fin N) (f : (Fin N → ℝ) → ℝ) :
    rsPartial J (rsPartial [j] f) = rsPartial (J ++ [j]) f := by
  induction J with
  | nil => rfl
  | cons j' J ih =>
    funext u
    have h1 : rsPartial (j' :: J) (rsPartial [j] f) u =
        fderiv ℝ (rsPartial J (rsPartial [j] f)) u (Pi.single j' 1) := rfl
    have h2 : rsPartial (j' :: (J ++ [j])) f u =
        fderiv ℝ (rsPartial (J ++ [j]) f) u (Pi.single j' 1) := rfl
    rw [List.cons_append, h1, h2, ih]

theorem fderiv_prod_partial {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    {T : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hT : IsOpen T) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F T)
    {η u : Fin N → ℝ} (h : (η, u) ∈ T) (v : Fin N → ℝ) :
    fderiv ℝ F (η, u) (0, v) = fderiv ℝ (fun w => F (η, w)) u v := by
  have hd : DifferentiableAt ℝ F (η, u) :=
    (hF.contDiffAt (hT.mem_nhds h)).differentiableAt (by simp)
  have h' : HasFDerivAt (fun w => F (η, w))
      ((fderiv ℝ F (η, u)).comp (ContinuousLinearMap.inr ℝ _ _)) u :=
    hd.hasFDerivAt.comp u (hasFDerivAt_prodMk_right η u)
  rw [h'.fderiv]
  simp

theorem contDiffOn_slice {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    {T : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F T) (η : Fin N → ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w => F (η, w)) {w | (η, w) ∈ T} :=
  hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hw => hw)

theorem isOpen_slice {T : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hT : IsOpen T) (η : Fin N → ℝ) :
    IsOpen {w : Fin N → ℝ | (η, w) ∈ T} :=
  hT.preimage (continuous_const.prodMk continuous_id)

theorem contDiffOn_partial {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    {T : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hT : IsOpen T) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F T)
    (v : Fin N → ℝ) : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ F z (0, v)) T :=
  (hF.fderiv_of_isOpen hT (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffOn_const

theorem JetVanish.pdv_family {ω : Fin N → ℕ} {D : ℤ} {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    {T : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hT : IsOpen T) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F T)
    {η : Fin N → ℝ} (h0 : (η, (0 : Fin N → ℝ)) ∈ T) (hJ : JetVanish ω D (fun u => F (η, u)))
    (j : Fin N) :
    JetVanish ω (D - (ω j : ℤ)) (fun u => fderiv ℝ F (η, u) (0, Pi.single j 1)) := by
  intro J hJw
  have hslice : {w : Fin N → ℝ | (η, w) ∈ T} ∈ 𝓝 (0 : Fin N → ℝ) :=
    (isOpen_slice hT η).mem_nhds h0
  have hgerm : (fun u => fderiv ℝ F (η, u) (0, Pi.single j 1)) =ᶠ[𝓝 0]
      rsPartial [j] (fun u => F (η, u)) := by
    filter_upwards [hslice] with u hu
    exact fderiv_prod_partial hT hF hu _
  rw [(rsPartial_germ J hgerm).self_of_nhds, rsPartial_append]
  apply hJ
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Nat.cast_add]
  omega

theorem exists_abs_coord_le (G : HomogeneousGroup N) {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : Fin N → ℝ) (i : Fin N), |u i| ≤ c * ν u ^ G.weight i := by
  obtain ⟨a, b, ha, hb, hab⟩ := G2.gauge_equivalent_max hν
  refine ⟨1 + ∑ i, (a⁻¹) ^ G.weight i, by positivity, fun u i => ?_⟩
  have h1 := G2.coordinate_root_le_gauge G u i
  have hμ : rsGauge G.weight G.weight_pos u ≤ ν u / a := by
    rw [le_div_iff₀ ha]
    linarith [(hab u).1]
  have h2 : |u i| ≤ rsGauge G.weight G.weight_pos u ^ G.weight i := by
    have := (Real.rpow_inv_le_iff_of_pos (abs_nonneg (u i)) (G2.gauge_nonneg G u)
      (Nat.cast_pos.mpr (G.weight_pos i))).mp (by simpa only [Real.rpow_eq_pow] using h1)
    simpa [Real.rpow_natCast] using this
  have h3 : rsGauge G.weight G.weight_pos u ^ G.weight i ≤ (ν u / a) ^ G.weight i :=
    pow_le_pow_left₀ (G2.gauge_nonneg G u) hμ _
  have h4 : (ν u / a) ^ G.weight i = (a⁻¹) ^ G.weight i * ν u ^ G.weight i := by
    rw [div_eq_inv_mul, mul_pow]
  have h5 : (a⁻¹) ^ G.weight i ≤ 1 + ∑ i, (a⁻¹) ^ G.weight i := by
    have := Finset.single_le_sum (f := fun i => (a⁻¹) ^ G.weight i)
      (fun i _ => pow_nonneg (inv_nonneg.mpr ha.le) _) (Finset.mem_univ i)
    linarith
  calc |u i| ≤ (ν u / a) ^ G.weight i := h2.trans h3
    _ = (a⁻¹) ^ G.weight i * ν u ^ G.weight i := h4
    _ ≤ (1 + ∑ i, (a⁻¹) ^ G.weight i) * ν u ^ G.weight i :=
      mul_le_mul_of_nonneg_right h5 (pow_nonneg (hν.2.1 u) _)

theorem dilate_zero (G : HomogeneousGroup N) (u : Fin N → ℝ) : G.dilate 0 u = 0 := by
  ext i
  simp [HomogeneousGroup.dilate, coordinateDilation, zero_pow (G.weight_pos i).ne']

theorem dilate_one (G : HomogeneousGroup N) (u : Fin N → ℝ) : G.dilate 1 u = u := by
  ext i
  simp [HomogeneousGroup.dilate, coordinateDilation]

theorem gauge_dilate_le (G : HomogeneousGroup N) {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (u : Fin N → ℝ) :
    ν (G.dilate s u) ≤ ν u := by
  rcases hs0.eq_or_lt with h | h
  · subst h
    rw [dilate_zero, (hν.2.2.1 0).mpr rfl]
    exact hν.2.1 u
  · rw [hν.2.2.2 s h]
    nlinarith [hν.2.1 u]

theorem term_bound {ν ν' s c C u p : ℝ} {w D D' : ℕ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hν' : 0 ≤ ν') (hνν' : ν' ≤ ν) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hu : |u| ≤ c * ν ^ w) (hp : |p| ≤ C * ν' ^ D') (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hD : D ≤ w + D') :
    |(w : ℝ) * s ^ (w - 1) * u * p| ≤ w * c * C * ν ^ D := by
  have hs : s ^ (w - 1) ≤ 1 := pow_le_one₀ hs0 hs1
  have hs' : 0 ≤ s ^ (w - 1) := pow_nonneg hs0 _
  have hp' : |p| ≤ C * ν ^ D' :=
    hp.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hν' hνν' _) hC)
  have hpow : ν ^ (w + D') ≤ ν ^ D := pow_le_pow_of_le_one hν0 hν1 hD
  have hu0 : 0 ≤ c * ν ^ w := (abs_nonneg _).trans hu
  calc |(w : ℝ) * s ^ (w - 1) * u * p|
      = (w : ℝ) * s ^ (w - 1) * |u| * |p| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs', abs_of_nonneg (Nat.cast_nonneg w)]
    _ ≤ (w : ℝ) * 1 * (c * ν ^ w) * (C * ν ^ D') := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg w)
          · exact hu
          · exact abs_nonneg _
          · positivity
        · exact hp'
        · exact abs_nonneg _
        · positivity
    _ = w * c * C * ν ^ (w + D') := by rw [pow_add]; ring
    _ ≤ w * c * C * ν ^ D := by
        apply mul_le_mul_of_nonneg_left hpow
        positivity

/-- The weighted Taylor remainder bound: vanishing weighted jets below `D` give
`|F η u| ≤ C ν(u)^D` uniformly in `η ∈ Kc` (BB pp. 547–548). -/
theorem jet_bound (G : HomogeneousGroup N) {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {Kc : Set (Fin N → ℝ)} (hKc : IsCompact Kc)
    {T : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hT : IsOpen T)
    (hKT : ∀ η ∈ Kc, ∀ u, ν u ≤ ρ → (η, u) ∈ T) :
    ∀ (D : ℕ) (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) F T →
      (∀ η ∈ Kc, JetVanish G.weight (D : ℤ) (fun u => F (η, u))) →
      ∃ C : ℝ, ∀ η ∈ Kc, ∀ u, ν u ≤ ρ → |F (η, u)| ≤ C * ν u ^ D := by
  have hν0 : ν 0 = 0 := (hν.2.2.1 0).mpr rfl
  have hcomp : IsCompact (Kc ×ˢ {u : Fin N → ℝ | ν u ≤ ρ}) :=
    hKc.prod (G2.isCompact_gauge_le hν ρ)
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro F hF hJ
    obtain ⟨B, hB⟩ := hcomp.exists_bound_of_continuousOn
      (hF.continuousOn.mono (fun z hz => hKT z.1 hz.1 z.2 hz.2))
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      exact ⟨B, fun η hη u hu => by simpa using hB (η, u) ⟨hη, hu⟩⟩
    · obtain ⟨c, hc, hcoord⟩ := exists_abs_coord_le G hν
      have hdiff : ∀ j : Fin N, ∃ Cj : ℝ, ∀ η ∈ Kc, ∀ u, ν u ≤ ρ →
          |fderiv ℝ F (η, u) (0, Pi.single j 1)| ≤ Cj * ν u ^ (D - G.weight j) := by
        intro j
        have hwj := G.weight_pos j
        refine ih (D - G.weight j) (by omega) (fun z => fderiv ℝ F z (0, Pi.single j 1))
          (contDiffOn_partial hT hF _) (fun η hη => ?_)
        by_cases hle : G.weight j ≤ D
        · have h := JetVanish.pdv_family hT hF (hKT η hη 0 (by rw [hν0]; exact hρ0)) (hJ η hη) j
          rwa [show ((D - G.weight j : ℕ) : ℤ) = (D : ℤ) - (G.weight j : ℤ) by
            rw [Nat.cast_sub hle]]
        · exact JetVanish.of_nonpos (by omega) _
      choose Cj hCj using hdiff
      refine ⟨∑ j, (G.weight j : ℝ) * c * |Cj j|, fun η hη u hu => ?_⟩
      set f : (Fin N → ℝ) → ℝ := fun v => F (η, v) with hf
      have hf0 : f 0 = 0 := by
        have := hJ η hη [] (by simpa using hD)
        simpa [rsPartial] using this
      have hslice := contDiffOn_slice hF η
      have hdiffAt : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f (G.dilate s u) := by
        intro s hs
        have hmem : (η, G.dilate s u) ∈ T :=
          hKT η hη _ ((gauge_dilate_le G hν hs.1 hs.2 u).trans hu)
        exact ((hslice.contDiffAt ((isOpen_slice hT η).mem_nhds hmem)).differentiableAt (by simp))
      let v : ℝ → Fin N → ℝ := fun s i => (G.weight i : ℝ) * s ^ (G.weight i - 1) * u i
      have hpath : ∀ s ∈ Icc (0 : ℝ) 1,
          HasDerivAt (fun s => f (G.dilate s u)) (fderiv ℝ f (G.dilate s u) (v s)) s := by
        intro s hs
        have hd : HasDerivAt (fun s : ℝ => G.dilate s u) (v s) s := by
          refine hasDerivAt_pi.2 (fun i => ?_)
          simpa [HomogeneousGroup.dilate, coordinateDilation, v] using
            (hasDerivAt_pow (G.weight i) s).mul_const (u i)
        exact (hdiffAt s hs).hasFDerivAt.comp_hasDerivAt s hd
      have hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ f (G.dilate s u) (v s)‖ ≤
          (∑ j, (G.weight j : ℝ) * c * |Cj j|) * ν u ^ D := by
        intro s hs
        have hmem : (η, G.dilate s u) ∈ T :=
          hKT η hη _ ((gauge_dilate_le G hν hs.1 hs.2 u).trans hu)
        have hle : ν (G.dilate s u) ≤ ν u := gauge_dilate_le G hν hs.1 hs.2 u
        rw [Real.norm_eq_abs, fderiv_apply_eq_sum, Finset.sum_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
        have hpj : pdv j f (G.dilate s u) = fderiv ℝ F (η, G.dilate s u) (0, Pi.single j 1) :=
          (fderiv_prod_partial hT hF hmem _).symm
        have hbj := hCj j η hη (G.dilate s u) (hle.trans hu)
        have hbj' : |pdv j f (G.dilate s u)| ≤ |Cj j| * ν (G.dilate s u) ^ (D - G.weight j) := by
          rw [hpj]
          exact hbj.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (pow_nonneg (hν.2.1 _) _))
        have := term_bound (ν := ν u) (ν' := ν (G.dilate s u)) (s := s) (c := c)
          (C := |Cj j|) (u := u j) (p := pdv j f (G.dilate s u)) (w := G.weight j) (D := D)
          (D' := D - G.weight j) (hν.2.1 u) (hu.trans hρ1) (hν.2.1 _) hle hs.1 hs.2
          (hcoord u j) hbj' (abs_nonneg _) hc.le (by omega)
        simpa [v, mul_assoc] using this
      have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun s hs => (hpath s hs).hasDerivWithinAt) hbd (convex_Icc (0 : ℝ) 1)
        (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
      simp only [dilate_zero, dilate_one, hf0, sub_zero, norm_one, mul_one,
        Real.norm_eq_abs] at hmv
      exact hmv

/-- Jointly smooth families with vanishing weighted jets lie in every symbol class of their
degree (the coefficient-jet bounds, BB pp. 547–548). -/
theorem Sym.of_jets (G : HomogeneousGroup N) {c : SymCtx N} (hc : c.Good)
    (hω : c.ω = G.weight) (hν : G.IsHomogeneousGauge c.ν) (hKc : IsCompact c.Kc)
    {T : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hT : IsOpen T)
    (hKT : ∀ η ∈ c.Kc, ∀ u, c.ν u ≤ c.ρ → (η, u) ∈ T) :
    ∀ (k : ℕ) (D : ℤ) (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) F T →
      (∀ η ∈ c.Kc, JetVanish G.weight D (fun u => F (η, u))) →
        Sym c k D (fun η u => F (η, u)) := by
  have hν0 : c.ν 0 = 0 := (hν.2.2.1 0).mpr rfl
  have hPT : ∀ η ∈ c.Kc, ∀ u ∈ c.P, (η, u) ∈ T := fun η hη u hu => hKT η hη u hu.2.le
  intro k
  induction k with
  | zero =>
    intro D F hF hJ
    refine Sym.intro_zero c
      (fun η hη => (contDiffOn_slice hF η).mono (fun u hu => hPT η hη u hu)) ?_
    by_cases hD : 0 ≤ D
    · obtain ⟨C, hC⟩ := jet_bound G hν hc.ρ_pos.le hc.ρ_le hKc hT hKT D.toNat F hF
        (fun η hη => by rw [Int.toNat_of_nonneg hD]; exact hJ η hη)
      refine ⟨C, fun η hη u hu => ?_⟩
      have := hC η hη u hu.2.le
      rwa [← zpow_natCast, Int.toNat_of_nonneg hD] at this
    · obtain ⟨C, hC⟩ := jet_bound G hν hc.ρ_pos.le hc.ρ_le hKc hT hKT 0 F hF
        (fun η hη => JetVanish.of_nonpos (by simp) _)
      refine ⟨|C|, fun η hη u hu => ?_⟩
      have h1 := hC η hη u hu.2.le
      have hpow : (1 : ℝ) ≤ c.ν u ^ D := by
        have := zpow_le_zpow_right_of_le_one₀ hu.1 (hu.2.le.trans hc.ρ_le)
          (show D ≤ 0 by omega)
        simpa using this
      calc |F (η, u)| ≤ C * c.ν u ^ 0 := h1
        _ = C := by simp
        _ ≤ |C| := le_abs_self C
        _ = |C| * 1 := (mul_one _).symm
        _ ≤ |C| * c.ν u ^ D := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
  | succ k ih =>
    intro D F hF hJ
    refine Sym.intro_succ c ((ih D F hF hJ).zero_part c) (fun j => ?_)
    have h0 : ∀ η ∈ c.Kc, (η, (0 : Fin N → ℝ)) ∈ T :=
      fun η hη => hKT η hη 0 (by rw [hν0]; exact hc.ρ_pos.le)
    have hj : (c.ω j : ℤ) = G.weight j := by rw [hω]
    have h := ih (D - G.weight j) (fun z => fderiv ℝ F z (0, Pi.single j 1))
      (contDiffOn_partial hT hF _)
      (fun η hη => JetVanish.pdv_family hT hF (h0 η hη) (hJ η hη) j)
    rw [hj]
    refine Sym.congr c hc ?_ h
    intro η hη u hu
    exact (fderiv_prod_partial hT hF (hPT η hη u hu) _).symm

end RothschildStein.P2
