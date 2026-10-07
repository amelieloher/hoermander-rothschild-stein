-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderLocalize
public import RothschildStein.P2.BaseHolderCutoff
public import RothschildStein.P2.TransferCover
public import RothschildStein.P2.SobolevInterpolationNhds
public import RothschildStein.S.ContinuousSupNorm

/-!
# The lifted base Hölder estimate for drift charts

Part of the base Hölder estimate (BB pp. 600–602, Thms 11.57–11.58, (11.92)–(11.93)).
`liftedBaseHolderEstimate_of_representation` proves the lifted base Hölder estimate
`LiftedBaseHolderEstimate C ν (driftOpWords q) α` (the input of
the transfer and finite-cover theorem `holder_finite_cover_of_lifted` and the hypothesis `LiftedBaseHolderAllChartsDrift`
of the drift Hölder root), assuming exactly the hypotheses of the first- and second-order
representations
(`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`, the `SignedParametrix`s with the density data), a
standard frame and a cutoff `a = 1` near the chart centre; the `(HD)` package of the lifted control distance
is that of the chart (`LiftedChart.distanceGeometry`).

For `0 < t < s < r₀` put `m = (t + s)/2`, `a = m - t = s - m` and let `ζ` be the cutoff of the radial cutoff construction between `U_t`
and `U_m`.

1. (`BaseHolderLocalize`) `u ∈ C^{2,α}_{X̃}(W)` is replaced by `u' = η u ∈ C^{2,α}_{X̃,0}(F.V)`, equal to `u` on
   `U_s`.
2. (`BaseHolderCutoff`) The compact Hölder estimate applied to `ζ u'` gives
   `ψ(t) ≤ c a^{-4} (‖L̃u‖_{C^α(U_s)} + ‖Du‖_{C^α(U_m)} + ‖u‖_{L^∞(U_s)})`.
3. (here) The nested Hölder interpolation between `m` and `s` bounds `‖Du‖_{C^α(U_m)}` by
   `δ ‖L̃u‖_∞ + C δ^{-γ} a^{-γ} ‖u‖_∞` (`δ = 1/4`), which gives `ψ(t) ≤ C a^{-β} (‖L̃u‖_{C^α(U_s)} + ‖u‖_∞)`,
   `β = 4 + ⌈γ⌉`: the hole-filling inequality with `θ = 0` (the Hölder interpolation iteration is inside
   the nested interpolation; no `ψ(s)` occurs).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

section Arith

theorem cutoffConst_le {Λ C₃ Cb A : ℝ} (hΛ : 0 ≤ Λ) (hC₃ : 0 ≤ C₃) (hCb : 0 ≤ Cb) (hA : 1 ≤ A) :
    cutoffConst Λ C₃ Cb A ≤ Λ * (3 * Cb + 5 * (C₃ * Cb) + 1) * A ^ 4 := by
  have h1 : A ≤ A ^ 4 := by
    calc A = A ^ 1 := (pow_one A).symm
      _ ≤ A ^ 4 := pow_le_pow_right₀ hA (by norm_num)
  have h2 : A ^ 2 ≤ A ^ 4 := pow_le_pow_right₀ hA (by norm_num)
  have h3 : A ^ 3 ≤ A ^ 4 := pow_le_pow_right₀ hA (by norm_num)
  have h0 : 1 ≤ A ^ 4 := one_le_pow₀ hA
  unfold cutoffConst
  have hmain : Cb * A + 2 * (Cb * A ^ 2) + C₃ * ((Cb * A ^ 2 + 2 * (Cb * A ^ 3) + Cb * A ^ 4) + Cb * A ^ 2)
      + 1 ≤ (3 * Cb + 5 * (C₃ * Cb) + 1) * A ^ 4 := by
    have e1 := mul_le_mul_of_nonneg_left h1 hCb
    have e2 := mul_le_mul_of_nonneg_left h2 hCb
    have e3 := mul_le_mul_of_nonneg_left h3 hCb
    have f2 := mul_le_mul_of_nonneg_left e2 hC₃
    have f3 := mul_le_mul_of_nonneg_left e3 hC₃
    have f4 : C₃ * (Cb * A ^ 4) ≤ C₃ * (Cb * A ^ 4) := le_rfl
    nlinarith
  calc Λ * _ ≤ Λ * ((3 * Cb + 5 * (C₃ * Cb) + 1) * A ^ 4) := mul_le_mul_of_nonneg_left hmain hΛ
    _ = _ := by ring

/-- `a^{-γ} ≤ A^{⌈γ⌉}` for `A = a⁻¹ ≥ 1`. -/
theorem rpow_neg_le_pow_ceil {a γ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a ^ (-γ) ≤ (a⁻¹) ^ ⌈γ⌉₊ := by
  have hA : 1 ≤ a⁻¹ := one_le_inv₀ ha |>.2 ha1
  rw [Real.rpow_neg ha.le, ← Real.inv_rpow ha.le]
  calc (a⁻¹) ^ γ ≤ (a⁻¹) ^ ((⌈γ⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hA (Nat.le_ceil γ)
    _ = (a⁻¹) ^ ⌈γ⌉₊ := Real.rpow_natCast _ _

theorem lifted_const_le {Λ C₃ Cb Cn γ : ℝ} (hΛ : 0 ≤ Λ) (hC₃ : 0 ≤ C₃) (hCb : 0 ≤ Cb)
    (hCn : 0 ≤ Cn) {t s : ℝ} (hts : t < s) (hs1 : s ≤ 1) (ht : 0 < t) :
    cutoffConst Λ C₃ Cb ((((t + s) / 2) - t)⁻¹) *
        (1 + (1 / 4 + Cn * (1 / 4 : ℝ) ^ (-γ) * (s - (t + s) / 2) ^ (-γ))) ≤
      (Λ * (3 * Cb + 5 * (C₃ * Cb) + 1)) * (1 + (1 / 4 + Cn * (1 / 4 : ℝ) ^ (-γ))) *
        2 ^ (4 + ⌈γ⌉₊) / (s - t) ^ (((4 + ⌈γ⌉₊ : ℕ)) : ℝ) := by
  have hd : 0 < s - t := sub_pos.2 hts
  set a : ℝ := (s - t) / 2 with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have e1 : (t + s) / 2 - t = a := by rw [ha]; ring
  have e2 : s - (t + s) / 2 = a := by rw [ha]; ring
  rw [e1, e2]
  set A : ℝ := a⁻¹ with hA
  have hA1 : 1 ≤ A := (one_le_inv₀ ha0).2 ha1
  have hA0 : 0 ≤ A := by linarith
  have hc := cutoffConst_le hΛ hC₃ hCb hA1
  set N : ℕ := ⌈γ⌉₊ with hN
  have hAN : 1 ≤ A ^ N := one_le_pow₀ hA1
  set q4 : ℝ := (1 / 4 : ℝ) ^ (-γ) with hq4
  have hq40 : 0 ≤ q4 := Real.rpow_nonneg (by norm_num) _
  have hcn : Cn * q4 * a ^ (-γ) ≤ Cn * q4 * A ^ N :=
    mul_le_mul_of_nonneg_left (rpow_neg_le_pow_ceil ha0 ha1) (mul_nonneg hCn hq40)
  have hbr : 1 + (1 / 4 + Cn * q4 * a ^ (-γ)) ≤ (1 + (1 / 4 + Cn * q4)) * A ^ N := by
    have : (5 / 4 : ℝ) ≤ 5 / 4 * A ^ N := by nlinarith
    nlinarith
  have hK1 : 0 ≤ Λ * (3 * Cb + 5 * (C₃ * Cb) + 1) := by positivity
  have hbr0 : 0 ≤ 1 + (1 / 4 + Cn * q4 * a ^ (-γ)) := by
    have := Real.rpow_nonneg ha0.le (-γ)
    positivity
  calc cutoffConst Λ C₃ Cb A * (1 + (1 / 4 + Cn * q4 * a ^ (-γ)))
      ≤ (Λ * (3 * Cb + 5 * (C₃ * Cb) + 1) * A ^ 4) * ((1 + (1 / 4 + Cn * q4)) * A ^ N) :=
        mul_le_mul hc hbr hbr0 (by positivity)
    _ = (Λ * (3 * Cb + 5 * (C₃ * Cb) + 1)) * (1 + (1 / 4 + Cn * q4)) * A ^ (4 + N) := by
        rw [pow_add]; ring
    _ = (Λ * (3 * Cb + 5 * (C₃ * Cb) + 1)) * (1 + (1 / 4 + Cn * q4)) * 2 ^ (4 + N) /
        (s - t) ^ (((4 + N : ℕ)) : ℝ) := by
        rw [Real.rpow_natCast]
        have : A = 2 / (s - t) := by rw [hA, ha]; field_simp
        rw [this, div_pow]
        ring

end Arith

section Zero

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The Hölder norm of order zero is the scalar Hölder norm. -/
theorem holderXENorm_zero_eq {N k : ℕ} (w' : Fin k → ℕ+) (X' : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (V : Opens (Fin N → ℝ)) (α : ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    holderXENorm w' X' d V 0 α f = holderENorm d α (V : Set (Fin N → ℝ)) f := by
  unfold holderXENorm
  rw [RothschildStein.S.wordFamily_zero, Finset.sum_singleton]
  exact intrinsicWordENorm_eq_holderENorm (X' := X') (d := d) (V := V) (I := []) (f := f) (g := f)
    (fun _ _ => rfl)

end Zero

section Main

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart driftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The lifted base Hölder estimate for drift charts** (BB pp. 600-602, Thms 11.57-11.58,
(11.92)-(11.93)), under the hypotheses of the derivative representations. Let `C` be a lifted
drift chart, `F` a standard frame of it, `a ∈ C_c^∞(V)` a cutoff with `a = 1` near the centre `(x₀, 0)` for
which the derivative representations hold (`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`, the
`SignedParametrix`s with the density data `c`) and `ν` a smooth homogeneous norm. Then for `0 < α < 1`
`LiftedBaseHolderEstimate C ν (driftOpWords q) α`: there are `r₀, β, C > 0` with
`‖u‖_{C^{2,α}_{X̃}(U_t^ρ)} ≤ C (s - t)^{-β} (‖L̃u‖_{C^α_{X̃}(U_s^ρ)} + ‖u‖_{L^∞(U_s^ρ)})`
for `0 < t < s < r₀`, `u ∈ C^{2,α}_{X̃}(W)` on a neighbourhood `W` of the closed `ρ`-ball of radius `s` and
every value `f = L̃u` of the operator. -/
theorem liftedBaseHolderEstimate_of_representation (hF : C.IsStandardFrame F H K hQ)
    (B : Fin (n + m) → List (Fin (q + 1))) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F driftWeight C.Xl)
    (hRightDiff : RightDifferentiation F driftWeight C.Xl hF.lifted.contDiffOn_Xl)
    (hTransfer : DerivativeTransfer F driftWeight C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrix F C.Xl c a b)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth)
    (ha : ∀ᶠ x in 𝓝 (joinPoint x₀ (0 : Fin m → ℝ)),
      x ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ a x = 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    LiftedBaseHolderEstimate C ν (driftOpWords q) α := by
  classical
  set η₀ : Fin (n + m) → ℝ := joinPoint x₀ (0 : Fin m → ℝ) with hη₀def
  have hη₀ : η₀ ∈ C.U := C.center_mem
  obtain ⟨Λ, hΛ, hcomp⟩ := exists_compactHolder_of_representation hF B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a
    hParametrix hα0 hα1
  obtain ⟨C₃, hC₃, hsupH⟩ := exists_holderFromSup_of_representation hF hLeftDiff hc hc0 a hParametrix hα0 hα1
  obtain ⟨Rstar, γ, Cn, hR0, hR1, hγ, hCn, hnest⟩ := exists_nestedInterpolation_of_representation
    hF hLeftDiff hc hc0 a hParametrix C.chartOpens C.distanceGeometry rfl hF.lifted.subset_U ν hν hη₀ hα0 hα1
  obtain ⟨rstar, Cb, hr0, hr1, hCb, hcut⟩ := exists_cutoffData C ν hν hη₀ hα0 hα1
  obtain ⟨ρ₀, hρ0, hρ1, hT⟩ := exists_chart_radius C ν (isCompact_singleton (x := η₀))
    (singleton_subset_iff.2 hη₀)
  obtain ⟨r₂, hr₂, hsub⟩ := exists_rhoBall_subset_of_mem_nhds C ν hη₀ ha
  set N : ℕ := ⌈γ⌉₊ with hN
  set K1 : ℝ := Λ * (3 * Cb + 5 * (C₃ * Cb) + 1) with hK1
  set K2 : ℝ := 1 + (1 / 4 + Cn * (1 / 4 : ℝ) ^ (-γ)) with hK2
  have hq40 : 0 ≤ (1 / 4 : ℝ) ^ (-γ) := Real.rpow_nonneg (by norm_num) _
  have hK10 : 0 < K1 := by rw [hK1]; positivity
  have hK20 : 0 < K2 := by rw [hK2]; positivity
  refine ⟨min (min Rstar rstar) (min ρ₀ r₂), lt_min (lt_min hR0 hr0) (lt_min hρ0 hr₂),
    ((4 + N : ℕ) : ℝ), by positivity, K1 * K2 * 2 ^ (4 + N), by positivity, ?_⟩
  intro t s ht hts hsr W hW u f hu hf
  have hs0 : 0 < s := ht.trans hts
  have hsR : s ≤ Rstar := (hsr.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hsrs : s < rstar := hsr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hsρ : s < ρ₀ := hsr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsr₂ : s < r₂ := hsr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hs1 : s ≤ 1 := hsR.trans hR1
  set mm : ℝ := (t + s) / 2 with hmm
  have htm : t < mm := by rw [hmm]; linarith
  have hms : mm < s := by rw [hmm]; linarith
  -- the closed ball
  have hcpt : IsCompact (closedRhoBall C ν η₀ s) :=
    isCompact_closedRhoBall C ν hη₀ fun u hu' => hT η₀ (mem_singleton _) u (hu'.trans hsρ.le)
  have hcl : closure (rhoBall C ν η₀ s) ⊆ closedRhoBall C ν η₀ s :=
    hcpt.isClosed.closure_subset_iff.2 (rhoBall_subset_closed C ν η₀)
  have hUsV : rhoBall C ν η₀ s ⊆ (F.V : Set (Fin (n + m) → ℝ)) := fun x hx =>
    (hsub s hsr₂.le hx).1
  have ha1 : ∀ x ∈ rhoBall C ν η₀ s, a x = 1 := fun x hx => (hsub s hsr₂.le hx).2
  have hBc : IsCompact (closure ((rhoBallOpen C ν s : Opens (Fin (n + m) → ℝ)) :
      Set (Fin (n + m) → ℝ))) := hcpt.of_isClosed_subset isClosed_closure hcl
  have hBW : closure ((rhoBallOpen C ν s : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) ⊆
      (W : Set (Fin (n + m) → ℝ)) := hcl.trans hW
  have hBV : closure ((rhoBallOpen C ν s : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) ⊆
      (F.V : Set (Fin (n + m) → ℝ)) := hcl.trans
    ((closedRhoBall_subset_rhoBall C ν η₀ hsr₂).trans fun x hx => (hsub r₂ le_rfl hx).1)
  -- localization
  obtain ⟨u', D', hmem, hjet, hu'u, hLf, hnorm⟩ := exists_localization (C := C) hF.lifted hα0
    hα1.le hu hf hBc hBW hBV
  have hu'fin : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u' ≠ ⊤ := hmem.1.1.ne
  -- the cutoff
  obtain ⟨hζs, hζc, hζr, hζ1, hζsupp, hζsupp2, hH0, hH1, hs0', hs1', hs2'⟩ :=
    hcut t mm ht htm (hms.trans hsrs)
  have hZ : CutoffData C F a α Cb ((mm - t)⁻¹) (rhoBallOpen C ν t) (rhoBallOpen C ν mm)
      (rhoBallOpen C ν s) (radialCutoff C ν η₀ t mm) :=
    { Ut_Um := rhoBall_mono C ν η₀ htm.le
      Um_Us := rhoBall_mono C ν η₀ hms.le
      Us_V := hUsV
      a_one := ha1
      smooth := hζs
      compact := hζc
      range := hζr
      one_on := hζ1
      supp := hζsupp.trans hζsupp2
      holder0 := hH0
      holder1 := hH1
      sup0 := hs0'
      sup1 := hs1'
      sup2 := hs2'
      Cb_nonneg := hCb
      A_nonneg := inv_nonneg.2 (sub_pos.2 htm).le }
  have hbound := cutoff_estimate hF.lifted hα0 hα1 a hΛ.le hC₃.le hcomp hsupH hZ hu'fin hjet
  -- the nested interpolation
  have hnest' := hnest s hs0 hsR hUsV ha1 u' D' hmem.1 hjet mm (ht.trans htm) hms (1 / 4)
    (by norm_num) (by norm_num)
  -- identifications on `U_s`
  have hucont : ContinuousOn u (rhoBallOpen C ν s : Set (Fin (n + m) → ℝ)) := by
    have hu1 : holderENorm C.dl α (W : Set (Fin (n + m) → ℝ)) u < ⊤ := hu.1
    have hUsW : (rhoBallOpen C ν s : Set (Fin (n + m) → ℝ)) ⊆ W :=
      (subset_closure.trans hBW)
    exact LiftedChart.continuousOn_of_holderENorm_lt_top (hUsV.trans hF.lifted.subset_U) hα0
      (lt_of_le_of_lt (S.holderENorm_mono C.dl α _ _ hUsW) hu1)
  have hUsEq : ∀ x ∈ (rhoBallOpen C ν s : Set (Fin (n + m) → ℝ)), weakSumSquaresWithDrift D' x = f x :=
    hLf
  set Us : Set (Fin (n + m) → ℝ) := (rhoBallOpen C ν s : Set (Fin (n + m) → ℝ)) with hUsdef
  set Hf := holderENorm C.dl α Us f with hHf
  set Eu := supNormE Us u with hEu
  set Y2 := Hf + Eu with hY2
  have hHfeq : holderENorm C.dl α Us (weakSumSquaresWithDrift D') = Hf :=
    S.holderENorm_congr C.dl α Us _ hUsEq
  have hSfeq : supNormE Us (weakSumSquaresWithDrift D') = supNormE Us f := supNormE_congr hUsEq
  have hSueq : supNormE Us u' = Eu := supNormE_congr fun x hx => by rw [hu'u x hx]
  have hSfle : supNormE Us f ≤ Hf := supNormE_le_holderENorm _ _
  have hE1 : ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν η₀ mm) (D' [l.succ]) ≤
      ENNReal.ofReal (1 / 4) * supNormE Us (weakSumSquaresWithDrift D') +
        ENNReal.ofReal (Cn * (1 / 4 : ℝ) ^ (-γ) * (s - mm) ^ (-γ)) * supNormE Us u' := hnest'
  rw [hSfeq, hSueq] at hE1
  have hE1' : BoundedBy (∑ l : Fin q, holderENorm C.dl α (rhoBall C ν η₀ mm) (D' [l.succ])) Y2
      (1 / 4 + Cn * (1 / 4 : ℝ) ^ (-γ) * (s - mm) ^ (-γ)) := by
    have hs : 0 ≤ Cn * (1 / 4 : ℝ) ^ (-γ) * (s - mm) ^ (-γ) :=
      mul_nonneg (mul_nonneg hCn.le hq40) (Real.rpow_nonneg (sub_pos.2 hms).le _)
    have b1 : BoundedBy (ENNReal.ofReal (1 / 4) * supNormE Us f) Y2 (1 / 4) :=
      BoundedBy.of_const_mul_le (by norm_num) (hSfle.trans le_self_add)
    have b2 : BoundedBy (ENNReal.ofReal (Cn * (1 / 4 : ℝ) ^ (-γ) * (s - mm) ^ (-γ)) * Eu) Y2
        (Cn * (1 / 4 : ℝ) ^ (-γ) * (s - mm) ^ (-γ)) := BoundedBy.of_const_mul_le hs le_add_self
    exact (b1.add b2 (by norm_num) hs).mono_left hE1
  -- combine
  have hHf' : holderENorm C.dl α (Us) (weakSumSquaresWithDrift D') +
      ∑ l : Fin q, holderENorm C.dl α (rhoBallOpen C ν mm : Set (Fin (n + m) → ℝ)) (D' [l.succ]) +
        supNormE Us u' ≤ ENNReal.ofReal (1 + (1 / 4 + Cn * (1 / 4 : ℝ) ^ (-γ) * (s - mm) ^ (-γ))) * Y2 := by
    rw [hHfeq, hSueq]
    have hs : 0 ≤ Cn * (1 / 4 : ℝ) ^ (-γ) * (s - mm) ^ (-γ) :=
      mul_nonneg (mul_nonneg hCn.le hq40) (Real.rpow_nonneg (sub_pos.2 hms).le _)
    have := ((BoundedBy.of_le (le_refl Y2)).add hE1' zero_le_one (by positivity))
    unfold BoundedBy at this
    calc Hf + _ + Eu = (Hf + Eu) + ∑ l : Fin q, holderENorm C.dl α (rhoBallOpen C ν mm : Set (Fin (n + m) → ℝ))
          (D' [l.succ]) := by rw [add_right_comm]
      _ ≤ _ := this
  have hψ : holderXENorm driftWeight C.Xl C.dl (rhoBallOpen C ν t) 2 α u =
      jetENorm C.dl α (rhoBallOpen C ν t : Set (Fin (n + m) → ℝ)) D' :=
    hnorm (rhoBallOpen C ν t) (rhoBall_mono C ν η₀ hts.le)
  have hzero : holderXENorm driftWeight C.Xl C.dl (rhoBallOpen C ν s) 0 α f = Hf :=
    holderXENorm_zero_eq _ _ _ _ _ _
  have hEueq : eLpNorm u ⊤ (volume.restrict (rhoBallOpen C ν s : Set (Fin (n + m) → ℝ))) = Eu :=
    S.eLpNorm_top_eq_iSup_of_continuousOn (rhoBallOpen C ν s) hucont
  rw [hψ, hzero, hEueq]
  refine hbound.trans ?_
  have hco := cutoffConst_nonneg hΛ.le hC₃.le hCb (inv_nonneg.2 (sub_pos.2 htm).le)
  have hconst := lifted_const_le (Cn := Cn) (γ := γ) hΛ.le hC₃.le hCb hCn.le hts hs1 ht
  rw [← hmm] at hconst
  calc ENNReal.ofReal (cutoffConst Λ C₃ Cb ((mm - t)⁻¹)) *
        (holderENorm C.dl α Us (weakSumSquaresWithDrift D') +
          ∑ l : Fin q, holderENorm C.dl α (rhoBallOpen C ν mm : Set (Fin (n + m) → ℝ)) (D' [l.succ]) +
            supNormE Us u')
      ≤ ENNReal.ofReal (cutoffConst Λ C₃ Cb ((mm - t)⁻¹)) *
        (ENNReal.ofReal (1 + (1 / 4 + Cn * (1 / 4 : ℝ) ^ (-γ) * (s - mm) ^ (-γ))) * Y2) :=
        mul_le_mul' le_rfl hHf'
    _ = ENNReal.ofReal (cutoffConst Λ C₃ Cb ((mm - t)⁻¹) *
        (1 + (1 / 4 + Cn * (1 / 4 : ℝ) ^ (-γ) * (s - mm) ^ (-γ)))) * Y2 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hco]
    _ ≤ ENNReal.ofReal (K1 * K2 * 2 ^ (4 + N) / (s - t) ^ (((4 + N : ℕ)) : ℝ)) * Y2 :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) le_rfl

end Main

section HoleFilling

variable {n k st m : ℕ} {w : Fin k → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

end HoleFilling

end RothschildStein.P2
