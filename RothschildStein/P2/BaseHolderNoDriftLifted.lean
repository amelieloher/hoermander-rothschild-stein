-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderNoDriftPatch
public import RothschildStein.P2.TransferCover
public import RothschildStein.S.ContinuousSupNorm

/-!
# No drift: the lifted base Hölder estimate for no-drift charts

Part of the base Hölder estimate (BB pp. 600–602, Thms 11.57–11.58, (11.92)-(11.93)), without drift. From the base Hölder estimate on the
frame patch (`exists_patchHolder_noDrift_of_representation`) to the statement
`LiftedBaseHolderEstimate C ν (noDriftOpWords q) α` of the lifted estimate (the input of
`holder_finite_cover_noDrift_of_lifted`): a function `u ∈ C^{2,α}_{X̃}(W)` on a neighbourhood `W` of the closed
`ρ`-ball `{ν ∘ Θ ≤ s}` is localized by the cutoff `η = φ(s', s)` of the radial cutoff construction (`s' = (t + s)/2`, `η = 1` on `U_{s'}^ρ`,
`tsupport η ⊆ U_s^ρ`), so that `η u ∈ C^{2,α}_{X̃,0}(V)` (zero extension of the product,
`memHolderXCompact_prod_ext_noDrift`) with the Leibniz jet of `u`; the intrinsic jet of `u` on `U_s^ρ` is the weak
jet (continuous weak derivatives are the intrinsic ones), `L̃u = f` on `U_s^ρ`, and the sup norm on the
open ball is the `L^∞` norm of a continuous function.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart noDriftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The lifted base Hölder estimate for no-drift charts** (BB pp. 600-602, Thms 11.57-11.58,
(11.92)-(11.93)), under the hypotheses of the derivative representations without drift
(`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`, `SignedParametrixNoDrift`) on a standard frame `F` of the
lifted no-drift chart `C`, a cutoff `a` equal to `1` near the chart centre, and a smooth homogeneous norm `ν`.
Then `LiftedBaseHolderEstimate C ν (noDriftOpWords q) α`: there are `r₀ > 0`, `β > 0` and `C` with
`‖u‖_{C^{2,α}_{X̃}(U_t^ρ)} ≤ C (s - t)^{-β} (‖L̃u‖_{C^α_{X̃}(U_s^ρ)} + ‖u‖_{L^∞(U_s^ρ)})`
for `0 < t < s < r₀`, every `u ∈ C^{2,α}_{X̃}(W)` on a neighbourhood `W` of `{ν ∘ Θ ≤ s}` and `L̃u = f` (intrinsic
word derivatives of `[i, i]`). -/
theorem liftedBaseHolderEstimate_noDrift_of_representation (hF : C.IsStandardFrame F H K hQ)
    (B : Fin (n + m) → List (Fin q)) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F noDriftWeight C.Xl)
    (hRightDiff : RightDifferentiation F noDriftWeight C.Xl hF.lifted.contDiffOn_Xl)
    (hTransfer : DerivativeTransfer F noDriftWeight C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth)
    (ha : ∀ᶠ x in 𝓝 (joinPoint x₀ (0 : Fin m → ℝ)),
      x ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ a x = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    LiftedBaseHolderEstimate C ν (noDriftOpWords q) α := by
  classical
  set ξ₀ : Fin (n + m) → ℝ := joinPoint x₀ (0 : Fin m → ℝ) with hξ₀def
  have hξ₀ : ξ₀ ∈ C.U := C.center_mem
  obtain ⟨r₁, β, Kc, hr₁0, hr₁1, hβ, hKc, hball, hA⟩ :=
    exists_patchHolder_noDrift_of_representation hF B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix ν hν hξ₀ ha hα0
      hα1
  obtain ⟨rstar, b₁, b₂, B₀, B₁, B₂, hr0, hr1, -, -, -, -, -, hcut⟩ :=
    exists_cutoffData_noDrift C ν hν hξ₀ hα0 hα1
  refine ⟨min r₁ (rstar / 2), lt_min hr₁0 (by linarith), β, hβ, Kc * 2 ^ β, by positivity, ?_⟩
  intro t s ht hts hsr W hW u f hu hf
  have hsr₁ : s ≤ r₁ := hsr.le.trans (min_le_left _ _)
  have hsrstar : s < rstar := by
    have := min_le_right r₁ (rstar / 2)
    linarith
  have hst : 0 < s - t := sub_pos.2 hts
  set s' : ℝ := (t + s) / 2 with hs'
  have hts' : t < s' := by rw [hs']; linarith
  have hs's : s' < s := by rw [hs']; linarith
  have hs'0 : 0 < s' := by linarith
  have hs'r₁ : s' ≤ r₁ := hs's.le.trans hsr₁
  obtain ⟨hPV', hPa⟩ := hball s hsr₁
  set P : Opens (Fin (n + m) → ℝ) := rhoBallOpen C ν s with hPdef
  have hPc : (P : Set (Fin (n + m) → ℝ)) = rhoBall C ν ξ₀ s := rfl
  have hPV : (P : Set (Fin (n + m) → ℝ)) ⊆ (F.V : Set (Fin (n + m) → ℝ)) := by rw [hPc]; exact hPV'
  have hPW : (P : Set (Fin (n + m) → ℝ)) ⊆ (W : Set (Fin (n + m) → ℝ)) :=
    (rhoBall_subset_closed C ν ξ₀).trans hW
  have hPU : (P : Set (Fin (n + m) → ℝ)) ⊆ C.U := fun x hx => hx.1
  have hXP : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (P : Set (Fin (n + m) → ℝ)) := fun i =>
    (hF.lifted.contDiffOn_Xl i).mono hPV
  have huP : memHolderX noDriftWeight C.Xl C.dl P 2 α u := memHolderX_mono_domain noDriftWeight hPW hu
  obtain ⟨D, hD0, hD⟩ := exists_weakJet_of_memHolderX_noDrift hPU hXP hα0 huP
  have hDP : ∀ I ∈ wordFamily noDriftWeight 2, hasWeakWordDeriv C.Xl P I u (D I) ∧
      holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) (D I) ≠ ⊤ := fun I hI =>
    ⟨(hD I hI).1, ne_top_of_lt (hD I hI).2⟩
  have huc : ContinuousOn u (P : Set (Fin (n + m) → ℝ)) :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hPU hα0 huP.1
  -- the cutoff `η`
  set η : (Fin (n + m) → ℝ) → ℝ := radialCutoff C ν ξ₀ s' s with hη
  have hηs : ContDiff ℝ (⊤ : ℕ∞) η := hcut.smooth s' s hs'0 hs's hsrstar
  have hηc : HasCompactSupport η := hcut.compact s' s hs'0 hs's hsrstar
  have hη1 : EqOn η (fun _ => 1) (rhoBall C ν ξ₀ s') := hcut.eq_one s' s hs'0 hs's hsrstar
  have hηP : tsupport η ⊆ (P : Set (Fin (n + m) → ℝ)) := hcut.support s' s hs'0 hs's hsrstar
  have hu'C := memHolderXCompact_prod_ext_noDrift hF.lifted hPV hα0 hα1.le hηs hηc hηP
    (ne_top_of_lt huP.1) hDP
  have hjet' := isHolderWeakJet_prodJet_ext_noDrift hF.lifted hPV hα0 hα1.le hηs hηc hηP
    (ne_top_of_lt huP.1) hDP
  have hAx := hA t s' ht hts' hs'r₁ _ _ hu'C.1 hjet'
  -- the jet on the small balls
  have hopen : IsOpen (rhoBall C ν ξ₀ s') := isOpen_rhoBall C ν hξ₀ s'
  have hnil : EqOn (D []) u (rhoBall C ν ξ₀ s') := fun x _ => by rw [hD0]
  have hjetEq : jetENormNoDrift C.dl α (rhoBall C ν ξ₀ t) D =
      jetENormNoDrift C.dl α (rhoBall C ν ξ₀ t) (prodJetNoDrift C.Xl η u D) :=
    jetENormNoDrift_congr fun I hI =>
      ((prodJetNoDrift_eq_of_eqOn_one (C := C) hopen hη1 hnil hI).mono
        (rhoBall_mono C ν ξ₀ hts'.le)).symm
  -- the left side
  have hVtP : (rhoBallOpen C ν t : Set (Fin (n + m) → ℝ)) ⊆ (P : Set (Fin (n + m) → ℝ)) :=
    rhoBall_mono C ν ξ₀ hts.le
  have hVtU : (rhoBallOpen C ν t : Set (Fin (n + m) → ℝ)) ⊆ C.U := fun x hx => hx.1
  have huVt : memHolderX noDriftWeight C.Xl C.dl (rhoBallOpen C ν t) 2 α u :=
    memHolderX_mono_domain noDriftWeight hVtP huP
  have hDVt : ∀ I ∈ wordFamily noDriftWeight 2,
      hasWeakWordDeriv C.Xl (rhoBallOpen C ν t) I u (D I) ∧
        holderENorm C.dl α (rhoBallOpen C ν t : Set (Fin (n + m) → ℝ)) (D I) < ⊤ := fun I hI =>
    ⟨S.hasWeakWordDeriv_restrict C.Xl P (rhoBallOpen C ν t) hVtP (hD I hI).1,
      lt_of_le_of_lt (S.holderENorm_mono C.dl α _ _ hVtP) (hD I hI).2⟩
  have hLeft : holderXENorm noDriftWeight C.Xl C.dl (rhoBallOpen C ν t) 2 α u =
      jetENormNoDrift C.dl α (rhoBall C ν ξ₀ t) D :=
    holderXENorm_eq_jetENormNoDrift hVtU
      (fun i => (hF.lifted.contDiffOn_Xl i).mono (hVtP.trans hPV)) hα0 huVt hDVt
  -- `L̃u = f` on the ball
  obtain ⟨g, hg, hfg⟩ := hf
  have hintr := holderWeakJet_hasIntrinsicWordDeriv_noDrift hPU hXP hα0 huc hD
  have hmem : ∀ i : Fin q, [i, i] ∈ wordFamily noDriftWeight 2 := fun i =>
    (S.mem_wordFamily_iff _ _ _).2 (by simp [wordWeight, noDriftWeight])
  have hfD : EqOn f (weakSumSquares D []) (P : Set (Fin (n + m) → ℝ)) := fun x hx => by
    rw [← hfg x (hPW hx)]
    unfold weakSumSquares
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hasIntrinsicWordDeriv_mono hPW (noDriftOpWords q i) (hg i)
    exact S.hasIntrinsicWordDeriv_unique P C.Xl [i, i] h1 (hintr [i, i] (hmem i)) hx
  have hLD' : EqOn (weakSumSquares (prodJetNoDrift C.Xl η u D) []) (weakSumSquares D [])
      (rhoBall C ν ξ₀ s') := fun x hx => by
    unfold weakSumSquares
    refine Finset.sum_congr rfl fun i _ => ?_
    exact prodJetNoDrift_eq_of_eqOn_one (C := C) hopen hη1 hnil (hmem i) hx
  have hHf : holderENorm C.dl α (rhoBall C ν ξ₀ s') (weakSumSquares (prodJetNoDrift C.Xl η u D) []) ≤
      holderXENorm noDriftWeight C.Xl C.dl P 0 α f := by
    rw [S.holderXENorm_zero, S.holderENorm_congr C.dl α _ _ hLD']
    calc holderENorm C.dl α (rhoBall C ν ξ₀ s') (weakSumSquares D [])
        = holderENorm C.dl α (rhoBall C ν ξ₀ s') f :=
          (S.holderENorm_congr C.dl α _ _ (fun x hx => (hfD (rhoBall_mono C ν ξ₀ hs's.le hx)).symm))
      _ ≤ _ := S.holderENorm_mono C.dl α _ _ (rhoBall_mono C ν ξ₀ hs's.le)
  have hSu : supNormE (rhoBall C ν ξ₀ s') (fun x => u x * η x) ≤
      eLpNorm u ⊤ (volume.restrict (P : Set (Fin (n + m) → ℝ))) := by
    rw [S.eLpNorm_top_eq_iSup_of_continuousOn P huc]
    have e : supNormE (rhoBall C ν ξ₀ s') (fun x => u x * η x) =
        supNormE (rhoBall C ν ξ₀ s') u :=
      supNormE_congr fun x hx => by simp [hη1 hx]
    rw [e]
    exact supNormE_mono (rhoBall_mono C ν ξ₀ hs's.le) u
  have hcoef : Kc * (s' - t) ^ (-β) = Kc * 2 ^ β / (s - t) ^ β := by
    have e : s' - t = (s - t) / 2 := by rw [hs']; ring
    rw [e, Real.rpow_neg (by positivity), Real.div_rpow hst.le (by norm_num), inv_div, mul_div_assoc]
  rw [hLeft, hjetEq]
  refine hAx.trans ?_
  rw [hcoef]
  exact mul_le_mul' le_rfl (add_le_add hHf hSu)

end RothschildStein.P2
