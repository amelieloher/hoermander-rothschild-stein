-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherHolderPiece

/-!
# The step estimate on `ρ`-balls

Part of the higher Hölder estimate (BB p. 604). `stage_core`: for a patch `B ⊆ V` and a cutoff `ζ` (smooth, `tsupport ζ ⊆ B` compact, `ζ = 1`
on `Bs ⊆ B`) with the Hölder bounds `‖X̃_J ζ‖_{C^α(B)} ≤ c'` for `|J| ≤ j' + 3`, a Hölder weak jet `D` of order
`j' + 2` of `D []` on `B` and a Hölder weak jet `Df` of order `j' + 1` of `Df [] = ∑ᵢ D [i, i]` there, the function
`D []` has a Hölder weak jet `D''` of order `j' + 3` on `Bs`, extending `D`, with
`‖D''‖_{j'+3, C^α(Bs)} ≤ Λ (|W_{j'+1}| 2^{j'+1} (3q + 1) + |W_{j'+2}| 2^{j'+2}) c' (‖Df‖_{j'+1, B} + ‖D‖_{j'+2, B})`
(from the compact recurrence `compact_regularity` and the Leibniz jets of the product `ζ D []`).
`stage_step` applies this to the radial cutoff `φ(s, r)` of the radial cutoff construction on the `ρ`-balls `Bs = U_s^ρ ⊆ B = U_r^ρ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2.HigherHolder

open RothschildStein.P1

section Core

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart noDriftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r₀ : ℕ} {H : H1.StandingHypotheses C.G r₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {a : TestFunction F.V ℝ (⊤ : ℕ∞)}

/-- **The abstract step** (BB p. 604): see the module
docstring. -/
theorem stage_core (hH : HolderFrame C H K hQ F a) {α : ℝ} (hα0 : 0 < α) (j' : ℕ) {Λ c' : ℝ}
    (hΛ0 : 0 ≤ Λ) (hc'0 : 0 ≤ c')
    (hreg : ∀ (v : (Fin (n + m) → ℝ) → ℝ) (D Df : List (Fin q) → (Fin (n + m) → ℝ) → ℝ)
      (K₀ : Set (Fin (n + m) → ℝ)),
      IsCompact K₀ → K₀ ⊆ (F.V : Set (Fin (n + m) → ℝ)) →
      (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), x ∉ K₀ → v x = 0) → (∀ x, a x * v x = v x) →
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) v ≠ ⊤ →
      LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V (j' + 2) α v D →
      LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V (j' + 1) α (Df []) Df →
      (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), weakSumSquares D [] x = Df [] x) →
      ∃ D' : List (Fin q) → (Fin (n + m) → ℝ) → ℝ,
        LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V (j' + 3) α v D' ∧
        (∀ K' : List (Fin q), K'.length ≤ j' + 2 → D' K' = D K') ∧
        holderJetNorm noDriftWeight C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 3) D' ≤ ENNReal.ofReal Λ *
          (holderJetNorm noDriftWeight C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 1) Df +
            holderJetNorm noDriftWeight C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 2) D))
    {B Bs : Opens (Fin (n + m) → ℝ)} (hBsB : (Bs : Set (Fin (n + m) → ℝ)) ⊆ B)
    (hBV : (B : Set (Fin (n + m) → ℝ)) ⊆ F.V) (hBU : (B : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    {ζ : (Fin (n + m) → ℝ) → ℝ} (hζsm : ContDiff ℝ (⊤ : ℕ∞) ζ) (hKc : IsCompact (tsupport ζ))
    (hKB : tsupport ζ ⊆ (B : Set (Fin (n + m) → ℝ)))
    (hζ1 : ∀ x ∈ (Bs : Set (Fin (n + m) → ℝ)), ζ x = 1) (hBa : ∀ x ∈ (B : Set (Fin (n + m) → ℝ)), a x = 1)
    (hcw : ∀ J : List (Fin q), J.length ≤ j' + 3 →
      holderENorm C.dl α (B : Set (Fin (n + m) → ℝ)) (wordDerivative C.Xl J ζ) ≤ ENNReal.ofReal c')
    {D Df : List (Fin q) → (Fin (n + m) → ℝ) → ℝ}
    (hD : LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl B (j' + 2) α (D []) D)
    (hDf : LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl B (j' + 1) α (Df []) Df)
    (hrel : ∀ x ∈ (B : Set (Fin (n + m) → ℝ)), weakSumSquares D [] x = Df [] x) :
    ∃ D'' : List (Fin q) → (Fin (n + m) → ℝ) → ℝ,
      LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl Bs (j' + 3) α (D'' []) D'' ∧
      (∀ K' : List (Fin q), K'.length ≤ j' + 2 →
        ∀ x ∈ (Bs : Set (Fin (n + m) → ℝ)), D'' K' x = D K' x) ∧
      holderJetNorm noDriftWeight C.dl (Bs : Set (Fin (n + m) → ℝ)) α (j' + 3) D'' ≤
        ENNReal.ofReal (Λ * (jetConst q (j' + 1) * (3 * q + 1) + jetConst q (j' + 2)) * c') *
          (holderJetNorm noDriftWeight C.dl (B : Set (Fin (n + m) → ℝ)) α (j' + 1) Df +
            holderJetNorm noDriftWeight C.dl (B : Set (Fin (n + m) → ℝ)) α (j' + 2) D) := by
  classical
  have hw : ∀ j : Fin q, ((noDriftWeight j : ℕ+) : ℕ) = 1 := fun j => noDriftWeight_coe_eq_one j
  have hXV := hH.std.lifted.contDiffOn_Xl
  obtain ⟨hs1, hζ1sm, hζ2sm, hζ10, hζ20⟩ := cutoff_deriv_facts (C := C) hζsm (hKB.trans hBU)
  have hcw1 : ∀ (i : Fin q) (J : List (Fin q)), J.length ≤ j' + 2 →
      holderENorm C.dl α (B : Set (Fin (n + m) → ℝ))
        (wordDerivative C.Xl J (fieldDerivative (C.Xl i) ζ)) ≤ ENNReal.ofReal c' := fun i J hJ =>
    word_bound_field hcw [i] J (by simp only [List.length_cons, List.length_nil]; omega)
  have hcw2 : ∀ (i : Fin q) (J : List (Fin q)), J.length ≤ j' + 1 →
      holderENorm C.dl α (B : Set (Fin (n + m) → ℝ))
        (wordDerivative C.Xl J (fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i) ζ))) ≤
          ENNReal.ofReal c' := fun i J hJ =>
    word_bound_field hcw [i, i] J (by simp only [List.length_cons, List.length_nil]; omega)
  have hDw : ∀ K' ∈ wordFamily noDriftWeight (j' + 2),
      hasWeakWordDeriv C.Xl B K' (D []) (D K') := fun K' hK' => (hD K' hK').1
  have hDfw : ∀ K' ∈ wordFamily noDriftWeight (j' + 1),
      hasWeakWordDeriv C.Xl B K' (Df []) (Df K') := fun K' hK' => (hDf K' hK').1
  have hDfin : ∀ K' ∈ wordFamily noDriftWeight (j' + 2),
      holderENorm C.dl α (B : Set (Fin (n + m) → ℝ)) (D K') ≠ ⊤ := fun K' hK' => (hD K' hK').2
  have hDffin : ∀ K' ∈ wordFamily noDriftWeight (j' + 1),
      holderENorm C.dl α (B : Set (Fin (n + m) → ℝ)) (Df K') ≠ ⊤ := fun K' hK' => (hDf K' hK').2
  have hJDtop : holderJetNorm noDriftWeight C.dl (B : Set (Fin (n + m) → ℝ)) α (j' + 2) D ≠ ⊤ :=
    holderJetNorm_ne_top hDfin
  have hJFtop : holderJetNorm noDriftWeight C.dl (B : Set (Fin (n + m) → ℝ)) α (j' + 1) Df ≠ ⊤ :=
    holderJetNorm_ne_top hDffin
  -- the norms of the three Leibniz parts
  have hlv := leibJet_norm_le (C := C) (V := F.V) (B := B) hBV hBU hα0 hKc hKB subset_rfl (N := j' + 2)
    (c := c') (D := D) hDfin (fun J hJ => hcw J (by omega))
  have hl1 := leibJet_norm_le (C := C) (V := F.V) (B := B) hBV hBU hα0 hKc hKB subset_rfl (N := j' + 1)
    (c := c') (D := Df) hDffin (fun J hJ => hcw J (by omega))
  have hl2 : ∀ i : Fin q, holderJetNorm noDriftWeight C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 1)
      (leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) (fieldDerivative (C.Xl i) ζ) (fun K'' => D (K'' ++ [i]))) ≤
      ENNReal.ofReal (jetConst q (j' + 1)) * ENNReal.ofReal c' *
        holderJetNorm noDriftWeight C.dl (B : Set (Fin (n + m) → ℝ)) α (j' + 2) D := fun i => by
    have h := leibJet_norm_le (C := C) (V := F.V) (B := B) hBV hBU hα0 hKc hKB (hs1 i) (N := j' + 1)
      (c := c') (D := fun K'' => D (K'' ++ [i]))
      (fun J hJ => hDfin (J ++ [i]) (by
        rw [mem_wordFamily_iff_length hw] at hJ ⊢
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega))
      (fun J hJ => hcw1 i J (by omega))
    exact h.trans (mul_le_mul' le_rfl
      (holderJetNorm_shift_le hw C.dl (B : Set (Fin (n + m) → ℝ)) α (j' + 1) D i))
  have hl3 : ∀ i : Fin q, holderJetNorm noDriftWeight C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 1)
      (leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) (fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i) ζ)) D) ≤
      ENNReal.ofReal (jetConst q (j' + 1)) * ENNReal.ofReal c' *
        holderJetNorm noDriftWeight C.dl (B : Set (Fin (n + m) → ℝ)) α (j' + 2) D := fun i => by
    have h := leibJet_norm_le (C := C) (V := F.V) (B := B) hBV hBU hα0 hKc hKB
      ((S.tsupport_fieldDerivative_subset _ _).trans (hs1 i)) (N := j' + 1) (c := c') (D := D)
      (fun J hJ => hDfin J (by
        rw [mem_wordFamily_iff_length hw] at hJ ⊢
        omega))
      (fun J hJ => hcw2 i J (by omega))
    exact h.trans (mul_le_mul' le_rfl
      (holderJetNorm_mono_order hw C.dl (B : Set (Fin (n + m) → ℝ)) α (Nat.le_succ (j' + 1)) D))
  have hJfv := holderJetNorm_forcingJet_le (X := C.Xl) (w := noDriftWeight) C.dl (F.V : Set (Fin (n + m) → ℝ))
    (B : Set (Fin (n + m) → ℝ)) hα0.le (j' + 1) ζ D Df
    (hl1.trans (mul_le_mul' le_rfl le_self_add))
    (fun i => (hl2 i).trans (mul_le_mul' le_rfl le_add_self))
    (fun i => (hl3 i).trans (mul_le_mul' le_rfl le_add_self))
  -- finiteness
  have hJvtop : holderJetNorm noDriftWeight C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 2)
      (leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) hJDtop) hlv
  have hq3 : (1 + 3 * (q : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.natCast_ne_top q)⟩
  have hJfvtop : holderJetNorm noDriftWeight C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 1)
      (forcingJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D Df) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (ENNReal.add_ne_top.2 ⟨hJFtop, hJDtop⟩)) hq3) hJfv
  -- the jets of the product and of the forcing term on the patch
  have hDvJ := leibJet_isHolderWeakJet (C := C) (V := F.V) (B := B) hBV hXV hζsm hKc hKB hDw hJvtop
  have hDfvJ := forcingJet_isHolderWeakJet (C := C) (V := F.V) (B := B) hBV hXV hζsm hζ1sm hζ2sm hKc hKB
    hζ10 hζ20 (N := j' + 1) hDw hDfw hJfvtop
  have hrelV : ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)),
      weakSumSquares (leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D) [] x =
        forcingJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D Df [] x := fun x _ =>
    weakSumSquares_leibJet (X := C.Xl) (B : Set (Fin (n + m) → ℝ)) ζ D Df hrel x
  have hz : ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), x ∉ tsupport ζ →
      leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D [] x = 0 := fun x _ hx => by
    rw [leibJet_nil]
    by_cases hxB : x ∈ (B : Set (Fin (n + m) → ℝ))
    · rw [Set.indicator_of_mem hxB, image_eq_zero_of_notMem_tsupport hx, mul_zero]
    · rw [Set.indicator_of_notMem hxB]
  have hav : ∀ x, a x * leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D [] x =
      leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D [] x := fun x => by
    rw [leibJet_nil]
    by_cases hxB : x ∈ (B : Set (Fin (n + m) → ℝ))
    · rw [hBa x hxB, one_mul]
    · rw [Set.indicator_of_notMem hxB, mul_zero]
  have hvfin : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
      (leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D []) ≠ ⊤ :=
    ne_top_of_le_ne_top hJvtop (single_le_holderJetNorm (S.nil_mem_wordFamily _ _))
  obtain ⟨D', hD'J, hD'eq, hD'norm⟩ := hreg (leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D [])
    (leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D) (forcingJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D Df)
    (tsupport ζ) hKc (hKB.trans hBV) hz hav hvfin hDvJ hDfvJ hrelV
  have hvD : ∀ x ∈ (Bs : Set (Fin (n + m) → ℝ)),
      leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D [] x = D [] x := fun x hx => by
    rw [leibJet_nil, Set.indicator_of_mem (hBsB hx), hζ1 x hx, mul_one]
  obtain ⟨hD'Bs, hD'agree⟩ := stage_restrict (C := C) (V := F.V) (B := B) (Bs := Bs) hBsB hBV
    (hBsB.trans hBU) hα0 hvD hD'J (hD'eq [] (Nat.zero_le _)) hDw hDfin
  refine ⟨D', hD'Bs, hD'agree, ?_⟩
  refine (holderJetNorm_mono_set C.dl (hBsB.trans hBV) α (j' + 3) D').trans (hD'norm.trans ?_)
  exact stage_arith hΛ0 (jetConst_nonneg _ _) (jetConst_nonneg _ _) hc'0 hJfv hlv

end Core

section Step

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart noDriftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r₀ : ℕ} {H : H1.StandingHypotheses C.G r₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {a : TestFunction F.V ℝ (⊤ : ℕ∞)}

/-- **One step of the recurrence on `ρ`-balls** (BB p. 604).
Let `U_R^ρ ⊆ V` with `a = 1` on `U_R^ρ`. There are `r_* > 0` and `C_s > 0` such that for
`0 < s < r < r_*`, `r ≤ R`: if `D` is a Hölder weak jet of order `j' + 2` of `D []` on `U_r^ρ` and `Df` a Hölder weak
jet of order `j' + 1` of `Df [] = ∑ᵢ D [i, i]` on `U_r^ρ`, then `D []` has a Hölder weak jet `D''` of order `j' + 3`
on `U_s^ρ`, extending `D`, with
`‖D''‖_{j'+3, C^α(U_s)} ≤ C_s (r - s)^{-(j'+4)} (‖Df‖_{j'+1, C^α(U_r)} + ‖D‖_{j'+2, C^α(U_r)})`. -/
theorem stage_step (hH : HolderFrame C H K hQ F a) (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (j' : ℕ) {R : ℝ}
    (hRV : rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) R ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    (hRa : ∀ x ∈ rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) R, a x = 1) :
    ∃ rstar Cs : ℝ, 0 < rstar ∧ 0 < Cs ∧ ∀ s r : ℝ, 0 < s → s < r → r < rstar → r ≤ R →
      ∀ D Df : List (Fin q) → (Fin (n + m) → ℝ) → ℝ,
        LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl (rhoBallOpen C ν r) (j' + 2) α (D []) D →
        LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl (rhoBallOpen C ν r) (j' + 1) α (Df []) Df →
        (∀ x ∈ rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) r, weakSumSquares D [] x = Df [] x) →
        ∃ D'' : List (Fin q) → (Fin (n + m) → ℝ) → ℝ,
          LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl (rhoBallOpen C ν s) (j' + 3) α (D'' []) D'' ∧
          (∀ K' : List (Fin q), K'.length ≤ j' + 2 →
            ∀ x ∈ rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) s, D'' K' x = D K' x) ∧
          holderJetNorm noDriftWeight C.dl (rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) s) α (j' + 3) D'' ≤
            ENNReal.ofReal (Cs * ((r - s)⁻¹) ^ (j' + 4)) *
              (holderJetNorm noDriftWeight C.dl (rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) r) α (j' + 1) Df +
                holderJetNorm noDriftWeight C.dl (rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) r) α (j' + 2) D) := by
  classical
  obtain ⟨Λ, hΛ0, hreg⟩ := compact_regularity hH hα0 hα1 j'
  obtain ⟨rstar, c, hr0, hr1, hc0, hcut⟩ := exists_cutoff_package C ν hν hα0 hα1 (j' + 3)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hΛc : 0 ≤ Λ * (jetConst q (j' + 1) * (3 * q + 1) + jetConst q (j' + 2)) * c :=
    mul_nonneg (mul_nonneg hΛ0.le (add_nonneg (mul_nonneg (jetConst_nonneg _ _) (by positivity))
      (jetConst_nonneg _ _))) hc0.le
  refine ⟨rstar, 1 + Λ * (jetConst q (j' + 1) * (3 * q + 1) + jetConst q (j' + 2)) * c, hr0,
    by linarith, ?_⟩
  intro s r hs hsr hr hrR D Df hD hDf hrel
  obtain ⟨hζsm, hζc, hζ1, hζsub, hbnd⟩ := hcut s r hs hsr hr
  have hΔ0 : 0 < r - s := sub_pos.2 hsr
  have hΔ1 : r - s ≤ 1 := by linarith
  have hBR : rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) r ⊆
      rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) R := rhoBall_mono C ν _ hrR
  have hBV : rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) r ⊆ (F.V : Set (Fin (n + m) → ℝ)) :=
    hBR.trans hRV
  have hBU : rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) r ⊆ C.U := fun x hx => hx.1
  have hBO : rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) r ⊆ C.O := fun x hx =>
    holderTransfer_U_subset_O C (hBU hx)
  have hBsB : rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) s ⊆
      rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) r := rhoBall_mono C ν _ hsr.le
  have hc'0 : 0 ≤ c * ((r - s)⁻¹) ^ (j' + 3 + 1) := by positivity
  have hcw : ∀ J : List (Fin q), J.length ≤ j' + 3 →
      holderENorm C.dl α (rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) r)
        (wordDerivative C.Xl J (radialCutoff C ν (joinPoint x₀ (0 : Fin m → ℝ)) s r)) ≤
        ENNReal.ofReal (c * ((r - s)⁻¹) ^ (j' + 3 + 1)) := fun J hJ =>
    (S.holderENorm_mono C.dl α C.O _ hBO).trans (hbnd J hJ)
  obtain ⟨D'', h1, h2, h3⟩ := stage_core hH hα0 j' hΛ0.le hc'0 hreg
    (B := rhoBallOpen C ν r) (Bs := rhoBallOpen C ν s) hBsB hBV hBU hζsm hζc hζsub
    (fun x hx => hζ1 hx) (fun x hx => hRa x (hBR hx)) hcw hD hDf hrel
  refine ⟨D'', h1, h2, h3.trans ?_⟩
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hP : 0 ≤ ((r - s)⁻¹) ^ (j' + 4) := by positivity
  have e : Λ * (jetConst q (j' + 1) * (3 * q + 1) + jetConst q (j' + 2)) *
      (c * ((r - s)⁻¹) ^ (j' + 3 + 1)) =
      (Λ * (jetConst q (j' + 1) * (3 * q + 1) + jetConst q (j' + 2)) * c) * ((r - s)⁻¹) ^ (j' + 4) := by
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) hP

end Step

end RothschildStein.P2.HigherHolder
