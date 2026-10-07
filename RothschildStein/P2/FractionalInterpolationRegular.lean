-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FractionalInterpolationPrincipal
public import RothschildStein.P1.ContinuityRegular

/-!
# Hölder interpolation: the regular remainder

A regular remainder `r` of budget `3` (jointly `C³` with compact support in `V × V`, as in the type calculus) needs no
splitting: one integration by parts in `η` (`far_estimate`, with the jet bound of the compactly
supported `C³` function `r`) bounds `∫ r(x, η) (L̃ v)(η) dη` by `C ‖v‖_∞` in sup norm and in the
Hölder seminorm for `d̃` (BB pp. 594-595: "regular components have bounds from their sup norms").
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

/-- A compactly supported `C³` function has a jet bound. -/
theorem exists_jetSup_of_compactSupport {N : ℕ} {H : E2 N → ℝ} (hH : ContDiff ℝ 3 H)
    (hc : HasCompactSupport H) : ∃ B : ℝ, JetSup H B := by
  have hb : ∀ j : Fin 4, ∃ A : ℝ, 0 ≤ A ∧ ∀ p, ‖iteratedFDeriv ℝ (j : ℕ) H p‖ ≤ A := by
    intro j
    have hj : (j : ℕ) ≤ 3 := Nat.lt_succ_iff.mp j.2
    have hcont : Continuous (iteratedFDeriv ℝ (j : ℕ) H) :=
      hH.continuous_iteratedFDeriv (by exact_mod_cast hj)
    obtain ⟨D, hD⟩ := hcont.bounded_above_of_compact_support (hc.iteratedFDeriv (j : ℕ))
    exact ⟨max D 0, le_max_right _ _, fun p => (hD p).trans (le_max_left _ _)⟩
  choose A hA0 hA using hb
  refine ⟨∑ j, A j, hH, fun j hj p => ?_⟩
  have hjj : j < 4 := by omega
  exact (hA ⟨j, hjj⟩ p).trans
    (Finset.single_le_sum (f := A) (fun i _ => hA0 i) (Finset.mem_univ (⟨j, hjj⟩ : Fin 4)))

/-- **The regular remainder** (budget `3`): `∫ r(x, η) (L̃ v)(η) dη` is bounded by
`Cr ‖v‖_∞` and `C^α`-Hölder for `d̃` with constant `Cr ‖v‖_∞`. -/
theorem regular_interpolation (hF : C.IsLiftedFrame F) (hw : ∀ i, (w i : ℕ) ≤ 2)
    {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} (hr : IsRegularKernel F 3 r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    {Lop : ((Fin (n + m) → ℝ) → ℝ) → (Fin (n + m) → ℝ) → ℝ} (hL : IsCoordinateOp C Lop) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ v : (Fin (n + m) → ℝ) → ℝ, ContDiffOn ℝ 2 v C.O →
      ∀ Mv : ℝ, 0 ≤ Mv → (∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |v y| ≤ Mv) →
      (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), |∫ η, r x η * Lop v η| ≤ Cr * Mv) ∧
      (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)),
        |(∫ η, r x η * Lop v η) - ∫ η, r y η * Lop v η| ≤ Cr * Mv * (C.dl x y).toReal ^ α) := by
  obtain ⟨A, B, hA, hB, hLop⟩ := hL
  set S : Set (Fin (n + m) → ℝ) := closure (F.V : Set (Fin (n + m) → ℝ)) with hS
  have hSc : IsCompact S := hF.isCompact_closure
  have hSU : S ⊆ C.U := hF.closure_subset
  have hSO : S ⊆ C.O := hSU.trans C.U_subset_O
  have hVS : (F.V : Set (Fin (n + m) → ℝ)) ⊆ S := subset_closure
  have hO : IsOpen C.O := isOpen_liftedDomain C
  obtain ⟨Cc, hCc⟩ := exists_coeffBound hO hSc hSO hA hB
  obtain ⟨CE, hCE, hE⟩ := exists_norm_le_mul_dl C hw hSc hSU
  obtain ⟨D₀, hD₀, hD⟩ := C.exists_dl_bound hSc hSU
  have hα' : 0 < 1 - α := by linarith
  obtain ⟨Bj, hJ⟩ := exists_jetSup_of_compactSupport hr.1 hr.2.1
  have hBj : 0 ≤ Bj := hJ.nonneg
  have hHK : ∀ ξ η : Fin (n + m) → ℝ, η ∉ S →
      (fun p : E2 (n + m) => r p.1 p.2) (ξ, η) = 0 := by
    intro ξ η hη
    have hnot : (ξ, η) ∉ tsupport (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => r z.1 z.2) :=
      fun hmem => hη (subset_closure (hr.2.2 hmem).2)
    exact image_eq_zero_of_notMem_tsupport
      (f := fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => r z.1 z.2) hnot
  set Cf : ℝ := (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) *
    (((n + m : ℕ) : ℝ) + 1) with hCf
  have hCf0 : 0 ≤ Cf := by have := hCc.1; positivity
  refine ⟨Cf * Bj * (1 + CE * D₀ ^ (1 - α)), by positivity, ?_⟩
  intro v hv Mv hMv0 hMv
  have hvS : ∀ y ∈ S, |v y| ≤ Mv := abs_le_of_mem_closure (hv.continuousOn.mono hSO) hMv
  have hfar := fun ξ ξ' => far_estimate hO hSc hSO hA hB hCc hJ hHK hv hvS ξ ξ'
  have hint : ∀ x : Fin (n + m) → ℝ, ∫ η, r x η * Lop v η =
      ∫ η, (fun p : E2 (n + m) => r p.1 p.2) (x, η) * diffOp2 A B v η := by
    intro x
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    beta_reduce
    by_cases hη : η ∈ S
    · rw [hLop v hv η (hSO hη)]
    · have := hHK x η hη
      simp only at this
      rw [this, zero_mul, zero_mul]
  have hsup : ∀ x : Fin (n + m) → ℝ, |∫ η, r x η * Lop v η| ≤ Cf * Bj * Mv := by
    intro x
    rw [hint x]
    refine (hfar x x).1.trans ?_
    have h1 : (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) ≤
        Cf := by
      rw [hCf]
      have := hCc.1
      have : 0 ≤ (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) := by
        positivity
      nlinarith [Nat.cast_nonneg (α := ℝ) (n + m)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hBj) hMv0
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · refine (hsup x).trans ?_
    have : 0 ≤ Cf * Bj * Mv * (CE * D₀ ^ (1 - α)) := by positivity
    nlinarith
  · rw [hint x, hint y]
    refine (hfar x y).2.trans ?_
    have h1 : (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) *
        (((n + m : ℕ) : ℝ) * Bj) ≤ Cf * Bj := by
      have hc := hCc.1
      have e : Cf * Bj = (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) *
          ((((n + m : ℕ) : ℝ) + 1) * Bj) := by rw [hCf]; ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) (n + m)]
    have hxd := hE y (hVS hy) x (hVS hx)
    have hdd : (C.dl y x).toReal = (C.dl x y).toReal := by rw [C.dl_symm y x]
    rw [hdd] at hxd
    have hd0 : 0 ≤ (C.dl x y).toReal := ENNReal.toReal_nonneg
    have hdle : (C.dl x y).toReal ≤ D₀ ^ (1 - α) * (C.dl x y).toReal ^ α := by
      calc (C.dl x y).toReal = (C.dl x y).toReal ^ (1 - α) * (C.dl x y).toReal ^ α := by
            rw [← Real.rpow_add' hd0 (by linarith)]; simp
        _ ≤ D₀ ^ (1 - α) * (C.dl x y).toReal ^ α :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd0 (hD x (hVS hx) y (hVS hy)) hα'.le)
              (Real.rpow_nonneg hd0 _)
    have hnorm : ‖x - y‖ ≤ CE * D₀ ^ (1 - α) * (C.dl x y).toReal ^ α := by
      calc ‖x - y‖ ≤ CE * (C.dl x y).toReal := hxd
        _ ≤ CE * (D₀ ^ (1 - α) * (C.dl x y).toReal ^ α) := mul_le_mul_of_nonneg_left hdle hCE.le
        _ = CE * D₀ ^ (1 - α) * (C.dl x y).toReal ^ α := by ring
    calc _ ≤ (volume S).toReal * ((4 * ((n + m : ℕ) : ℝ) ^ 2 + 2 * ((n + m : ℕ) : ℝ)) * Cc) *
          (((n + m : ℕ) : ℝ) * Bj) * Mv * ‖x - y‖ := le_rfl
      _ ≤ Cf * Bj * Mv * ‖x - y‖ := by gcongr
      _ ≤ Cf * Bj * Mv * (CE * D₀ ^ (1 - α) * (C.dl x y).toReal ^ α) := by
          have : 0 ≤ Cf * Bj * Mv := by positivity
          exact mul_le_mul_of_nonneg_left hnorm this
      _ ≤ _ := by
          have : 0 ≤ Cf * Bj * Mv * (C.dl x y).toReal ^ α := by positivity
          nlinarith

end RothschildStein.P2
