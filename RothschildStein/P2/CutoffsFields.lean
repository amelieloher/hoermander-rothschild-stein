-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.CutoffsJets
public import RothschildStein.P1.LiftedChart
public import RothschildStein.H3.SmoothGaugeCutoff
public import RothschildStein.Definitions.wordDerivative
public import RothschildStein.Definitions.wordWeight

/-!
# The fields `Z_i = Y_i + R_{[i],η}` and the gauge word bound

By `C.bracket_approx` with `I = [i]`, a lifted field acts on a function of `Θ(η, ·)` as
`X̃_i (g ∘ Θ η) = (Z_i g) ∘ Θ η` with `Z_i = Y_i + R_{[i],η}` (BB p. 579). The coordinates of
`Z_i` lie in the symbol classes of degree `ω_j - w_i`, so every word derivative `Z_I ν` of the
gauge satisfies `|Z_I ν| ≤ M ν^{1 - |I|}` on the punctured ball (BB p. 579: "a weighted derivative of order `j` of `N` has magnitude at most `C N^{1-j}`").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P2

open RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The model field plus the bracket remainder, `Z_{i,η} u = Y_i u + R_{[i],η} u`. -/
def zField (C : LiftedChart w st Ω hΩ X x₀ m) (i : Fin k) (η u : Fin (n + m) → ℝ) :
    Fin (n + m) → ℝ :=
  C.Y i u + C.R [i] η u

/-- The symbol context of a chart, a gauge, a parameter set and a radius. -/
def chartCtx (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (Kc : Set (Fin (n + m) → ℝ)) (ρ : ℝ) : SymCtx (n + m) :=
  ⟨C.G.weight, ν, Kc, ρ⟩

theorem chartCtx_good (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (Kc : Set (Fin (n + m) → ℝ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (chartCtx C ν Kc ρ).Good :=
  ⟨ν.gauge.1, hρ0, hρ1⟩

theorem wordWeight_cons (i : Fin k) (I : List (Fin k)) :
    wordWeight w (i :: I) = (w i : ℕ) + wordWeight w I := by
  simp [wordWeight]

theorem wordWeight_singleton (i : Fin k) : wordWeight w [i] = (w i : ℕ) := by
  simp [wordWeight]

/-- The coordinates of `Z_{i,η}` have symbol degree `ω_j - w_i`. -/
theorem zField_sym (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hT : ∀ η ∈ Kc, ∀ u, ν u ≤ ρ → (η, u) ∈ C.T) (i : Fin k) (j : Fin (n + m)) (kk : ℕ) :
    Sym (chartCtx C ν Kc ρ) kk ((C.G.weight j : ℤ) - ((w i : ℕ) : ℤ))
      (fun η u => zField C i η u j) := by
  have hc := chartCtx_good C ν Kc hρ0 hρ1
  have hY : Sym (chartCtx C ν Kc ρ) kk ((C.G.weight j : ℤ) - ((w i : ℕ) : ℤ))
      (fun _ u => C.Y i u j) := by
    refine Sym.of_homogeneous C.G (c := chartCtx C ν Kc ρ) rfl ν.gauge kk _ (fun u => C.Y i u j)
      ((contDiff_pi.1 (C.model_field_smooth i) j).contDiffOn) ?_
    intro t ht u _
    have h := congrFun (C.model_field_homogeneous i t ht u) j
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    simp only [HomogeneousGroup.dilate, coordinateDilation]
    rw [sub_eq_add_neg, zpow_add₀ ht.ne', zpow_natCast]
    ring
  have hR : Sym (chartCtx C ν Kc ρ) kk ((C.G.weight j : ℤ) - ((w i : ℕ) : ℤ))
      (fun η u => C.R [i] η u j) := by
    have hjet : ∀ η ∈ Kc, JetVanish C.G.weight (1 - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ))
        (fun u => C.R [i] η u j) := by
      intro η hη
      have h := C.remainder_weight [i] (List.cons_ne_nil i []) η (hKU hη)
      rw [wordWeight_singleton] at h
      exact weightedJet_iff.1 h j
    have h := Sym.of_jets C.G (c := chartCtx C ν Kc ρ) hc rfl ν.gauge hKc C.isOpen_T
      (fun η hη u hu => hT η hη u hu) kk _ (fun z => C.R [i] z.1 z.2 j)
      (contDiffOn_pi.1 (C.remainder_smooth [i]) j) hjet
    exact Sym.mono_d _ hc (by linarith) h
  exact Sym.add _ hc hY hR

/-- Iterated action of the fields `Z_{i,η}` on a parameter family. -/
def zIter (C : LiftedChart w st Ω hΩ X x₀ m) :
    List (Fin k) → ((Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) →
      ((Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
  | [], A => A
  | i :: I, A => fun η u => fderiv ℝ (zIter C I A η) u (zField C i η u)

/-- Every word of fields lowers the symbol degree by its weighted length. -/
theorem zIter_sym (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hT : ∀ η ∈ Kc, ∀ u, ν u ≤ ρ → (η, u) ∈ C.T) {d : ℤ}
    {A : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hA : ∀ kk, Sym (chartCtx C ν Kc ρ) kk d A) :
    ∀ (I : List (Fin k)) (kk : ℕ),
      Sym (chartCtx C ν Kc ρ) kk (d - (wordWeight w I : ℤ)) (zIter C I A) := by
  have hc := chartCtx_good C ν Kc hρ0 hρ1
  intro I
  induction I with
  | nil => intro kk; simpa [zIter, wordWeight] using hA kk
  | cons i I ih =>
    intro kk
    have h := Sym.fieldDeriv (chartCtx C ν Kc ρ) hc (Z := zField C i) (w := ((w i : ℕ) : ℤ))
      (fun j kk' => zField_sym C ν hKc hKU hρ0 hρ1 hT i j kk') (ih (kk + 1))
    have e : d - (wordWeight w (i :: I) : ℤ) = d - (wordWeight w I : ℤ) - ((w i : ℕ) : ℤ) := by
      rw [wordWeight_cons]; push_cast; ring
    rw [e]
    exact h

/-- The gauge itself, as a (constant) parameter family. -/
def gaugeFamily (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G) :
    (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ :=
  fun _ u => ν u

theorem gaugeFamily_sym (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) (Kc : Set (Fin (n + m) → ℝ)) (ρ : ℝ) (kk : ℕ) : Sym (chartCtx C ν Kc ρ) kk 1 (gaugeFamily C ν) := by
  refine Sym.of_homogeneous C.G (c := chartCtx C ν Kc ρ) rfl ν.gauge kk 1 (fun u => ν u) hν ?_
  intro t ht u _
  rw [zpow_one]
  exact ν.gauge.2.2.2 t ht u

/-- The weighted derivatives of the gauge in the fields `Z`:
`|Z_I ν| ≤ M ν^{1 - |I|}` on the punctured ball, uniformly in the parameter (BB p. 579). -/
theorem zIter_gauge_bound (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hT : ∀ η ∈ Kc, ∀ u, ν u ≤ ρ → (η, u) ∈ C.T) (I : List (Fin k)) :
    ∃ M : ℝ, ∀ η ∈ Kc, ∀ u : Fin (n + m) → ℝ, 0 < ν u → ν u < ρ →
      |zIter C I (gaugeFamily C ν) η u| ≤ M * ν u ^ (1 - (wordWeight w I : ℤ)) := by
  have h := zIter_sym C ν hKc hKU hρ0 hρ1 hT (gaugeFamily_sym C ν hν Kc ρ) I 0
  obtain ⟨M, hM⟩ := h.bound _
  exact ⟨M, fun η hη u hu0 hu1 => hM η hη u ⟨hu0, hu1⟩⟩

/-- The smoothly truncated field `χ(ν u) • Z_{i,η} u`, where the profile `χ` equals `1` for
`ν ≤ ρ / 2` and `0` for `ν ≥ ρ`; it is smooth on the whole space. -/
def zCut (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G) (ρ : ℝ)
    (η : Fin (n + m) → ℝ) (i : Fin k) (u : Fin (n + m) → ℝ) : Fin (n + m) → ℝ :=
  H3.quasiballProfile (ρ / 2) (3 * ρ / 2) (ν u) • zField C i η u

theorem zCut_eq (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G) {ρ : ℝ}
    (hρ : 0 < ρ) {η : Fin (n + m) → ℝ} {i : Fin k} {u : Fin (n + m) → ℝ} (hu : ν u ≤ ρ / 2) :
    zCut C ν ρ η i u = zField C i η u := by
  rw [zCut, H3.quasiballProfile_one (by linarith) hu, one_smul]

theorem zCut_contDiff (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {ρ : ℝ} (hρ : 0 < ρ) {η : Fin (n + m) → ℝ}
    (hT : ∀ u, ν u ≤ ρ → (η, u) ∈ C.T) (i : Fin k) :
    ContDiff ℝ (⊤ : ℕ∞) (zCut C ν ρ η i) := by
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun u => H3.quasiballProfile (ρ / 2) (3 * ρ / 2) (ν u)) :=
    H3.contDiff_radial_quasiballProfile ν hν (by linarith) (by linarith)
  refine contDiff_iff_contDiffAt.2 (fun u => ?_)
  by_cases hu : ν u ≤ ρ
  · have hmem : (η, u) ∈ C.T := hT u hu
    have hR : ContDiffAt ℝ (⊤ : ℕ∞) (C.R [i] η) u :=
      ((C.remainder_smooth [i]).comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun _ hw => hw)).contDiffAt ((isOpen_slice C.isOpen_T η).mem_nhds hmem)
    have hZ : ContDiffAt ℝ (⊤ : ℕ∞) (zField C i η) u :=
      (C.model_field_smooth i).contDiffAt.add hR
    exact hχ.contDiffAt.smul hZ
  · have h0 : ∀ᶠ v in 𝓝 u, zCut C ν ρ η i v = 0 := by
      filter_upwards [(isOpen_lt continuous_const ν.gauge.1).mem_nhds (not_le.1 hu)] with v hv
      have hv' : ρ < ν v := hv
      simp [zCut, H3.quasiballProfile_zero (show ρ / 2 < 3 * ρ / 2 by linarith)
        (show (ρ / 2 + 3 * ρ / 2) / 2 ≤ ν v by linarith)]
    exact contDiffAt_const.congr_of_eventuallyEq h0

/-- On the punctured ball of radius `ρ / 2` the truncated word derivatives of the gauge are the
iterates of `Z`. -/
theorem zCut_wordDerivative (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {ρ : ℝ} (hρ : 0 < ρ) (η : Fin (n + m) → ℝ) (I : List (Fin k)) :
    ∀ u : Fin (n + m) → ℝ, 0 < ν u → ν u < ρ / 2 →
      wordDerivative (zCut C ν ρ η) I (fun v => ν v) u =
        zIter C I (gaugeFamily C ν) η u := by
  induction I with
  | nil => intro u _ _; rfl
  | cons i I ih =>
    intro u hu0 hu1
    have hopen : IsOpen (punctBall (ν : (Fin (n + m) → ℝ) → ℝ) (ρ / 2)) :=
      isOpen_punctBall ν.gauge.1 _
    have hev : wordDerivative (zCut C ν ρ η) I (fun v => ν v) =ᶠ[𝓝 u]
        zIter C I (gaugeFamily C ν) η :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds ⟨hu0, hu1⟩) (fun v hv => ih v hv.1 hv.2)
    show fderiv ℝ (wordDerivative (zCut C ν ρ η) I fun v => ν v) u (zCut C ν ρ η i u) =
      fderiv ℝ (zIter C I (gaugeFamily C ν) η) u (zField C i η u)
    rw [hev.fderiv_eq, zCut_eq C ν hρ hu1.le]

end RothschildStein.P2
