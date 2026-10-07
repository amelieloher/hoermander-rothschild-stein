-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialBracketSumIdentity
public import RothschildStein.L1.LieBracketSubtraction
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology BigOperators
namespace RothschildStein.L1

/-- Subtracting the two bracketed radial identities gives the exact
remainder decomposition used before the weighted approximation induction. -/
theorem radial_bracket_remainder_identity {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (Z Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Z k) Ω)
    (hY : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Y k) Ω)
    (hradZ : ∀ u ∈ Ω, ∑ k, u k • Z k u = u)
    (hradY : ∀ u ∈ Ω, ∑ k, u k • Y k u = u)
    {u : Fin N → ℝ} (hu : u ∈ Ω) (i j : Fin N) :
    VectorField.lieBracket ℝ (fun v => Z j v - Y j v) (fun _ => Pi.single i 1) u -
      (∑ k, VectorField.lieBracket ℝ (fun _ => Pi.single j 1)
        (fun v => v k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1)
          (fun w => Z k w - Y k w) v) u) =
      (VectorField.lieBracket ℝ (Z j) (Z i) u - VectorField.lieBracket ℝ (Y j) (Y i) u) +
      (∑ k, VectorField.lieBracket ℝ (fun v => Z j v - Y j v)
        (fun v => v k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1) (Z k) v) u) +
      ∑ k, VectorField.lieBracket ℝ (fun v => Y j v - Pi.single j 1)
        (fun v => v k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1)
          (fun w => Z k w - Y k w) v) u := by
  let E := fun k (_ : Fin N → ℝ) => (Pi.single k (1 : ℝ) : Fin N → ℝ)
  let R := fun k v => Z k v - Y k v
  let TZ := fun k v => v k • VectorField.lieBracket ℝ (E i) (Z k) v
  let TY := fun k v => v k • VectorField.lieBracket ℝ (E i) (Y k) v
  let TR := fun k v => v k • VectorField.lieBracket ℝ (E i) (R k) v
  have hdZ := fun k => ((hZ k).contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp)
  have hdY := fun k => ((hY k).contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp)
  have hTZ (k : Fin N) : ContDiffOn ℝ (⊤ : ℕ∞) (TZ k) Ω :=
    (contDiffOn_apply ℝ ℝ k Ω).smul (lieBracket_contDiffOn Ω _ _ contDiffOn_const (hZ k))
  have hTY (k : Fin N) : ContDiffOn ℝ (⊤ : ℕ∞) (TY k) Ω :=
    (contDiffOn_apply ℝ ℝ k Ω).smul (lieBracket_contDiffOn Ω _ _ contDiffOn_const (hY k))
  have hTR (k : Fin N) : (fun v => TZ k v - TY k v) =ᶠ[𝓝 u] TR k :=
    Filter.Eventually.mono (Ω.isOpen.mem_nhds hu) (fun v hv => by
      have hz := ((hZ k).contDiffAt (Ω.isOpen.mem_nhds hv)).differentiableAt (by simp)
      have hy := ((hY k).contDiffAt (Ω.isOpen.mem_nhds hv)).differentiableAt (by simp)
      dsimp only [TZ,TY,TR,R]
      rw [lieBracket_fun_sub_right (E i) (Z k) (Y k) v hz hy,smul_sub])
  have hsplit (k : Fin N) :
      VectorField.lieBracket ℝ (Z j) (TZ k) u - VectorField.lieBracket ℝ (Y j) (TY k) u =
      VectorField.lieBracket ℝ (R j) (TZ k) u +
        VectorField.lieBracket ℝ (E j) (TR k) u +
        VectorField.lieBracket ℝ (fun v => Y j v - Pi.single j 1) (TR k) u := by
    have hleft := lieBracket_fun_sub_left (Z j) (Y j) (TZ k) u (hdZ j) (hdY j)
    have hright := lieBracket_fun_sub_right (Y j) (TZ k) (TY k) u
      (((hTZ k).contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp))
      (((hTY k).contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp))
    have hg := (Filter.EventuallyEq.refl (𝓝 u) (Y j)).lieBracket_vectorField_eq
      (𝕜 := ℝ) (hTR k)
    rw [hg] at hright
    have hf : Y j = fun v => E j v + (Y j v - Pi.single j 1) := by
      funext v
      dsimp only [E]
      abel
    have hy := lieBracket_fun_add_left (E j) (fun v => Y j v - Pi.single j 1) (TR k) u
      (differentiableAt_const _) ((hdY j).fun_sub (differentiableAt_const _))
    rw [← hf] at hy
    have rearrange (a b c d e f g : Fin N → ℝ)
        (hl : c = a-d) (hr : f=d-b) (hs : f=e+g) : a-b=c+e+g := by
      calc
        a-b = (a-d)+(d-b) := by abel
        _ = c+f := by rw [← hl,← hr]
        _ = c+e+g := by rw [hs]; abel
    exact rearrange _ _ _ _ _ _ _ hleft hright hy
  have hz := radial_frame_bracket_sum_identity Ω Z hZ hradZ (Z j) hu i
  have hy := radial_frame_bracket_sum_identity Ω Y hY hradY (Y j) hu i
  have hd := lieBracket_fun_sub_left (Z j) (Y j) (E i) u (hdZ j) (hdY j)
  change VectorField.lieBracket ℝ (R j) (E i) u = _ at hd
  rw [hz,hy] at hd
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun k _ => hsplit k)
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib] at hsum
  change VectorField.lieBracket ℝ (R j) (E i) u - _ = _
  have rearrange (a b c d e f g : Fin N → ℝ)
      (hd : a=(b+c)-(d+e)) (hs : c-e=f+g) : a-g=(b-d)+f := by
    rw [hd]
    have hc : c=e+(f+g) := by
      calc
        c = e+(c-e) := by abel
        _ = e+(f+g) := by rw [hs]
    rw [hc]
    abel
  have hsplitSum : (∑ k, VectorField.lieBracket ℝ (Z j) (TZ k) u) -
      (∑ k, VectorField.lieBracket ℝ (Y j) (TY k) u) =
      (∑ k, VectorField.lieBracket ℝ (R j) (TZ k) u) +
      ((∑ k, VectorField.lieBracket ℝ (E j) (TR k) u) +
        ∑ k, VectorField.lieBracket ℝ (fun v => Y j v - Pi.single j 1) (TR k) u) := by
    rw [hsum]
    abel
  have ha := rearrange _ _ _ _ _ _ _ hd hsplitSum
  have finalRearrange (a b c d : Fin N → ℝ) (h : a-(c+d)=b) : a-c=b+d := by
    rw [← h]
    abel
  exact finalRearrange _ _ _ _ ha
end RothschildStein.L1
