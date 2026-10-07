-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicUniformLimit
public import RothschildStein.S.IntrinsicUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.H3
variable {N m : ℕ}

/-- iterated form. Compatible continuous intrinsic jets retain
all their word derivatives under uniform convergence. Intermediate
representatives are identified by the shared pointwise uniqueness theorem,
so no unproved compatibility of chosen derivatives is required. -/
theorem hasIntrinsicWordDeriv_of_uniform_jet_limits
    (Ω : Opens (Fin N → ℝ))
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) (I : List (Fin m))
    (F : ℕ → List (Fin m) → (Fin N → ℝ) → ℝ)
    (G : List (Fin m) → (Fin N → ℝ) → ℝ)
    (hf : ∀ n J, J.Sublist I → hasIntrinsicWordDeriv X Ω J (F n []) (F n J))
    (hc : ∀ n J, J.Sublist I → ContinuousOn (F n J) (Ω : Set (Fin N → ℝ)))
    (hlim : ∀ J, J.Sublist I → TendstoUniformlyOn (fun n => F n J) (G J)
      atTop (Ω : Set (Fin N → ℝ))) :
    hasIntrinsicWordDeriv X Ω I (G []) (G I) := by
  induction I with
  | nil => exact fun _ _ => rfl
  | cons i I ih =>
    have hsub (J : List (Fin m)) (hJ : J.Sublist I) : J.Sublist (i :: I) :=
      hJ.trans (List.sublist_cons_self _ _)
    have hfirst (n : ℕ) : hasIntrinsicDeriv Ω (X i) (F n I) (F n (i :: I)) := by
      obtain ⟨a, ha, hi⟩ := hf n (i :: I) (List.Sublist.refl _)
      exact S.hasIntrinsicDeriv_congr_input Ω (X i)
        (S.hasIntrinsicWordDeriv_unique Ω X I ha (hf n I (hsub I (List.Sublist.refl _)))) hi
    have H := hasIntrinsicDeriv_of_uniform_limits Ω (X i)
      (fun n => F n I) (fun n => F n (i :: I)) (G I) (G (i :: I)) hfirst
      (fun n => hc n I (hsub I (List.Sublist.refl _)))
      (fun n => hc n (i :: I) (List.Sublist.refl _))
      (hlim I (hsub I (List.Sublist.refl _))) (hlim (i :: I) (List.Sublist.refl _))
    exact ⟨G I, ih (fun n J hJ => hf n J (hsub J hJ))
      (fun n J hJ => hc n J (hsub J hJ)) (fun J hJ => hlim J (hsub J hJ)), H.2.2⟩

end RothschildStein.H3
