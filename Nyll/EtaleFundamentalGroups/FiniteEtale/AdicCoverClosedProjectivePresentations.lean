/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectiveLifts
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelPresentations
import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
import Nyll.SchemeTheory.Modules.Tensor.TensorNilpotentSections
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
import Nyll.SchemeTheory.ProjectiveSpace.ClosedImmersionGlobalGeneration

/-!
# Compatible finite presentations on a closed projective family

A single finite family of lifted sections generates every original cover
thickening. The proof combines eventual generation on the closed family,
uniform lifting, and the actual nilpotent transition-kernel criterion.
No generators at higher stages or global lifting assumptions are supplied.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem epi_of_compatible_twisted_lifts
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (I : Ideal A)
    (V : MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
    (L : X.Modules) (hL : IsInvertible L) (d : ℕ)
    (P : X.Modules) [P.IsQuasicoherent]
    (α : ∀ k : ℕ, P ⟶ moduleSheaf f I V k ⊗ L.tensorPow d)
    (hzero : Epi (α 0))
    (hα : ∀ k : ℕ, α (k + 1) ≫ (moduleTransition f I V k ▷ L.tensorPow d) = α k)
    (k : ℕ) : Epi (α k) := by
  induction k with
  | zero => exact hzero
  | succ k ih =>
    let N : X.Modules := moduleSheaf f I V k
    let M : X.Modules := moduleSheaf f I V (k + 1)
    let q : M ⟶ N := moduleTransition f I V k
    have : (tensor N (L.tensorPow d)).IsQuasicoherent :=
      IsInvertible.isQuasicoherent_tensorPow N hL d
    have : Epi (α (k + 1) ≫ (q ▷ L.tensorPow d)) :=
      Eq.mp (congrArg Epi (hα k).symm) ih
    obtain ⟨C, t, ht, hcover⟩ := hL.exists_frame_cover
    apply Hom.epi_of_tensor_nilpotent_quotient q (α (k + 1)) C
      (fun i => tensorPowSection (t i) d)
      (fun i => (ht i).tensorPowSection_monoidalV2 d) hcover
      (sectionsIdeal f I) (k + 2)
    · intro U hU
      exact (moduleTransition_app_ker f I V k U hU).le.trans
        (Submodule.smul_mono (Ideal.pow_le_self (Nat.succ_ne_zero k)) le_rfl)
    · intro U _hU
      exact moduleSheaf_sections_annihilated f I V (k + 1) U

/-- One finite free source presents all original twisted cover modules,
and the presenting maps commute with every original transition. -/
theorem exists_closedProjective_twisting_bound_compatible_presentations
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j]
    (V : MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level (j ≫ π R n) I 0)) :
    let f := j ≫ π R n
    let L := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∃ J : Type u, Finite J ∧
      ∃ α : ∀ k : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶
          moduleSheaf f I V k ⊗ L.tensorPow d,
        (∀ k : ℕ, Epi (α k)) ∧
        (∀ k : ℕ, α (k + 1) ≫ (moduleTransition f I V k ▷ L.tensorPow d) = α k) := by
  intro f L
  obtain ⟨c₀, h₀⟩ := exists_closedImmersion_twisting_bound_finiteFree_epi
    R n j (moduleSheaf f I V 0)
  obtain ⟨c₁, h₁⟩ := exists_closedProjective_twisting_bound_globalLifts R I n j V
  refine ⟨max c₀ c₁, ?_⟩
  intro d hd
  obtain ⟨J, hJ, φ, hφ⟩ := h₀ d ((le_max_left c₀ c₁).trans hd)
  have : Finite J := hJ
  let M : ℕ → Y.Modules := fun k => moduleSheaf f I V k ⊗ L.tensorPow d
  let z : J → Γ(M 0, ⊤) := freeHomTopSectionsEquiv (M 0) J φ
  have hlift : ∀ i : J, ∃ t : ∀ k : ℕ, Γ(M k, ⊤),
      t 0 = z i ∧ ∀ k : ℕ,
        (moduleTransition f I V k ▷ L.tensorPow d).app ⊤ (t (k + 1)) = t k :=
    fun i => h₁ d ((le_max_right c₀ c₁).trans hd) (z i)
  let s : ∀ k : ℕ, J → Γ(M k, ⊤) := fun k i => (Classical.choose (hlift i)) k
  let α : ∀ k : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶ M k :=
    fun k => (freeHomTopSectionsEquiv (M k) J).symm (s k)
  have hzero : α 0 = φ := by
    apply (freeHomTopSectionsEquiv (M 0) J).injective
    funext i
    exact (congrFun ((freeHomTopSectionsEquiv (M 0) J).apply_symm_apply (s 0)) i).trans
      (Classical.choose_spec (hlift i)).1
  have hα : ∀ k : ℕ, α (k + 1) ≫ (moduleTransition f I V k ▷ L.tensorPow d) = α k := by
    intro k
    apply (freeHomTopSectionsEquiv (M k) J).injective
    funext i
    let q : M (k + 1) ⟶ M k := moduleTransition f I V k ▷ L.tensorPow d
    exact (freeHomTopSectionsEquiv_comp (M (k + 1)) J (α (k + 1)) q i).trans
      ((congrArg (q.app ⊤)
        (congrFun ((freeHomTopSectionsEquiv (M (k + 1)) J).apply_symm_apply (s (k + 1))) i)).trans
        (((Classical.choose_spec (hlift i)).2 k).trans
          (congrFun ((freeHomTopSectionsEquiv (M k) J).apply_symm_apply (s k)) i).symm))
  have hEpi : Epi (α 0) := hzero.symm ▸ hφ
  refine ⟨J, hJ, α, ?_, hα⟩
  exact fun k => epi_of_compatible_twisted_lifts f I V L
    (IsInvertible.pullback j (isInvertible_twistingSheaf R n)) d
    (show Y.Modules from SheafOfModules.free J) α hEpi hα k

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
