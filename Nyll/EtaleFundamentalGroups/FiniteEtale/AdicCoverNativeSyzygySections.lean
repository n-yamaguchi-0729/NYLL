/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineSyzygies
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelFreeSections
import Nyll.SchemeTheory.Modules.Sections.KernelSections

/-!
# Native syzygy sections and the original affine presentation kernels

The original closed-level presentation agrees with the original
quotient-coefficient linear combination. Taking its actual categorical
kernel and its original affine sections therefore recovers the actual
affine syzygy module, without changing the presentation or its scalars.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules AdicModuleSystem

private def kernel_equiv_of_comp
    {R Q M T : Type u} [CommRing R] [AddCommGroup Q] [AddCommGroup M] [AddCommGroup T]
    [Module R Q] [Module R M] [Module R T]
    (e : Q ≃ₗ[R] M) (τ : M →ₗ[R] T) (α : Q →ₗ[R] T)
    (h : τ.comp e.toLinearMap = α) : τ.ker ≃ₗ[R] α.ker where
  toFun x := ⟨e.symm x.val, by
    change α (e.symm x.val) = 0
    exact (LinearMap.congr_fun h (e.symm x.val)).symm.trans
      ((congrArg τ (e.apply_symm_apply x.val)).trans x.property)⟩
  invFun x := ⟨e x.val, (LinearMap.congr_fun h x.val).trans x.property⟩
  left_inv x := Subtype.ext (e.apply_symm_apply x.val)
  right_inv x := Subtype.ext (e.symm_apply_apply x.val)
  map_add' x y := Subtype.ext (e.symm.map_add x.val y.val)
  map_smul' a x := Subtype.ext (e.symm.map_smul a x.val)

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L : X.Modules) (d : ℕ) [(L.tensorPow d).IsQuasicoherent]
  (J : Type u) [Finite J]
  (s : ∀ n : ℕ, J → Γ(moduleSheaf f I V n ⊗ L.tensorPow d, ⊤))
  (U : X.affineOpens) (t : Γ(L.tensorPow d, U)) (ht : IsFrameOn t (U : X.Opens))

/-- The original native presentation agrees on the literal quotient coefficient vectors. -/
theorem levelPresentation_app_freeSectionsEquiv (n : ℕ)
    (c : J →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) :
    (levelPresentation f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free J) n
      ((freeHomTopSectionsEquiv (moduleSheaf f I V n ⊗ L.tensorPow d) J).symm (s n))).app U
        (levelFreeSectionsEquiv f I J U n c) =
      affinePresentationMap f I V L d J s U t ht n c := by
  obtain ⟨a, rfl⟩ := quotientFreeCoefficients_surjective
    ((sectionsIdeal f I U) ^ (n + 1)) J c
  let P : X.Modules := SheafOfModules.free J
  let α : P ⟶ moduleSheaf f I V n ⊗ L.tensorPow d :=
    (freeHomTopSectionsEquiv (moduleSheaf f I V n ⊗ L.tensorPow d) J).symm (s n)
  let β := levelPresentation f I V (L.tensorPow d) P n α
  have hu : β.app U (levelFreeSectionsCoefficients f I J U n a) =
      α.app U (finiteFreeSectionsEquiv (X := X) J (U : X.Opens) a) := by
    have h := congrArg (fun k => k.app U
      (finiteFreeSectionsEquiv (X := X) J (U : X.Opens) a))
      (levelUnit_levelPresentation f I V (L.tensorPow d) P n α)
    simp only [Scheme.Modules.Hom.comp_app] at h
    exact (congrArg (β.app U) (levelFreeSectionsCoefficients_apply f I J U n a)).trans h
  exact (congrArg (β.app U) (levelFreeSectionsEquiv_coefficients f I J U n a)).trans
    (hu.trans (affinePresentationMap_coefficients_free f I V L d J s U t ht n a).symm)

/-- Sections of the native kernel specified by a family of global generators
are the actual original affine syzygies. -/
def levelPresentationKernelSectionsEquivOfSections (n : ℕ) :
    (moduleSectionsFunctor (U : X.Opens)).obj
      (levelPresentationKernel f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free J) n
        ((freeHomTopSectionsEquiv (moduleSheaf f I V n ⊗ L.tensorPow d) J).symm (s n)))
      ≃ₗ[Γ(X, U)] affineSyzygyKernel f I V L d J s U t ht n := by
  let P : X.Modules := SheafOfModules.free J
  let α : P ⟶ moduleSheaf f I V n ⊗ L.tensorPow d :=
    (freeHomTopSectionsEquiv (moduleSheaf f I V n ⊗ L.tensorPow d) J).symm (s n)
  let β := levelPresentation f I V (L.tensorPow d) P n α
  let τ := ((moduleSectionsFunctor (U : X.Opens)).map β).hom
  let e := levelFreeSectionsEquiv f I J U n
  have h : τ.comp e.toLinearMap = affinePresentationMap f I V L d J s U t ht n := by
    apply LinearMap.ext
    exact levelPresentation_app_freeSectionsEquiv f I V L d J s U t ht n
  exact (kernelSectionsEquiv β (U : X.Opens)).trans
    (kernel_equiv_of_comp e τ (affinePresentationMap f I V L d J s U t ht n) h)

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
