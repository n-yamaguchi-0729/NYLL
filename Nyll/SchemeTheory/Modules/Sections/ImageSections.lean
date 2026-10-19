/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.LocalMorphisms
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentCokernel
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentKernelGlobal
import Nyll.SchemeTheory.Modules.Sections.AffineEpi
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Images

/-!
# Actual affine sections of the image sheaf

For a morphism of quasicoherent module sheaves, the abelian image is
quasicoherent. Its original inclusion identifies its sections on each
affine open with the image of the original section map: the epimorphic
corestriction is surjective on that affine open.

The resulting linear equivalence keeps the original inclusion and
commutes with actual restriction maps. This permits affine image
presheaves, including the Rees image, to be compared with a native sheaf.
-/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N : X.Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)

/-- The actual abelian image of a quasicoherent sheaf morphism is quasicoherent. -/
theorem isQuasicoherent_abelianImage : (Abelian.image φ).IsQuasicoherent := by
  have : (cokernel φ).IsQuasicoherent := isQuasicoherent_cokernel φ
  exact isQuasicoherent_kernel (cokernel.π φ)

variable (U : X.Opens) (hU : IsAffineOpen U)

include hU in
/-- The original inclusion of the image sheaf has the same affine
section image as the original sheaf morphism. -/
theorem range_image_inclusion_app :
    ((moduleSectionsFunctor U).map (Abelian.image.ι φ)).hom.range =
      ((moduleSectionsFunctor U).map φ).hom.range := by
  have : (Abelian.image φ).IsQuasicoherent := isQuasicoherent_abelianImage φ
  have hsurj := Hom.app_surjective_of_epi_of_isAffineOpen
    (Abelian.factorThruImage φ) U hU
  have hfac (x : (moduleSectionsFunctor U).obj M) :
      (Abelian.image.ι φ).app U ((Abelian.factorThruImage φ).app U x) = φ.app U x :=
    congrArg (fun ψ : M ⟶ N => ψ.app U x) (Abelian.image.fac φ)
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := hsurj z
    refine ⟨x, ?_⟩
    exact (hfac x).symm.trans (congrArg (fun y => (Abelian.image.ι φ).app U y) hx)
  · rintro _ ⟨x, rfl⟩
    exact ⟨(Abelian.factorThruImage φ).app U x, hfac x⟩

/-- Actual affine sections of the image sheaf are the image of the
original section map, via the original inclusion. -/
def imageSectionsEquiv :
    (moduleSectionsFunctor U).obj (Abelian.image φ) ≃ₗ[Γ(X, U)]
      ↥(((moduleSectionsFunctor U).map φ).hom.range) := by
  let i := ((moduleSectionsFunctor U).map (Abelian.image.ι φ)).hom
  have hi : Function.Injective i :=
    (Hom.mono_iff_injective (Abelian.image.ι φ)).mp inferInstance U
  exact (LinearEquiv.ofInjective i hi).trans
    (LinearEquiv.ofEq i.range ((moduleSectionsFunctor U).map φ).hom.range
      (range_image_inclusion_app φ U hU))

/-- The section comparison is the literal original image inclusion. -/
theorem imageSectionsEquiv_apply (x : (moduleSectionsFunctor U).obj (Abelian.image φ)) :
    (imageSectionsEquiv φ U hU x).val = (Abelian.image.ι φ).app U x := rfl

/-- Corestricting an original section produces the class of its
original image, with no replacement of the section map. -/
theorem imageSectionsEquiv_factorThruImage (x : (moduleSectionsFunctor U).obj M) :
    (imageSectionsEquiv φ U hU ((Abelian.factorThruImage φ).app U x)).val =
      φ.app U x :=
  congrArg (fun ψ : M ⟶ N => ψ.app U x) (Abelian.image.fac φ)

/-- The affine image comparison retains the original restriction in
the ambient sheaf on every affine subopen. -/
theorem imageSectionsEquiv_restriction {V : X.Opens} (hV : IsAffineOpen V) (h : V ≤ U)
    (x : (moduleSectionsFunctor U).obj (Abelian.image φ)) :
    (imageSectionsEquiv φ V hV ((Abelian.image φ).presheaf.map (homOfLE h).op x)).val =
      N.presheaf.map (homOfLE h).op (imageSectionsEquiv φ U hU x).val := by
  let y : Γ(Abelian.image φ, U) := x
  have hnat := congrArg (fun ψ : Γ(Abelian.image φ, U) ⟶ Γ(N, V) => ψ y)
    ((Abelian.image.ι φ).mapPresheaf.naturality (homOfLE h).op)
  exact hnat

end AlgebraicGeometry.Scheme.Modules
