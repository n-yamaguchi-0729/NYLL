/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafDEqDDMemPow
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebraImage
import Nyll.SchemeTheory.Modules.LocalMorphisms
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# A native coherent sheaf for the actual Rees image

Take the image of the original map from the Rees base change to the
polynomial base change, as a native module sheaf. Affineness of that
morphism proves quasicoherence and finite type.

On every affine open the original source section maps have equal
kernels, and both image projections are surjective. The first
isomorphism theorem therefore compares the actual native sections
with the existing Rees image presheaf. The comparison retains the
original inclusion and every affine restriction.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

open AlgebraicGeometry

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)
  {P : Scheme.{u}} (q : P ⟶ Spec (.of A))

/-- The actual native image sheaf on the original Rees base change. -/
def imageModule : (P' I q).Modules :=
  Scheme.DirectImageAlgebra.imageModule (g I q)

/-- The native Rees image is quasicoherent, as the actual image of
the structural map of an affine morphism. -/
theorem imageModule_isQuasicoherent : (imageModule I q).IsQuasicoherent :=
  Scheme.DirectImageAlgebra.isQuasicoherent_imageModule (g I q)

/-- The native Rees image is of finite type; its generators come
from the original unit sheaf. -/
theorem imageModule_isFiniteType : (imageModule I q).IsFiniteType :=
  Scheme.DirectImageAlgebra.isFiniteType_imageModule (g I q)

/-- The original source-to-image section map with the original Rees action. -/
def imageProjectionSections (U : (P' I q).Opens) :
    (OModulePresheaf.unit (π' I q)).obj U →ₗ[Rr I]
      Scheme.Modules.sectionModuleOverBase (π' I q) (imageModule I q) U := by
  let p := (Scheme.Modules.toOModulePresheafHom (π' I q)
    (Scheme.DirectImageAlgebra.imageModuleProjection (g I q))).app U
  exact p

/-- On an affine open, the actual native image projection is surjective. -/
theorem imageProjectionSections_surjective
    (U : (P' I q).Opens) (hU : IsAffineOpen U) :
    Function.Surjective (imageProjectionSections I q U) :=
  Scheme.DirectImageAlgebra.imageModuleProjection_app_surjective (g I q) U hU

private theorem φg_app_eq_app (U : (P' I q).Opens) (a : Γ(P' I q, U)) :
    (φg I q).app U a = (g I q).app U a := by
  have h := congrArg (fun k : Γ(P' I q, U) ⟶ Γ(P₁ I q, g I q ⁻¹ᵁ U) => k a)
    ((g I q).appLE_eq_app (U := U))
  exact (φg_app I q U a).trans h

/-- The kernel of the native image projection is the kernel of the
original Rees-to-polynomial section map. -/
theorem ker_imageProjectionSections (U : (P' I q).Opens) :
    (imageProjectionSections I q U).ker = ((φg I q).app U).ker := by
  let i := Scheme.DirectImageAlgebra.imageModuleInclusion (g I q)
  have hi : Function.Injective (i.app U) :=
    (Scheme.Modules.Hom.mono_iff_injective i).mp
      (inferInstanceAs (Mono (C := (P' I q).Modules) (Abelian.image.ι
        (C := (P' I q).Modules) (Scheme.DirectImageAlgebra.unitMap (g I q))))) U
  ext a
  change imageProjectionSections I q U a = 0 ↔ (φg I q).app U a = 0
  have hφ := φg_app_eq_app I q U (show Γ(P' I q, U) from a)
  have hfac : i.app U (imageProjectionSections I q U a) = (φg I q).app U a :=
    (Scheme.DirectImageAlgebra.imageModule_factorization (g I q) U a).trans hφ.symm
  constructor
  · intro ha
    exact hfac.symm.trans
      ((congrArg (fun x => i.app U x) ha).trans (i.app U).hom.map_zero)
  · intro ha
    apply hi
    exact hfac.trans (ha.trans (i.app U).hom.map_zero.symm)

/-- Actual affine sections of the native sheaf are the original Rees
image sections, with their original coefficient action. -/
def imageAffineSectionsEquiv (U : (P' I q).Opens) (hU : IsAffineOpen U) :
    Scheme.Modules.sectionModuleOverBase (π' I q) (imageModule I q) U ≃ₗ[Rr I]
      (F' I q).obj U := by
  let p := imageProjectionSections I q U
  let f := (φg I q).app U
  let e₁ := LinearMap.quotKerEquivOfSurjective p
    (imageProjectionSections_surjective I q U hU)
  let e₂ := Submodule.quotEquivOfEq (R := Rr I)
    (M := (OModulePresheaf.unit (π' I q)).obj U) p.ker f.ker
    (ker_imageProjectionSections I q U)
  let e₃ := LinearMap.quotKerEquivRange f
  exact e₁.symm.trans (e₂.trans e₃)

/-- On an original source section the comparison is the original
map to the polynomial base change. -/
theorem imageAffineSectionsEquiv_projection (U : (P' I q).Opens) (hU : IsAffineOpen U)
    (a : (OModulePresheaf.unit (π' I q)).obj U) :
    F'val I q (imageAffineSectionsEquiv I q U hU (imageProjectionSections I q U a)) =
      (g I q).app U a := by
  let p := imageProjectionSections I q U
  let e := LinearMap.quotKerEquivOfSurjective p
    (imageProjectionSections_surjective I q U hU)
  have hmk : e (Submodule.Quotient.mk a) = p a :=
    LinearMap.quotKerEquivOfSurjective_apply_mk
      p (imageProjectionSections_surjective I q U hU) a
  have hinv : e.symm (p a) = Submodule.Quotient.mk a :=
    (LinearEquiv.symm_apply_eq e).mpr hmk.symm
  change (((φg I q).app U).quotKerEquivRange
    (Submodule.quotEquivOfEq p.ker ((φg I q).app U).ker
      (ker_imageProjectionSections I q U) (e.symm (p a)))).val = _
  rw [hinv, Submodule.quotEquivOfEq_mk]
  have hφ := φg_app_eq_app I q U (show Γ(P' I q, U) from a)
  exact (LinearMap.quotKerEquivRange_apply_mk ((φg I q).app U) a).trans hφ

/-- The comparison keeps the actual inclusion in the original
direct-image algebra on every affine open. -/
theorem imageAffineSectionsEquiv_apply (U : (P' I q).Opens) (hU : IsAffineOpen U)
    (x : Scheme.Modules.sectionModuleOverBase (π' I q) (imageModule I q) U) :
    F'val I q (imageAffineSectionsEquiv I q U hU x) =
      (Scheme.DirectImageAlgebra.imageModuleInclusion (g I q)).app U x := by
  obtain ⟨a, rfl⟩ := imageProjectionSections_surjective I q U hU x
  exact (imageAffineSectionsEquiv_projection I q U hU a).trans
    (Scheme.DirectImageAlgebra.imageModule_factorization (g I q) U a).symm

/-- The affine comparison commutes with the original restriction maps. -/
theorem imageAffineSectionsEquiv_restriction
    {U V : (P' I q).Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    (x : Scheme.Modules.sectionModuleOverBase (π' I q) (imageModule I q) U) :
    imageAffineSectionsEquiv I q V hV
        (Scheme.Modules.sectionRestrictionOverBase (π' I q) (imageModule I q) h x) =
      (F' I q).res h (imageAffineSectionsEquiv I q U hU x) := by
  let i := Scheme.DirectImageAlgebra.imageModuleInclusion (g I q)
  have hnat := LinearMap.congr_fun
    ((Scheme.Modules.toOModulePresheafHom (π' I q) i).naturality h) x
  apply F'_ext I q
  have heV : F'val I q (imageAffineSectionsEquiv I q V hV
        (Scheme.Modules.sectionRestrictionOverBase (π' I q) (imageModule I q) h x)) =
      (i.app V
        (Scheme.Modules.sectionRestrictionOverBase (π' I q) (imageModule I q) h x) :
          Γ(P₁ I q, g I q ⁻¹ᵁ V)) :=
    imageAffineSectionsEquiv_apply I q V hV _
  have hnat' :
      (i.app V
        (Scheme.Modules.sectionRestrictionOverBase (π' I q) (imageModule I q) h x) :
          Γ(P₁ I q, g I q ⁻¹ᵁ V)) =
        (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono h)).op (i.app U x) := hnat
  have heU : (i.app U x : Γ(P₁ I q, g I q ⁻¹ᵁ U)) =
      F'val I q (imageAffineSectionsEquiv I q U hU x) :=
    (imageAffineSectionsEquiv_apply I q U hU x).symm
  exact heV.trans (hnat'.trans
    ((congrArg (fun z : Γ(P₁ I q, g I q ⁻¹ᵁ U) =>
      (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono h)).op z) heU).trans
        (F'_res_val I q h _).symm))

end AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS
