/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Quasicoherent.TildePullback
import Nyll.SchemeTheory.Modules.Quasicoherent.IsoBaseChangeSectionsIsoFromTildeGamma
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Actual affine pullback sections of quasicoherent modules

The section comparison is the scalar-adjoint of the original sheaf
pullback unit. Its value on every pure tensor is scalar multiplication
of that unit section, and its naturality uses the original module maps.

Quasicoherence of the actual pullback is supplied by the genuine tilde
pullback isomorphism and the affine counit. No pullback presentation or
section-comparison hypothesis is introduced.
-/

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The original pullback unit on actual global sections, with the
native restriction of coefficient scalars. -/
def specPullbackUnitSections :
    moduleSpecΓFunctor (R := R) ⟶
      pullback (Spec.map φ) ⋙ moduleSpecΓFunctor (R := S) ⋙
        ModuleCat.restrictScalars φ.hom :=
  (Functor.leftUnitor (moduleSpecΓFunctor (R := R))).inv ≫
    Functor.whiskerRight (pullbackPushforwardAdjunction (Spec.map φ)).unit
      (moduleSpecΓFunctor (R := R)) ≫
    (Functor.associator (pullback (Spec.map φ)) (pushforward (Spec.map φ))
      (moduleSpecΓFunctor (R := R))).hom ≫
    Functor.whiskerLeft (pullback (Spec.map φ)) (pushforwardSpecCompΓIso φ).hom

/-- The section transformation retains the literal original sheaf
adjunction unit on the global section. -/
theorem specPullbackUnitSections_app_apply (M : (Spec R).Modules)
    (x : (moduleSpecΓFunctor (R := R)).obj M) :
    (specPullbackUnitSections φ).app M x =
      ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ x := rfl

/-- The scalar extension map adjoint to the actual sheaf pullback unit. -/
def specPullbackSectionsMap (M : (Spec R).Modules) :
    (ModuleCat.extendScalars φ.hom).obj ((moduleSpecΓFunctor (R := R)).obj M) ⟶
      (moduleSpecΓFunctor (R := S)).obj ((pullback (Spec.map φ)).obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv
    ((moduleSpecΓFunctor (R := R)).obj M)
    ((moduleSpecΓFunctor (R := S)).obj ((pullback (Spec.map φ)).obj M))).symm
      ((specPullbackUnitSections φ).app M)

/-- The original unit section is the image of the pure tensor with one. -/
theorem specPullbackSectionsMap_one_tmul (M : (Spec R).Modules)
    (x : (moduleSpecΓFunctor (R := R)).obj M) :
    specPullbackSectionsMap φ M ((1 : S) ⊗ₜ[R,φ.hom] x) =
      (specPullbackUnitSections φ).app M x := by
  let P : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj M
  let Q : ModuleCat.{u} S :=
    (moduleSpecΓFunctor (R := S)).obj ((pullback (Spec.map φ)).obj M)
  let e := (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv P Q
  have h := congrArg (fun k : P ⟶ (ModuleCat.restrictScalars φ.hom).obj Q => k x)
    (e.apply_symm_apply ((specPullbackUnitSections φ).app M))
  have h₁ := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
    (specPullbackSectionsMap φ M) x
  exact h₁.symm.trans h

/-- Every pure tensor is sent to its original scalar multiple of the
actual pullback unit section. -/
theorem specPullbackSectionsMap_tmul (M : (Spec R).Modules) (s : S)
    (x : (moduleSpecΓFunctor (R := R)).obj M) :
    specPullbackSectionsMap φ M (s ⊗ₜ[R,φ.hom] x) =
      s • (show (moduleSpecΓFunctor (R := S)).obj ((pullback (Spec.map φ)).obj M) from
        (specPullbackUnitSections φ).app M x) := by
  have ht := ModuleCat.ExtendScalars.smul_tmul φ.hom s (1 : S) x
  have h₁ := ht.trans
    (congrArg (fun a : S => a ⊗ₜ[R,φ.hom] x) (mul_one s))
  have h₂ := (specPullbackSectionsMap φ M).hom.map_smul s ((1 : S) ⊗ₜ[R,φ.hom] x)
  have h₃ := congrArg
    (fun y : (moduleSpecΓFunctor (R := S)).obj ((pullback (Spec.map φ)).obj M) => s • y)
    (specPullbackSectionsMap_one_tmul φ M x)
  exact (congrArg (specPullbackSectionsMap φ M) h₁.symm).trans (h₂.trans h₃)

/-- The original affine pullback section comparison commutes with the
given sheaf morphism, including its actual scalar-extension map. -/
theorem specPullbackSectionsMap_naturality {M N : (Spec R).Modules} (θ : M ⟶ N) :
    (ModuleCat.extendScalars φ.hom).map ((moduleSpecΓFunctor (R := R)).map θ) ≫
        specPullbackSectionsMap φ N =
      specPullbackSectionsMap φ M ≫
        (moduleSpecΓFunctor (R := S)).map ((pullback (Spec.map φ)).map θ) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  have hmap := ModuleCat.ExtendScalars.map_tmul φ.hom
    ((moduleSpecΓFunctor (R := R)).map θ) (1 : S) x
  have hunit := congrArg
    (fun k : (moduleSpecΓFunctor (R := R)).obj M ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        ((moduleSpecΓFunctor (R := S)).obj ((pullback (Spec.map φ)).obj N)) => k x)
    ((specPullbackUnitSections φ).naturality θ)
  have hright := congrArg
    (fun y : (moduleSpecΓFunctor (R := S)).obj ((pullback (Spec.map φ)).obj M) =>
      ((moduleSpecΓFunctor (R := S)).map ((pullback (Spec.map φ)).map θ)) y)
    (specPullbackSectionsMap_one_tmul φ M x).symm
  exact (congrArg (specPullbackSectionsMap φ N) hmap).trans
    ((specPullbackSectionsMap_one_tmul φ N
      (((moduleSpecΓFunctor (R := R)).map θ) x)).trans (hunit.trans hright))

/-- The actual pullback of an affine quasicoherent module is quasicoherent. -/
theorem isQuasicoherent_pullback_specMap (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((pullback (Spec.map φ)).obj M).IsQuasicoherent := by
  let P : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj M
  let ε : (tilde P : (Spec R).Modules) ⟶ M := fromTildeΓ (R := R) M
  have hε : IsIso (C := (Spec R).Modules) ε :=
    isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  let eM : tilde P ≅ M := asIso (C := (Spec R).Modules) ε
  let e : tilde ((ModuleCat.extendScalars φ.hom).obj P) ≅
      (pullback (Spec.map φ)).obj M :=
    (tilde.pullbackSpecIso φ P).symm ≪≫ (pullback (Spec.map φ)).mapIso eM
  have hP : (tilde ((ModuleCat.extendScalars φ.hom).obj P)).IsQuasicoherent :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso
    ((sheafOfModulesEquivalence (Spec S)).functor.mapIso e) hP

/-- The actual scalar-adjoint section map is invertible for an affine
quasicoherent module. -/
theorem isIso_specPullbackSectionsMap (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsIso (specPullbackSectionsMap φ M) :=
  isIso_baseChange_sections_of_isIso_fromTildeGamma φ M
    (isIso_fromTildeΓ_of_isQuasicoherent (R := R) M)

/-- The original global sections of an affine pullback are the actual
scalar extension of the original global sections. -/
def specPullbackSectionsEquiv (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj ((moduleSpecΓFunctor (R := R)).obj M) ≃ₗ[S]
      (moduleSpecΓFunctor (R := S)).obj ((pullback (Spec.map φ)).obj M) := by
  let α := specPullbackSectionsMap φ M
  have hα : IsIso α := isIso_specPullbackSectionsMap φ M
  exact (asIso α).toLinearEquiv

/-- The affine pullback section equivalence retains the original pure-tensor formula. -/
theorem specPullbackSectionsEquiv_tmul (M : (Spec R).Modules) [M.IsQuasicoherent]
    (s : S) (x : (moduleSpecΓFunctor (R := R)).obj M) :
    specPullbackSectionsEquiv φ M (s ⊗ₜ[R,φ.hom] x) =
      s • (show (moduleSpecΓFunctor (R := S)).obj ((pullback (Spec.map φ)).obj M) from
        (specPullbackUnitSections φ).app M x) :=
  specPullbackSectionsMap_tmul φ M s x

end AlgebraicGeometry.Scheme.Modules
