/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Tensor.TildeTensor
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Actual tensor sections of quasicoherent modules on a spectrum

The tilde tensor comparison is transported by the original tilde--Gamma
counits of both sheaves. Its global section map is precisely the original
bilinear tensor-section map, by naturality and the adjunction unit formula.

This supplies both quasicoherence of the actual tensor sheaf and the
linear equivalence on actual global sections, with its pure-tensor and
sheaf-morphism naturality formulas.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

private def affineCounitIso (F : (Spec R).Modules) [F.IsQuasicoherent] :
    tilde ((moduleSpecΓFunctor (R := R)).obj F) ≅ F := by
  let M : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj F
  let ε : (tilde M : (Spec R).Modules) ⟶ F := fromTildeΓ (R := R) F
  have hε : IsIso (C := (Spec R).Modules) ε :=
    isIso_fromTildeΓ_of_isQuasicoherent (R := R) F
  exact asIso (C := (Spec R).Modules) ε

private theorem isIso_specTensorSectionsMap_tilde (M N : ModuleCat.{u} R) :
    IsIso (specTensorSectionsMap (tilde M) (tilde N)) := by
  let eA : M ⊗ N ≅
      (moduleSpecΓFunctor (R := R)).obj (tilde M) ⊗
        (moduleSpecΓFunctor (R := R)).obj (tilde N) :=
    tilde.isoTop M ⊗ᵢ tilde.isoTop N
  let eB : M ⊗ N ≅
      (moduleSpecΓFunctor (R := R)).obj (tensor (tilde M) (tilde N)) :=
    tilde.isoTop (M ⊗ N) ≪≫
      (moduleSpecΓFunctor (R := R)).mapIso (tildeTensorIso M N)
  let a : M ⊗ N ⟶
      (moduleSpecΓFunctor (R := R)).obj (tilde M) ⊗
        (moduleSpecΓFunctor (R := R)).obj (tilde N) :=
    eA.hom
  let b : M ⊗ N ⟶
      (moduleSpecΓFunctor (R := R)).obj (tensor (tilde M) (tilde N)) :=
    eB.hom
  have ha : IsIso a := eA.isIso_hom
  have hb : IsIso b := eB.isIso_hom
  have h : b = a ≫ specTensorSectionsMap (tilde M) (tilde N) :=
    tildeTensorMap_globalSections M N
  have hc : IsIso (a ≫ specTensorSectionsMap (tilde M) (tilde N)) :=
    Eq.mp (congrArg (fun k => IsIso (C := ModuleCat.{u} R) k) h) hb
  exact (isIso_comp_left_iff a (specTensorSectionsMap (tilde M) (tilde N))).mp hc

/-- The actual global tensor-section morphism is invertible for two
quasicoherent modules on a spectrum. -/
theorem isIso_specTensorSectionsMap (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] : IsIso (specTensorSectionsMap F G) := by
  let M : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj F
  let N : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj G
  let eF : tilde M ≅ F := affineCounitIso F
  let eG : tilde N ≅ G := affineCounitIso G
  let a : (moduleSpecΓFunctor (R := R)).obj (tilde M) ⊗
      (moduleSpecΓFunctor (R := R)).obj (tilde N) ⟶ M ⊗ N :=
    (moduleSpecΓFunctor (R := R)).map eF.hom ⊗ₘ
      (moduleSpecΓFunctor (R := R)).map eG.hom
  let b : (moduleSpecΓFunctor (R := R)).obj (tensor (tilde M) (tilde N)) ⟶
      (moduleSpecΓFunctor (R := R)).obj (tensor F G) :=
    (moduleSpecΓFunctor (R := R)).map (eF.hom ⊗ₘ eG.hom)
  have ha : IsIso a := inferInstance
  have hb : IsIso b := inferInstance
  have ht : IsIso (specTensorSectionsMap (tilde M) (tilde N)) :=
    isIso_specTensorSectionsMap_tilde M N
  have h : a ≫ specTensorSectionsMap F G =
      specTensorSectionsMap (tilde M) (tilde N) ≫ b :=
    specTensorSectionsMap_naturality eF.hom eG.hom
  have hd : IsIso (specTensorSectionsMap (tilde M) (tilde N) ≫ b) := inferInstance
  have hc : IsIso (a ≫ specTensorSectionsMap F G) :=
    Eq.mp (congrArg (fun k => IsIso (C := ModuleCat.{u} R) k) h.symm) hd
  exact (isIso_comp_left_iff a (specTensorSectionsMap F G)).mp hc

/-- Actual global sections of a tensor of affine quasicoherent sheaves
are the tensor product of their original global section modules. -/
def specTensorSectionsEquiv (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ((moduleSpecΓFunctor (R := R)).obj F ⊗[R]
      (moduleSpecΓFunctor (R := R)).obj G) ≃ₗ[R]
        (moduleSpecΓFunctor (R := R)).obj (tensor F G) := by
  have h : IsIso (specTensorSectionsMap F G) := isIso_specTensorSectionsMap F G
  exact (asIso (specTensorSectionsMap F G)).toLinearEquiv

/-- The equivalence maps a pure tensor to the original tensor of sections. -/
theorem specTensorSectionsEquiv_tmul (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (x : (moduleSpecΓFunctor (R := R)).obj F)
    (y : (moduleSpecΓFunctor (R := R)).obj G) :
    specTensorSectionsEquiv F G (x ⊗ₜ[R] y) = tensorSections x y :=
  specTensorSectionsMap_tmul F G x y

/-- This equivalence is natural for the actual morphisms on both factors. -/
theorem specTensorSectionsEquiv_naturality
    {F F' G G' : (Spec R).Modules}
    [F.IsQuasicoherent] [F'.IsQuasicoherent]
    [G.IsQuasicoherent] [G'.IsQuasicoherent]
    (φ : F ⟶ F') (ψ : G ⟶ G')
    (z : (moduleSpecΓFunctor (R := R)).obj F ⊗[R]
      (moduleSpecΓFunctor (R := R)).obj G) :
    specTensorSectionsEquiv F' G'
        (((moduleSpecΓFunctor (R := R)).map φ ⊗ₘ
          (moduleSpecΓFunctor (R := R)).map ψ) z) =
      ((moduleSpecΓFunctor (R := R)).map (φ ⊗ₘ ψ)) (specTensorSectionsEquiv F G z) :=
  congrArg (fun k : (moduleSpecΓFunctor (R := R)).obj F ⊗
      (moduleSpecΓFunctor (R := R)).obj G ⟶
        (moduleSpecΓFunctor (R := R)).obj (tensor F' G') => k z)
    (specTensorSectionsMap_naturality φ ψ)

/-- The actual tensor product of two affine quasicoherent modules is
quasicoherent, by its constructed tilde comparison. -/
theorem isQuasicoherent_tensor_toSpec (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] : (tensor F G).IsQuasicoherent := by
  let M : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj F
  let N : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj G
  let e : tilde (M ⊗ N) ≅ tensor F G :=
    tildeTensorIso M N ≪≫ (affineCounitIso F ⊗ᵢ affineCounitIso G)
  have h : (tilde (M ⊗ N)).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((sheafOfModulesEquivalence (Spec R)).functor.mapIso e) h

end AlgebraicGeometry.Scheme.Modules
