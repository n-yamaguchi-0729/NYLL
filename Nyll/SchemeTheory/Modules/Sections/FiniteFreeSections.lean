/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Sections.AffineEpi
import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Original sections and generators of a finite free module sheaf

Native evaluation preserves the product of finitely many structure
modules, hence their biproduct and coproduct. Its actual colimit comparison
therefore identifies the original sections of the finite free sheaf with
the finite free module over the original open's coefficient ring.

The comparison sends each coefficient vector to that coefficient times
the original free section. Consequently the native morphism specified by
global sections becomes their literal local linear combination. If this
morphism is epimorphic and its target is quasicoherent, this original
linear combination is surjective on each affine open.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] Abelian.hasFiniteBiproducts

variable {X : Scheme.{u}} (J : Type u) [Finite J] (U : X.Opens)

private def freeSectionsIsColimit : IsColimit
    (Cofan.mk ((moduleSectionsFunctor U).obj (show X.Modules from SheafOfModules.free J))
      (fun j : J => (SheafOfModules.ιFree (R := X.ringCatSheaf) j).val.app (op U)) :
        Cofan (fun _ : J => ModuleCat.of Γ(X, U) Γ(X, U))) := by
  let E : SheafOfModules.{u} X.ringCatSheaf ⥤ ModuleCat.{u} Γ(X, U) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  let B : J → SheafOfModules.{u} X.ringCatSheaf :=
    fun _ => SheafOfModules.unit X.ringCatSheaf
  have : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have : PreservesLimit (Discrete.functor B) E :=
    inferInstanceAs (PreservesLimit (Discrete.functor B)
      (SheafOfModules.evaluation X.ringCatSheaf (op U)))
  have : PreservesBiproduct B E := preservesBiproduct_of_preservesProduct E
  have : PreservesColimit (Discrete.functor B) E :=
    preservesCoproduct_of_preservesBiproduct E
  exact isColimitCofanMkObjOfIsColimit E B
    (fun j => SheafOfModules.ιFree (R := X.ringCatSheaf) j)
    (SheafOfModules.isColimitFreeCofan J)

/-- The original sections of a finite free sheaf are the finite free module over
the original coefficient ring, by the actual evaluated coproduct. -/
def finiteFreeSectionsEquiv :
    (J →₀ Γ(X, U)) ≃ₗ[Γ(X, U)] Γ((show X.Modules from SheafOfModules.free J), U) :=
  ((ModuleCat.finsuppCoconeIsColimit Γ(X, U) Γ(X, U) J).coconePointUniqueUpToIso
    (freeSectionsIsColimit J U)).toLinearEquiv

/-- Each basis vector goes to its actual coefficient times the original free section. -/
theorem finiteFreeSectionsEquiv_single (j : J) (a : Γ(X, U)) :
    finiteFreeSectionsEquiv J U (Finsupp.single j a) =
      a • (show Γ((show X.Modules from SheafOfModules.free J), U) from
        (SheafOfModules.freeSection (R := X.ringCatSheaf) j).val (op U)) := by
  let F : X.Modules := SheafOfModules.free J
  let ι : ModuleCat.of Γ(X, U) Γ(X, U) ⟶ (moduleSectionsFunctor U).obj F :=
    (SheafOfModules.ιFree (R := X.ringCatSheaf) j).val.app (op U)
  let g : Γ(F, U) := (SheafOfModules.freeSection (R := X.ringCatSheaf) j).val (op U)
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (ModuleCat.finsuppCoconeIsColimit Γ(X, U) Γ(X, U) J)
    (freeSectionsIsColimit J U) (Discrete.mk j)
  have hval : finiteFreeSectionsEquiv J U (Finsupp.single j a) =
      ι.hom a :=
    congrArg (fun k : ModuleCat.of Γ(X, U) Γ(X, U) ⟶
      (moduleSectionsFunctor U).obj (show X.Modules from SheafOfModules.free J) => k.hom a) h
  have ha : ι.hom a = a • ι.hom (1 : Γ(X, U)) := by
    simpa only [smul_eq_mul, mul_one] using
      ι.hom.map_smul a (1 : Γ(X, U))
  have hg : ι.hom (1 : Γ(X, U)) = g := rfl
  exact hval.trans (ha.trans (congrArg (fun x : Γ(F, U) => a • x) hg))

variable (M : X.Modules) (s : J → Γ(M, ⊤))

/-- The native free morphism acts on the coefficient vector by the literal linear
combination of the original restricted global sections. -/
theorem freeHomTopSectionsEquiv_app_linearCombination (c : J →₀ Γ(X, U)) :
    ((freeHomTopSectionsEquiv M J).symm s).app U (finiteFreeSectionsEquiv J U c) =
      Finsupp.linearCombination Γ(X, U)
        (fun j : J => M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s j)) c := by
  let φ : (show X.Modules from SheafOfModules.free J) ⟶ M :=
    (freeHomTopSectionsEquiv M J).symm s
  let φU : (moduleSectionsFunctor U).obj (show X.Modules from SheafOfModules.free J) ⟶
      (moduleSectionsFunctor U).obj M := (moduleSectionsFunctor U).map φ
  have hgen (j : J) :
      φ.app U ((SheafOfModules.freeSection (R := X.ringCatSheaf) j).val (op U)) =
        M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s j) := by
    have h := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun i : J => (sectionsTopEquiv M).symm (s i)) j
    exact congrArg (fun z : M.sections => z.val (op U)) h
  let l : (J →₀ Γ(X, U)) →ₗ[Γ(X, U)] Γ(M, U) :=
    φU.hom.comp (finiteFreeSectionsEquiv J U).toLinearMap
  have hl : l = Finsupp.linearCombination Γ(X, U)
      (fun j : J => M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s j)) := by
    apply Finsupp.lhom_ext
    intro j a
    change φ.app U (finiteFreeSectionsEquiv J U (Finsupp.single j a)) = _
    rw [finiteFreeSectionsEquiv_single, Finsupp.linearCombination_single]
    exact (φU.hom.map_smul a
      ((SheafOfModules.freeSection (R := X.ringCatSheaf) j).val (op U))).trans
        (congrArg (fun z : Γ(M, U) => a • z) (hgen j))
  exact LinearMap.congr_fun hl c

/-- An actual epimorphic finite free presentation gives surjectivity of the original
local linear combination on every affine open. -/
theorem linearCombination_restriction_surjective_of_epi [M.IsQuasicoherent]
    [Epi ((freeHomTopSectionsEquiv M J).symm s)] (hU : IsAffineOpen U) :
    Function.Surjective (Finsupp.linearCombination Γ(X, U)
      (fun j : J => M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s j))) := by
  let φ : (show X.Modules from SheafOfModules.free J) ⟶ M :=
    (freeHomTopSectionsEquiv M J).symm s
  have hφ : Function.Surjective (φ.app U) :=
    Hom.app_surjective_of_epi_of_isAffineOpen φ U hU
  intro y
  obtain ⟨x, hx⟩ := hφ y
  let e := finiteFreeSectionsEquiv J U
  refine ⟨e.symm x, ?_⟩
  exact (freeHomTopSectionsEquiv_app_linearCombination J U M s (e.symm x)).symm.trans
    ((congrArg (φ.app U) (e.apply_symm_apply x)).trans hx)

end AlgebraicGeometry.Scheme.Modules
