/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
import Nyll.SchemeTheory.Modules.Sections.PullbackFreeSections
import Nyll.SchemeTheory.Modules.Tensor.FiniteFreePullback
import Nyll.SchemeTheory.Modules.Tensor.FiniteFreeSections
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialMatrix
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Original polynomial matrix morphisms under coefficient base change

The actual pullback of a finite free twist is compared with the
corresponding twist over the new coefficient ring by its original
finite biproduct coordinates and the constructed twisting-power
isomorphism. Under this comparison, pulling back the original native
matrix morphism maps precisely the coefficients of every entry.

The proof checks the original free generators and the original target
coordinates. Thus the resulting square involves the actual pullback
of the original sheaf morphism, rather than an independently specified
map with a prescribed cokernel.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules

private theorem pullbackFree_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Type u) {N : X.Modules}
    (a b : (Scheme.Modules.pullback f).obj (SheafOfModules.free I) ⟶ N)
    (h : ∀ i : I, a.app ⊤ (pullbackLocalSection f
        ((SheafOfModules.freeSection (R := Y.ringCatSheaf) i).val (op ⊤))) =
      b.app ⊤ (pullbackLocalSection f
        ((SheafOfModules.freeSection (R := Y.ringCatSheaf) i).val (op ⊤)))) : a = b := by
  apply ((pullbackPushforwardAdjunction f).homEquiv (SheafOfModules.free I) N).injective
  apply (freeHomTopSectionsEquiv ((Scheme.Modules.pushforward f).obj N) I).injective
  funext i
  exact h i

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/-- The actual finite free twist comparison, with original
biproduct coordinates and the actual twisting-power comparison. -/
def freeTwistBaseChangeIso (J : Type u) [Finite J] (d : ℕ) :
    (Scheme.Modules.pullback (map R A n)).obj
        ((show (Proj 𝒜R).Modules from SheafOfModules.free J) ⊗
          (twistingSheaf R n).tensorPow d) ≅
      (show (Proj 𝒜A).Modules from SheafOfModules.free J) ⊗
        (twistingSheaf A n).tensorPow d :=
  finiteFreeTensorPullbackIso (map R A n) J (twistingPowerBaseChangeIso R A n d)

/-- The original native polynomial matrix morphism commutes with
coefficient base change and the constructed source and target comparisons. -/
theorem polynomialMatrixHom_baseChange (I J : Type u) [Finite J] (d : ℕ)
    (m : I → J → 𝒜R d) :
    (Scheme.Modules.pullback (map R A n)).map (polynomialMatrixHom R n I J d m) ≫
        (freeTwistBaseChangeIso R A n J d).hom =
      (pullbackFreeIso (map R A n) I).hom ≫
        polynomialMatrixHom A n I J d
          (fun i j => (mvMapGraded R A n).gradedAddHom d (m i j)) := by
  let f : Proj 𝒜A ⟶ Proj 𝒜R := map R A n
  let LR : (Proj 𝒜R).Modules := (twistingSheaf R n).tensorPow d
  let LA : (Proj 𝒜A).Modules := (twistingSheaf A n).tensorPow d
  let TR : (Proj 𝒜R).Modules := (show (Proj 𝒜R).Modules from SheafOfModules.free J) ⊗ LR
  let TA : (Proj 𝒜A).Modules := (show (Proj 𝒜A).Modules from SheafOfModules.free J) ⊗ LA
  let e : (Scheme.Modules.pullback f).obj LR ≅ LA := twistingPowerBaseChangeIso R A n d
  let eT : (Scheme.Modules.pullback f).obj TR ≅ TA := freeTwistBaseChangeIso R A n J d
  let φR : (show (Proj 𝒜R).Modules from SheafOfModules.free I) ⟶ TR :=
    polynomialMatrixHom R n I J d m
  let mA : I → J → 𝒜A d :=
    fun i j => (mvMapGraded R A n).gradedAddHom d (m i j)
  let φA : (show (Proj 𝒜A).Modules from SheafOfModules.free I) ⟶ TA :=
    polynomialMatrixHom A n I J d mA
  apply pullbackFree_hom_ext f I
  intro i
  let sR : Γ((show (Proj 𝒜R).Modules from SheafOfModules.free I), ⊤) :=
    (SheafOfModules.freeSection (R := (Proj 𝒜R).ringCatSheaf) i).val (op ⊤)
  let sA : Γ((show (Proj 𝒜A).Modules from SheafOfModules.free I), ⊤) :=
    (SheafOfModules.freeSection (R := (Proj 𝒜A).ringCatSheaf) i).val (op ⊤)
  let zR : Γ(TR, ⊤) := φR.app ⊤ sR
  have hz : eT.hom.app ⊤ (pullbackLocalSection f zR) = φA.app ⊤ sA := by
    apply (finiteFreeTensorSectionsEquiv J ⊤ (π A n) LA).injective
    funext j
    have hcoord := finiteFreeTensorPullbackIso_hom_section_coordinate f J e ⊤ zR j
    have hR := finiteFreeTensorSectionsEquiv_apply J ⊤ (π R n) LR zR j
    have hA := finiteFreeTensorSectionsEquiv_apply J ⊤ (π A n) LA
      (eT.hom.app ⊤ (pullbackLocalSection f zR)) j
    let tR : Γ(LR, ⊤) := polynomialTwistingSection R n d (m i j)
    let tA : Γ(LA, ⊤) := polynomialTwistingSection A n d (mA i j)
    have hpoly : finiteFreeTensorSectionsEquiv J ⊤ (π R n) LR zR j = tR :=
      polynomialMatrixHom_generator R n I J d m i j
    have hbase : e.hom.app ⊤ (pullbackLocalSection f tR) = tA :=
      polynomialTwistingSection_baseChange R A n d (m i j)
    have htarget : tA = finiteFreeTensorSectionsEquiv J ⊤ (π A n) LA (φA.app ⊤ sA) j :=
      (polynomialMatrixHom_generator A n I J d mA i j).symm
    have hfirst : finiteFreeTensorSectionsEquiv J ⊤ (π A n) LA
        (eT.hom.app ⊤ (pullbackLocalSection f zR)) j =
      e.hom.app ⊤ (pullbackLocalSection f
        (finiteFreeTensorSectionsEquiv J ⊤ (π R n) LR zR j)) :=
      hA.trans (hcoord.trans (congrArg
        (fun t : Γ(LR, ⊤) => e.hom.app ⊤ (pullbackLocalSection f t)) hR.symm))
    exact hfirst.trans ((congrArg
      (fun t : Γ(LR, ⊤) => e.hom.app ⊤ (pullbackLocalSection f t)) hpoly).trans
        (hbase.trans htarget))
  have hR : ((Scheme.Modules.pullback f).map φR ≫ eT.hom).app ⊤
        (pullbackLocalSection f sR) = eT.hom.app ⊤ (pullbackLocalSection f zR) :=
    congrArg (eT.hom.app ⊤) (pullbackLocalSection_app f φR sR).symm
  have hA : ((pullbackFreeIso f I).hom ≫ φA).app ⊤ (pullbackLocalSection f sR) =
      φA.app ⊤ sA :=
    congrArg (φA.app ⊤) (pullbackFreeIso_hom_app_pullback_freeSection f I i ⊤)
  exact hR.trans (hz.trans hA.symm)

end AlgebraicGeometry.ProjSpace
