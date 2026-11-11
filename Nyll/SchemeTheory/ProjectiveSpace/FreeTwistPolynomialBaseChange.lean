/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
public import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
public import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
public import Nyll.SchemeTheory.Modules.Sections.PullbackFreeSections
public import Nyll.SchemeTheory.Modules.Tensor.FiniteFreePullback
public import Nyll.SchemeTheory.Modules.Tensor.FiniteFreeSections
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialMatrix
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafBaseChange
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialBaseChange
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Basic

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

@[expose] public section

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

/-- A square from a free sheaf to a finite free tensor product commutes when its
original generator coordinates commute with pullback. -/
private theorem pullbackFreeTensorHom_eq_of_coordinates
    {X Y : Scheme.{u}} (f : X ⟶ Y) (I J : Type u) [Finite J]
    {R A : Type u} [CommRing R] [CommRing A]
    (pR : Y ⟶ Spec (.of R)) (pA : X ⟶ Spec (.of A))
    {L : Y.Modules} {M : X.Modules} (e : (Scheme.Modules.pullback f).obj L ≅ M)
    (φR : (show Y.Modules from SheafOfModules.free I) ⟶
      (show Y.Modules from SheafOfModules.free J) ⊗ L)
    (φA : (show X.Modules from SheafOfModules.free I) ⟶
      (show X.Modules from SheafOfModules.free J) ⊗ M)
    (h : ∀ (i : I) (j : J),
      e.hom.app ⊤ (pullbackLocalSection f
        (finiteFreeTensorSectionsEquiv J ⊤ pR L
          (φR.app ⊤
            ((SheafOfModules.freeSection (R := Y.ringCatSheaf) i).val (op ⊤))) j)) =
      finiteFreeTensorSectionsEquiv J ⊤ pA M
        (φA.app ⊤
          ((SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (op ⊤))) j) :
    (Scheme.Modules.pullback f).map φR ≫ (finiteFreeTensorPullbackIso f J e).hom =
      (pullbackFreeIso f I).hom ≫ φA := by
  let eT := finiteFreeTensorPullbackIso f J e
  apply pullbackFree_hom_ext f I
    (N := (show X.Modules from SheafOfModules.free J) ⊗ M)
  intro i
  let sR : Γ((show Y.Modules from SheafOfModules.free I), ⊤) :=
    (SheafOfModules.freeSection (R := Y.ringCatSheaf) i).val (op ⊤)
  let sA : Γ((show X.Modules from SheafOfModules.free I), ⊤) :=
    (SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (op ⊤)
  let zR : Γ((show Y.Modules from SheafOfModules.free J) ⊗ L, ⊤) := φR.app ⊤ sR
  have hz : eT.hom.app ⊤ (pullbackLocalSection f zR) = φA.app ⊤ sA := by
    apply (finiteFreeTensorSectionsEquiv J ⊤ pA M).injective
    funext j
    have hcoord := finiteFreeTensorPullbackIso_hom_section_coordinate f J e ⊤ zR j
    have hR := finiteFreeTensorSectionsEquiv_apply J ⊤ pR L zR j
    have hA := finiteFreeTensorSectionsEquiv_apply J ⊤ pA M
      (eT.hom.app ⊤ (pullbackLocalSection f zR)) j
    have hfirst : finiteFreeTensorSectionsEquiv J ⊤ pA M
        (eT.hom.app ⊤ (pullbackLocalSection f zR)) j =
      e.hom.app ⊤ (pullbackLocalSection f
        (finiteFreeTensorSectionsEquiv J ⊤ pR L zR j)) :=
      hA.trans (hcoord.trans (congrArg
        (fun t : Γ(L, ⊤) => e.hom.app ⊤ (pullbackLocalSection f t)) hR.symm))
    exact hfirst.trans (h i j)
  have hR : ((Scheme.Modules.pullback f).map φR ≫ eT.hom).app ⊤
        (pullbackLocalSection f sR) = eT.hom.app ⊤ (pullbackLocalSection f zR) :=
    congrArg (eT.hom.app ⊤) (pullbackLocalSection_app f φR sR).symm
  have hA : ((pullbackFreeIso f I).hom ≫ φA).app ⊤ (pullbackLocalSection f sR) =
      φA.app ⊤ sA :=
    congrArg (φA.app ⊤) (pullbackFreeIso_hom_app_pullback_freeSection f I i ⊤)
  have hresult := hR.trans (hz.trans hA.symm)
  exact hresult

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
  refine pullbackFreeTensorHom_eq_of_coordinates (map R A n) I J
    (π R n) (π A n) (twistingPowerBaseChangeIso R A n d)
    (polynomialMatrixHom R n I J d m)
    (polynomialMatrixHom A n I J d
      (fun i j => (mvMapGraded R A n).gradedAddHom d (m i j))) ?_
  intro i j
  have hpoly := polynomialMatrixHom_generator R n I J d m i j
  have hbase := polynomialTwistingSection_baseChange R A n d (m i j)
  have htarget := polynomialMatrixHom_generator A n I J d
    (fun i j => (mvMapGraded R A n).gradedAddHom d (m i j)) i j
  have hresult := (congrArg
    (fun t : Γ((twistingSheaf R n).tensorPow d, ⊤) =>
      (twistingPowerBaseChangeIso R A n d).hom.app ⊤
        (pullbackLocalSection (map R A n) t)) hpoly).trans
      (hbase.trans htarget.symm)
  exact hresult

end AlgebraicGeometry.ProjSpace
