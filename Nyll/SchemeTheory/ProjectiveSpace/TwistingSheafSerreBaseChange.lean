/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafSerreVanishing
import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafCohomologyIso
import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafSchemeIsoCech
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeSchemeRestriction
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Actual Serre vanishing on a coefficient base change

The literal pullback of projective space is identified with projective
space over the new coefficient ring. The actual twisting sheaf agrees
under that isomorphism with the pulled-back twisting sheaf, by the
coordinate-section comparison already constructed.

Transport the original native sheaf, its tensor powers and its actual
Čech complex through this scheme isomorphism. This gives one twist
bound on the literal pullback, without assuming a graded presentation
or an independent comparison of its cohomology. The result applies, in
particular, when the new coefficient ring is a Noetherian Rees algebra.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem coherent_pullback_of_openImmersion
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g] (F : Y.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) F]
    [SheafOfModules.IsFiniteType (R := Y.ringCatSheaf) F] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ((Scheme.Modules.pullback g).obj F) ∧
      SheafOfModules.IsFiniteType (R := X.ringCatSheaf)
        ((Scheme.Modules.pullback g).obj F) := by
  let E : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf := sheafOfModulesEquivalence X
  let e : F.restrict g ≅ (Scheme.Modules.pullback g).obj F :=
    (restrictFunctorIsoPullback g).app F
  have hqc : (F.restrict g).IsQuasicoherent := isQuasicoherent_restrictFunctor g F
  have hft : (F.restrict g).IsFiniteType := isFiniteType_restrictFunctor g F inferInstance
  exact ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (E.functor.mapIso e) hqc,
    SheafOfModules.IsFiniteType.of_iso (R := X.ringCatSheaf) (E.functor.mapIso e) hft⟩

private theorem serre_of_projectiveSpaceIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] (n : ℕ)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsSeparated f]
    (e : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) ≅ X)
    (hf : e.hom ≫ f = π A n) (L : X.Modules)
    (hL : (Scheme.Modules.pullback e.hom).obj L ≅ twistingSheaf A n)
    (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFiniteType (R := X.ringCatSheaf) F] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ q : ℕ,
      Subsingleton ((toOModulePresheaf f (F ⊗ L.tensorPow d)).HSucc
        (stdCoverPullback e.inv) q) := by
  let Z : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
  let P : Z.Modules := (Scheme.Modules.pullback e.hom).obj F
  obtain ⟨hPqc, hPft⟩ := coherent_pullback_of_openImmersion e.hom F
  have : SheafOfModules.IsQuasicoherent (R := Z.ringCatSheaf) P := hPqc
  have : SheafOfModules.IsFiniteType (R := Z.ringCatSheaf) P := hPft
  obtain ⟨c, hc⟩ := exists_twisting_bound_subsingleton_HSucc A n P
  refine ⟨c, ?_⟩
  intro d hd q
  let T : X.Modules := F ⊗ L.tensorPow d
  let epow : (Scheme.Modules.pullback e.hom).obj (L.tensorPow d) ≅
      (twistingSheaf A n).tensorPow d :=
    pullbackTensorPowIso e.hom L d ≪≫ tensorPowMapIso hL d
  let etwist : (Scheme.Modules.pullback e.hom).obj T ≅
      P ⊗ (twistingSheaf A n).tensorPow d :=
    pullbackTensorObjIso e.hom F (L.tensorPow d) ≪≫ whiskerLeftIso P epow
  have : Subsingleton ((toOModulePresheaf ((𝟙 Z) ≫ π A n)
      (P ⊗ (twistingSheaf A n).tensorPow d)).HSucc (stdCoverPullback (𝟙 Z)) q) := hc d hd q
  have hvanish : Subsingleton ((toOModulePresheaf ((𝟙 Z) ≫ π A n)
      ((Scheme.Modules.pullback e.hom).obj T)).HSucc (stdCoverPullback (𝟙 Z)) q) :=
    subsingleton_HSucc_of_iso ((𝟙 Z) ≫ π A n) (stdCoverPullback (𝟙 Z)) etwist.symm q
  have hK : (stdCoverPullback e.inv).preimage e.hom = stdCoverPullback (𝟙 Z) := by
    change stdCoverPullback (e.hom ≫ e.inv) = stdCoverPullback (𝟙 Z)
    congr 1
    exact e.hom_inv_id
  have hstruct : e.hom ≫ f = (𝟙 Z) ≫ π A n := hf.trans (Category.id_comp (π A n)).symm
  have : Subsingleton ((toOModulePresheaf (e.hom ≫ f)
      ((Scheme.Modules.pullback e.hom).obj T)).HSucc
        ((stdCoverPullback e.inv).preimage e.hom) q) := by
    rw [hstruct, hK]
    exact hvanish
  exact subsingleton_HSucc_of_schemeIso_pullback f e T (stdCoverPullback e.inv) q

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)

local notation "Y" => pullback (π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A)))
local notation "p" => pullback.fst (π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A)))
local notation "f" => pullback.snd (π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- Serre vanishing on the literal projective-space coefficient pullback,
twisted by the original first-projection pullback of `𝒪(1)`. -/
theorem exists_baseChange_twisting_bound_subsingleton_HSucc [IsNoetherianRing A]
    (F : (Y).Modules)
    [SheafOfModules.IsQuasicoherent (R := (Y).ringCatSheaf) F]
    [SheafOfModules.IsFiniteType (R := (Y).ringCatSheaf) F] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ q : ℕ,
      Subsingleton ((toOModulePresheaf f
        (F ⊗ ((Scheme.Modules.pullback p).obj (twistingSheaf R n)).tensorPow d)).HSucc
          (stdCoverPullback (isPullback_map R A n).isoPullback.inv) q) :=
  serre_of_projectiveSpaceIso A n f (isPullback_map R A n).isoPullback
    (isPullback_map R A n).isoPullback_hom_snd
    ((Scheme.Modules.pullback p).obj (twistingSheaf R n))
    (twistingSheafPullbackComparison R A n) F

end AlgebraicGeometry.ProjSpace
