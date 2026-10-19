/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafCohomologyIso
import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafPushforwardCech
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeFinitePushforward
import Nyll.SchemeTheory.Modules.Quasicoherent.DirectImageAlgebraQuasicoherent
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPushforward
import Nyll.SchemeTheory.Modules.Tensor.AffineProjectionFormula
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafSerreVanishing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Serre vanishing on an actual projective closed subscheme

The finite direct image of the given quasicoherent finite-type module
is again quasicoherent and finite type. The actual affine projection
formula identifies its twists with the direct images of the original
twists on the closed subscheme. The original direct-image Čech
comparison then transfers projective-space Serre vanishing to the
actual inverse-image coordinate cover.

One bound works for every positive cohomological degree. Neither a
graded presentation nor vanishing of the closed subscheme is supplied
as additional data.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

private theorem twistingPower_quasicoherent (d : ℕ) :
    SheafOfModules.IsQuasicoherent
      (R := (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).ringCatSheaf)
      ((twistingSheaf R n).tensorPow d) := by
  let P : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  let U : P.Modules := 𝟙_ P.Modules
  let T : P.Modules := (twistingSheaf R n).tensorPow d
  have hU : SheafOfModules.IsQuasicoherent (R := P.ringCatSheaf) U :=
    isQuasicoherent_unit P
  have hT : SheafOfModules.IsQuasicoherent (R := P.ringCatSheaf) (tensor U T) :=
    isQuasicoherent_tensor_twistingSheaf R n U d
  let E : P.Modules ≌ SheafOfModules.{u} P.ringCatSheaf := sheafOfModulesEquivalence P
  let e : E.functor.obj (tensor U T) ≅ E.functor.obj T := E.functor.mapIso (λ_ T)
  exact (SheafOfModules.isQuasicoherent (C := P.Opens) P.ringCatSheaf).prop_of_iso e hT

variable {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
  [IsClosedImmersion j] (M : Y.Modules)
  [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M]

/-- The original projection morphism and pullback tensor-power
comparison identify the actual twists and their finite direct images. -/
def closedImmersionTwistingProjectionIso (d : ℕ) :
    (pushforward j).obj M ⊗ (twistingSheaf R n).tensorPow d ≅
      (pushforward j).obj
        (M ⊗ ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d) := by
  have hT : SheafOfModules.IsQuasicoherent
      (R := (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).ringCatSheaf)
      ((twistingSheaf R n).tensorPow d) := twistingPower_quasicoherent R n d
  exact affineProjectionFormulaIso j M ((twistingSheaf R n).tensorPow d) ≪≫
    (pushforward j).mapIso (whiskerLeftIso M (pullbackTensorPowIso j (twistingSheaf R n) d))

/-- A single twist bound kills every positive Čech cohomology group
of the original finite-type quasicoherent module on the actual closed
subscheme, on the actual inverse-image coordinate cover. -/
theorem exists_closedImmersion_twisting_bound_subsingleton_HSucc [IsNoetherianRing R]
    [SheafOfModules.IsFiniteType (R := Y.ringCatSheaf) M] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ q : ℕ,
      Subsingleton ((toOModulePresheaf (R := R) (j ≫ π R n)
        (M ⊗ ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d)).HSucc
          (stdCoverPullback (A := R) (n := n) j) q) := by
  let P : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  let F : P.Modules := (pushforward j).obj M
  have hFQC : SheafOfModules.IsQuasicoherent (R := P.ringCatSheaf) F :=
    isQuasicoherent_pushforward_of_isAffineHom j M
  have hFFT : SheafOfModules.IsFiniteType (R := P.ringCatSheaf) F :=
    isFiniteType_pushforward_of_isFinite j M
  obtain ⟨c, hc⟩ := exists_twisting_bound_subsingleton_HSucc R n F
  refine ⟨c, ?_⟩
  intro d hd q
  let T : Y.Modules :=
    M ⊗ ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d
  let f : P ⟶ Spec (.of R) := (𝟙 P) ≫ π R n
  let K : P.OrderedAffineCover := stdCoverPullback (A := R) (n := n) (𝟙 P)
  have hVan : Subsingleton ((toOModulePresheaf (R := R) f
      (F ⊗ (twistingSheaf R n).tensorPow d)).HSucc K q) := hc d hd q
  have hPush : Subsingleton
      ((toOModulePresheaf (R := R) f ((pushforward j).obj T)).HSucc K q) :=
    subsingleton_HSucc_of_iso f K (closedImmersionTwistingProjectionIso R n j M d) q
  let e := pushforwardHSuccEquiv f j T K q
  have hPre : Subsingleton
      ((toOModulePresheaf (R := R) (j ≫ f) T).HSucc (K.preimage j) q) :=
    ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩
  have hStruct : j ≫ f = j ≫ π R n :=
    congrArg (fun g : P ⟶ Spec (.of R) => j ≫ g) (Category.id_comp (π R n))
  have hCover : K.preimage j = stdCoverPullback (A := R) (n := n) j := by
    change stdCoverPullback (A := R) (n := n) (j ≫ 𝟙 P) =
      stdCoverPullback (A := R) (n := n) j
    congr 1
  rw [hStruct, hCover] at hPre
  exact hPre

end AlgebraicGeometry.ProjSpace
