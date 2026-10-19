/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeFinitePushforward
import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionCounit
import Nyll.SchemeTheory.Modules.Tensor.FiniteFreePullback
import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafGlobalGeneration
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Eventual global generation on a closed projective family

Finite direct image, actual pullback, and the closed-immersion counit
transport the original finite global generating families from projective
space to every closed projective subscheme. The bound is independent of
the twist, and no flatness assumption on the family is imposed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

private def pullback_tensorPow_iso {X Y : Scheme.{u}} (j : Y ⟶ X)
    (L : X.Modules) (d : ℕ) :
    (Scheme.Modules.pullback j).obj (L.tensorPow d) ≅
      ((Scheme.Modules.pullback j).obj L).tensorPow d := by
  induction d with
  | zero => exact pullbackTensorUnitObjIso j
  | succ d ih =>
    exact pullbackTensorObjIso j (L.tensorPow d) L ≪≫ (ih ⊗ᵢ Iso.refl _)

private def pullback_free_iso {X Y : Scheme.{u}} (j : Y ⟶ X)
    (J : Type u) [Finite J] :
    (Scheme.Modules.pullback j).obj (show X.Modules from SheafOfModules.free J) ≅
      (show Y.Modules from SheafOfModules.free J) :=
  (Scheme.Modules.pullback j).mapIso
      (ρ_ (show X.Modules from SheafOfModules.free J)).symm ≪≫
    finiteFreeTensorPullbackIso j J (pullbackTensorUnitObjIso j) ≪≫
      ρ_ (show Y.Modules from SheafOfModules.free J)

/-- Every sufficiently positive pullback twist of a finite-type
quasicoherent module on a closed projective subscheme has a finite
free presentation map which is an epimorphism. -/
theorem exists_closedImmersion_twisting_bound_finiteFree_epi
    (R : Type u) [CommRing R] (n : ℕ) {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j] (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∃ J : Type u, Finite J ∧
      ∃ φ : (show Y.Modules from SheafOfModules.free J) ⟶
          M ⊗ ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d,
        Epi φ := by
  let X := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  let F : X.Modules := (pushforward j).obj M
  have : F.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom j M
  have : F.IsFiniteType := isFiniteType_pushforward_of_isFinite j M
  obtain ⟨c, hc⟩ := exists_twisting_bound_generatingSections R n F
  refine ⟨c, ?_⟩
  intro d hd
  obtain ⟨G, hG⟩ := hc d hd
  have : G.IsFiniteType := hG
  have : Finite G.I := SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := G)
  let E : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf := sheafOfModulesEquivalence X
  let q : (show X.Modules from SheafOfModules.free G.I) ⟶
      F ⊗ (twistingSheaf R n).tensorPow d := E.inverse.map G.π
  have : Epi G.π := G.epi
  have : Epi q := Functor.map_epi E.inverse G.π
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback j) :=
    (pullbackPushforwardAdjunction j).leftAdjoint_preservesColimits
  have : Epi ((Scheme.Modules.pullback j).map q) :=
    Functor.map_epi (Scheme.Modules.pullback j) q
  have : IsIso ((pullbackPushforwardAdjunction j).counit.app M) :=
    isIso_pullbackCounit_of_isClosedImmersion j M
  let e : (Scheme.Modules.pullback j).obj F ≅ M :=
    asIso ((pullbackPushforwardAdjunction j).counit.app M)
  let t : (Scheme.Modules.pullback j).obj (F ⊗ (twistingSheaf R n).tensorPow d) ≅
      M ⊗ ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d :=
    pullbackTensorObjIso j F ((twistingSheaf R n).tensorPow d) ≪≫
      (e ⊗ᵢ pullback_tensorPow_iso j (twistingSheaf R n) d)
  let φ := (pullback_free_iso j G.I).inv ≫ (Scheme.Modules.pullback j).map q ≫ t.hom
  exact ⟨G.I, inferInstance, φ, inferInstance⟩

end AlgebraicGeometry.ProjSpace
