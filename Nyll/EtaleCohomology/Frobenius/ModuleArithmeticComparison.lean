/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.ModulePullbackSiteComparison
import Nyll.EtaleCohomology.Frobenius.ArithmeticComparison
import Nyll.EtaleCohomology.Frobenius.Cohomology

/-!
# Coefficient-linear geometric and arithmetic Frobenius

The equality of the actual étale site functors identifies the existing
coefficient-linear Frobenius endomorphism with the pullback induced by the
inverse q-power automorphism of the extended constants.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X : Scheme.{u}} {f g : X ⟶ X} (e : etaleBaseChange f ≅ etaleBaseChange g)
  (R : Type u) [CommRing R]

include e in
/-- An actual site isomorphism identifies the canonical constant-coefficient
pullback as a linear map over the original coefficient ring. -/
theorem etaleConstantCohomologyPullbackMap_siteIso (M : ModuleCat.{u} R) (n : ℕ) :
    etaleConstantCohomologyPullbackMap f R M n =
      etaleConstantCohomologyPullbackMap g R M n := by
  apply LinearMap.ext
  intro x
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M
  let τ : (etalePullback f R).obj F ⟶ (etalePullback g R).obj F :=
    (etalePullbackSiteIso e R).hom.app F
  let ef : (etalePullback f R).obj F ⟶ F := (etalePullbackConstantIso f R).hom.app M
  let eg : (etalePullback g R).obj F ⟶ F := (etalePullbackConstantIso g R).hom.app M
  let y : Sheaf.H.{u} (U.obj ((etalePullback f R).obj F)) n :=
    etaleCohomologyPullbackMap f R F n x
  have hA : τ ≫ eg = ef := etalePullbackSiteIso_constant e R M
  have h : Sheaf.H.map (U.map τ) n y = etaleCohomologyPullbackMap g R F n x :=
    etaleCohomologyPullbackMap_siteIso e R F n x
  change Sheaf.H.map (U.map ef) n y =
    Sheaf.H.map (U.map eg) n (etaleCohomologyPullbackMap g R F n x)
  calc
    _ = Sheaf.H.map (U.map (τ ≫ eg)) n y :=
      congrArg (fun φ : (etalePullback f R).obj F ⟶ F =>
        Sheaf.H.map (U.map φ) n y) hA.symm
    _ = Sheaf.H.map (U.map eg) n (etaleCohomologyPullbackMap g R F n x) := by
      rw [Functor.map_comp, Sheaf.H.map_comp_apply, h]

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (S : Scheme.{u}) [S.Over (Spec (.of k))]

local notation "SΩ" => pullback (S ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

/-- The actual linear pullback induced by inverse arithmetic Frobenius on
extended constants. This uses the existing scheme automorphism and cohomology. -/
def finiteFieldInverseArithmeticCohomology (M : ModuleCat.{u} R) (n : ℕ) :
    Module.End R
      (etaleCohomology SΩ R
        ((constantSheaf (SΩ).smallEtaleTopology (ModuleCat.{u} R)).obj M) n) :=
  etaleConstantCohomologyPullbackMap (Scheme.constantFieldTwist k Ω S
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm) R M n

/-- The existing coefficient-linear geometric Frobenius is exactly the
actual pullback of inverse arithmetic Frobenius on the constants. -/
theorem finiteFieldFrobeniusCohomology_eq_inverseArithmetic
    (M : ModuleCat.{u} R) (n : ℕ) :
    finiteFieldFrobeniusCohomology R k Ω S M n =
      finiteFieldInverseArithmeticCohomology R k Ω S M n :=
  etaleConstantCohomologyPullbackMap_siteIso
    (finiteFieldGeometricArithmeticSiteIso k Ω S) R M n

end EtaleCohomology
