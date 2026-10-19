/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.Support.SourceOpenRestriction
import Nyll.JacobianVarieties.Albanese.OpenCurveDivisorSums

/-!
# Evaluating regular divisor sums on supported families

The actual regular sum on the open divisor parameter scheme evaluates any
supported family on the original proper curve. This gives an actual morphism
over the base, compatible with arbitrary changes of test scheme. The target
may be any separated commutative algebraic group.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Albanese

variable {K : Type u} [Field K] {C B Y : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (U : C.Opens) {n : ℕ}
  {y : Y ⟶ Spec (CommRingCat.of K)}
  {E : RelEffCartierDiv (U.ι ≫ c) n y} (hE : E.IsUniversal)
  {b : B ⟶ Spec (CommRingCat.of K)} (sum : SchemeHomOver y b)

/-- Evaluate the regular divisor-sum morphism on an actual supported family. -/
def supportedDivisorSum {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (A : RelEffCartierDiv c n t) (hA : A.SupportedIn U) : SchemeHomOver t b :=
  ⟨hE.lift (A.restrictToOpen c U hA) ≫ sum.1,
    by rw [Category.assoc, sum.2, hE.lift_comp]⟩

private theorem divisor_lift_naturality {X S Y T T' : Scheme.{u}}
    {c : X ⟶ S} {n : ℕ} {y : Y ⟶ S} {E : RelEffCartierDiv c n y}
    (hE : E.IsUniversal) {t : T ⟶ S} (A : RelEffCartierDiv c n t)
    {t' : T' ⟶ S} (f : T' ⟶ T) (hf : f ≫ t = t') :
    hE.lift (A.pullbackAlong f hf) = f ≫ hE.lift A := by
  symm
  apply hE.eq_lift (by rw [Category.assoc, hE.lift_comp, hf])
  have he : E.pullbackAlong (f ≫ hE.lift A)
      (by rw [Category.assoc, hE.lift_comp, hf]) = A.pullbackAlong f hf := by
    rw [← E.pullbackAlong_comp (hE.lift A) (hE.lift_comp A) f hf,
      hE.pullbackAlong_lift]
  exact congrArg RelEffCartierDiv.I he

/-- Pulling back the family pulls back the actual regular sum, including over
nonreduced test schemes. -/
theorem supportedDivisorSum_naturality
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {t' : T' ⟶ Spec (CommRingCat.of K)}
    (A : RelEffCartierDiv c n t) (hA : A.SupportedIn U)
    (f : T' ⟶ T) (hf : f ≫ t = t') :
    GoodReductionJacobian.schemeHomOverComp f hf (supportedDivisorSum c U hE sum A hA) =
      supportedDivisorSum c U hE sum (A.pullbackAlong f hf) (hA.pullbackAlong f hf) := by
  apply Subtype.ext
  change f ≫ (hE.lift (A.restrictToOpen c U hA) ≫ sum.1) =
    hE.lift ((A.pullbackAlong f hf).restrictToOpen c U (hA.pullbackAlong f hf)) ≫ sum.1
  rw [RelEffCartierDiv.restrictToOpen_pullbackAlong, divisor_lift_naturality,
    Category.assoc]

end JacobianVarieties.Albanese
