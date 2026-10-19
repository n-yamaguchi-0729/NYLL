/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.Representability.OpenCurveUniversalDivisor
import Nyll.JacobianVarieties.Albanese.SameDivisorDescent
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected

/-!
# Regular sums on the actual divisor space of an open curve

The proper curve supplies its open divisor parameter scheme. A morphism from
the open curve to any separated commutative group then has an actual regular
sum morphism on this scheme. The finite flat tuple cover and its full
scheme-valued divisor relation are retained for use in family descent.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Albanese

/-- Actual regular finite sums on the represented open-curve divisor functor.
Neither a chosen divisor representer nor its existence is an input. -/
theorem exists_openCurveDivisorSum
    {K : Type u} [Field K] {C B : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U : C.Opens) (ε : Spec (CommRingCat.of K) ⟶ (U : Scheme.{u}))
    (hε : ε ≫ (U.ι ≫ c) = 𝟙 _)
    {b : B ⟶ Spec (CommRingCat.of K)} [IsSeparated b]
    (G : RelativeGroupLaw K b) (hc : G.IsCommutative)
    (q : SchemeHomOver (U.ι ≫ c) b) (n : ℕ) :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of K))
      (E : RelEffCartierDiv (U.ι ≫ c) n y), E.IsUniversal ∧
      ∃ (σ : finFibrePow (U.ι ≫ c) n ⟶ Y)
        (hσ : σ ≫ y = finFibrePow.toBase (U.ι ≫ c) n)
        (sum : SchemeHomOver y b),
        E.I.comap (mapOnProdOver (U.ι ≫ c) σ hσ) =
          fibrePowOver.tautIdeal (U.ι ≫ c) n ∧
        IsFinite σ ∧ Flat σ ∧ Surjective σ ∧
        σ ≫ sum.1 = (G.finiteSumMap (U.ι ≫ c) q n).1 ∧
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (v w : T ⟶ finFibrePow (U.ι ≫ c) n)
          (hv : v ≫ finFibrePow.toBase (U.ι ≫ c) n = t)
          (hw : w ≫ finFibrePow.toBase (U.ι ≫ c) n = t),
          v ≫ σ = w ≫ σ ↔
            SameDivisor (U.ι ≫ c)
              (fun i => v ≫ finFibrePow.proj (U.ι ≫ c) n i)
              (fun i => by rw [Category.assoc, finFibrePow.proj_comp, hv])
              (fun i => w ≫ finFibrePow.proj (U.ι ≫ c) n i)
              (fun i => by rw [Category.assoc, finFibrePow.proj_comp, hw]) := by
  have : SmoothOfRelativeDimension 1 (U.ι ≫ c) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ c))
  have : Surjective (U.ι ≫ c) := ⟨fun x => ⟨ε x, Subsingleton.elim _ _⟩⟩
  have : GeometricallyIrreducible (U.ι ≫ c) := inferInstance
  have : GeometricallyConnected (U.ι ≫ c) :=
    GeometricallyIrreducible.geometricallyConnected (U.ι ≫ c)
  obtain ⟨Y, y, E, hE⟩ := RelEffCartierDiv.exists_isUniversal_on_open c U n
  exact ⟨Y, y, E, hE,
    exists_finiteSumMap_desc_of_commutative (U.ι ≫ c) ε hε G hc q hE⟩

end JacobianVarieties.Albanese
