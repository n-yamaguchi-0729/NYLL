/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.DominantPreimmersionPullback
import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import Nyll.SchemeTheory.Normalization.Normal
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The common degree on normal charts of a Galois cover

Restricting a finite étale Galois cover along a dominant quasi-compact
preimmersion of normal integral schemes preserves its automorphism
group. The degree of the resulting function-field extension is the
order of the original global automorphism group.

The comparison uses the actual restriction functor. Connected covers
remain connected, which makes that functor fully faithful; its
automorphism equivalence and the Galois function-field calculation give
the degree equality. Thus normal affine charts use one common Galois
order as the root exponent in the specialization construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- On every normal dense chart, the function-field degree of the actual
restricted Galois cover equals the order of its original automorphism group. -/
theorem natCard_finiteEtaleAut_eq_finrank_restrictedFunctionField
    {X U : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X]
    [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsPreimmersion j] [IsDominant j] [QuasiCompact j]
    (Y : FiniteEtale X) [IsGalois Y] :
    let P := (FiniteEtale.pullback j).obj Y
    let : IsGalois P :=
      FiniteEtale.pullback_obj_isGalois_of_isPreimmersion_of_isDominant j Y inferInstance
    let : IsIntegral P.left := isIntegral_left_of_isConnected_finiteEtale P
    let : Algebra U.functionField P.left.functionField := finiteEtaleFunctionFieldAlgebra P
    Nat.card (Aut Y) = Module.finrank U.functionField P.left.functionField := by
  intro P hGaloisP hIntegralP aKL
  obtain ⟨hRestriction⟩ := FiniteEtale.pullback_fullyFaithful_of_preserves_connected j
    (fun Z hZ ↦ by
      have : IsConnected Z := hZ
      exact FiniteEtale.pullback_obj_isConnected_of_isPreimmersion_of_isDominant j Z)
  let e : Aut Y ≃* Aut P := hRestriction.autMulEquivOfFullyFaithful Y
  calc
    Nat.card (Aut Y) = Nat.card (Aut P) := Nat.card_congr e.toEquiv
    _ = Module.finrank U.functionField P.left.functionField :=
      natCard_finiteEtaleAut_eq_finrank_functionField_of_isGalois P hGaloisP

end EtaleFundamentalGroups
