/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenKummerGenericRootFiber
import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroKummerCover

/-!
# The same named generic Kummer fiber on an order-zero local cover

The actual generic-w coordinate identifies the original named arithmetic
fiber with points of the literal local root algebra. The unchanged function
and its literal valuation-ring unit determine both equations. Root scaling
and the original generic Galois action are retained in that same coordinate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicCurve JacobianVarieties.Kummer
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel.OpenKummer

/-- The actual named generic fiber is the generic point set of the local
finite étale unit-root cover, using the same function and exponent. -/
theorem exists_arithmeticKummerFiber_ordZeroLocalPoints
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (w : Pic0.openKummerUnits K F S n)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hi : ∀ (y : X) (x : closedPoints M.C), x.val = j y → M.placeOfPoint x ∉ S)
    (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] [Algebra X.functionField Ω]
    [IsSepClosure X.functionField Ω]
    :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let W := M.openKummerCover S n hn w j hj hi
    let ι : F →+* Ω := (algebraMap X.functionField Ω).comp
      ((j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    letI : Algebra F Ω := ι.toAlgebra
    letI := kummerGeometricRootAction M S n w j hj hi hn ξ
    ∃ e : (FiniteEtale.fiber ξ).obj W ≃
        {b : Ω // b ^ (n : ℕ) = ι (w.val : F)},
      (∀ (ζ : rootsOfUnity (n : ℕ) K) x,
        (e (ζ • x)).val = pointScalar (j ≫ M.toBase) ξ (ζ.val : K) * (e x).val) ∧
      (∀ (σ : Ω ≃ₐ[X.functionField] Ω) x,
        (e (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
          (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ) • x)).val =
            σ (e x).val) ∧
      ∀ (v : Place K F) (hv : v.ord (w.val : F) = 0),
        letI : Algebra v.toValuationSubring Ω :=
          (ι.comp (algebraMap v.toValuationSubring F)).toAlgebra
        let T := EtaleCohomology.kummerRootAlgebra (n : ℕ) (v.ordZeroUnit w.val hv)
        ∃ E : (FiniteEtale.fiber ξ).obj W ≃ (T →ₐ[v.toValuationSubring] Ω),
          ∀ x, E x (AdjoinRoot.root _) = (e x).val := by
  intro η ξ W ι
  let : Algebra F Ω := ι.toAlgebra
  let := kummerGeometricRootAction M S n w j hj hi hn ξ
  obtain ⟨e, heμ, heG⟩ := exists_arithmeticKummerFiber_genericRootEquiv
    M S n w j hj hi hn (Ω := Ω)
  refine ⟨e, heμ, heG, ?_⟩
  intro v hv T
  let : Algebra v.toValuationSubring Ω :=
    (ι.comp (algebraMap v.toValuationSubring F)).toAlgebra
  let : IsScalarTower v.toValuationSubring F Ω := IsScalarTower.of_algebraMap_eq' rfl
  let r := Place.ordZeroKummerPointEquivRoots v w.val hv (n : ℕ) Ω
  refine ⟨e.trans r.symm, ?_⟩
  intro x
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

end AlgebraicCurve.CurveModel.OpenKummer
