/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponentPointCount
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteIntermediateFieldDegree
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Actual component point counts for the original smooth proper curve

Properness supplies finiteness of the original extension-field point
type. Smoothness supplies the original geometric component separation.
Thus the original curve hypotheses alone give the decomposition of
every positive-degree point count into fixed points of the actual
geometric component restrictions, including the empty curve.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace NeronModelInfra

namespace AlgebraicGeometry.SmoothProperCurve

variable (k K : Type) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K] (X : Scheme)
  [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  (m : ℕ) [NeZero m]

local notation "f" => X ↘ Spec (CommRingCat.of k)
local notation "Y" => (pullback (C := Scheme) f (Spec.algebraMap k K))
local notation "g" => pullback.snd f (Spec.algebraMap k K)
local notation "e" => Scheme.constantFieldTwistIso k K X
  (AlgEquiv.symm (FiniteField.frobeniusAlgEquivOfAlgebraic k K) ^ m)
local notation "B" =>
  {Z : irreducibleComponents Y // Scheme.irreducibleComponentsIsoEquiv e Z = Z}
local notation "P" => fun Z : B =>
  {s : Spec (CommRingCat.of K) ⟶
      Scheme.reducedIrreducibleComponent Y
        (Subtype.val (Subtype.val Z)) (Subtype.property (Subtype.val Z)) //
    s ≫ (Scheme.reducedIrreducibleComponentι Y
      (Subtype.val (Subtype.val Z)) (Subtype.property (Subtype.val Z)) ≫ g) = 𝟙 _ ∧
      s ≫ Scheme.constantBaseChangeFrobeniusFixedComponent k K X m
        (Subtype.val Z) (Subtype.property Z) = s}

/-- The original curve hypotheses supply actual finite fixed-point
types for all actual fixed geometric components. -/
theorem finite_nativeFrobeniusFixedComponentPoints (Z : B) : Finite (P Z) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian Y := smoothProperScheme_isNoetherian g
  exact finite_frobeniusFixedComponentPoints k K X m (smoothSchemeDomainStalks g) Z

/-- The original finite-extension point count is the actual sum of
geometric component fixed-point counts, without a supplied decomposition. -/
theorem nativeFiniteFieldPointCount_eq_sum_fixedComponents :
    Nat.card (SchemeHomOver
      (Spec.algebraMap k (LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k K m)) f) =
      ∑ᶠ Z : B, Nat.card (P Z) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian Y := smoothProperScheme_isNoetherian g
  exact finiteFieldPointCount_eq_sum_fixedComponents k K X m (smoothSchemeDomainStalks g)

end AlgebraicGeometry.SmoothProperCurve
