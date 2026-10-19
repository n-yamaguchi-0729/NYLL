/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperAlgebraicallyClosedExtensionComparison
import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperAlgebraicallyClosedExtensionModel
import Nyll.EtaleFundamentalGroups.GeometricFiber.AlgebraicallyClosedConstantExtension
import Nyll.SchemeTheory.Affine.FiniteSchemeScalarNaturality
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleOverAlgebraicallyClosed
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite étale invariance for proper schemes over algebraically closed fields

Every finite étale cover after extending algebraically closed constants
descends to a finite coefficient algebra. A maximal ideal of this algebra
gives a rational point. The actual rational-fibre cover recovers the original
cover by the henselian valuation comparison. This proves essential
surjectivity; the existing full-faithfulness theorem gives the equivalence.

The forward functor is the native finite étale pullback along the original
constant-extension projection. This proves Stacks Project, Lemma 58.9.3,
https://stacks.math.columbia.edu/tag/0A49, including transcendental extensions.
-/

noncomputable section

open CategoryTheory
open SchemeTheory.Affine.FiniteScheme
open AlgebraicCurves.Geometry.Curves.Proofs
open GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.IsAlgClosed.BaseChangeIrreducible

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K]
  [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- An actual finite étale cover of a proper scheme is constructed from
every cover after an algebraically closed constant extension. The recovery
isomorphism is along the original constant-extension projection. -/
theorem exists_model_of_isProper_of_isAlgClosed_constant_extension
    (W : FiniteEtale (Limits.pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    ∃ M : FiniteEtale X,
      Nonempty ((FiniteEtale.pullback (Limits.pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M ≅ W) := by
  obtain ⟨A, hA, N, ⟨eN⟩⟩ := exists_fg_constant_extension_model k K f W
  have hfiniteType : Algebra.FiniteType k A := (Subalgebra.fg_iff_finiteType A).mp hA
  obtain ⟨m, hm⟩ := (Ideal.exists_maximal A : ∃ m : Ideal A, m.IsMaximal)
  have hm' : m.IsMaximal := hm
  let t : A →ₐ[k] k := pointOfMaximal k m
  obtain ⟨eM⟩ := proper_rational_fiber_recovers_constant_model f t A.val
    Subtype.val_injective N
  exact ⟨(FiniteEtale.pullback (coefficientRationalPointMap f t)).obj N, ⟨eM ≪≫ eN⟩⟩

/-- Pullback along an extension of algebraically closed fields is an
equivalence on finite étale covers of a proper scheme. -/
@[stacks 0A49]
theorem pullback_isEquivalence_of_isProper_of_isAlgClosed_constant_extension :
    (FiniteEtale.pullback (Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).IsEquivalence := by
  let FF : (FiniteEtale.pullback (Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).FullyFaithful :=
    pullbackFullyFaithful_of_isAlgClosed_constant_extension k K f
  refine { faithful := FF.faithful, full := FF.full, essSurj := ⟨?_⟩ }
  intro W
  exact exists_model_of_isProper_of_isAlgClosed_constant_extension k K f W

/-- The actual finite étale comparison equivalence, whose forward functor
is pullback by the original constant-extension projection. -/
def properAlgebraicallyClosedConstantExtensionEquivalence :
    FiniteEtale X ≌ FiniteEtale (Limits.pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  let F : FiniteEtale X ⥤ FiniteEtale (Limits.pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    FiniteEtale.pullback (Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  have hF : F.IsEquivalence :=
    pullback_isEquivalence_of_isProper_of_isAlgClosed_constant_extension k K f
  exact F.asEquivalence

end AlgebraicGeometry.FiniteEtale
