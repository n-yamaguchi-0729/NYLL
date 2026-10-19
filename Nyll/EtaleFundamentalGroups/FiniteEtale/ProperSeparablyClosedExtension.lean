/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperAlgebraicallyClosedExtension
import Nyll.EtaleFundamentalGroups.FiniteEtale.UniversalHomeomorphism
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.PurelyInseparablePullback
import Nyll.SchemeTheory.Affine.CoefficientPullbackSquare
import Nyll.SchemeTheory.Affine.FiniteSchemeScalarNaturality
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Nyll.SchemeTheory.Pi1.Affine.Over
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Proper comparison for separably closed coefficient fields

Choose the actual algebraic closures of the two fields and an embedding
between them extending the original coefficient map. The algebraic-closure
projections are universal homeomorphisms, since the starting fields are
separably closed. Combining their finite étale equivalences with Stacks 0A49
gives the comparison for the original separably closed fields. This allows
the residue field of a strict henselization to be used without imposing
perfectness or algebraic closedness on it.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

private theorem pullback_equivalence_of_cartesian_square
    {P X Y S : Scheme.{u}} {q : P ⟶ X} {r : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (h : IsPullback q r f g)
    [(pullback (Limits.pullback.fst f g)).IsEquivalence] :
    (pullback q).IsEquivalence := by
  let e : P ≅ Limits.pullback f g := h.isoPullback
  let E : FiniteEtale (Limits.pullback f g) ≌ FiniteEtale P :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ e.symm
  have hE : (pullback e.hom).IsEquivalence := E.isEquivalence_functor
  let c : pullback q ≅ pullback (Limits.pullback.fst f g) ⋙ pullback e.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      e.hom (Limits.pullback.fst f g) q h.isoPullback_hom_fst.symm
  exact Functor.isEquivalence_of_iso c.symm

private theorem pullback_equivalence_of_pure_field_square
    (a b : Type u) [Field a] [Field b] [Algebra a b] [IsPurelyInseparable a b]
    {P X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of a))
    (q : P ⟶ X) (r : P ⟶ Spec (CommRingCat.of b))
    (h : IsPullback q r f (Spec.map (CommRingCat.ofHom (algebraMap a b)))) :
    (pullback q).IsEquivalence := by
  let i : Spec (CommRingCat.of b) ⟶ Spec (CommRingCat.of a) :=
    Spec.map (CommRingCat.ofHom (algebraMap a b))
  have hIntegral : IsIntegralHom i :=
    IsIntegralHom.SpecMap_iff.mpr (Algebra.IsIntegral.isIntegral (R := a))
  have hInjective : UniversallyInjective i :=
    EtaleFundamentalGroups.purelyInseparable_specMap_universallyInjective a b
  have hSurjective : Surjective i :=
    ⟨fun y => ⟨IsLocalRing.closedPoint b, Subsingleton.elim _ y⟩⟩
  have hIntegralQ : IsIntegralHom q :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom) h.flip hIntegral
  have hInjectiveQ : UniversallyInjective q :=
    UniversallyInjective.isStableUnderBaseChange.of_isPullback h.flip hInjective
  have hSurjectiveQ : Surjective q :=
    MorphismProperty.of_isPullback (P := @Surjective) h.flip hSurjective
  exact pullback_isEquivalence_of_universalHomeomorphism q

/-- Extending separably closed constants preserves the finite étale covers
of a proper scheme. The functor is the original coefficient projection. -/
theorem pullback_isEquivalence_of_isProper_of_isSepClosed_constant_extension
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [IsSepClosed K]
    [Algebra k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    (pullback (Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).IsEquivalence := by
  let L : Type u := AlgebraicClosure K
  let kbar : Type u := AlgebraicClosure k
  let j : kbar →ₐ[k] L := IsAlgClosed.lift
  let akbarL : Algebra kbar L := j.toRingHom.toAlgebra
  let g : K →ₐ[k] L := IsScalarTower.toAlgHom k K L
  let XK : Scheme.{u} := Limits.pullback f (coefficientMap (K := k) K)
  let Xbar : Scheme.{u} := Limits.pullback f (coefficientMap (K := k) kbar)
  let XL : Scheme.{u} := Limits.pullback f (coefficientMap (K := k) L)
  let pK : XK ⟶ X := Limits.pullback.fst f (coefficientMap (K := k) K)
  let pbar : Xbar ⟶ X := Limits.pullback.fst f (coefficientMap (K := k) kbar)
  let pL : XL ⟶ X := Limits.pullback.fst f (coefficientMap (K := k) L)
  let cK : XK ⟶ Spec (CommRingCat.of K) :=
    Limits.pullback.snd f (coefficientMap (K := k) K)
  let cbar : Xbar ⟶ Spec (CommRingCat.of kbar) :=
    Limits.pullback.snd f (coefficientMap (K := k) kbar)
  let cL : XL ⟶ Spec (CommRingCat.of L) :=
    Limits.pullback.snd f (coefficientMap (K := k) L)
  let qK : XL ⟶ XK := coefficientPullbackMap f g
  let qbar : XL ⟶ Xbar := coefficientPullbackMap f j
  have hK : IsPullback qK cL cK (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    coefficientPullbackMap_isPullback f g
  have hbar : IsPullback qbar cL cbar
      (Spec.map (CommRingCat.ofHom (algebraMap kbar L))) :=
    coefficientPullbackMap_isPullback f j
  have hEquivalenceK : (pullback qK).IsEquivalence :=
    pullback_equivalence_of_pure_field_square K L cK qK cL hK
  have hEquivalenceBar : (pullback pbar).IsEquivalence :=
    pullback_equivalence_of_pure_field_square k kbar f pbar cbar
      (IsPullback.of_hasPullback f (coefficientMap (K := k) kbar))
  have hProperBar : IsProper cbar := inferInstance
  have hNativeBar : (pullback (Limits.pullback.fst cbar
      (Spec.map (CommRingCat.ofHom (algebraMap kbar L))))).IsEquivalence :=
    pullback_isEquivalence_of_isProper_of_isAlgClosed_constant_extension kbar L cbar
  have hEquivalenceQbar : (pullback qbar).IsEquivalence :=
    pullback_equivalence_of_cartesian_square hbar
  let cbarComp : pullback pL ≅ pullback pbar ⋙ pullback qbar :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      qbar pbar pL (coefficientPullbackMap_fst f j).symm
  have hEquivalenceL : (pullback pL).IsEquivalence :=
    Functor.isEquivalence_of_iso cbarComp.symm
  let cKComp : pullback pL ≅ pullback pK ⋙ pullback qK :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      qK pK pL (coefficientPullbackMap_fst f g).symm
  have hEquivalenceComp : (pullback pK ⋙ pullback qK).IsEquivalence :=
    Functor.isEquivalence_of_iso cKComp
  exact Functor.isEquivalence_of_comp_right (pullback pK) (pullback qK)

/-- The comparison holds for the actual morphisms of any cartesian field
extension square, including pullbacks formed inside a larger base scheme. -/
theorem pullback_isEquivalence_of_isProper_of_isSepClosed_field_square
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [IsSepClosed K]
    (ι : k →+* K) {P X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (q : P ⟶ X) (r : P ⟶ Spec (CommRingCat.of K))
    (h : IsPullback q r f (Spec.map (CommRingCat.ofHom ι))) :
    (pullback q).IsEquivalence := by
  let : Algebra k K := ι.toAlgebra
  have hNative : (pullback (Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).IsEquivalence :=
    pullback_isEquivalence_of_isProper_of_isSepClosed_constant_extension k K f
  exact pullback_equivalence_of_cartesian_square h

end AlgebraicGeometry.FiniteEtale
