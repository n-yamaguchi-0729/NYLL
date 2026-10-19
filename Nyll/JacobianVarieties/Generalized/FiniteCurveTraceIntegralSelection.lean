/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FiniteCurveTraceCompletedFiber
import Nyll.AlgebraicCurves.RelativeDivisors.Support.HenselianCompletedFiberSelection
import Nyll.ValuedFieldTheory.Valuation.ValuedAdicComplete
import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-! # The integral graph family and its selected completed components

The original finite curve morphism supplies the integral Cartier family by
pulling back its graph divisor to the actual base completion integers. The
proper base curve supplies the required integral base point. The canonical
completed coproduct then supplies every generic component of this family.
Applying the Henselian block theorem identifies the selected components by
the centres of their original places; no integral model or component
partition is an additional hypothesis.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open NeronModelInfra GoodReductionJacobian
open scoped AlgebraicCurve.Place
open scoped AlgebraicCurves.FunctionFields.Proofs.CompletionTraceSum_of_isSeparable

namespace AlgebraicGeometry.GeneralizedJacobian

/-- The full graph divisor, pulled back along any base map, is the actual
pullback of the original finite cover. This includes base maps meeting the
boundary, where the trace-open family itself is not defined. -/
theorem finiteMapFiberDivisor_subscheme_pullback
    {C B S T : Scheme.{u}} (c : C ⟶ S) (b : B ⟶ S)
    (π : C ⟶ B) (hπ : π ≫ b = c)
    [IsSeparated b] [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y : B, π.finrank y = n) (a : T ⟶ B) :
    let D := (finiteMapFiberDivisor c b π hπ n hn).pullbackAlong a rfl
    ∃ d : D.I.subscheme ≅ pullback π a,
      d.hom ≫ pullback.fst π a = D.I.subschemeι ≫ pullback.fst c (a ≫ b) ∧
      d.hom ≫ pullback.snd π a = D.I.subschemeι ≫ pullback.snd c (a ≫ b) := by
  intro D
  let D₀ := finiteMapFiberDivisor c b π hπ n hn
  let γ := finiteMapGraph c b π hπ
  have : IsClosedImmersion γ := finiteMapGraph_isClosedImmersion c b π hπ
  let e₀ : C ≅ γ.ker.subscheme := asIso γ.toImage
  have hfst : D₀.I.subschemeι ≫ pullback.fst c b = e₀.inv := by
    apply (cancel_epi e₀.hom).mp
    change γ.toImage ≫ (γ.imageι ≫ pullback.fst c b) = e₀.hom ≫ e₀.inv
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, finiteMapGraph_fst,
      Iso.hom_inv_id]
  have hsnd : D₀.I.subschemeι ≫ pullback.snd c b = e₀.inv ≫ π := by
    apply (cancel_epi e₀.hom).mp
    change γ.toImage ≫ (γ.imageι ≫ pullback.snd c b) = e₀.hom ≫ (e₀.inv ≫ π)
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, finiteMapGraph_snd,
      Iso.hom_inv_id_assoc]
  let m := comapSubschemeMapOver D₀.I a rfl
  have h : IsPullback m (D.I.subschemeι ≫ pullback.snd c (a ≫ b))
      (D₀.I.subschemeι ≫ pullback.snd c b) a :=
    isPullback_comap_snd_over D₀.I a rfl
  have hp : IsPullback (m ≫ e₀.inv)
      (D.I.subschemeι ≫ pullback.snd c (a ≫ b)) π a := by
    apply h.of_iso (Iso.refl _) e₀.symm (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
    · rfl
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id]
      exact hsnd
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  refine ⟨hp.isoPullback, hp.isoPullback_hom_fst.trans ?_, hp.isoPullback_hom_snd⟩
  rw [← hfst, ← Category.assoc,
    (isPullback_comapSubschemeMapOver D₀.I a rfl).w,
    Category.assoc, mapOnProdOver_fst]
  rfl

private theorem completionIntegers_henselian
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) : HenselianLocalRing v.adicCompletionIntegers := by
  have : IsAdicComplete (IsLocalRing.maximalIdeal v.adicCompletionIntegers)
      v.adicCompletionIntegers :=
    ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete
  refine { is_henselian := ?_ }
  intro P hP a ha hu
  exact HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal v.adicCompletionIntegers)
    P hP a ha (hu.map (Ideal.Quotient.mk _))

/-- The native integral map for a labelled completed fibre component. -/
def completedFiberIntegerMap
    {K E F : Type u} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F] [AlgebraicCurve.HasPrincipalDivisors K F]
    (v : AlgebraicCurve.Place K E) (w : v.fiber F) :
    v.adicCompletionIntegers →+* w.1.adicCompletionIntegers := by
  rcases w with ⟨w, hw⟩
  have hv := AlgebraicCurve.Place.mem_fiber.mp hw
  subst v
  exact AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers E w

/-- The integral map of a completed fibre component is local. -/
theorem completedFiberIntegerMap_isLocalHom
    {K E F : Type u} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F] [AlgebraicCurve.HasPrincipalDivisors K F]
    (v : AlgebraicCurve.Place K E) (w : v.fiber F) :
    IsLocalHom (completedFiberIntegerMap v w) := by
  rcases w with ⟨w, hw⟩
  have hv := AlgebraicCurve.Place.mem_fiber.mp hw
  subst v
  exact AlgebraicCurve.adicCompletionComapIntegers_isLocalHom E w

/-- The native integral component map agrees with its generic completed map. -/
theorem completedFiberIntegerMap_spec
    {K E F : Type u} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [AlgebraicCurve.HasPrincipalDivisors K E] [AlgebraicCurve.HasPrincipalDivisors K F]
    (v : AlgebraicCurve.Place K E) (w : v.fiber F) :
    Spec.map (CommRingCat.ofHom (algebraMap v.adicCompletion w.1.adicCompletion)) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap v.adicCompletionIntegers v.adicCompletion)) =
    Spec.map (CommRingCat.ofHom
      (algebraMap w.1.adicCompletionIntegers w.1.adicCompletion)) ≫
      Spec.map (CommRingCat.ofHom (completedFiberIntegerMap v w)) := by
  rcases w with ⟨w, hw⟩
  have hv := AlgebraicCurve.Place.mem_fiber.mp hw
  subst v
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The actual integral graph divisor over a completed base place, with its
labelled completed components and the regular-block selection by valuation
centres. The base extension, integral family, generic component maps and
Henselian selected block are all constructed from the original finite map. -/
theorem exists_finiteCurveTrace_integral_completed_selection
    {K : Type u} [Field K] {C B : Scheme.{u}}
    [IsIntegral C] [IsNormalIntegral C] [IsIntegral B]
    (c : C ⟶ Spec (.of K)) (b : B ⟶ Spec (.of K)) [IsProper b]
    (π : C ⟶ B) (hπ : π ≫ b = c)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y : B, π.finrank y = n) (U : C.Opens) :
    let _ : Algebra K B.functionField := (AlgebraicCurve.baseToFunctionField b).toAlgebra
    let _ : Algebra K C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ [Algebra B.functionField C.functionField]
      [IsScalarTower K B.functionField C.functionField]
      [FiniteDimensional B.functionField C.functionField]
      [Algebra.IsSeparable B.functionField C.functionField]
      [AlgebraicCurve.HasPrincipalDivisors K B.functionField]
      [AlgebraicCurve.HasPrincipalDivisors K C.functionField],
    (C.fromSpecStalk (genericPoint C) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap B.functionField C.functionField)) ≫
        B.fromSpecStalk (genericPoint B)) →
    ∀ v : AlgebraicCurve.Place K B.functionField,
    ∃ a₀ : Spec (.of v.adicCompletionIntegers) ⟶ B,
      a₀ ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K v.adicCompletionIntegers)) ∧
      Spec.map (CommRingCat.ofHom
        (algebraMap v.adicCompletionIntegers v.adicCompletion)) ≫ a₀ =
        Spec.map (CommRingCat.ofHom (algebraMap B.functionField v.adicCompletion)) ≫
          B.fromSpecStalk (genericPoint B) ∧
      let D := (finiteMapFiberDivisor c b π hπ n hn).pullbackAlong a₀ rfl
      ∃ ξ : (w : v.fiber C.functionField) →
          (Spec (.of w.1.adicCompletion) ⟶ D.I.subscheme),
        (∀ w, ξ w ≫ D.I.subschemeι ≫ pullback.fst c (a₀ ≫ b) =
          Spec.map (CommRingCat.ofHom (algebraMap C.functionField w.1.adicCompletion)) ≫
            C.fromSpecStalk (genericPoint C)) ∧
        (∀ w, ξ w ≫ D.I.subschemeι ≫ pullback.snd c (a₀ ≫ b) =
          Spec.map (CommRingCat.ofHom (algebraMap v.adicCompletion w.1.adicCompletion)) ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap v.adicCompletionIntegers v.adicCompletion))) ∧
        ∃ V : D.I.subscheme.Opens, IsClosed (V : Set D.I.subscheme) ∧
          ∃ (m : ℕ) (D₀ : RelEffCartierDiv c m (a₀ ≫ b)),
            D₀.I = (V.ι ≫ D.I.subschemeι).ker ∧ D₀.SupportedIn U ∧
            ∀ w : v.fiber C.functionField, ∃ z : C,
              (∀ s : C.presheaf.stalk z,
                w.1.adicValuation (algebraMap _ C.functionField s) ≤ 1 ∧
                  (s ∈ IsLocalRing.maximalIdeal _ →
                    w.1.adicValuation (algebraMap _ C.functionField s) < 1)) ∧
              (ξ w (IsLocalRing.closedPoint w.1.adicCompletion) ∈ V ↔ z ∈ U) := by
  intro algB algC algBC tower fin sep divB divC hgeneric v
  let R := v.adicCompletionIntegers
  let aη := Spec.map (CommRingCat.ofHom (algebraMap B.functionField v.adicCompletion)) ≫
    B.fromSpecStalk (genericPoint B)
  let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R v.adicCompletion))
  have hsq : aη ≫ b = j₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
    dsimp only [aη, j₀]
    rw [Category.assoc, AlgebraicCurve.fromSpecStalk_genericPoint_comp_base,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have hVC : ValuativeCriterion b := by
    have hb : IsProper b := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hb
    exact hb.1.1.1
  let sq : ValuativeCommSq b :=
    { R := R
      K := v.adicCompletion
      i₁ := aη
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap K R))
      commSq := ⟨hsq⟩ }
  obtain ⟨hUnique⟩ := hVC sq
  let a₀ := hUnique.default.l
  have ha₀ : j₀ ≫ a₀ = aη := hUnique.default.fac_left
  let D := (finiteMapFiberDivisor c b π hπ n hn).pullbackAlong a₀ rfl
  obtain ⟨d, hdfst, hdsnd⟩ :=
    finiteMapFiberDivisor_subscheme_pullback c b π hπ n hn a₀
  obtain ⟨e, heBase, heComponent⟩ := π.exists_completedGenericFibre_coprod_iso hgeneric v
  let j : pullback π aη ⟶ pullback π a₀ :=
    pullback.lift (pullback.fst π aη) (pullback.snd π aη ≫ j₀) (by
      rw [Category.assoc, ha₀]
      exact pullback.condition)
  let ξ (w : v.fiber C.functionField) : Spec (.of w.1.adicCompletion) ⟶ D.I.subscheme :=
    Sigma.ι (fun w : v.fiber C.functionField => Spec (.of w.1.adicCompletion)) w ≫
      e.hom ≫ j ≫ d.inv
  have hsource (w : v.fiber C.functionField) :
      ξ w ≫ D.I.subschemeι ≫ pullback.fst c (a₀ ≫ b) =
        Spec.map (CommRingCat.ofHom (algebraMap C.functionField w.1.adicCompletion)) ≫
          C.fromSpecStalk (genericPoint C) := by
    rw [← hdfst]
    simp only [ξ, Category.assoc, Iso.inv_hom_id_assoc, j, pullback.lift_fst]
    exact heComponent w
  have hbaseStd (w : v.fiber C.functionField) :
      ξ w ≫ D.I.subschemeι ≫ pullback.snd c (a₀ ≫ b) =
        Spec.map (CommRingCat.ofHom (algebraMap v.adicCompletion w.1.adicCompletion)) ≫ j₀ := by
    rw [← hdsnd]
    simp only [ξ, Category.assoc, Iso.inv_hom_id_assoc, j, pullback.lift_snd]
    have hc : Sigma.ι (fun w : v.fiber C.functionField => Spec (.of w.1.adicCompletion)) w ≫
        e.hom ≫ pullback.snd π aη =
        Spec.map (CommRingCat.ofHom (algebraMap v.adicCompletion w.1.adicCompletion)) := by
      rw [heBase, Sigma.ι_comp_desc]
    simpa only [Category.assoc] using congrArg (fun f => f ≫ j₀) hc
  have hbase (w : v.fiber C.functionField) :
      ξ w ≫ D.I.subschemeι ≫ pullback.snd c (a₀ ≫ b) =
        Spec.map (CommRingCat.ofHom
          (algebraMap w.1.adicCompletionIntegers w.1.adicCompletion)) ≫
          Spec.map (CommRingCat.ofHom (completedFiberIntegerMap v w)) :=
    (hbaseStd w).trans (completedFiberIntegerMap_spec v w)
  have : HenselianLocalRing R := completionIntegers_henselian v
  obtain ⟨V, hV, m, D₀, hD₀, hU, hcomponents⟩ :=
    D.exists_henselian_regularBlock_completed_components (K := K) U
  refine ⟨a₀, hUnique.default.fac_right, ha₀, ξ, hsource, hbaseStd, V, hV, m, D₀, hD₀, hU, ?_⟩
  intro w
  have : IsLocalHom (completedFiberIntegerMap v w) := completedFiberIntegerMap_isLocalHom v w
  exact hcomponents w.1 (completedFiberIntegerMap v w) (ξ w) (hbase w) (hsource w)

end AlgebraicGeometry.GeneralizedJacobian
