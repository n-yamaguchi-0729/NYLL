/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.NormTrace.CompletionTraceSumSeparable
import Nyll.JacobianVarieties.Generalized.FiniteCurveTraceFormalEvaluation

/-! # The actual completed Cartier fibre of a finite curve map

The canonical tensor-product decomposition into completed fields is transported
through the finite normal generic-fibre square and the actual graph divisor.
Both projections of every labelled component are computed. Its degree over
the completed base field is the original ramification times inertia degree.
Thus the completed factors describe the full Cartier fibre itself, not only
its support or an unlabelled finite algebra of the same dimension.

-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct AlgebraicCurve.Place
open scoped AlgebraicCurves.FunctionFields.Proofs.CompletionTraceSum_of_isSeparable

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual generic fibre over a completed base field is the coproduct
of the completed fields above the chosen place. The labels preserve the
original field embeddings and the canonical completion scalar maps. -/
theorem exists_completedGenericFibre_coprod_iso
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsNormalIntegral Y]
    [Algebra K X.functionField] [Algebra K Y.functionField]
    (f : Y ⟶ X) [IsFinite f]
    [Algebra X.functionField Y.functionField]
    [IsScalarTower K X.functionField Y.functionField]
    [FiniteDimensional X.functionField Y.functionField]
    [Algebra.IsSeparable X.functionField Y.functionField]
    [AlgebraicCurve.HasPrincipalDivisors K X.functionField]
    [AlgebraicCurve.HasPrincipalDivisors K Y.functionField]
    (hgeneric : Y.fromSpecStalk (genericPoint Y) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Y.functionField)) ≫
        X.fromSpecStalk (genericPoint X))
    (v : AlgebraicCurve.Place K X.functionField) :
    ∃ e : (∐ fun w : v.fiber Y.functionField => Spec (.of w.1.adicCompletion)) ≅
        pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap X.functionField v.adicCompletion)) ≫ X.fromSpecStalk (genericPoint X)),
      e.hom ≫ pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap X.functionField v.adicCompletion)) ≫
            X.fromSpecStalk (genericPoint X)) =
        Sigma.desc (fun w : v.fiber Y.functionField =>
          Spec.map (CommRingCat.ofHom (algebraMap v.adicCompletion w.1.adicCompletion))) ∧
      ∀ w : v.fiber Y.functionField,
        Sigma.ι (fun w : v.fiber Y.functionField => Spec (.of w.1.adicCompletion)) w ≫
          e.hom ≫ pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap X.functionField v.adicCompletion)) ≫
              X.fromSpecStalk (genericPoint X)) =
          Spec.map (CommRingCat.ofHom (algebraMap Y.functionField w.1.adicCompletion)) ≫
            Y.fromSpecStalk (genericPoint Y) := by
  classical
  let E := X.functionField
  let F := Y.functionField
  let R := v.adicCompletion
  let eAlg := AlgebraicCurve.completionTensorEquiv (L := F) v
  let fields : v.fiber F → CommRingCat := fun w => .of w.1.adicCompletion
  let eSpec : Spec (.of ((w : v.fiber F) → w.1.adicCompletion)) ≅
      Spec (.of (R ⊗[E] F)) :=
    Scheme.Spec.mapIso eAlg.toRingEquiv.toCommRingCatIso.op
  let d : (∐ fun w : v.fiber F => Spec (fields w)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap E F)))
        (Spec.map (CommRingCat.ofHom (algebraMap E R))) :=
    asIso (sigmaSpec fields) ≪≫ eSpec ≪≫
      (pullbackSpecIso E R F).symm ≪≫ pullbackSymmetry _ _
  have heBase : eSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[E] F))) =
      Spec.map (CommRingCat.ofHom (algebraMap R ((w : v.fiber F) → w.1.adicCompletion))) := by
    change Spec.map (CommRingCat.ofHom eAlg.toRingHom) ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext eAlg.commutes)
  have hdBase : d.hom ≫ pullback.snd _ _ =
      Sigma.desc (fun w : v.fiber F =>
        Spec.map (CommRingCat.ofHom (algebraMap R w.1.adicCompletion))) := by
    simp only [d, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst']
    rw [heBase]
    apply Sigma.hom_ext
    intro w
    rw [ι_sigmaSpec_assoc, Sigma.ι_comp_desc, ← Spec.map_comp]
    rfl
  have hdComponent (w : v.fiber F) :
      Sigma.ι (fun w : v.fiber F => Spec (fields w)) w ≫
        d.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap F w.1.adicCompletion)) := by
    simp only [d, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      pullbackSymmetry_hom_comp_fst, pullbackSpecIso_inv_snd, ι_sigmaSpec_assoc]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ w)) ≫
      Spec.map (CommRingCat.ofHom eAlg.toRingHom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact AlgebraicCurve.completionTensorEquiv_one_tmul v a w
  have hNative := isPullback_finiteNormal_generic f hgeneric
  have hSquare := (IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    (Spec.map (CommRingCat.ofHom (algebraMap E R)))).paste_horiz hNative
  refine ⟨d ≪≫ hSquare.isoPullback, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc, hSquare.isoPullback_hom_snd]
    exact hdBase
  · intro w
    simp only [Iso.trans_hom, Category.assoc, hSquare.isoPullback_hom_fst]
    simpa only [Category.assoc] using
      congrArg (fun a => a ≫ Y.fromSpecStalk (genericPoint Y)) (hdComponent w)

end AlgebraicGeometry.Scheme.Hom

open NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.GeneralizedJacobian

/-- The completed-field components are the actual components of the Cartier
fibre used to define the regular trace. The map to the trace locus and the
full Cartier-fibre isomorphism are constructed, and each component has its
actual ramification-times-inertia degree. -/
theorem exists_finiteCurveTrace_completed_fibre
    {K : Type u} [Field K] {C B : Scheme.{u}}
    [IsIntegral C] [IsNormalIntegral C] [IsIntegral B]
    (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (b : B ⟶ Spec (.of K)) [IsSeparated b]
    (π : C ⟶ B) (hπ : π ≫ b = c)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y : B, π.finrank y = n)
    [Algebra K B.functionField] [Algebra K C.functionField]
    [Algebra B.functionField C.functionField]
    [IsScalarTower K B.functionField C.functionField]
    [FiniteDimensional B.functionField C.functionField]
    [Algebra.IsSeparable B.functionField C.functionField]
    [AlgebraicCurve.HasPrincipalDivisors K B.functionField]
    [AlgebraicCurve.HasPrincipalDivisors K C.functionField]
    (hgeneric : C.fromSpecStalk (genericPoint C) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap B.functionField C.functionField)) ≫
        B.fromSpecStalk (genericPoint B))
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (v : AlgebraicCurve.Place K B.functionField) :
    let V := finiteMapTraceLocus c b π hπ n hn U
    let A := finiteMapTraceFamily c b π hπ n hn U
    ∃ a : Spec (.of v.adicCompletion) ⟶ V,
      a ≫ V.ι = Spec.map (CommRingCat.ofHom (algebraMap B.functionField v.adicCompletion)) ≫
        B.fromSpecStalk (genericPoint B) ∧
      let D := A.pullbackAlong a rfl
      ∃ e : (∐ fun w : v.fiber C.functionField => Spec (.of w.1.adicCompletion)) ≅
          D.I.subscheme,
        (∀ w : v.fiber C.functionField,
          Sigma.ι (fun w : v.fiber C.functionField => Spec (.of w.1.adicCompletion)) w ≫
            e.hom ≫ D.I.subschemeι ≫ pullback.fst c (a ≫ (V.ι ≫ b)) =
              Spec.map (CommRingCat.ofHom (algebraMap C.functionField w.1.adicCompletion)) ≫
                C.fromSpecStalk (genericPoint C)) ∧
        (∀ w : v.fiber C.functionField,
          Sigma.ι (fun w : v.fiber C.functionField => Spec (.of w.1.adicCompletion)) w ≫
            e.hom ≫ D.I.subschemeι ≫ pullback.snd c (a ≫ (V.ι ≫ b)) =
              Spec.map (CommRingCat.ofHom (algebraMap v.adicCompletion w.1.adicCompletion))) ∧
        ∀ w : v.fiber C.functionField,
          (((Sigma.ι (fun w : v.fiber C.functionField => Spec (.of w.1.adicCompletion)) w ≫
            e.hom ≫ D.I.subschemeι ≫ pullback.snd c (a ≫ (V.ι ≫ b))).finrank
              (IsLocalRing.closedPoint v.adicCompletion)) : ℤ) =
            (w.1.ramificationIndex B.functionField : ℤ) *
              (w.1.inertiaDeg B.functionField : ℤ) := by
  intro V A
  have hηU : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr
      (by simpa only [Set.univ_inter] using hU)
  have hηV : genericPoint B ∈ V := by
    apply (mem_finiteMapTraceLocus_iff c b π hπ n hn U _).mpr
    intro x hx
    rw [π.eq_genericPoint_of_isIntegralHom x hx]
    exact hηU
  let a : Spec (.of v.adicCompletion) ⟶ V :=
    Spec.map (CommRingCat.ofHom (algebraMap B.functionField v.adicCompletion)) ≫
      V.fromSpecStalkOfMem (genericPoint B) hηV
  have ha : a ≫ V.ι =
      Spec.map (CommRingCat.ofHom (algebraMap B.functionField v.adicCompletion)) ≫
        B.fromSpecStalk (genericPoint B) := by
    simp only [a, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hsplit := π.exists_completedGenericFibre_coprod_iso hgeneric v
  rw [← ha] at hsplit
  obtain ⟨e', heBase, heComponent⟩ := hsplit
  let D := A.pullbackAlong a rfl
  obtain ⟨d, hdfst, hdsnd⟩ := traceFamily_subscheme_pullback c b π hπ n hn U a
  let e := e' ≪≫ d.symm
  have hfst (w : v.fiber C.functionField) :
      Sigma.ι (fun w : v.fiber C.functionField => Spec (.of w.1.adicCompletion)) w ≫
        e.hom ≫ D.I.subschemeι ≫ pullback.fst c (a ≫ (V.ι ≫ b)) =
          Spec.map (CommRingCat.ofHom (algebraMap C.functionField w.1.adicCompletion)) ≫
            C.fromSpecStalk (genericPoint C) := by
    rw [← hdfst]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    exact heComponent w
  have hsnd (w : v.fiber C.functionField) :
      Sigma.ι (fun w : v.fiber C.functionField => Spec (.of w.1.adicCompletion)) w ≫
        e.hom ≫ D.I.subschemeι ≫ pullback.snd c (a ≫ (V.ι ≫ b)) =
          Spec.map (CommRingCat.ofHom (algebraMap v.adicCompletion w.1.adicCompletion)) := by
    rw [← hdsnd]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [heBase, Sigma.ι_comp_desc]
  refine ⟨a, ha, e, hfst, hsnd, ?_⟩
  intro w
  rw [hsnd, Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  change (Module.finrank v.adicCompletion w.1.adicCompletion : ℤ) = _
  rcases w with ⟨w, hw⟩
  have hv : w.restrict B.functionField = v := AlgebraicCurve.Place.mem_fiber.mp hw
  subst v
  exact w.finrank_adicCompletion_restrict

end AlgebraicGeometry.GeneralizedJacobian
