/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FiniteCurveTraceBoundaryCompletedFiber
import Nyll.JacobianVarieties.Generalized.HenselianRegularBlockTrace
import Nyll.AlgebraicCurves.Places.Degree.LaurentCompletionIntegersDegEqOne

/-! # Actual power-series graph blocks of the original finite curve map

The proper base curve supplies its integral completion point. The native
Laurent identification transports that point to power series. The actual
graph divisor is then split into its Henselian regular and boundary blocks.
The boundary block is identified with precisely the original completed
places outside the source open, retaining both projection formulas. No
integral graph, selected partition, or matching of completed factors is
input data.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open NeronModelInfra GoodReductionJacobian
open scoped WithZero AlgebraicCurve.Place
open scoped AlgebraicCurves.FunctionFields.Proofs.CompletionTraceSum_of_isSeparable

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem powerSeriesHenselian {K : Type u} [Field K] :
    HenselianLocalRing (PowerSeries K) where
  is_henselian P hP a ha hu := by
    rw [PowerSeries.maximalIdeal_eq_span_X] at ha ⊢
    exact HenselianRing.is_henselian (I := Ideal.span {(PowerSeries.X : PowerSeries K)})
      P hP a ha (hu.map (Ideal.Quotient.mk _))

/-- The original finite curve graph constructs both full Cartier blocks
over power series and the actual labelled boundary completed fibre. The
only normalization input is the native valuation-preserving equivalence
of the base completion with the Laurent field. -/
theorem exists_finiteCurveTrace_powerSeries_completed_blocks
    {K : Type u} [Field K] [IsAlgClosed K]
    {C B : Scheme.{u}} [IsIntegral C] [IsNormalIntegral C] [IsIntegral B]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (b : B ⟶ Spec (.of K)) [IsProper b]
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
    ∀ (v : AlgebraicCurve.Place K B.functionField)
      (E : v.adicCompletion ≃ₐ[K] LaurentSeries K)
      (hE : ∀ x : v.adicCompletion,
        (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x),
    let O := v.powerSeriesEquivCompletionIntegers E hE
    let g := Spec.map (CommRingCat.ofHom
      ((algebraMap v.adicCompletionIntegers v.adicCompletion).comp O.toRingHom))
    ∃ a : Spec (.of (PowerSeries K)) ⟶ B,
      a ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K))) ∧
      g ≫ a = Spec.map (CommRingCat.ofHom
        (algebraMap B.functionField v.adicCompletion)) ≫ B.fromSpecStalk (genericPoint B) ∧
      let D := (finiteMapFiberDivisor c b π hπ n hn).pullbackAlong a rfl
      ∃ (V : D.I.subscheme.Opens) (hV : IsClosed (V : Set D.I.subscheme)),
        let W : D.I.subscheme.Opens := ⟨(V : Set D.I.subscheme)ᶜ, hV.isOpen_compl⟩
        (pullback.fst (D.I.subschemeι ≫ pullback.snd c (a ≫ b))
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (PowerSeries K)))) ⁻¹'
              (V : Set D.I.subscheme) =
          (pullback.fst (D.I.subschemeι ≫ pullback.snd c (a ≫ b))
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (PowerSeries K)))) ≫
              D.I.subschemeι ≫ pullback.fst c (a ≫ b)) ⁻¹' (U : Set C)) ∧
        ∃ (m k : ℕ) (D₀ : RelEffCartierDiv c m (a ≫ b))
          (D₁ : RelEffCartierDiv c k (a ≫ b)),
          D₀.I = (V.ι ≫ D.I.subschemeι).ker ∧
          D₁.I = (W.ι ≫ D.I.subschemeι).ker ∧
          D₀.SupportedIn U ∧ D.I = D₀.I * D₁.I ∧ n = m + k ∧
          let I := {w : v.fiber C.functionField //
            ((AlgebraicCurve.CurveModel.ofSmoothProperCurve c).placeEquiv.symm w.1).1 ∉ U}
          let Dg := D₁.pullbackAlong g (Category.assoc g a b).symm
          ∃ d : (∐ fun w : I => Spec (.of w.1.1.adicCompletion)) ≅ Dg.I.subscheme,
            (∀ w : I, Sigma.ι (fun w : I => Spec (.of w.1.1.adicCompletion)) w ≫
                d.hom ≫ Dg.I.subschemeι ≫ pullback.fst c ((g ≫ a) ≫ b) =
              Spec.map (CommRingCat.ofHom (algebraMap C.functionField w.1.1.adicCompletion)) ≫
                C.fromSpecStalk (genericPoint C)) ∧
            ∀ w : I, Sigma.ι (fun w : I => Spec (.of w.1.1.adicCompletion)) w ≫
                d.hom ≫ Dg.I.subschemeι ≫ pullback.snd c ((g ≫ a) ≫ b) =
              Spec.map (CommRingCat.ofHom
                (algebraMap v.adicCompletion w.1.1.adicCompletion)) := by
  intro algB algC algBC tower fin sep divB divC hgeneric v E hE O g
  obtain ⟨a₀, ha₀base, ha₀generic, _rest⟩ :=
    exists_finiteCurveTrace_integral_completed_selection c b π hπ n hn U hgeneric v
  let f := Spec.map (CommRingCat.ofHom O.symm.toRingHom)
  let a := f ≫ a₀
  have habase : a ≫ b =
      Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K))) := by
    rw [show a = f ≫ a₀ from rfl, Category.assoc, ha₀base, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext O.symm.toAlgHom.comp_algebraMap)
  have hgf : g ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap v.adicCompletionIntegers v.adicCompletion)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact congrArg (algebraMap v.adicCompletionIntegers v.adicCompletion)
      (O.apply_symm_apply x)
  have hageneric : g ≫ a = Spec.map (CommRingCat.ofHom
      (algebraMap B.functionField v.adicCompletion)) ≫ B.fromSpecStalk (genericPoint B) := by
    rw [show a = f ≫ a₀ from rfl, ← Category.assoc, hgf]
    exact ha₀generic
  let aInt (w : v.fiber C.functionField) :
      PowerSeries K →+* w.1.adicCompletionIntegers :=
    (completedFiberIntegerMap v w).comp O.toRingHom
  have localInt (w : v.fiber C.functionField) : IsLocalHom (aInt w) := by
    have : IsLocalHom (completedFiberIntegerMap v w) :=
      completedFiberIntegerMap_isLocalHom v w
    have : IsLocalHom O.toRingHom := isLocalHom_toRingHom O.toRingEquiv
    change IsLocalHom ((completedFiberIntegerMap v w).comp O.toRingHom)
    infer_instance
  have hgdef : g =
      Spec.map (CommRingCat.ofHom
        (algebraMap v.adicCompletionIntegers v.adicCompletion)) ≫
          Spec.map (CommRingCat.ofHom O.toRingHom) := by
    change Spec.map (CommRingCat.ofHom O.toRingHom ≫ CommRingCat.ofHom
      (algebraMap v.adicCompletionIntegers v.adicCompletion)) = _
    exact Spec.map_comp _ _
  have hInt (w : v.fiber C.functionField) :
      Spec.map (CommRingCat.ofHom
          (algebraMap v.adicCompletion w.1.adicCompletion)) ≫ g =
        Spec.map (CommRingCat.ofHom
          (algebraMap w.1.adicCompletionIntegers w.1.adicCompletion)) ≫
            Spec.map (CommRingCat.ofHom (aInt w)) := by
    calc
      _ = (Spec.map (CommRingCat.ofHom
          (algebraMap v.adicCompletion w.1.adicCompletion)) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap v.adicCompletionIntegers v.adicCompletion))) ≫
            Spec.map (CommRingCat.ofHom O.toRingHom) := by
              rw [hgdef, Category.assoc]
      _ = (Spec.map (CommRingCat.ofHom
          (algebraMap w.1.adicCompletionIntegers w.1.adicCompletion)) ≫
          Spec.map (CommRingCat.ofHom (completedFiberIntegerMap v w))) ≫
            Spec.map (CommRingCat.ofHom O.toRingHom) :=
        congrArg (fun h => h ≫ Spec.map (CommRingCat.ofHom O.toRingHom))
          (completedFiberIntegerMap_spec v w)
      _ = _ := by
        rw [Category.assoc, ← Spec.map_comp]
        rfl
  let D := (finiteMapFiberDivisor c b π hπ n hn).pullbackAlong a rfl
  have : HenselianLocalRing (PowerSeries K) := powerSeriesHenselian
  obtain ⟨V, hV, hsel, m, k, D₀, D₁, hD₀, hD₁, hD₀U, hmul, hdegree⟩ :=
    D.exists_henselian_regularBlock_decomposition U
  obtain ⟨d, hdsource, hdbase⟩ :=
    exists_finiteCurveTrace_boundary_completed_fibre c b π hπ n hn U
      hgeneric v a g hageneric aInt hInt V hV hsel k D₁ hD₁
  exact ⟨a, habase, hageneric, V, hV, hsel, m, k, D₀, D₁,
    hD₀, hD₁, hD₀U, hmul, hdegree, d, hdsource, hdbase⟩

end AlgebraicGeometry.GeneralizedJacobian
