/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.IEqProdKerGraphAlgClosed
import Nyll.AlgebraicCurves.RelativeDivisors.Support.RelEffCartierDivSupportedIn
import Nyll.JacobianVarieties.Albanese.OpenCurveSumChoice
import Nyll.JacobianVarieties.Albanese.DivisorSumEvaluation

/-! # Regular traces along finite flat curve morphisms

The graph of a finite flat map supplies its actual relative divisor of
fibres. Evaluating the regular divisor sum on this family constructs the
group-valued trace on the open locus where the whole fibre lies in the
domain of the original map. The evaluation formulas use equality of
Cartier ideals, including repeated points and nonreduced test schemes.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian JacobianVarieties.Albanese
open AlgebraicCurves.RelativeDivisors.Proofs

namespace AlgebraicGeometry.GeneralizedJacobian

section Fibres

variable {C B S : Scheme.{u}} (c : C ⟶ S) (b : B ⟶ S)
  (π : C ⟶ B) (hπ : π ≫ b = c)

/-- The graph of the finite map, with the source curve as its first coordinate. -/
def finiteMapGraph : C ⟶ pullback c b :=
  pullback.lift (𝟙 C) π ((Category.id_comp c).trans hπ.symm)

@[reassoc (attr := simp)]
theorem finiteMapGraph_fst : finiteMapGraph c b π hπ ≫ pullback.fst c b = 𝟙 C :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem finiteMapGraph_snd : finiteMapGraph c b π hπ ≫ pullback.snd c b = π :=
  pullback.lift_snd _ _ _

/-- Separatedness of the target makes the actual graph a closed immersion. -/
theorem finiteMapGraph_isClosedImmersion [IsSeparated b] :
    IsClosedImmersion (finiteMapGraph c b π hπ) := by
  have : IsClosedImmersion (finiteMapGraph c b π hπ ≫ pullback.fst c b) := by
    rw [finiteMapGraph_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (finiteMapGraph c b π hπ) (pullback.fst c b)

variable [IsSeparated b] [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  (n : ℕ) (hn : ∀ y : B, π.finrank y = n)

/-- The graph ideal gives the finite flat family of fibres, with its actual rank. -/
def finiteMapFiberDivisor : RelEffCartierDiv c n b := by
  let γ := finiteMapGraph c b π hπ
  have : IsClosedImmersion γ := finiteMapGraph_isClosedImmersion c b π hπ
  let e : C ≅ γ.ker.subscheme := asIso γ.toImage
  have hproj : γ.ker.subschemeι ≫ pullback.snd c b = e.inv ≫ π := by
    apply (cancel_epi e.hom).1
    change γ.toImage ≫ (γ.imageι ≫ pullback.snd c b) = e.hom ≫ (e.inv ≫ π)
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, finiteMapGraph_snd,
      e.hom_inv_id_assoc]
  refine ⟨γ.ker, ?_, ?_, ?_, ?_⟩
  · rw [hproj]
    infer_instance
  · rw [hproj]
    infer_instance
  · rw [hproj]
    infer_instance
  · intro y
    rw [hproj, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hn y

/-- The fibre family retains the full graph ideal, rather than only its support. -/
theorem finiteMapFiberDivisor_ideal :
    (finiteMapFiberDivisor c b π hπ n hn).I = (finiteMapGraph c b π hπ).ker := rfl

/-- The open subset of the target whose entire fibre lies in the chosen source open. -/
def finiteMapTraceLocus (U : C.Opens) : B.Opens :=
  (finiteMapFiberDivisor c b π hπ n hn).supportedInLocus U

/-- The actual fibre family restricted to the domain of the trace. -/
def finiteMapTraceFamily (U : C.Opens) :
    RelEffCartierDiv c n ((finiteMapTraceLocus c b π hπ n hn U).ι ≫ b) :=
  (finiteMapFiberDivisor c b π hπ n hn).pullbackAlong
    (finiteMapTraceLocus c b π hπ n hn U).ι rfl

/-- Every fibre in the trace domain is supported in the source domain. -/
theorem finiteMapTraceFamily_supported (U : C.Opens) :
    (finiteMapTraceFamily c b π hπ n hn U).SupportedIn U := by
  apply ((finiteMapFiberDivisor c b π hπ n hn).supportedIn_pullbackAlong_iff U
    (finiteMapTraceLocus c b π hπ n hn U).ι rfl).2
  rintro _ ⟨x, rfl⟩
  exact x.2

end Fibres

section Trace

variable {K : Type u} [Field K] {C B : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (b : B ⟶ Spec (CommRingCat.of K)) [IsSeparated b]
  (π : C ⟶ B) (hπ : π ≫ b = c)
  [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  (n : ℕ) (hn : ∀ y : B, π.finrank y = n) (U : C.Opens)
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ c))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (q : SchemeHomOver (U.ι ≫ c) G.X.hom)

/-- The regular group-valued trace, obtained by evaluating the actual fibre divisor. -/
def finiteCurveTrace :
    SchemeHomOver ((finiteMapTraceLocus c b π hπ n hn U).ι ≫ b) G.X.hom :=
  let A := finiteMapTraceFamily c b π hπ n hn U
  let hA := finiteMapTraceFamily_supported c b π hπ n hn U
  let s := chooseOpenCurveSum c U (commGroupRelativeLaw G) q n
    (commGroupRelativeLaw_isCommutative G) ε
  supportedDivisorSum c U s.universal s.sum A hA

/-- A full Cartier presentation of a fibre over any test scheme evaluates
the trace to the sum of the images of its sections, retaining multiplicities. -/
theorem finiteCurveTrace_evaluate_tuple :
    let V := finiteMapTraceLocus c b π hπ n hn U
    let A := finiteMapTraceFamily c b π hπ n hn U
    let hA := finiteMapTraceFamily_supported c b π hπ n hn U
    ∀ {T : Scheme.{u}} (a : T ⟶ V)
      (xs : Fin n → SchemeHomOver (a ≫ (V.ι ≫ b)) (U.ι ≫ c)),
      ((A.pullbackAlong a rfl).restrictToOpen c U (hA.pullbackAlong a rfl)).I =
        prodKerGraph (U.ι ≫ c) (fun i => (xs i).1) (fun i => (xs i).2) →
      GoodReductionJacobian.schemeHomOverComp a rfl
          (finiteCurveTrace c b π hπ n hn U ε G q) =
        (commGroupRelativeLaw G).sumList (a ≫ (V.ι ≫ b))
          (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q) := by
  intro V A hA T a xs hxs
  let s := chooseOpenCurveSum c U (commGroupRelativeLaw G) q n
    (commGroupRelativeLaw_isCommutative G) ε
  change GoodReductionJacobian.schemeHomOverComp a rfl
    (supportedDivisorSum c U s.universal s.sum A hA) = _
  rw [supportedDivisorSum_naturality]
  exact supportedDivisorSum_evaluate_tuple c U s.universal s.tupleMap
    s.tupleMap_toBase s.tuple_ideal (commGroupRelativeLaw G) q s.sum s.tuple_sum
    (a ≫ (V.ι ≫ b)) xs (A.pullbackAlong a rfl) (hA.pullbackAlong a rfl) hxs

/-- Every geometric fibre has a full Cartier tuple presentation, and the
regular trace is its sum in the original commutative group scheme. -/
theorem finiteCurveTrace_geometric_fibre :
    let V := finiteMapTraceLocus c b π hπ n hn U
    let A := finiteMapTraceFamily c b π hπ n hn U
    let hA := finiteMapTraceFamily_supported c b π hπ n hn U
    ∀ {L : Type u} [Field L] [IsAlgClosed L] (a : Spec (CommRingCat.of L) ⟶ V),
      ∃ xs : Fin n → SchemeHomOver (a ≫ (V.ι ≫ b)) (U.ι ≫ c),
        ((A.pullbackAlong a rfl).restrictToOpen c U (hA.pullbackAlong a rfl)).I =
          prodKerGraph (U.ι ≫ c) (fun i => (xs i).1) (fun i => (xs i).2) ∧
        GoodReductionJacobian.schemeHomOverComp a rfl
            (finiteCurveTrace c b π hπ n hn U ε G q) =
          (commGroupRelativeLaw G).sumList (a ≫ (V.ι ≫ b))
            (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q) := by
  intro V A hA L fieldL algClosedL a
  have : SmoothOfRelativeDimension 1 (U.ι ≫ c) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ c))
  obtain ⟨x, hx, hxs⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed
    ((A.pullbackAlong a rfl).restrictToOpen c U (hA.pullbackAlong a rfl))
  let xs : Fin n → SchemeHomOver (a ≫ (V.ι ≫ b)) (U.ι ≫ c) := fun i => ⟨x i, hx i⟩
  exact ⟨xs, hxs, finiteCurveTrace_evaluate_tuple c b π hπ n hn U ε G q a xs hxs⟩

/-- Over an algebraically closed ground field the rational point needed by
the divisor-sum construction is obtained from the nonempty source open. -/
theorem exists_finiteCurveTrace [IsAlgClosed K] (hU : (U : Set C).Nonempty) :
    let V := finiteMapTraceLocus c b π hπ n hn U
    let A := finiteMapTraceFamily c b π hπ n hn U
    let hA := finiteMapTraceFamily_supported c b π hπ n hn U
    ∃ τ : SchemeHomOver (V.ι ≫ b) G.X.hom,
      ∀ {L : Type u} [Field L] [IsAlgClosed L] (a : Spec (CommRingCat.of L) ⟶ V),
        ∃ xs : Fin n → SchemeHomOver (a ≫ (V.ι ≫ b)) (U.ι ≫ c),
          ((A.pullbackAlong a rfl).restrictToOpen c U (hA.pullbackAlong a rfl)).I =
            prodKerGraph (U.ι ≫ c) (fun i => (xs i).1) (fun i => (xs i).2) ∧
          GoodReductionJacobian.schemeHomOverComp a rfl τ =
            (commGroupRelativeLaw G).sumList (a ≫ (V.ι ≫ b))
              (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q) := by
  intro V A hA
  have : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  have : JacobsonSpace U := LocallyOfFiniteType.jacobsonSpace (U.ι ≫ c)
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set U).Nonempty) isClosed_univ.isLocallyClosed
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ c) :=
    ⟨pointOfClosedPoint (U.ι ≫ c) x hx, pointOfClosedPoint_comp (U.ι ≫ c) x hx⟩
  exact ⟨finiteCurveTrace c b π hπ n hn U ε G q,
    finiteCurveTrace_geometric_fibre c b π hπ n hn U ε G q⟩

end Trace

end AlgebraicGeometry.GeneralizedJacobian
