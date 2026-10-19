/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FiniteCurveTraceIntegralSelection
import Nyll.AlgebraicCurves.RelativeDivisors.Support.CompletedCartierBlockRestriction
import Nyll.AlgebraicCurves.Models.LocalGeometry.CompletedComponentCanonicalCentre

/-! # The actual boundary completed fibre of the finite curve graph

The completed coproduct is constructed from the original finite morphism.
The actual Henselian closed-fibre selection and the valuative criterion
identify its labels with the complement of the original source open.
The full Cartier kernel ideal identifies the boundary block, preserving
both its source projection and its native completed-base projection.
The integral base maps are the ones supplied by the original proper curve
and its completed valuation rings (or their actual power-series transport).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open NeronModelInfra GoodReductionJacobian
open scoped AlgebraicCurve.Place
open scoped AlgebraicCurves.FunctionFields.Proofs.CompletionTraceSum_of_isSeparable

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem comapDivisor_source_projection
    {C S R T : Scheme.{u}} {c : C ⟶ S} {r : R ⟶ S} {t : T ⟶ S}
    {n : ℕ} (D : RelEffCartierDiv c n r) (g : T ⟶ R) (hg : g ≫ r = t) :
    (comapSubschemeMapOver D.I g hg : (D.pullbackAlong g hg).I.subscheme ⟶ D.I.subscheme) ≫
        D.I.subschemeι ≫ pullback.fst c r =
      (D.pullbackAlong g hg).I.subschemeι ≫ pullback.fst c t := by
  change comapSubschemeMapOver D.I g hg ≫ D.I.subschemeι ≫ pullback.fst c r =
    (D.I.comap (mapOnProdOver c g hg)).subschemeι ≫ pullback.fst c t
  rw [(isPullback_comapSubschemeMapOver D.I g hg).w_assoc, mapOnProdOver_fst]

private theorem comapDivisor_base_projection
    {C S R T : Scheme.{u}} {c : C ⟶ S} {r : R ⟶ S} {t : T ⟶ S}
    {n : ℕ} (D : RelEffCartierDiv c n r) (g : T ⟶ R) (hg : g ≫ r = t) :
    (comapSubschemeMapOver D.I g hg : (D.pullbackAlong g hg).I.subscheme ⟶ D.I.subscheme) ≫
        D.I.subschemeι ≫ pullback.snd c r =
      (D.pullbackAlong g hg).I.subschemeι ≫ pullback.snd c t ≫ g := by
  change comapSubschemeMapOver D.I g hg ≫ D.I.subschemeι ≫ pullback.snd c r =
    (D.I.comap (mapOnProdOver c g hg)).subschemeι ≫ pullback.snd c t ≫ g
  rw [(isPullback_comapSubschemeMapOver D.I g hg).w_assoc, mapOnProdOver_snd]

private theorem completed_boundary_block_of_integral_components
    {K R L : Type u} [Field K] [IsAlgClosed K] [CommRing R] [IsLocalRing R] [Field L]
    {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) {r : Spec (.of R) ⟶ Spec (.of K)}
    {t : Spec (.of L) ⟶ Spec (.of K)} (g : Spec (.of L) ⟶ Spec (.of R))
    (hg : g ≫ r = t) {n : ℕ} (D : RelEffCartierDiv c n r)
    (V : D.I.subscheme.Opens) (hV : IsClosed (V : Set D.I.subscheme))
    (hsel : pullback.fst (D.I.subschemeι ≫ pullback.snd c r)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⁻¹'
          (V : Set D.I.subscheme) =
      (pullback.fst (D.I.subschemeι ≫ pullback.snd c r)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫
        D.I.subschemeι ≫ pullback.fst c r) ⁻¹' (U : Set C))
    {k : ℕ} (D₁ : RelEffCartierDiv c k r) :
    let W : D.I.subscheme.Opens := ⟨(V : Set D.I.subscheme)ᶜ, hV.isOpen_compl⟩
    D₁.I = (W.ι ≫ D.I.subschemeι).ker →
    let _ : Algebra K C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ {J : Type u} (w : J → AlgebraicCurve.Place K C.functionField)
      (aInt : (j : J) → R →+* (w j).adicCompletionIntegers)
      [∀ j, IsLocalHom (aInt j)]
      (e : (∐ fun j : J => Spec (.of (w j).adicCompletion)) ≅
        (D.pullbackAlong g hg).I.subscheme),
    (∀ j, Sigma.ι (fun j : J => Spec (.of (w j).adicCompletion)) j ≫ e.hom ≫
        (D.pullbackAlong g hg).I.subschemeι ≫ pullback.fst c t =
      Spec.map (CommRingCat.ofHom (algebraMap C.functionField (w j).adicCompletion)) ≫
        C.fromSpecStalk (genericPoint C)) →
    (∀ j, Sigma.ι (fun j : J => Spec (.of (w j).adicCompletion)) j ≫ e.hom ≫
        (D.pullbackAlong g hg).I.subschemeι ≫ pullback.snd c t ≫ g =
      Spec.map (CommRingCat.ofHom
        (algebraMap (w j).adicCompletionIntegers (w j).adicCompletion)) ≫
          Spec.map (CommRingCat.ofHom (aInt j))) →
    let P := fun j : J =>
      ((AlgebraicCurve.CurveModel.ofSmoothProperCurve c).placeEquiv.symm (w j)).1 ∉ U
    ∃ d : (∐ fun j : {j // P j} => Spec (.of (w j.1).adicCompletion)) ≅
        (D₁.pullbackAlong g hg).I.subscheme,
      ∀ j : {j // P j},
        Sigma.ι (fun j : {j // P j} => Spec (.of (w j.1).adicCompletion)) j ≫
            d.hom ≫ (D₁.pullbackAlong g hg).I.subschemeι =
          Sigma.ι (fun j : J => Spec (.of (w j).adicCompletion)) j.1 ≫
            e.hom ≫ (D.pullbackAlong g hg).I.subschemeι := by
  intro W hI algC J w aInt localInt e hsource hbase P
  let Z : J → Scheme.{u} := fun j => Spec (.of (w j).adicCompletion)
  let m : (D.pullbackAlong g hg).I.subscheme ⟶ D.I.subscheme :=
    comapSubschemeMapOver D.I g hg
  have hmfst : m ≫ D.I.subschemeι ≫ pullback.fst c r =
      (D.pullbackAlong g hg).I.subschemeι ≫ pullback.fst c t :=
    comapDivisor_source_projection D g hg
  have hmsnd : m ≫ D.I.subschemeι ≫ pullback.snd c r =
      (D.pullbackAlong g hg).I.subschemeι ≫ pullback.snd c t ≫ g :=
    comapDivisor_base_projection D g hg
  have hlabels (j : J) :
      (Sigma.ι Z j ≫ e.hom ≫ m)
          (IsLocalRing.closedPoint (w j).adicCompletion) ∈ W ↔ P j := by
    let ξ : Spec (.of (w j).adicCompletion) ⟶ D.I.subscheme :=
      Sigma.ι Z j ≫ e.hom ≫ m
    have hξsource : ξ ≫ D.I.subschemeι ≫ pullback.fst c r =
        Spec.map (CommRingCat.ofHom (algebraMap C.functionField (w j).adicCompletion)) ≫
          C.fromSpecStalk (genericPoint C) := by
      change (Sigma.ι Z j ≫ e.hom ≫ m) ≫
          D.I.subschemeι ≫ pullback.fst c r = _
      simp only [Category.assoc]
      rw [hmfst]
      exact hsource j
    have hξbase : ξ ≫ D.I.subschemeι ≫ pullback.snd c r =
        Spec.map (CommRingCat.ofHom
          (algebraMap (w j).adicCompletionIntegers (w j).adicCompletion)) ≫
            Spec.map (CommRingCat.ofHom (aInt j)) := by
      change (Sigma.ι Z j ≫ e.hom ≫ m) ≫
          D.I.subschemeι ≫ pullback.snd c r = _
      simp only [Category.assoc]
      rw [hmsnd]
      exact hbase j
    obtain ⟨ℓ, _, _, hz, hmember⟩ :=
      D.exists_completed_component_specialization U V hV hsel (w j) (aInt j)
        ξ hξbase hξsource
    have hzEq := AlgebraicCurve.CurveModel.eq_placeEquiv_symm_of_centre c (w j) _ hz
    rw [hzEq] at hmember
    exact not_congr hmember
  exact D.exists_completed_clopen_block_iso W
    (by change IsClosed (V : Set D.I.subscheme)ᶜ; exact V.isOpen.isClosed_compl)
    D₁ hI g hg (fun j : J => (w j).adicCompletion) e P hlabels

/-- The complementary Cartier block of the actual integral graph has
exactly the completed components whose canonical place centres lie outside
`U`. All component maps and their projections are constructed; the input
triangles only specify the actual integral base extension. -/
theorem exists_finiteCurveTrace_boundary_completed_fibre
    {K R : Type u} [Field K] [IsAlgClosed K] [CommRing R] [IsLocalRing R]
    {C B : Scheme.{u}} [IsIntegral C] [IsNormalIntegral C] [IsIntegral B]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (b : B ⟶ Spec (.of K)) [IsSeparated b]
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
      (a₀ : Spec (.of R) ⟶ B) (g : Spec (.of v.adicCompletion) ⟶ Spec (.of R)),
    g ≫ a₀ = Spec.map (CommRingCat.ofHom
      (algebraMap B.functionField v.adicCompletion)) ≫ B.fromSpecStalk (genericPoint B) →
    ∀ (aInt : (w : v.fiber C.functionField) → R →+* w.1.adicCompletionIntegers)
      [∀ w, IsLocalHom (aInt w)],
    (∀ w, Spec.map (CommRingCat.ofHom
        (algebraMap v.adicCompletion w.1.adicCompletion)) ≫ g =
      Spec.map (CommRingCat.ofHom
        (algebraMap w.1.adicCompletionIntegers w.1.adicCompletion)) ≫
          Spec.map (CommRingCat.ofHom (aInt w))) →
    let D := (finiteMapFiberDivisor c b π hπ n hn).pullbackAlong a₀ rfl
    ∀ (V : D.I.subscheme.Opens) (hV : IsClosed (V : Set D.I.subscheme)),
    let W : D.I.subscheme.Opens := ⟨(V : Set D.I.subscheme)ᶜ, hV.isOpen_compl⟩
    (pullback.fst (D.I.subschemeι ≫ pullback.snd c (a₀ ≫ b))
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⁻¹'
          (V : Set D.I.subscheme) =
      (pullback.fst (D.I.subschemeι ≫ pullback.snd c (a₀ ≫ b))
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫
          D.I.subschemeι ≫ pullback.fst c (a₀ ≫ b)) ⁻¹' (U : Set C)) →
    ∀ (k : ℕ) (D₁ : RelEffCartierDiv c k (a₀ ≫ b)),
    D₁.I = (W.ι ≫ D.I.subschemeι).ker →
    let I := {w : v.fiber C.functionField //
      ((AlgebraicCurve.CurveModel.ofSmoothProperCurve c).placeEquiv.symm w.1).1 ∉ U}
    let Dg := D₁.pullbackAlong g (Category.assoc g a₀ b).symm
    ∃ e : (∐ fun w : I => Spec (.of w.1.1.adicCompletion)) ≅ Dg.I.subscheme,
      (∀ w : I, Sigma.ι (fun w : I => Spec (.of w.1.1.adicCompletion)) w ≫
          e.hom ≫ Dg.I.subschemeι ≫ pullback.fst c ((g ≫ a₀) ≫ b) =
        Spec.map (CommRingCat.ofHom (algebraMap C.functionField w.1.1.adicCompletion)) ≫
          C.fromSpecStalk (genericPoint C)) ∧
      ∀ w : I, Sigma.ι (fun w : I => Spec (.of w.1.1.adicCompletion)) w ≫
          e.hom ≫ Dg.I.subschemeι ≫ pullback.snd c ((g ≫ a₀) ≫ b) =
        Spec.map (CommRingCat.ofHom (algebraMap v.adicCompletion w.1.1.adicCompletion)) := by
  intro algB algC algBC tower fin sep divB divC hgeneric v a₀ g hg aInt localInt
    hInt D V hV W hsel k D₁ hI I Dg
  let Fw (w : v.fiber C.functionField) := w.1.adicCompletion
  let Z (w : v.fiber C.functionField) : Scheme.{u} := Spec (.of (Fw w))
  let ha := (Category.assoc g a₀ b).symm
  let A := D.pullbackAlong g ha
  have hA : A = (finiteMapFiberDivisor c b π hπ n hn).pullbackAlong (g ≫ a₀) rfl :=
    RelEffCartierDiv.pullbackAlong_comp _ a₀ rfl g ha
  have hgraph := finiteMapFiberDivisor_subscheme_pullback c b π hπ n hn (g ≫ a₀)
  rw [← hA] at hgraph
  obtain ⟨d, hdfst, hdsnd⟩ := hgraph
  have hsplit := π.exists_completedGenericFibre_coprod_iso hgeneric v
  rw [← hg] at hsplit
  obtain ⟨e₀, heBase, heSource⟩ := hsplit
  let e := e₀ ≪≫ d.symm
  have hsource (w : v.fiber C.functionField) :
      Sigma.ι Z w ≫ e.hom ≫ A.I.subschemeι ≫ pullback.fst c ((g ≫ a₀) ≫ b) =
        Spec.map (CommRingCat.ofHom (algebraMap C.functionField w.1.adicCompletion)) ≫
          C.fromSpecStalk (genericPoint C) := by
    rw [← hdfst]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    exact heSource w
  have hbase (w : v.fiber C.functionField) :
      Sigma.ι Z w ≫ e.hom ≫ A.I.subschemeι ≫ pullback.snd c ((g ≫ a₀) ≫ b) =
        Spec.map (CommRingCat.ofHom (algebraMap v.adicCompletion w.1.adicCompletion)) := by
    rw [← hdsnd]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [heBase, Sigma.ι_comp_desc]
  have hbaseInt (w : v.fiber C.functionField) :
      Sigma.ι Z w ≫ e.hom ≫ A.I.subschemeι ≫
        pullback.snd c ((g ≫ a₀) ≫ b) ≫ g =
      Spec.map (CommRingCat.ofHom
        (algebraMap w.1.adicCompletionIntegers w.1.adicCompletion)) ≫
          Spec.map (CommRingCat.ofHom (aInt w)) := by
    simpa only [Category.assoc] using
      (congrArg (fun f => f ≫ g) (hbase w)).trans (hInt w)
  obtain ⟨dB, hdB⟩ := completed_boundary_block_of_integral_components
    c U g ha D V hV hsel D₁ hI
    (fun w : v.fiber C.functionField => w.1) aInt e hsource hbaseInt
  refine ⟨dB, ?_, ?_⟩
  · intro w
    have h := congrArg (fun f : Spec (.of w.1.1.adicCompletion) ⟶
        pullback c ((g ≫ a₀) ≫ b) => f ≫ pullback.fst c ((g ≫ a₀) ≫ b)) (hdB w)
    simpa only [Category.assoc] using h.trans (hsource w.1)
  · intro w
    have h := congrArg (fun f : Spec (.of w.1.1.adicCompletion) ⟶
        pullback c ((g ≫ a₀) ≫ b) => f ≫ pullback.snd c ((g ≫ a₀) ≫ b)) (hdB w)
    simpa only [Category.assoc] using h.trans (hbase w.1)

end AlgebraicGeometry.GeneralizedJacobian
