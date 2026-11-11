/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.BasicPerfectField
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveIffTranscendentalFiniteDimensional
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
public import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
public import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
public import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFields.OpenImmersionFunctionFieldIso
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.CompEqOpenImmersion
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothOfRelativeDimensionDVRStalkIsClosed
public import Nyll.SchemeTheory.LocalGeometry.Normality
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralDescent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Smooth compactification of the original curve

The perfect-field model of the original function field receives the whole
smooth separated curve, not merely its generic neighbourhood. Properness
extends that neighbourhood across the discrete valuation stalks. Its finite
complement gives finite fibres, and the normal birational open-immersion
criterion identifies the original scheme with an open of the proper model.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve

universe u

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- A smooth separated curve over a perfect field embeds in a proper smooth
model of its original function field. Both the structural coefficient map
and the original generic-point map are retained. -/
theorem exists_curveModel_openImmersion_of_smooth_curve
    (k : Type u) [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f] :
    let _ : Algebra k X.functionField := (baseToFunctionField f).toAlgebra
    ∃ (M : CurveModel k X.functionField) (j : X ⟶ M.C),
      IsOpenImmersion j ∧ j ≫ M.toBase = f ∧
      X.fromSpecStalk (genericPoint X) ≫ j =
        Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
          M.C.fromSpecStalk (genericPoint M.C) := by
  intro alg
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsCurveOver k X.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one f
      (RingEquiv.refl _) (fun _ => rfl)
  have : Algebra.EssFiniteType k X.functionField := essFiniteType_functionField f
  obtain ⟨t, ht, hfin, _⟩ :=
    (isCurveOver_iff_exists_transcendental_finiteDimensional
      (K := k) (F := X.functionField)).mp inferInstance
  obtain ⟨M⟩ := CurveModel.nonempty_of_perfectField k X.functionField ⟨t, ht, hfin⟩
  let ψ : X.functionField ≅ M.C.functionField := M.ffEquiv.toCommRingCatIso
  let bX : CommRingCat.of k ⟶ X.functionField := CommRingCat.ofHom (baseToFunctionField f)
  let bM : CommRingCat.of k ⟶ M.C.functionField :=
    CommRingCat.ofHom (baseToFunctionField M.toBase)
  have hbaseX : X.fromSpecStalk (genericPoint X) ≫ f = Spec.map bX :=
    fromSpecStalk_genericPoint_comp_base f
  have hbaseM : M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase = Spec.map bM :=
    fromSpecStalk_genericPoint_comp_base M.toBase
  have hb : bM ≫ ψ.inv = bX := by
    ext a
    change M.ffEquiv.symm (baseToFunctionField M.toBase a) = baseToFunctionField f a
    rw [← M.ffEquiv_algebraMap, M.ffEquiv.symm_apply_apply]
    rfl
  have hψ : Spec.map ψ.inv ≫ M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase =
      X.fromSpecStalk (genericPoint X) ≫ f := by
    rw [hbaseM, hbaseX, ← Spec.map_comp, hb]
  obtain ⟨W, hηW, a, ha, haBase, haGeneric⟩ :=
    Scheme.exists_isOpenImmersion_of_functionField_iso f M.toBase ψ hψ
  have : IsOpenImmersion a := ha
  have hW : (W : Set X).Nonempty := ⟨genericPoint X, hηW⟩
  have : Nonempty W := hW.to_subtype
  have hDVR (x : X) (hx : x ∉ Set.range W.ι.base) :
      IsDiscreteValuationRing (X.presheaf.stalk x) := by
    apply SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed f x
    apply isClosed_singleton_of_ne_genericPoint f x
    intro h
    apply hx
    exact ⟨⟨genericPoint X, hηW⟩, h.symm⟩
  obtain ⟨j, hjBase, hjW⟩ :=
    exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
      f W.ι hDVR M.toBase a haBase
  have : LocallyOfFiniteType (j ≫ M.toBase) := hjBase.symm ▸ inferInstance
  have : LocallyOfFiniteType j := locallyOfFiniteType_of_comp j M.toBase
  have : IsSeparated (j ≫ M.toBase) := hjBase.symm ▸ inferInstance
  have : IsSeparated j := IsSeparated.of_comp j M.toBase
  have : QuasiCompact (j ≫ M.toBase) := hjBase.symm ▸ inferInstance
  have : QuasiCompact j := QuasiCompact.of_comp j M.toBase
  have hpoint (w : W) : j w.val = a w :=
    congrArg (fun h : (W : Scheme) ⟶ M.C => h w) hjW
  have hfibre (y : M.C) : (j ⁻¹' {y}).Finite := by
    have hinside : ((W : Set X) ∩ j ⁻¹' {y}).Finite := by
      apply Set.Finite.of_injOn (f := j) (t := {y})
        (fun _ hx => hx.2) ?_ (Set.finite_singleton y)
      intro x hx z hz hxz
      exact congrArg Subtype.val (a.isOpenEmbedding.injective
        ((hpoint ⟨x, hx.1⟩).symm.trans (hxz.trans (hpoint ⟨z, hz.1⟩))))
    apply ((finite_compl_of_isOpen f W hW).union hinside).subset
    intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inr ⟨hxW, hx⟩
    · exact Or.inl hxW
  have : LocallyQuasiFinite j := LocallyQuasiFinite.of_finite_preimage_singleton j hfibre
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of k), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let D := a.opensRange
  let s : (D : Scheme) ⟶ X := a.isoOpensRange.inv ≫ W.ι
  have hs : s ≫ j = D.ι := by
    rw [Category.assoc, hjW, Scheme.Hom.isoOpensRange_inv_comp]
  have hD : (D : Set M.C).Nonempty :=
    ⟨a ⟨genericPoint X, hηW⟩, Set.mem_range_self _⟩
  have : Nonempty D := hD.to_subtype
  have hsDense : DenseRange s :=
    s.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace s
  have : IsOpenImmersion j :=
    isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
      j (fun x => Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x)
      D (D.isOpen.dense hD) s hs hsDense
  refine ⟨M, j, inferInstance, hjBase, ?_⟩
  rw [← Scheme.Opens.fromSpecStalkOfMem_ι W (genericPoint X) hηW,
    Category.assoc, hjW]
  exact haGeneric

/-- Geometric integrality passes from the original smooth curve to the
constructed compactification over the same coefficient field. -/
theorem exists_geometricallyIntegral_curveModel_openImmersion
    (k : Type u) [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    [GeometricallyIntegral f] :
    let _ : Algebra k X.functionField := (baseToFunctionField f).toAlgebra
    ∃ (M : CurveModel k X.functionField) (j : X ⟶ M.C),
      IsOpenImmersion j ∧ j ≫ M.toBase = f ∧ GeometricallyIntegral M.toBase := by
  intro alg
  obtain ⟨M, j, hj, hbase, _hgeneric⟩ := exists_curveModel_openImmersion_of_smooth_curve k f
  have : IsOpenImmersion j := hj
  have : IsDominant j := ⟨j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j⟩
  have : QuasiCompact (j ≫ M.toBase) := hbase.symm ▸ inferInstance
  have : QuasiCompact j := QuasiCompact.of_comp j M.toBase
  have hgeom : GeometricallyIntegral (j ≫ M.toBase) := hbase.symm ▸ inferInstance
  exact ⟨M, j, hj, hbase, GeometricallyIntegral.of_comp_of_isDominant
    j M.toBase (Field.toIsField k) hgeom⟩

/-- The original smooth separated curve is the exact complement of a finite
étale closed subscheme in its proper smooth compactification. The structure
map and the generic-point map of the original curve are preserved. -/
theorem exists_curveModel_finiteEtale_boundary_of_smooth_curve
    (k : Type u) [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f] :
    let _ : Algebra k X.functionField := (baseToFunctionField f).toAlgebra
    ∃ (M : CurveModel k X.functionField) (j : X ⟶ M.C)
      (D : Scheme.{u}) (i : D ⟶ M.C),
      IsOpenImmersion j ∧ j ≫ M.toBase = f ∧
        IsClosedImmersion i ∧ IsFinite (i ≫ M.toBase) ∧ Etale (i ≫ M.toBase) ∧
        Set.range i = (Set.range j)ᶜ ∧
        X.fromSpecStalk (genericPoint X) ≫ j =
          Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
            M.C.fromSpecStalk (genericPoint M.C) := by
  intro alg
  obtain ⟨M, j, hj, hbase, hgeneric⟩ :=
    exists_curveModel_openImmersion_of_smooth_curve k f
  have : IsOpenImmersion j := hj
  obtain ⟨hfinite, hetale⟩ := M.finite_etale_openBoundaryIdeal_toBase j
  exact ⟨M, j, (M.openBoundaryIdeal j).subscheme,
    (M.openBoundaryIdeal j).subschemeι, hj, hbase, inferInstance,
    hfinite, hetale, M.range_openBoundaryIdeal_subschemeι j, hgeneric⟩

end AlgebraicCurve
