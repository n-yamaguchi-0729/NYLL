/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FiniteCurveTraceDomain
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.TupleOfSplitDivisor
import Nyll.AlgebraicCurves.RelativeDivisors.Support.SupportedDivisorGeometricTuples
import Nyll.SchemeTheory.Normalization.FiniteNormalFormalSplitting
import Nyll.SchemeTheory.FunctionFields.IntegralGenericPointReflection

/-! # The regular finite-curve trace on the actual formal generic fibre

The finite graph divisor is identified with the actual base-changed cover.
Its formal splitting constructs the Cartier tuple. The coordinates of this
tuple are precisely the lifted field embeddings, and evaluate the previously
constructed regular trace over the entire power-series spectrum.
-/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.GeneralizedJacobian

/-- The full Cartier trace family is the actual pullback of the finite cover,
with both projections retained. -/
theorem traceFamily_subscheme_pullback
    {C B S T : Scheme.{u}} (c : C ⟶ S) (b : B ⟶ S)
    (π : C ⟶ B) (hπ : π ≫ b = c)
    [IsSeparated b] [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y : B, π.finrank y = n) (U : C.Opens) :
    let V := finiteMapTraceLocus c b π hπ n hn U
    let A := finiteMapTraceFamily c b π hπ n hn U
    ∀ (a : T ⟶ V),
      let D := A.pullbackAlong a rfl
      ∃ e : D.I.subscheme ≅ pullback π (a ≫ V.ι),
        e.hom ≫ pullback.fst π (a ≫ V.ι) =
          D.I.subschemeι ≫ pullback.fst c (a ≫ (V.ι ≫ b)) ∧
        e.hom ≫ pullback.snd π (a ≫ V.ι) =
          D.I.subschemeι ≫ pullback.snd c (a ≫ (V.ι ≫ b)) := by
  intro V A a D
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
  let m₁ : A.I.subscheme ⟶ D₀.I.subscheme := comapSubschemeMapOver D₀.I V.ι rfl
  let m₂ : D.I.subscheme ⟶ A.I.subscheme := comapSubschemeMapOver A.I a rfl
  have h₁ : IsPullback m₁ (A.I.subschemeι ≫ pullback.snd c (V.ι ≫ b))
      (D₀.I.subschemeι ≫ pullback.snd c b) V.ι :=
    isPullback_comap_snd_over D₀.I V.ι rfl
  have h₂ : IsPullback m₂ (D.I.subschemeι ≫ pullback.snd c (a ≫ (V.ι ≫ b)))
      (A.I.subschemeι ≫ pullback.snd c (V.ι ≫ b)) a :=
    isPullback_comap_snd_over A.I a rfl
  have hp : IsPullback (m₂ ≫ m₁ ≫ e₀.inv)
      (D.I.subschemeι ≫ pullback.snd c (a ≫ (V.ι ≫ b))) π (a ≫ V.ι) := by
    apply (h₂.paste_horiz h₁).of_iso
      (Iso.refl _) e₀.symm (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
      exact Category.assoc _ _ _
    · rfl
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id]
      exact hsnd
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  refine ⟨hp.isoPullback, ?_, hp.isoPullback_hom_snd⟩
  refine hp.isoPullback_hom_fst.trans ?_
  rw [← hfst]
  have hc₁ : m₁ ≫ D₀.I.subschemeι = A.I.subschemeι ≫ mapOnProdOver c V.ι rfl :=
    (isPullback_comapSubschemeMapOver D₀.I V.ι rfl).w
  have hc₂ : m₂ ≫ A.I.subschemeι = D.I.subschemeι ≫ mapOnProdOver c a rfl :=
    (isPullback_comapSubschemeMapOver A.I a rfl).w
  have hl₁ : m₁ ≫ D₀.I.subschemeι ≫ pullback.fst c b =
      A.I.subschemeι ≫ pullback.fst c (V.ι ≫ b) := by
    rw [← Category.assoc, hc₁, Category.assoc, mapOnProdOver_fst]
  have hl₂ : m₂ ≫ A.I.subschemeι ≫ pullback.fst c (V.ι ≫ b) =
      D.I.subschemeι ≫ pullback.fst c (a ≫ (V.ι ≫ b)) := by
    calc
      _ = (m₂ ≫ A.I.subschemeι) ≫ pullback.fst c (V.ι ≫ b) :=
        (Category.assoc _ _ _).symm
      _ = (D.I.subschemeι ≫ mapOnProdOver c a rfl) ≫
          pullback.fst c (V.ι ≫ b) :=
        congrArg (fun h => h ≫ pullback.fst c (V.ι ≫ b)) hc₂
      _ = _ := (Category.assoc _ _ _).trans
        (congrArg (fun h => D.I.subschemeι ≫ h) (mapOnProdOver_fst c a rfl))
  exact (congrArg (fun r => m₂ ≫ r) hl₁).trans hl₂

private def constantCoprodReindex {I : Type v} {J : Type w}
    [Small.{u} I] [Small.{u} J] (T : Scheme.{u}) (e : I ≃ J) :
    (∐ fun _ : I => T) ≅ (∐ fun _ : J => T) where
  hom := Sigma.desc (fun i => Sigma.ι (fun _ : J => T) (e i))
  inv := Sigma.desc (fun j => Sigma.ι (fun _ : I => T) (e.symm j))
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
      Equiv.symm_apply_apply, Category.comp_id]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro j
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
      Equiv.apply_symm_apply, Category.comp_id]

/-- The finite curve trace along a formal deformation is the sum over the
actual lifts of all residue embeddings. The map to the trace domain, the
ordering of the embeddings, and the sections in the source open are all
constructed here from the finite morphism and its native generic square. -/
theorem exists_finiteCurveTrace_formal_evaluation
    {K : Type u} [Field K] {C B : Scheme.{u}}
    [IsIntegral C] [IsNormalIntegral C] [IsIntegral B]
    (c : C ⟶ Spec (CommRingCat.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (b : B ⟶ Spec (CommRingCat.of K)) [IsSeparated b]
    (π : C ⟶ B) (hπ : π ≫ b = c)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y : B, π.finrank y = n)
    [Algebra B.functionField C.functionField]
    [FiniteDimensional B.functionField C.functionField]
    [Algebra.IsSeparable B.functionField C.functionField]
    (hgeneric : C.fromSpecStalk (genericPoint C) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap B.functionField C.functionField)) ≫
        B.fromSpecStalk (genericPoint B))
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ c))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom)
    {Ω : Type u} [Field Ω] [Algebra B.functionField Ω] [IsAlgClosed Ω]
    (τ : B.functionField →+* PowerSeries Ω)
    (hτ : PowerSeries.constantCoeff.comp τ = algebraMap B.functionField Ω) :
    let V := finiteMapTraceLocus c b π hπ n hn U
    ∃ (a : Spec (CommRingCat.of (PowerSeries Ω)) ⟶ V)
      (index : Fin n ≃ (C.functionField →ₐ[B.functionField] Ω))
      (xs : Fin n → SchemeHomOver (a ≫ (V.ι ≫ b)) (U.ι ≫ c)),
      a ≫ V.ι = Spec.map (CommRingCat.ofHom τ) ≫ B.fromSpecStalk (genericPoint B) ∧
      (∀ i, (xs i).val ≫ U.ι =
        Spec.map (CommRingCat.ofHom (PowerSeries.formalEmbeddingLift τ hτ (index i))) ≫
          C.fromSpecStalk (genericPoint C)) ∧
      GoodReductionJacobian.schemeHomOverComp a rfl
          (finiteCurveTrace c b π hπ n hn U ε G q) =
        (commGroupRelativeLaw G).sumList (a ≫ (V.ι ≫ b))
          (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q) := by
  classical
  intro V
  let E : Type u := B.functionField
  let F : Type u := C.functionField
  let R := PowerSeries Ω
  let T := Spec (CommRingCat.of R)
  have hηU : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr
      (by simpa only [Set.univ_inter] using hU)
  have hηV : genericPoint B ∈ V := by
    apply (mem_finiteMapTraceLocus_iff c b π hπ n hn U _).mpr
    intro x hx
    rw [π.eq_genericPoint_of_isIntegralHom x hx]
    exact hηU
  let a : T ⟶ V := Spec.map (CommRingCat.ofHom τ) ≫
    V.fromSpecStalkOfMem (genericPoint B) hηV
  have ha : a ≫ V.ι = Spec.map (CommRingCat.ofHom τ) ≫
      B.fromSpecStalk (genericPoint B) := by
    simp only [a, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  let pb := Field.powerBasisOfFiniteOfSeparable E F
  let _ : Fintype (F →ₐ[E] Ω) := PowerBasis.AlgHom.fintype pb
  have hcard : Fintype.card (F →ₐ[E] Ω) = n := by
    rw [AlgHom.card_of_powerBasis pb (Algebra.IsSeparable.isSeparable E pb.gen)
      (IsAlgClosed.splits _), ← pb.finrank]
    have hpb := π.isPullback_finiteNormal_generic hgeneric
    have hr := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb
      (IsLocalRing.closedPoint E)
    have hrank : (Spec.map (CommRingCat.ofHom (algebraMap E F))).finrank
        (IsLocalRing.closedPoint E) = Module.finrank E F := by
      rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
      rfl
    exact hrank.symm.trans (hr.trans (hn _))
  let index : Fin n ≃ (F →ₐ[E] Ω) := (Fintype.equivFinOfCardEq hcard).symm
  have hsplit := π.exists_formalGenericFibre_coprod_iso hgeneric τ hτ
  rw [← ha] at hsplit
  obtain ⟨e', he', hei'⟩ := hsplit
  let A := finiteMapTraceFamily c b π hπ n hn U
  let D := A.pullbackAlong a rfl
  obtain ⟨d, hdfst, hdsnd⟩ := traceFamily_subscheme_pullback c b π hπ n hn U a
  let reindex := constantCoprodReindex T index
  let total : (∐ fun _ : Fin n => T) ≅ D.I.subscheme := reindex ≪≫ e' ≪≫ d.symm
  have htotal : total.hom ≫ D.I.subschemeι ≫ pullback.snd c (a ≫ (V.ι ≫ b)) =
      Sigma.desc (fun _ : Fin n => 𝟙 T) := by
    rw [← hdsnd]
    simp only [total, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [he']
    apply Sigma.hom_ext
    intro i
    simp only [reindex, constantCoprodReindex, Sigma.ι_comp_desc_assoc,
      Sigma.ι_comp_desc]
    rfl
  obtain ⟨ys, hys, hI⟩ := D.exists_tuple_of_coprod_iso total htotal
  have hy (i : Fin n) : (ys i).val =
      Spec.map (CommRingCat.ofHom (PowerSeries.formalEmbeddingLift τ hτ (index i))) ≫
        C.fromSpecStalk (genericPoint C) := by
    rw [hys, ← hdfst]
    simp only [total, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      reindex, constantCoprodReindex, Sigma.ι_comp_desc_assoc]
    exact hei' (index i)
  let xu (i : Fin n) : T ⟶ U :=
    Spec.map (CommRingCat.ofHom (PowerSeries.formalEmbeddingLift τ hτ (index i))) ≫
      U.fromSpecStalkOfMem (genericPoint C) hηU
  have hxu (i : Fin n) : xu i ≫ U.ι = (ys i).val := by
    rw [hy]
    simp only [xu, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  let xs : Fin n → SchemeHomOver (a ≫ (V.ι ≫ b)) (U.ι ≫ c) :=
    fun i => ⟨xu i, by rw [← Category.assoc, hxu]; exact (ys i).property⟩
  have hIfull : D.I = prodKerGraph c (fun i => (xs i).val ≫ U.ι)
      (fun i => by rw [Category.assoc, (xs i).property]) := by
    simpa only [xs, hxu] using hI
  let hA := finiteMapTraceFamily_supported c b π hπ n hn U
  have hIopen : (D.restrictToOpen c U (hA.pullbackAlong a rfl)).I =
      prodKerGraph (U.ι ≫ c) (fun i => (xs i).val) (fun i => (xs i).property) := by
    rw [RelEffCartierDiv.restrictToOpen_I, hIfull]
    exact RelEffCartierDiv.prodKerGraph_comap_openProdMap c U xs
  refine ⟨a, index, xs, ha, ?_, ?_⟩
  · intro i
    exact (hxu i).trans (hy i)
  · exact finiteCurveTrace_evaluate_tuple c b π hπ n hn U ε G q a xs hIopen

end AlgebraicGeometry.GeneralizedJacobian
