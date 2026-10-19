/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.FormalProductFieldSplitting
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.TupleOfSplitDivisor
import Nyll.AlgebraicCurves.RelativeDivisors.Support.IEqProdKerGraphSupportedIn
import Nyll.AlgebraicCurves.RelativeDivisors.Support.SupportedDivisorGeometricTuples
import Nyll.JacobianVarieties.Albanese.OpenCurveSumChoice
import Nyll.JacobianVarieties.Albanese.DivisorSumEvaluation
import Nyll.SchemeTheory.RingTheory.Henselian.FormalEmbeddingLiftAlgebra
import Nyll.SchemeTheory.GroupSchemes.GroupDiagonalFormalSubstitution
import Mathlib.Algebra.BigOperators.Fin
import Nyll.AlgebraicCurves.Divisors.Degree.TameBoundaryGroupDifference

/-! # Actual formal tuple and sum of the completed boundary Cartier block

This calculation transports the completed-field coproduct of the actual
boundary block through the original divisor pullback square. The formal
field splittings construct the tuple and its full ideal equality. The rank
of the original divisor determines its number of labels, and the represented
sum is evaluated on that tuple. No tuple ideal or divisor-sum comparison is
assumed in this calculation.
-/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj BigOperators TensorProduct

namespace JacobianVarieties.Albanese

private def reindexConstantCoprod {I : Type v} {J : Type w}
    [Small.{u} I] [Small.{u} J]
    (T : Scheme.{u}) (index : I ≃ J) :
    (∐ fun _ : I => T) ≅ (∐ fun _ : J => T) where
  hom := Sigma.desc (fun i => Sigma.ι (fun _ : J => T) (index i))
  inv := Sigma.desc (fun j => Sigma.ι (fun _ : I => T) (index.symm j))
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

private theorem card_eq_degree_of_constant_coprod
    {R : Type u} [CommRing R] [IsLocalRing R]
    {C S : Scheme.{u}} {c : C ⟶ S} {m : ℕ}
    {t : Spec (.of R) ⟶ S} (D : RelEffCartierDiv c m t)
    {I : Type u} [Fintype I]
    (e : (∐ fun _ : I => Spec (.of R)) ≅ D.I.subscheme)
    (he : e.hom ≫ D.I.subschemeι ≫ pullback.snd c t =
      Sigma.desc (fun _ : I => 𝟙 (Spec (.of R)))) : Fintype.card I = m := by
  classical
  have : IsFinite (D.I.subschemeι ≫ pullback.snd c t) := D.isFinite
  have : Flat (D.I.subschemeι ≫ pullback.snd c t) := D.flat
  let s := asIso (sigmaSpec (fun _ : I => CommRingCat.of R))
  have hs : s.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (I → R))) =
      Sigma.desc (fun _ : I => 𝟙 (Spec (.of R))) := by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι (fun _ : I => Spec (.of R)) i ≫
      sigmaSpec (fun _ : I => CommRingCat.of R) ≫ _ = _
    rw [ι_sigmaSpec_assoc, Sigma.ι_comp_desc, ← Spec.map_comp]
    exact Spec.map_id _
  have hproj : s.inv ≫ e.hom ≫ D.I.subschemeι ≫ pullback.snd c t =
      Spec.map (CommRingCat.ofHom (algebraMap R (I → R))) := by
    rw [he, ← hs, s.inv_hom_id_assoc]
  let z : Spec (.of R) := IsLocalRing.closedPoint R
  have hr := congrArg (fun f : Spec (.of (I → R)) ⟶ Spec (.of R) =>
    f.finrank z) hproj
  rw [Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_comp_left_of_isIso, D.finrank_eq,
    Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free,
    Module.finrank_fintype_fun_eq_card] at hr
  exact hr.symm

-- This private calculation is consumed by the actual boundary-selection
-- construction. Its e/hbase/hsource are the labelled completed-fibre
-- identities constructed there, rather than new hypotheses on a curve map.
private theorem formal_boundary_block_tuple_and_sum
    {K E L : Type u} [Field K] [Field E] [Field L]
    [Algebra K L] [Algebra E L]
    {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    {m : ℕ}
    (r : Spec (.of E) ⟶ Spec (.of K)) (D : RelEffCartierDiv c m r)
    {I : Type u} [Finite I] (F : I → Type u)
    [∀ i, Field (F i)] [∀ i, Algebra E (F i)]
    [∀ i, FiniteDimensional E (F i)] [∀ i, Algebra.IsSeparable E (F i)]
    (n : I → ℕ) (hn : ∀ i, Module.finrank E (F i) = n i)
    (embeddings : ∀ i, Fin (n i) → F i →ₐ[E] L) (hι : ∀ i, Function.Injective (embeddings i))
    (j : ∀ i, C.functionField →+* F i)
    (e : (∐ fun i : I => Spec (.of (F i))) ≅ D.I.subscheme)
    (hbase : e.hom ≫ D.I.subschemeι ≫
        pullback.snd c r =
      Sigma.desc (fun i : I => Spec.map (CommRingCat.ofHom (algebraMap E (F i)))))
    (hsource : ∀ i : I,
      Sigma.ι (fun i : I => Spec (.of (F i))) i ≫ e.hom ≫ D.I.subschemeι ≫
        pullback.fst c r =
      Spec.map (CommRingCat.ofHom (j i)) ≫ C.fromSpecStalk (genericPoint C))
    (G : CommGrp (Over (Spec (.of K))))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom)
    (s : OpenCurveSum c U (commGroupRelativeLaw G) q m)
    (τ : E →+* PowerSeries L)
    (hτ : PowerSeries.constantCoeff.comp τ = algebraMap E L)
    (hstructure : Spec.map (CommRingCat.ofHom τ) ≫ r =
      Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries L)))) :
    let t := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries L)))
    let f := Spec.map (CommRingCat.ofHom τ)
    let hf : f ≫ r = t := hstructure
    let A := D.pullbackAlong f hf
    ∃ (index : Fin m ≃ (Σ i, Fin (n i)))
      (xs : Fin m → SchemeHomOver t (U.ι ≫ c)) (hA : A.SupportedIn U),
      (∀ a, (xs a).val ≫ U.ι =
        Spec.map (CommRingCat.ofHom
          ((PowerSeries.formalEmbeddingLift τ hτ
            (embeddings (index a).1 (index a).2)).comp (j (index a).1))) ≫
          C.fromSpecStalk (genericPoint C)) ∧
      (A.restrictToOpen c U hA).I =
        prodKerGraph (U.ι ≫ c) (fun a => (xs a).val) (fun a => (xs a).property) ∧
      supportedDivisorSum c U s.universal s.sum A hA =
        (commGroupRelativeLaw G).sumList t
          (List.ofFn fun a => NeronModelInfra.schemeHomOverComp (xs a) q) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  intro t f hf A
  let fields : I → CommRingCat := fun i => .of (F i)
  let productIso : Spec (.of (∀ i, F i)) ≅ D.I.subscheme :=
    (asIso (sigmaSpec fields)).symm ≪≫ e
  have hσProduct : sigmaSpec fields ≫ productIso.hom = e.hom := by
    change (asIso (sigmaSpec fields)).hom ≫
      (asIso (sigmaSpec fields)).inv ≫ e.hom = e.hom
    exact (asIso (sigmaSpec fields)).hom_inv_id_assoc _
  have hproductBase : productIso.hom ≫ D.I.subschemeι ≫
      pullback.snd c r =
        Spec.map (CommRingCat.ofHom (algebraMap E (∀ i, F i))) := by
    apply (cancel_epi (sigmaSpec fields)).mp
    calc
      sigmaSpec fields ≫ productIso.hom ≫ D.I.subschemeι ≫ pullback.snd c r =
          e.hom ≫ D.I.subschemeι ≫ pullback.snd c r := by
        rw [← Category.assoc, hσProduct]
      _ = Sigma.desc (fun i : I =>
          Spec.map (CommRingCat.ofHom (algebraMap E (F i)))) := hbase
      _ = sigmaSpec fields ≫
          Spec.map (CommRingCat.ofHom (algebraMap E (∀ i, F i))) := by
        apply Sigma.hom_ext
        intro i
        rw [Sigma.ι_comp_desc, ι_sigmaSpec_assoc, ← Spec.map_comp]
        rfl
  have hproductSource (i : I) :
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom F i)) ≫
        productIso.hom ≫ D.I.subschemeι ≫
          pullback.fst c r =
        Spec.map (CommRingCat.ofHom (j i)) ≫ C.fromSpecStalk (genericPoint C) := by
    calc
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom F i)) ≫
          productIso.hom ≫ D.I.subschemeι ≫ pullback.fst c r =
        Sigma.ι (fun i : I => Spec (.of (F i))) i ≫ sigmaSpec fields ≫
          productIso.hom ≫ D.I.subschemeι ≫ pullback.fst c r := by
        rw [← ι_sigmaSpec fields i, Category.assoc]
      _ = Sigma.ι (fun i : I => Spec (.of (F i))) i ≫
          e.hom ≫ D.I.subschemeι ≫ pullback.fst c r := by
        rw [← Category.assoc (sigmaSpec fields) productIso.hom
          (D.I.subschemeι ≫ pullback.fst c r), hσProduct]
      _ = Spec.map (CommRingCat.ofHom (j i)) ≫
          C.fromSpecStalk (genericPoint C) := hsource i
  let mA : A.I.subscheme ⟶ D.I.subscheme := comapSubschemeMapOver D.I f hf
  have hraw : IsPullback mA (A.I.subschemeι ≫ pullback.snd c t)
      (D.I.subschemeι ≫ pullback.snd c r) f :=
    isPullback_comap_snd_over D.I f hf
  have hp : IsPullback (mA ≫ productIso.inv)
      (A.I.subschemeι ≫ pullback.snd c t)
      (Spec.map (CommRingCat.ofHom (algebraMap E (∀ i, F i)))) f := by
    apply hraw.of_iso (Iso.refl _) productIso.symm (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id]
      exact (productIso.inv_hom_id_assoc _).symm.trans
        (congrArg (fun z => productIso.inv ≫ z) hproductBase)
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  obtain ⟨d, hdBase, hdSource⟩ :=
    Scheme.exists_formal_product_field_fiber_coprod_iso F n hn embeddings hι τ hτ
  let total : (∐ fun _ : Σ i, Fin (n i) => Spec (.of (PowerSeries L))) ≅
      A.I.subscheme := d ≪≫ hp.isoPullback.symm
  have htotalBase : total.hom ≫ A.I.subschemeι ≫ pullback.snd c t =
      Sigma.desc (fun _ : Σ i, Fin (n i) => 𝟙 (Spec (.of (PowerSeries L)))) := by
    rw [← hp.isoPullback_hom_snd]
    simp only [total, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
    exact hdBase
  have hmSource : mA ≫ D.I.subschemeι ≫
      pullback.fst c r =
        A.I.subschemeι ≫ pullback.fst c t := by
    change comapSubschemeMapOver D.I f hf ≫ D.I.subschemeι ≫ pullback.fst c r =
      (D.I.comap (mapOnProdOver c f hf)).subschemeι ≫ pullback.fst c t
    rw [(isPullback_comapSubschemeMapOver D.I f hf).w_assoc, mapOnProdOver_fst]
  have htotalSource (i : I) (a : Fin (n i)) :
      Sigma.ι (fun _ : Σ i, Fin (n i) => Spec (.of (PowerSeries L))) ⟨i, a⟩ ≫
        total.hom ≫ A.I.subschemeι ≫ pullback.fst c t =
      Spec.map (CommRingCat.ofHom
        ((PowerSeries.formalEmbeddingLift τ hτ (embeddings i a)).comp (j i))) ≫
          C.fromSpecStalk (genericPoint C) := by
    rw [← hmSource]
    have hm : mA = hp.isoPullback.hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap E (∀ i, F i)))) f ≫
          productIso.hom := by
      rw [hp.isoPullback_hom_fst_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hm]
    simp only [total, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [reassoc_of% hdSource i a]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hproductSource]
  have hcard : Fintype.card (Σ i, Fin (n i)) = m :=
    card_eq_degree_of_constant_coprod A total htotalBase
  let index : Fin m ≃ (Σ i, Fin (n i)) := (Fintype.equivFinOfCardEq hcard).symm
  let reindex := reindexConstantCoprod (Spec (.of (PowerSeries L))) index
  let labelled := reindex ≪≫ total
  have hlabelled : labelled.hom ≫ A.I.subschemeι ≫ pullback.snd c t =
      Sigma.desc (fun _ : Fin m => 𝟙 (Spec (.of (PowerSeries L)))) := by
    simp only [labelled, Iso.trans_hom, Category.assoc]
    rw [htotalBase]
    apply Sigma.hom_ext
    intro a
    simp only [reindex, reindexConstantCoprod, Sigma.ι_comp_desc_assoc,
      Sigma.ι_comp_desc]
  obtain ⟨ys, hys, hI⟩ := A.exists_tuple_of_coprod_iso labelled hlabelled
  have hηU : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr
      (by simpa only [Set.univ_inter] using hU)
  let xu (a : Fin m) : Spec (.of (PowerSeries L)) ⟶ U :=
    Spec.map (CommRingCat.ofHom
      ((PowerSeries.formalEmbeddingLift τ hτ
        (embeddings (index a).1 (index a).2)).comp (j (index a).1))) ≫
      U.fromSpecStalkOfMem (genericPoint C) hηU
  have hxu (a : Fin m) : xu a ≫ U.ι = (ys a).val := by
    rw [hys]
    simp only [labelled, Iso.trans_hom, reindex, reindexConstantCoprod,
      Category.assoc, Sigma.ι_comp_desc_assoc]
    rw [htotalSource]
    simp only [xu, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  let xs : Fin m → SchemeHomOver t (U.ι ≫ c) :=
    fun a => ⟨xu a, by rw [← Category.assoc, hxu]; exact (ys a).property⟩
  have : SmoothOfRelativeDimension 1 (U.ι ≫ c) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ c))
  obtain ⟨A', hA'I, hA'U⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph_and_supportedIn U
    (fun a => (ys a).val) (fun a => (ys a).property) (by
      intro a z hz
      obtain ⟨y, rfl⟩ := hz
      rw [← hxu a]
      exact (xu a y).property)
  have hA : A.SupportedIn U := by
    change (A.I.support : Set ↥(pullback c t : Scheme.{u})) ⊆ (pullback.fst c t) ⁻¹' (U : Set C)
    rw [hI, ← hA'I]
    exact hA'U
  have hIopen : (A.restrictToOpen c U hA).I =
      prodKerGraph (U.ι ≫ c) (fun a => (xs a).val) (fun a => (xs a).property) := by
    rw [RelEffCartierDiv.restrictToOpen_I]
    have hIfull : A.I = prodKerGraph c (fun a => (xs a).val ≫ U.ι)
        (fun a => by rw [Category.assoc, (xs a).property]) := by
      simpa only [xs, hxu] using hI
    rw [hIfull]
    exact RelEffCartierDiv.prodKerGraph_comap_openProdMap c U xs
  refine ⟨index, xs, hA, ?_, hIopen, ?_⟩
  · intro a
    simp only [xs, xu, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  · exact supportedDivisorSum_evaluate_tuple c U s.universal s.tupleMap
      s.tupleMap_toBase s.tuple_ideal (commGroupRelativeLaw G) q s.sum s.tuple_sum
      t xs A hA hIopen

private def boundaryScalarPointMap
    {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K B))
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext f.comp_algebraMap))

private theorem boundaryPointEquiv_sumList
    {K : Type u} [Field K] (G : CommGrp (Over (Spec (.of K))))
    {T : Scheme.{u}} (t : T ⟶ Spec (.of K))
    (xs : List (SchemeHomOver t G.X.hom)) :
    commGroupPointEquiv G t ((commGroupRelativeLaw G).sumList t xs) =
      (xs.map (commGroupPointEquiv G t)).prod := by
  induction xs with
  | nil => exact (commGroupPointEquiv G t).apply_symm_apply 1
  | cons x xs ih =>
      rw [RelativeGroupLaw.sumList_cons]
      change commGroupPointEquiv G t
        ((commGroupPointEquiv G t).symm
          (commGroupPointEquiv G t x *
            commGroupPointEquiv G t ((commGroupRelativeLaw G).sumList t xs))) = _
      rw [(commGroupPointEquiv G t).apply_symm_apply, ih,
        List.map_cons, List.prod_cons]

/-- Evaluate the actual pulled-back Cartier block as the product of the
constructed finite-separable formal factors. The full tuple ideal and its
support are derived from the labelled completed fibre; no pointwise trace
identity is assumed. The original structure map `r` is retained literally. -/
theorem supportedDivisorSum_formal_completed_factors
    {K E L : Type u} [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    {C : Scheme.{u}} [IsIntegral C] [Algebra K C.functionField]
    (c : C ⟶ Spec (.of K)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (genericMap : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K C.functionField))) ⟶
      Over.mk (U.ι ≫ c))
    (hη : genericMap.left ≫ U.ι = C.fromSpecStalk (genericPoint C))
    {m : ℕ} (r : Spec (.of E) ⟶ Spec (.of K)) (D : RelEffCartierDiv c m r)
    {I : Type u} [Fintype I] (F : I → Type u)
    [∀ i, Field (F i)] [∀ i, Algebra K (F i)] [∀ i, Algebra E (F i)]
    [∀ i, IsScalarTower K E (F i)]
    [∀ i, FiniteDimensional E (F i)] [∀ i, Algebra.IsSeparable E (F i)]
    (n : I → ℕ) (hn : ∀ i, Module.finrank E (F i) = n i)
    (embeddings : ∀ i, Fin (n i) → F i →ₐ[E] L) (hι : ∀ i, Function.Injective (embeddings i))
    (j : ∀ i, C.functionField →ₐ[K] F i)
    (e : (∐ fun i : I => Spec (.of (F i))) ≅ D.I.subscheme)
    (hbase : e.hom ≫ D.I.subschemeι ≫ pullback.snd c r =
      Sigma.desc (fun i : I => Spec.map (CommRingCat.ofHom (algebraMap E (F i)))))
    (hsource : ∀ i : I,
      Sigma.ι (fun i : I => Spec (.of (F i))) i ≫ e.hom ≫ D.I.subschemeι ≫
        pullback.fst c r =
      Spec.map (CommRingCat.ofHom (j i).toRingHom) ≫ C.fromSpecStalk (genericPoint C))
    (G : CommGrp (Over (Spec (.of K))))
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom)
    (s : OpenCurveSum c U (commGroupRelativeLaw G) q m)
    (τ : E →ₐ[K] PowerSeries L)
    (hτ : PowerSeries.constantCoeff.comp τ.toRingHom = algebraMap E L)
    (hstructure : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ r =
      Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries L)))) :
    let t := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries L)))
    let f := Spec.map (CommRingCat.ofHom τ.toRingHom)
    let A := D.pullbackAlong f hstructure
    let x := genericMap ≫ commGroupPointEquiv G (U.ι ≫ c) q
    ∃ hA : A.SupportedIn U,
      commGroupPointEquiv G t (supportedDivisorSum c U s.universal s.sum A hA) =
        ∏ a : Σ i, Fin (n i),
          boundaryScalarPointMap
            ((PowerSeries.formalEmbeddingLiftAlgHom τ hτ
              (embeddings a.1 a.2)).comp (j a.1)) ≫ x := by
  classical
  intro t f A x
  obtain ⟨index, xs, hA, hxs, _hI, hsum⟩ :=
    formal_boundary_block_tuple_and_sum c U hU r D F n hn embeddings hι
      (fun i => (j i).toRingHom) e hbase hsource G q s τ.toRingHom hτ hstructure
  refine ⟨hA, ?_⟩
  rw [hsum, boundaryPointEquiv_sumList]
  simp only [List.map_ofFn, List.prod_ofFn]
  apply Fintype.prod_equiv index
  intro a
  apply Over.OverMorphism.ext
  change (xs a).val ≫ q.val = _ ≫ genericMap.left ≫ q.val
  have hx : (xs a).val =
      Spec.map (CommRingCat.ofHom
        ((PowerSeries.formalEmbeddingLiftAlgHom τ hτ
          (embeddings (index a).1 (index a).2)).comp (j (index a).1)).toRingHom) ≫
        genericMap.left := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, hη]
    exact hxs a
  rw [hx, Category.assoc]
  rfl

private theorem formalEmbeddingLift_constant
    {E F L : Type u} [Field E] [Field F] [Field L]
    [Algebra E F] [Algebra E L] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (embeddings : F →ₐ[E] L) :
    let τ : E →+* PowerSeries L := PowerSeries.C.comp (algebraMap E L)
    let hτ : PowerSeries.constantCoeff.comp τ = algebraMap E L := by
      ext a
      exact PowerSeries.constantCoeff_C _
    PowerSeries.formalEmbeddingLift τ hτ embeddings = PowerSeries.C.comp embeddings.toRingHom := by
  intro τ hτ
  have hres : PowerSeries.constantCoeff.comp τ =
      embeddings.toRingHom.comp (algebraMap E F) := by
    rw [hτ]
    exact embeddings.comp_algebraMap.symm
  have hc : (PowerSeries.C.comp embeddings.toRingHom).comp (algebraMap E F) = τ ∧
      PowerSeries.constantCoeff.comp (PowerSeries.C.comp embeddings.toRingHom) =
        embeddings.toRingHom := by
    constructor
    · apply RingHom.ext
      intro a
      exact congrArg PowerSeries.C (embeddings.commutes a)
    · ext a
      exact PowerSeries.constantCoeff_C _
  exact (PowerSeries.existsUnique_formalLift_finiteSeparable_embedding
    embeddings.toRingHom τ hres).unique
      (PowerSeries.formalEmbeddingLift_spec τ hτ embeddings) hc

private theorem boundaryScalarPointMap_comp
    {K A B C : Type u} [CommRing K] [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    boundaryScalarPointMap (g.comp f) =
      boundaryScalarPointMap g ≫ boundaryScalarPointMap f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (g.comp f).toRingHom) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
  rw [← Spec.map_comp]
  rfl

private theorem boundary_diagonalDifference_evaluation
    {K F L : Type u} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L]
    (G : CommGrp (Over (Spec (.of K))))
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X)
    (i : F →ₐ[K] L) (θ : F →ₐ[K] PowerSeries L) :
    Spec.map (CommRingCat.ofHom (PowerSeries.diagonalTensorMapAlong i θ).toRingHom) ≫
      GroupDiagonal.diagonalDifference x =
        ((boundaryScalarPointMap θ ≫ x) *
          (boundaryScalarPointMap
            ((IsScalarTower.toAlgHom K L (PowerSeries L)).comp i) ≫ x)⁻¹).left := by
  let d := boundaryScalarPointMap (PowerSeries.diagonalTensorMapAlong i θ)
  let l := boundaryScalarPointMap
    (Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] F)
  let r := boundaryScalarPointMap
    (Algebra.TensorProduct.includeRight : F →ₐ[K] F ⊗[K] F)
  have hl : d ≫ l = boundaryScalarPointMap θ := by
    rw [← boundaryScalarPointMap_comp]
    congr 1
    exact Algebra.TensorProduct.productMap_left _ _
  have hr : d ≫ r =
      boundaryScalarPointMap ((IsScalarTower.toAlgHom K L (PowerSeries L)).comp i) := by
    rw [← boundaryScalarPointMap_comp]
    congr 1
    exact Algebra.TensorProduct.productMap_right _ _
  change (d ≫ ((l ≫ x) * (r ≫ x)⁻¹)).left = _
  rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, hl, hr]

private def boundaryPrecompHom
    {K : Type u} [Field K] (G : CommGrp (Over (Spec (.of K))))
    {A B : Over (Spec (.of K))} (f : A ⟶ B) : (B ⟶ G.X) →* (A ⟶ G.X) where
  toFun p := f ≫ p
  map_one' := MonObj.comp_one f
  map_mul' p q := MonObj.comp_mul f p q

private theorem laurent_coefficient_tower
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    [Algebra E (LaurentSeries K)] [IsScalarTower K E (LaurentSeries K)] :
    @IsScalarTower K E (LaurentSeries K)
      (inferInstance : Algebra K E).toSMul
      (inferInstance : Algebra E (LaurentSeries K)).toSMul
      (inferInstance : Algebra K (LaurentSeries K)).toSMul := by
  refine @IsScalarTower.mk K E (LaurentSeries K)
    (inferInstance : Algebra K E).toSMul
    (inferInstance : Algebra E (LaurentSeries K)).toSMul
    (inferInstance : Algebra K (LaurentSeries K)).toSMul ?_
  intro a b f
  change (a • b) • f = algebraMap K (LaurentSeries K) a * (b • f)
  change (a • b) • f = HahnSeries.ofPowerSeries ℤ K (PowerSeries.C a) * (b • f)
  rw [HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]
  exact smul_assoc a b f

/-- Constant coefficients in the completed boundary calculation, retaining
its native Laurent coefficient algebra and the given completed-base tower. -/
noncomputable def completedBoundaryConstantMap
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    [Algebra E (LaurentSeries K)] [tower : IsScalarTower K E (LaurentSeries K)] :
    E →ₐ[K] PowerSeries (LaurentSeries K) :=
  let _ := laurent_coefficient_tower (K := K) (E := E)
  (IsScalarTower.toAlgHom K (LaurentSeries K) (PowerSeries (LaurentSeries K))).comp
    (IsScalarTower.toAlgHom K E (LaurentSeries K))

/-- A single divisor bounds the actual formal difference of every completed
boundary block. The block's full ideal, all formal lifts, both pulled-back
sums, and the integral group point are computed. The normalized completed
embeddings are retained as labelled factors; no integral trace or tuple
identity is an input. This calculation is applied to the completed block
constructed from the original finite curve morphism. -/
theorem exists_completedBoundaryBlock_uniform_integral_difference
    {K : Type u} [Field K] [PerfectField K]
    {C : Scheme.{u}} [IsIntegral C] [Algebra K C.functionField]
    [Algebra.EssFiniteType K C.functionField] [AlgebraicCurve.IsCurveOver K C.functionField]
    (c : C ⟶ Spec (.of K)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (genericMap : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K C.functionField))) ⟶
      Over.mk (U.ι ≫ c))
    (hη : genericMap.left ≫ U.ι = C.fromSpecStalk (genericPoint C))
    (G : CommGrp (Over (Spec (.of K)))) [LocallyOfFiniteType G.X.hom]
    (q : SchemeHomOver (U.ι ≫ c) G.X.hom)
    (V : G.X.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G.X).left ⊆ V) :
    ∃ t : C.functionField, Transcendental K t ∧
      ∃ Dpole : AlgebraicCurve.Modulus K C.functionField,
    ∀ (E : Type u) [Field E] [Algebra K E]
      [Algebra E (LaurentSeries K)] [towerKEL : IsScalarTower K E (LaurentSeries K)],
      let _ := laurent_coefficient_tower (K := K) (E := E)
      ∀ (m : ℕ) (r : Spec (.of E) ⟶ Spec (.of K)) (D : RelEffCartierDiv c m r)
      (I : Type u) [Fintype I] (F : I → Type u)
      [∀ i, Field (F i)] [∀ i, Algebra K (F i)] [∀ i, Algebra E (F i)]
      [∀ i, IsScalarTower K E (F i)]
      [∀ i, FiniteDimensional E (F i)] [∀ i, Algebra.IsSeparable E (F i)]
      (n : I → ℕ) (_ : ∀ i, Module.finrank E (F i) = n i)
      (embeddings : ∀ i, Fin (n i) → F i →ₐ[E] LaurentSeries K)
      (_ : ∀ i, Function.Injective (embeddings i))
      (j : ∀ i, C.functionField →ₐ[K] F i)
      (d : (∐ fun i : I => Spec (.of (F i))) ≅ D.I.subscheme)
      (_ : d.hom ≫ D.I.subschemeι ≫ pullback.snd c r =
        Sigma.desc (fun i : I => Spec.map (CommRingCat.ofHom (algebraMap E (F i)))))
      (_ : ∀ i : I,
        Sigma.ι (fun i : I => Spec (.of (F i))) i ≫ d.hom ≫ D.I.subschemeι ≫
          pullback.fst c r =
        Spec.map (CommRingCat.ofHom (j i).toRingHom) ≫ C.fromSpecStalk (genericPoint C))
      (s : OpenCurveSum c U (commGroupRelativeLaw G) q m)
      (τ : E →ₐ[K] PowerSeries (LaurentSeries K))
      (_ : PowerSeries.constantCoeff.comp τ.toRingHom = algebraMap E (LaurentSeries K)),
      let τ₀ : E →ₐ[K] PowerSeries (LaurentSeries K) :=
        completedBoundaryConstantMap (K := K) (E := E) (tower := towerKEL)
      ∀ (hstructure : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ r =
          Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries (LaurentSeries K)))))
        (hstructure₀ : Spec.map (CommRingCat.ofHom τ₀.toRingHom) ≫ r =
          Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries (LaurentSeries K)))))
        (v : I → AlgebraicCurve.Place K C.functionField),
        (∀ i a f, (embeddings i a (j i f)).order = (v i).ord f) →
      ∀ (g : C.functionFieldˣ) (e : ℕ), 0 < e → (e : K) ≠ 0 →
        (∀ i, (v i).ord ((g : C.functionField) - 1) = (e : ℤ)) →
        (∀ i a, embeddings i a (j i ((g : C.functionField) - 1)) =
          HahnSeries.single (e : ℤ) (1 : K)) →
        (∀ i, let cc : ℤ := max 1 (2 * (Dpole (v i) : ℤ))
          cc - min ((v i).ord t) cc < (e : ℤ)) →
      ∀ z : E,
        (∀ i, j i (((g : C.functionField) - 1)⁻¹) = algebraMap E (F i) z) →
        τ z = PowerSeries.C (algebraMap E (LaurentSeries K) z) + PowerSeries.X →
      let A := D.pullbackAlong (Spec.map (CommRingCat.ofHom τ.toRingHom)) hstructure
      let A₀ := D.pullbackAlong (Spec.map (CommRingCat.ofHom τ₀.toRingHom)) hstructure₀
      let O := (LaurentSeries.orderPlace (K := K)).toValuationSubring
      let tL := Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries (LaurentSeries K))))
      ∃ (hA : A.SupportedIn U) (hA₀ : A₀.SupportedIn U)
        (pB : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries O)))) ⟶ G.X),
        Spec.map (CommRingCat.ofHom (PowerSeries.map O.subtype)) ≫ pB.left =
          (commGroupPointEquiv G tL (supportedDivisorSum c U s.universal s.sum A hA) *
            (commGroupPointEquiv G tL
              (supportedDivisorSum c U s.universal s.sum A₀ hA₀))⁻¹).left ∧
        Spec.map (CommRingCat.ofHom (PowerSeries.map (IsLocalRing.residue O))) ≫ pB.left =
          (1 : Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap K (PowerSeries (IsLocalRing.ResidueField O))))) ⟶ G.X).left := by
  classical
  let x := genericMap ≫ commGroupPointEquiv G (U.ι ≫ c) q
  obtain ⟨t, ht, Dpole, hlocal⟩ :=
    AlgebraicCurve.exists_groupFormalDifference_reciprocal_integral G.X x V hV hunit
  refine ⟨t, ht, Dpole, ?_⟩
  intro E fieldE algKE algEL towerKEL algebraTowerKEL m r D I finiteI F fieldF algKF algEF
    towerKEF finiteEF separableEF n hn embeddings hι j d hbase hsource s τ hτ τ₀
    hstructure hstructure₀ v horder g e hepos he hcontact hnormal hlarge z hjz hτz
    A A₀ O tL
  let θ (a : Σ i, Fin (n i)) :=
    (PowerSeries.formalEmbeddingLiftAlgHom τ hτ (embeddings a.1 a.2)).comp (j a.1)
  let iL (a : Σ i, Fin (n i)) := ((embeddings a.1 a.2).restrictScalars K).comp (j a.1)
  have hθ0 (a) : PowerSeries.constantCoeff.comp (θ a).toRingHom = (iL a).toRingHom :=
    PowerSeries.constantCoeff_formalEmbeddingLiftAlgHom_comp τ hτ (embeddings a.1 a.2) (j a.1)
  have hθz (a) : θ a (((g : C.functionField) - 1)⁻¹) =
      PowerSeries.C (iL a (((g : C.functionField) - 1)⁻¹)) + PowerSeries.X :=
    PowerSeries.formalEmbeddingLiftAlgHom_comp_reciprocal_shift τ hτ (embeddings a.1 a.2)
      (j a.1) _ z (hjz a.1) hτz
  have hex (a : Σ i, Fin (n i)) :
      ∃ p : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries O)))) ⟶ G.X,
        Spec.map (CommRingCat.ofHom (PowerSeries.map O.subtype)) ≫ p.left =
          Spec.map (CommRingCat.ofHom
            (PowerSeries.diagonalTensorMapAlong (iL a) (θ a)).toRingHom) ≫
              GroupDiagonal.diagonalDifference x ∧
        Spec.map (CommRingCat.ofHom (PowerSeries.map (IsLocalRing.residue O))) ≫ p.left =
          (1 : Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap K (PowerSeries (IsLocalRing.ResidueField O))))) ⟶ G.X).left := by
    obtain ⟨ρ, _hρ0, _hρz, hρunique, p, hp, hpred⟩ :=
      hlocal (v a.1) (iL a) (horder a.1 a.2) g e hepos he
        (hcontact a.1) (hnormal a.1 a.2) (hlarge a.1)
    have hθ : θ a = ρ := hρunique (θ a) (hθ0 a) (hθz a)
    rw [hθ]
    exact ⟨p, hp, hpred⟩
  choose p hp hpred using hex
  obtain ⟨hA, hsum⟩ := supportedDivisorSum_formal_completed_factors c U hU genericMap hη
    r D F n hn embeddings hι j d hbase hsource G q s τ hτ hstructure
  have hτ₀ : PowerSeries.constantCoeff.comp τ₀.toRingHom =
      algebraMap E (LaurentSeries K) := by
    ext a
    exact PowerSeries.constantCoeff_C _
  obtain ⟨hA₀, hsum₀⟩ := supportedDivisorSum_formal_completed_factors c U hU genericMap hη
    r D F n hn embeddings hι j d hbase hsource G q s τ₀ hτ₀ hstructure₀
  have hconstant (a : Σ i, Fin (n i)) :
      (PowerSeries.formalEmbeddingLiftAlgHom τ₀ hτ₀ (embeddings a.1 a.2)).comp (j a.1) =
        (IsScalarTower.toAlgHom K (LaurentSeries K) (PowerSeries (LaurentSeries K))).comp
          (iL a) := by
    apply AlgHom.ext
    intro f
    exact RingHom.congr_fun (formalEmbeddingLift_constant (embeddings a.1 a.2)) (j a.1 f)
  let inc : O →ₐ[K] LaurentSeries K :=
    { toRingHom := O.subtype
      commutes' _ := rfl }
  let red : O →ₐ[K] IsLocalRing.ResidueField O :=
    IsScalarTower.toAlgHom K O (IsLocalRing.ResidueField O)
  let fInc := boundaryScalarPointMap (PowerSeries.mapAlgHom inc)
  let fRed := boundaryScalarPointMap (PowerSeries.mapAlgHom red)
  have hp' (a : Σ i, Fin (n i)) : fInc ≫ p a =
      (boundaryScalarPointMap (θ a) ≫ x) *
        (boundaryScalarPointMap
          ((IsScalarTower.toAlgHom K (LaurentSeries K)
            (PowerSeries (LaurentSeries K))).comp (iL a)) ≫ x)⁻¹ := by
    apply Over.OverMorphism.ext
    exact (hp a).trans (boundary_diagonalDifference_evaluation G x (iL a) (θ a))
  have hpred' (a) : fRed ≫ p a = 1 := by
    apply Over.OverMorphism.ext
    exact hpred a
  let pB := ∏ a, p a
  refine ⟨hA, hA₀, pB, ?_, ?_⟩
  · have hpoint : fInc ≫ pB =
        commGroupPointEquiv G tL (supportedDivisorSum c U s.universal s.sum A hA) *
          (commGroupPointEquiv G tL
            (supportedDivisorSum c U s.universal s.sum A₀ hA₀))⁻¹ := by
      change boundaryPrecompHom G fInc (∏ a, p a) = _
      rw [map_prod]
      change (∏ a, fInc ≫ p a) = _
      simp_rw [hp']
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hsum, hsum₀]
      simp only [hconstant]
      rfl
    exact congrArg (fun f => f.left) hpoint
  · have hpoint : fRed ≫ pB = 1 := by
      change boundaryPrecompHom G fRed (∏ a, p a) = _
      rw [map_prod]
      change (∏ a, fRed ≫ p a) = 1
      simp only [hpred', Finset.prod_const_one]
    exact congrArg (fun f => f.left) hpoint

end JacobianVarieties.Albanese
