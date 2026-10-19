/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.OpenCurveSumChoice
import Nyll.JacobianVarieties.Albanese.DivisorSumEvaluation
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.SplittingCover
import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.ProdKerGraphComapMapOnProdOver
import Nyll.SchemeTheory.Sheaves.IdealSheafComap
import Mathlib.Data.List.OfFn

/-!
# Additivity of the actual regular divisor sum

Successive actual finite flat splitting covers split the two families
simultaneously. The full Cartier product becomes concatenation of the two
section tuples. Tuple evaluation and the epimorphism supplied by the flat
surjective cover then prove additivity on the original test scheme.
This retains multiplicities and works over nonreduced bases.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Albanese

private theorem prodKerGraph_append
    {C S T : Scheme.{u}} (c : C ⟶ S) {t : T ⟶ S} {m n : ℕ}
    (xs : Fin m → SchemeHomOver t c) (ys : Fin n → SchemeHomOver t c) :
    prodKerGraph c (fun i => (Fin.append xs ys i).val)
        (fun i => (Fin.append xs ys i).property) =
      prodKerGraph c (fun i => (xs i).val) (fun i => (xs i).property) *
      prodKerGraph c (fun i => (ys i).val) (fun i => (ys i).property) := by
  classical
  simp only [prodKerGraph, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-- Full Cartier addition is evaluated by group multiplication, for any
of the actual represented regular sum maps and every test scheme. -/
theorem supportedDivisorSum_mul
    {K : Type u} [Field K] {C B : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (U : C.Opens)
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    {b : B ⟶ Spec (.of K)} (G : RelativeGroupLaw K b)
    (q : SchemeHomOver (U.ι ≫ c) b) {m n : ℕ}
    (s : OpenCurveSum c U G q (m + n))
    (s₀ : OpenCurveSum c U G q m) (s₁ : OpenCurveSum c U G q n)
    {T : Scheme.{u}} {t : T ⟶ Spec (.of K)}
    (D : RelEffCartierDiv c (m + n) t)
    (D₀ : RelEffCartierDiv c m t) (D₁ : RelEffCartierDiv c n t)
    (hD : D.SupportedIn U) (hD₀ : D₀.SupportedIn U) (hD₁ : D₁.SupportedIn U)
    (hI : D.I = D₀.I * D₁.I) :
    supportedDivisorSum c U s.universal s.sum D hD =
      G.mul t (supportedDivisorSum c U s₀.universal s₀.sum D₀ hD₀)
        (supportedDivisorSum c U s₁.universal s₁.sum D₁ hD₁) := by
  have : SmoothOfRelativeDimension 1 (U.ι ≫ c) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ c))
  let A₀ := D₀.restrictToOpen c U hD₀
  let A₁ := D₁.restrictToOpen c U hD₁
  obtain ⟨P, tP, p, hp, x, hx, _, hpflat, _, hpsurj, _, hIx, _⟩ := A₀.exists_split
  have : Flat p := hpflat
  have : Surjective p := hpsurj
  obtain ⟨Q, tQ, r, hr, y, hy, _, hrflat, _, hrsurj, _, hIy, _⟩ :=
    (A₁.pullbackAlong p hp).exists_split
  have : Flat r := hrflat
  have : Surjective r := hrsurj
  let f : Q ⟶ T := r ≫ p
  have hf : f ≫ t = tQ := by
    change (r ≫ p) ≫ t = tQ
    rw [Category.assoc, hp, hr]
  have : Epi f := Flat.epi_of_flat_of_surjective f
  let xs : Fin m → SchemeHomOver tQ (U.ι ≫ c) := fun i =>
    ⟨r ≫ x i, by rw [Category.assoc, hx, hr]⟩
  let ys : Fin n → SchemeHomOver tQ (U.ι ≫ c) := fun i => ⟨y i, hy i⟩
  let zs : Fin (m + n) → SchemeHomOver tQ (U.ι ≫ c) := Fin.append xs ys
  have hxs :
      ((D₀.pullbackAlong f hf).restrictToOpen c U (hD₀.pullbackAlong f hf)).I =
        prodKerGraph (U.ι ≫ c) (fun i => (xs i).val) (fun i => (xs i).property) := by
    rw [RelEffCartierDiv.restrictToOpen_pullbackAlong]
    change (A₀.pullbackAlong f hf).I = _
    rw [← A₀.pullbackAlong_comp p hp r hr]
    change (A₀.pullbackAlong p hp).I.comap (mapOnProdOver (U.ι ≫ c) r hr) = _
    rw [hIx]
    exact prodKerGraph_comap_mapOnProdOver x hx r hr
  have hys :
      ((D₁.pullbackAlong f hf).restrictToOpen c U (hD₁.pullbackAlong f hf)).I =
        prodKerGraph (U.ι ≫ c) (fun i => (ys i).val) (fun i => (ys i).property) := by
    rw [RelEffCartierDiv.restrictToOpen_pullbackAlong]
    change (A₁.pullbackAlong f hf).I = _
    rw [← A₁.pullbackAlong_comp p hp r hr]
    exact hIy
  have hmul :
      ((D.pullbackAlong f hf).restrictToOpen c U (hD.pullbackAlong f hf)).I =
        ((D₀.pullbackAlong f hf).restrictToOpen c U (hD₀.pullbackAlong f hf)).I *
        ((D₁.pullbackAlong f hf).restrictToOpen c U (hD₁.pullbackAlong f hf)).I := by
    change (D.I.comap (mapOnProdOver c f hf)).comap (RelEffCartierDiv.openProdMap c U tQ) =
      (D₀.I.comap (mapOnProdOver c f hf)).comap (RelEffCartierDiv.openProdMap c U tQ) *
      (D₁.I.comap (mapOnProdOver c f hf)).comap (RelEffCartierDiv.openProdMap c U tQ)
    rw [hI, Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_mul]
  have hzs :
      ((D.pullbackAlong f hf).restrictToOpen c U (hD.pullbackAlong f hf)).I =
        prodKerGraph (U.ι ≫ c) (fun i => (zs i).val) (fun i => (zs i).property) := by
    rw [hmul, hxs, hys]
    exact (prodKerGraph_append (U.ι ≫ c) xs ys).symm
  have he := supportedDivisorSum_evaluate_tuple c U s.universal s.tupleMap
    s.tupleMap_toBase s.tuple_ideal G q s.sum s.tuple_sum tQ zs
    (D.pullbackAlong f hf) (hD.pullbackAlong f hf) hzs
  have he₀ := supportedDivisorSum_evaluate_tuple c U s₀.universal s₀.tupleMap
    s₀.tupleMap_toBase s₀.tuple_ideal G q s₀.sum s₀.tuple_sum tQ xs
    (D₀.pullbackAlong f hf) (hD₀.pullbackAlong f hf) hxs
  have he₁ := supportedDivisorSum_evaluate_tuple c U s₁.universal s₁.tupleMap
    s₁.tupleMap_toBase s₁.tuple_ideal G q s₁.sum s₁.tuple_sum tQ ys
    (D₁.pullbackAlong f hf) (hD₁.pullbackAlong f hf) hys
  have hconcat :
      (fun i => NeronModelInfra.schemeHomOverComp (zs i) q) =
        Fin.append (fun i => NeronModelInfra.schemeHomOverComp (xs i) q)
          (fun i => NeronModelInfra.schemeHomOverComp (ys i) q) := by
    funext i
    exact Fin.addCases (fun j => by simp only [zs, Fin.append_left])
      (fun j => by simp only [zs, Fin.append_right]) i
  have hbase :
      GoodReductionJacobian.schemeHomOverComp f hf
          (supportedDivisorSum c U s.universal s.sum D hD) =
        GoodReductionJacobian.schemeHomOverComp f hf
          (G.mul t (supportedDivisorSum c U s₀.universal s₀.sum D₀ hD₀)
            (supportedDivisorSum c U s₁.universal s₁.sum D₁ hD₁)) := by
    rw [G.mul_natural, supportedDivisorSum_naturality,
      supportedDivisorSum_naturality, supportedDivisorSum_naturality,
      he, he₀, he₁, hconcat, List.ofFn_fin_append, G.sumList_append]
  apply Subtype.ext
  exact (cancel_epi f).mp (congrArg Subtype.val hbase)

end JacobianVarieties.Albanese
