/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.Support.SourceOpenRestriction
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.IEqProdKerGraphAlgClosed
import Nyll.SchemeTheory.Sheaves.IdealSheafComap
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.SchemeTheory.Divisors.LocalComplement
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # One geometric tuple for a supported divisor and its open restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace AlgebraicGeometry.RelEffCartierDiv

variable {C S T : Scheme.{u}} (c : C ⟶ S) (U : C.Opens) [IsSeparated c]
  {t : T ⟶ S}

/-- The graph in the open curve is the actual inverse image of the original graph. -/
theorem graphOver_ker_comap_openProdMap (x : SchemeHomOver t (U.ι ≫ c)) :
    (graphOver c (x.val ≫ U.ι) (by rw [Category.assoc, x.property])).ker.comap
        (openProdMap c U t) = (graphOver (U.ι ≫ c) x.val x.property).ker := by
  have hcomp : graphOver (U.ι ≫ c) x.val x.property ≫ openProdMap c U t =
      graphOver c (x.val ≫ U.ι) (by rw [Category.assoc, x.property]) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, openProdMap_fst, graphOver_fst_assoc, graphOver_fst]
    · simp only [Category.assoc, openProdMap_snd, graphOver_snd]
  have hs : IsPullback (graphOver (U.ι ≫ c) x.val x.property) (𝟙 T)
      (openProdMap c U t)
      (graphOver c (x.val ≫ U.ι) (by rw [Category.assoc, x.property])) := by
    apply IsPullback.flip
    exact IsPullback.of_horiz_isIso_mono ⟨(Category.id_comp _).trans hcomp.symm⟩
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← hs.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- Restriction preserves the full graph-product ideal, including repeated points. -/
theorem prodKerGraph_comap_openProdMap {n : ℕ}
    (xs : Fin n → SchemeHomOver t (U.ι ≫ c)) :
    (prodKerGraph c (fun j => (xs j).val ≫ U.ι)
        (fun j => by rw [Category.assoc, (xs j).property])).comap (openProdMap c U t) =
      prodKerGraph (U.ι ≫ c) (fun j => (xs j).val) (fun j => (xs j).property) := by
  classical
  change (∏ j, (graphOver c ((xs j).val ≫ U.ι) _).ker).comap (openProdMap c U t) =
    ∏ j, (graphOver (U.ι ≫ c) (xs j).val (xs j).property).ker
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.comap_top]
  | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj,
        Scheme.IdealSheafData.comap_mul, graphOver_ker_comap_openProdMap, ih]

/-- Over a geometric field, the same tuple on the open curve represents both full ideals. -/
theorem exists_supported_geometric_tuple [SmoothOfRelativeDimension 1 c]
    {L : Type u} [Field L] [IsAlgClosed L]
    {t : Spec (CommRingCat.of L) ⟶ S} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn U) :
    ∃ xs : Fin n → SchemeHomOver t (U.ι ≫ c),
      E.I = prodKerGraph c (fun j => (xs j).val ≫ U.ι)
        (fun j => by rw [Category.assoc, (xs j).property]) ∧
      (E.restrictToOpen c U hE).I =
        prodKerGraph (U.ι ≫ c) (fun j => (xs j).val) (fun j => (xs j).property) := by
  classical
  obtain ⟨a, ha, hI⟩ := E.exists_I_eq_prodKerGraph_of_isAlgClosed
  have haU : ∀ j, Set.range (a j) ⊆ Set.range U.ι := by
    intro j y hy
    obtain ⟨z, rfl⟩ := hy
    rw [Scheme.Opens.range_ι]
    have hs : (graphOver c (a j) (ha j)).ker.support ≤ E.I.support := by
      rw [hI, prodKerGraph_eq_prod, Scheme.IdealSheafData.support_finset_prod]
      exact Finset.le_sup (f := fun k => (graphOver c (a k) (ha k)).ker.support)
        (Finset.mem_univ j)
    have hz := hE (hs ((graphOver c (a j) (ha j)).range_subset_ker_support
      (Set.mem_range_self z)))
    change pullback.fst c t (graphOver c (a j) (ha j) z) ∈ U at hz
    rwa [← Scheme.Hom.comp_apply, graphOver_fst] at hz
  let xs : Fin n → SchemeHomOver t (U.ι ≫ c) := fun j =>
    ⟨IsOpenImmersion.lift U.ι (a j) (haU j), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac, ha]⟩
  have hfull : E.I = prodKerGraph c (fun j => (xs j).val ≫ U.ι)
      (fun j => by rw [Category.assoc, (xs j).property]) := by
    dsimp only [xs]
    simpa only [IsOpenImmersion.lift_fac] using hI
  refine ⟨xs, hfull, ?_⟩
  rw [restrictToOpen_I, hfull, prodKerGraph_comap_openProdMap]

end AlgebraicGeometry.RelEffCartierDiv
