/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.ChangeBase
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivSum
import Nyll.SchemeTheory.Sheaves.IdealSheafComap
import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.HomPullbackKerPowInvModuleIso

/-! # Full graph-product divisor ideals under an actual change of curve base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicCurves.Geometry.Schemes.Proofs
open Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry.BCKerGlue

namespace AlgebraicGeometry.RelEffCartierDiv

variable {C S S' T : Scheme.{u}} (c : C ⟶ S) (s : S' ⟶ S) (t : T ⟶ S')

/-- Projecting a point of the extended curve gives the same graph under the
canonical pullback associator. -/
theorem graphOver_changeBase_comp
    (p : SchemeHomOver t (pullback.snd c s)) :
    graphOver (pullback.snd c s) p.val p.property ≫
      (pullbackLeftPullbackSndIso c s t).hom =
        graphOver c (p.val ≫ pullback.fst c s)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc, p.property]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      graphOver_fst_assoc, graphOver_fst]
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      graphOver_snd]

/-- The complete graph ideal, rather than only its support, survives curve base change. -/
theorem graphOver_ker_comap_changeBase
    (p : SchemeHomOver t (pullback.snd c s)) :
    (graphOver (pullback.snd c s) p.val p.property).ker.comap
      (pullbackLeftPullbackSndIso c s t).inv =
        (graphOver c (p.val ≫ pullback.fst c s)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc, p.property])).ker := by
  apply ker_comap_eq_ker (pullbackLeftPullbackSndIso c s t).inv
  rw [← graphOver_changeBase_comp c s t p, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Scalar extension preserves full finite graph products, including repeated points. -/
theorem prodKerGraph_comap_changeBase {n : ℕ}
    (p : Fin n → SchemeHomOver t (pullback.snd c s)) :
    (prodKerGraph (pullback.snd c s) (fun j => (p j).val) (fun j => (p j).property)).comap
      (pullbackLeftPullbackSndIso c s t).inv =
        prodKerGraph c (fun j => (p j).val ≫ pullback.fst c s)
          (fun j => by
            rw [Category.assoc, pullback.condition, ← Category.assoc, (p j).property]) := by
  classical
  change (∏ j, (graphOver (pullback.snd c s) (p j).val (p j).property).ker).comap
      (pullbackLeftPullbackSndIso c s t).inv =
    ∏ j, (graphOver c ((p j).val ≫ pullback.fst c s) _).ker
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.comap_top]
  | insert j I hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj,
      Scheme.IdealSheafData.comap_mul, graphOver_ker_comap_changeBase, ih]

/-- An actual divisor tuple over the extended curve projects to a tuple for its
original-base family with exactly the same multiplicities. -/
theorem changeBaseEquiv_I_eq_prodKerGraph {n : ℕ}
    (E : RelEffCartierDiv (pullback.snd c s) n t)
    (p : Fin n → SchemeHomOver t (pullback.snd c s))
    (hp : E.I = prodKerGraph (pullback.snd c s) (fun j => (p j).val)
      (fun j => (p j).property)) :
    (changeBaseEquiv c s t n E).I =
      prodKerGraph c (fun j => (p j).val ≫ pullback.fst c s)
        (fun j => by
          rw [Category.assoc, pullback.condition, ← Category.assoc, (p j).property]) := by
  rw [changeBaseEquiv_ideal, hp, prodKerGraph_comap_changeBase]

end AlgebraicGeometry.RelEffCartierDiv
