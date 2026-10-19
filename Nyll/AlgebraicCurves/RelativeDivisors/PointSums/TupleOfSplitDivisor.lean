/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivSum
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Ideal.Operations

/-! # Actual sections and Cartier ideals from a split divisor scheme

The components of a coproduct decomposition of the divisor subscheme are
constructed as sections. Their disjoint closed images give coprime graph
ideals, whose product is the original full Cartier ideal over any test scheme.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace AlgebraicGeometry.RelEffCartierDiv

/-- The components of a coproduct splitting give the complete Cartier tuple.
The displayed section formula retains the labels supplied by the splitting. -/
theorem exists_tuple_of_coprod_iso
    {C S T : Scheme.{u}} {c : C ⟶ S} [IsSeparated c] {t : T ⟶ S} {n : ℕ}
    (D : RelEffCartierDiv c n t)
    (e : (∐ fun _ : Fin n => T) ≅ D.I.subscheme)
    (he : e.hom ≫ D.I.subschemeι ≫ pullback.snd c t =
      Sigma.desc (fun _ : Fin n => 𝟙 T)) :
    ∃ xs : Fin n → SchemeHomOver t c,
      (∀ i, (xs i).val = Sigma.ι (fun _ : Fin n => T) i ≫
        e.hom ≫ D.I.subschemeι ≫ pullback.fst c t) ∧
      D.I = prodKerGraph c (fun i => (xs i).val) (fun i => (xs i).property) := by
  classical
  let j : (∐ fun _ : Fin n => T) ⟶ pullback c t := e.hom ≫ D.I.subschemeι
  have : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (e.hom ≫ D.I.subschemeι))
  have hj : j ≫ pullback.snd c t = Sigma.desc (fun _ : Fin n => 𝟙 T) := by
    simpa only [j, Category.assoc] using he
  have hs (i : Fin n) :
      (Sigma.ι (fun _ : Fin n => T) i ≫ j) ≫ pullback.snd c t = 𝟙 T := by
    rw [Category.assoc, hj, Sigma.ι_comp_desc]
  let a (i : Fin n) : T ⟶ C :=
    (Sigma.ι (fun _ : Fin n => T) i ≫ j) ≫ pullback.fst c t
  have ha (i : Fin n) : a i ≫ c = t := by
    dsimp only [a]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  have hgraph (i : Fin n) : graphOver c (a i) (ha i) =
      Sigma.ι (fun _ : Fin n => T) i ≫ j := by
    apply pullback.hom_ext
    · exact graphOver_fst c (a i) (ha i)
    · rw [graphOver_snd, hs]
  have hsupport (i : Fin n) :
      ((graphOver c (a i) (ha i)).ker.support : Set ↥(pullback c t)) =
        Set.range (Sigma.ι (fun _ : Fin n => T) i ≫ j) := by
    rw [Scheme.Hom.support_ker,
      (Scheme.Hom.isClosedEmbedding (graphOver c (a i) (ha i))).isClosed_range.closure_eq,
      hgraph]
  have hcoprime (U : (pullback c t).affineOpens) (i k : Fin n) (hik : i ≠ k) :
      IsCoprime ((graphOver c (a i) (ha i)).ker.ideal U)
        ((graphOver c (a k) (ha k)).ker.ideal U) := by
    have hsup : (graphOver c (a i) (ha i)).ker ⊔
        (graphOver c (a k) (ha k)).ker = ⊤ := by
      apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
      rw [Scheme.IdealSheafData.support_sup]
      apply SetLike.coe_injective
      change (((graphOver c (a i) (ha i)).ker.support : Set ↥(pullback c t)) ∩
        ((graphOver c (a k) (ha k)).ker.support : Set ↥(pullback c t))) = ∅
      rw [hsupport, hsupport]
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hxy : j (Sigma.ι (fun _ : Fin n => T) i x) =
          j (Sigma.ι (fun _ : Fin n => T) k y) := by
        simpa only [Scheme.Hom.comp_apply] using hx.trans hy.symm
      have hι := j.isClosedEmbedding.injective hxy
      exact hik (congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin n => T) i k x y).mp hι))
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact congrArg (fun I : (pullback c t).IdealSheafData => I.ideal U) hsup
  have hI : D.I = prodKerGraph c a ha := by
    apply Scheme.IdealSheafData.ext
    funext U
    rw [ideal_prodKerGraph]
    have hprod : (∏ i, (graphOver c (a i) (ha i)).ker.ideal U) =
        ⨅ i, (graphOver c (a i) (ha i)).ker.ideal U := by
      simpa only [Finset.mem_univ, iInf_true] using
        (Ideal.prod_eq_iInf_of_pairwise_isCoprime
          (s := Finset.univ) (J := fun i => (graphOver c (a i) (ha i)).ker.ideal U)
          (fun i _ k _ hik => hcoprime U i k hik))
    rw [hprod]
    have hk : j.ker = D.I := by
      exact (Scheme.Hom.ker_comp_of_isIso e.hom D.I.subschemeι).trans D.I.ker_subschemeι
    have hcover : j.ker.ideal U =
        ⨅ i : Fin n, (Sigma.ι (fun _ : Fin n => T) i ≫ j).ker.ideal U :=
      (j.iInf_ker_openCover_map_comp_apply (sigmaOpenCover (fun _ : Fin n => T)) U).symm
    rw [← hk, hcover]
    apply congrArg iInf
    funext i
    rw [hgraph]
  refine ⟨fun i => ⟨a i, ha i⟩, ?_, hI⟩
  intro i
  simp only [a, j, Category.assoc]

end AlgebraicGeometry.RelEffCartierDiv
