/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RationalFunctionTracePrincipalDivisor
import Nyll.AlgebraicCurves.Geometry.Projective.ProjectiveLineGroupConstancy
import Nyll.JacobianVarieties.Generalized.ModulusEmptyRegularMap
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncModel
import Nyll.AlgebraicCurves.Models.Points.IsoCompToBaseEqPlaceOfPointCongrEq
import Nyll.AlgebraicCurves.Models.Points.InfinitePlace

/-! # Whole-curve maps to separated commutative groups have zero modulus

The actual rational-function trace on the entire curve has no missing
fibres. Constancy on the projective line therefore annihilates every full
principal-divisor evaluation. No extension of a trace across the boundary
of a proper open curve is assumed here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.GeneralizedJacobian NeronModelInfra GoodReductionJacobian
open scoped BigOperators CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.GeneralizedJacobian

/-- When the original map is defined everywhere, the actual graph-family
trace excludes no target point. -/
theorem finiteMapTraceLocus_top
    {K : Type u} [Field K] {C B : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (b : B ⟶ Spec (CommRingCat.of K))
    [IsSeparated b] (π : C ⟶ B) (hπ : π ≫ b = c)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y : B, π.finrank y = n) :
    finiteMapTraceLocus c b π hπ n hn ⊤ = ⊤ := by
  apply top_unique
  intro y _
  exact (mem_finiteMapTraceLocus_iff c b π hπ n hn ⊤ y).mpr (fun _ _ => trivial)

end AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private theorem exists_eq_const_ratFuncModel
    {K : Type u} [Field K] (P : CurveModel K (RatFunc K))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver P.toBase G.X.hom) :
    ∃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) G.X.hom,
      q.1 = P.toBase ≫ a.1 := by
  let P₀ := ProjSpace.projectiveLineRatFuncModel K
  obtain ⟨e, he, _⟩ := exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
    (AlgEquiv.refl : RatFunc K ≃ₐ[K] RatFunc K) P₀ P
  have hqP : (e.hom ≫ q.1) ≫ G.X.hom = P₀.toBase :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => e.hom ≫ f) q.2).trans he)
  obtain ⟨a, ha, hq⟩ := exists_eq_const_of_projectiveLine_group K G.X
    (e.hom ≫ q.1) (hqP.trans (ProjSpace.projectiveLineRatFuncModel_toBase K))
  refine ⟨⟨a, ha⟩, ?_⟩
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, he]
  exact hq

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F)

/-- A whole-curve map to any separated commutative group annihilates every
principal divisor, with no properness assumption on the target. -/
theorem zero_hasModulus_of_separated_group
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : Over.mk M.toBase ⟶ G.X) :
    (0 : Modulus K F).HasModulus (fun w =>
      Additive.ofMul ((Over.homMk (M.pointEquivPlace.symm w).1
        (M.pointEquivPlace.symm w).2 :
          Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk M.toBase) ≫ q)) := by
  intro g _
  classical
  by_cases hg : (g : F) ∈ Set.range (algebraMap K F)
  · obtain ⟨a, ha⟩ := hg
    simp only [← ha, Place.ord_algebraMap, zero_zsmul, finsum_zero]
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  have : Infinite (Place K F) := M.infinite_place
  let ε := M.pointEquivPlace.symm (Classical.arbitrary (Place K F))
  obtain ⟨P, φ, hφX, hφ, hfinite, π, hπ, hfin, hflat, hlfp, hn, hgeneric⟩ :=
    exists_finiteFlatMap_of_nonconstant M (g : F) hg
  let U : M.C.Opens := ⊤
  let qU : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom :=
    ⟨U.ι ≫ q.left, by rw [Category.assoc, Over.w q]; rfl⟩
  let εU : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase) :=
    ⟨ε.1 ≫ M.C.topIso.inv, by
      rw [← Category.assoc, Category.assoc ε.1, Scheme.toIso_inv_ι,
        Category.comp_id, ε.2]⟩
  let V := finiteMapTraceLocus M.toBase P.toBase π hπ (finrankAlong K φ) hn U
  have hV : V = ⊤ := finiteMapTraceLocus_top M.toBase P.toBase π hπ _ hn
  have : IsIso V.ι := by
    rw [hV]
    exact inferInstanceAs (IsIso P.C.topIso.hom)
  let τ := finiteCurveTrace M.toBase P.toBase π hπ (finrankAlong K φ) hn U εU G qU
  let τP : SchemeHomOver P.toBase G.X.hom :=
    ⟨inv V.ι ≫ τ.1, by rw [Category.assoc, τ.2, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]⟩
  obtain ⟨a, ha⟩ := exists_eq_const_ratFuncModel P G τP
  have hτ : τ.1 = (V.ι ≫ P.toBase) ≫ a.1 := by
    calc
      τ.1 = V.ι ≫ τP.1 := by
        change τ.1 = V.ι ≫ (inv V.ι ≫ τ.1)
        rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
      _ = _ := by rw [ha, ← Category.assoc]
  let p₀ := P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K 0)
  let pInf := P.pointEquivPlace.symm (RationalFunctionField.placeInfty K)
  let liftPoint (p : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) P.toBase) :
      SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (V.ι ≫ P.toBase) :=
    ⟨p.1 ≫ inv V.ι, by rw [← Category.assoc, Category.assoc p.1,
      IsIso.inv_hom_id, Category.comp_id, p.2]⟩
  have hlift (p : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) P.toBase) :
      (liftPoint p).1 ≫ V.ι = p.1 := by
    change (p.1 ≫ inv V.ι) ≫ V.ι = p.1
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hpoint (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (V.ι ≫ P.toBase)) :
      NeronModelInfra.schemeHomOverComp x τ = a := by
    apply Subtype.ext
    change x.1 ≫ τ.1 = a.1
    rw [hτ, ← Category.assoc, x.2, Category.id_comp]
  have h := rationalFunctionTrace_principalEvaluation P M φ hφ hfinite π hπ
    (finrankAlong K φ) hn hgeneric U εU G qU (liftPoint p₀) (liftPoint pInf)
    (hlift p₀) (hlift pInf)
  rw [hpoint, hpoint, sub_self, hφX] at h
  have hvalues (w : Place K F) :
      M.regularMapValues U G qU w =
        Additive.ofMul ((Over.homMk (M.pointEquivPlace.symm w).1
          (M.pointEquivPlace.symm w).2 :
            Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk M.toBase) ≫ q) := by
    let p := M.pointEquivPlace.symm w
    let x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase) :=
      ⟨p.1 ≫ M.C.topIso.inv, by
        rw [← Category.assoc, Category.assoc p.1, Scheme.toIso_inv_ι,
          Category.comp_id, p.2]⟩
    have hx : M.openPointPlace U x = w := by
      change M.pointEquivPlace
        ⟨x.1 ≫ U.ι, (Category.assoc _ _ _).trans x.2⟩ = w
      have hp : (⟨x.1 ≫ U.ι, (Category.assoc _ _ _).trans x.2⟩ :
          SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) = p := by
        apply Subtype.ext
        change (p.1 ≫ M.C.topIso.inv) ≫ U.ι = p.1
        rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
      rw [hp, M.pointEquivPlace.apply_symm_apply]
    have hv := M.regularMapValues_apply U G qU x
    rw [hx] at hv
    refine hv.trans ?_
    change Additive.ofMul _ = Additive.ofMul _
    apply congrArg Additive.ofMul
    apply Over.OverMorphism.ext
    change (p.1 ≫ M.C.topIso.inv) ≫ (U.ι ≫ q.left) = p.1 ≫ q.left
    rw [Category.assoc, ← Category.assoc M.C.topIso.inv, Scheme.toIso_inv_ι,
      Category.id_comp]
  have he := congrArg finsum (funext fun w =>
    congrArg (fun z => w.ord (g : F) • z) (hvalues w))
  exact he.symm.trans h.symm

/-- Restricting an everywhere-defined map to a separated commutative group
satisfies the full condition for every effective modulus. -/
theorem regularMapHasModulus_restriction_of_separated_group
    {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : Over.mk M.toBase ⟶ G.X) :
    M.regularMapHasModulus D G
      ⟨(modulusComplement (modulusCurveMap D)).ι ≫ q.left,
        by rw [Category.assoc, Over.w q]; rfl⟩ := by
  let U := modulusComplement (modulusCurveMap D)
  have hzero := M.zero_hasModulus_of_separated_group G q
  have hmod := hzero.mono (show (0 : Modulus K F) ≤ M.functionFieldModulus D from bot_le)
  apply hmod.congr
  intro w hw
  obtain ⟨x, rfl⟩ := M.exists_modulusPlace_eq D w hw
  have hx : M.pointEquivPlace.symm (M.modulusPlace D x) =
      (⟨x.left ≫ U.ι, (Category.assoc _ _ _).trans (Over.w x)⟩ :
        SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :=
    M.pointEquivPlace.symm_apply_apply _
  rw [hx]
  change _ = M.regularMapValues U G _ (M.openPointPlace U ⟨x.left, Over.w x⟩)
  rw [M.regularMapValues_apply]
  change Additive.ofMul _ = Additive.ofMul _
  congr 1

/-- A whole-curve map has its unique translated Abel factor for every full
modulus, including degree zero, in the original separated target group. -/
theorem existsUnique_groupHom_wholeCurve_translation
    {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : Over.mk M.toBase ⟶ G.X) :
    let _ : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
    let U := modulusComplement (modulusCurveMap D)
    let b : Over.mk (U.ι ≫ M.toBase) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    let qU : Over.mk (U.ι ≫ M.toBase) ⟶ G.X :=
      Over.homMk (U.ι ≫ q.left) (by rw [Category.assoc, Over.w q]; rfl)
    ∃! φ : groupScheme M.toBase D ⟶ G,
      modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom = qU / (b ≫ ε ≫ qU) := by
  intro hgeom U b qU
  exact M.existsUnique_groupHom_fullModulus_translation D ε G
    ⟨U.ι ≫ q.left, by rw [Category.assoc, Over.w q]; rfl⟩
    (M.regularMapHasModulus_restriction_of_separated_group D G q)

end AlgebraicCurve.CurveModel
