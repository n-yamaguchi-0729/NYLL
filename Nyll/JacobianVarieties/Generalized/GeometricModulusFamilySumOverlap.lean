/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusMapScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionClasses
import Nyll.JacobianVarieties.Generalized.GeometricModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusFamilySumScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusFamilyPointEvaluation
import Nyll.JacobianVarieties.Generalized.PicardZeroGeometricEquality
import Nyll.JacobianVarieties.Generalized.ModulusAbelCanonicalPoint
import Nyll.JacobianVarieties.Generalized.ModulusAbelGroupScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusDivisorFamily
import Nyll.JacobianVarieties.Generalized.PicardZeroLocalSums
import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
import Nyll.SchemeTheory.GroupSchemes.GeometricPointHom

/-! # Full geometric modulus glues the original family sums over every field

On each geometric test, the actual full-frame class equality is transported
to the extended curve. Its principal-divisor modulus condition identifies the
two corrected sums. Their proved scalar-extension comparison brings this
equality back to the original target, and reducedness detects the original
regular maps. No reducedness of a field-extension overlap is assumed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
  (hmod : geometricRegularMapHasModulus c D G q)

include hmod in
/-- Equal actual zero-sheaf classes determine equal regular family sums on
a reduced parameter scheme over an arbitrary ground field. -/
theorem geometricModulusFamilySum_eq_of_zeroSheafClass
    {T : Over (Spec (CommRingCat.of K))} [IsReduced T.left] {n₀ n₁ : ℕ}
    (E₀ : RelEffCartierDiv c n₀ T.hom)
    (hE₀ : E₀.SupportedIn (modulusComplement (modulusCurveMap D)))
    (E₁ : RelEffCartierDiv c n₁ T.hom)
    (hE₁ : E₁.SupportedIn (modulusComplement (modulusCurveMap D))) :
    let ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
        ((modulusComplement (modulusCurveMap D)).ι ≫ c) := ⟨ε.left, Over.w ε⟩
    let q' : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ c)
        G.X.hom := ⟨q.left, Over.w q⟩
    let e := RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c (modulusCurveMap D)
      (GoodReductionJacobian.schemeHomOverComp T.hom (Category.comp_id _) ε'))
    let z₀ := modulusDivisorFamilyClass c (modulusCurveMap D) E₀ hE₀ / e ^ n₀
    let z₁ := modulusDivisorFamilyClass c (modulusCurveMap D) E₁ hE₁ / e ^ n₁
    ∀ (hz₀ : z₀ ∈ (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj (op T))
      (hz₁ : z₁ ∈ (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj (op T)),
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf c (modulusCurveMap D))).app (op T) ⟨z₀, hz₀⟩ =
        (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf c (modulusCurveMap D))).app (op T) ⟨z₁, hz₁⟩ →
      modulusFamilySum c D ε' (commGroupRelativeLaw G)
          (commGroupRelativeLaw_isCommutative G) q' E₀ hE₀ =
        modulusFamilySum c D ε' (commGroupRelativeLaw G)
          (commGroupRelativeLaw_isCommutative G) q' E₁ hE₁ := by
  intro ε' q' e z₀ z₁ hz₀ hz₁ hη
  have : IsReduced (Over.mk T.hom).left := by
    change IsReduced T.left
    infer_instance
  apply (commGroupPointEquiv G T.hom).injective
  apply GroupSchemes.hom_ext_geometricPoints
  intro Ω fieldΩ closedΩ a p
  let : Algebra K Ω := (Spec.preimage a).hom.toAlgebra
  have ha : specMap K Ω = a := Spec.map_preimage a
  let t := 𝟙 (Spec (CommRingCat.of Ω))
  let p' : Over.mk (t ≫ specMap K Ω) ⟶ T :=
    Over.homMk p.left ((Over.w p).trans
      ((Category.id_comp (specMap K Ω)).trans ha).symm)
  let E₀' := E₀.pullbackAlong p'.left (Over.w p')
  let E₁' := E₁.pullbackAlong p'.left (Over.w p')
  let hE₀' := hE₀.pullbackAlong p'.left (Over.w p')
  let hE₁' := hE₁.pullbackAlong p'.left (Over.w p')
  let b : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk T.hom (Category.comp_id _)
  let bΩ : Over.mk (t ≫ specMap K Ω) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk (t ≫ specMap K Ω) (Category.comp_id _)
  have hb : p' ≫ b = bΩ := by
    apply Over.OverMorphism.ext
    exact Over.w p'
  have he : e = modulusAbelPointClass c (modulusCurveMap D) (b ≫ ε) :=
    (modulusAbelPointClass_eq_canonical c (modulusCurveMap D) (b ≫ ε)).symm
  have hraw := modulusPicardZero_raw_eq_on_geometricPoint c (modulusCurveMap D)
    ⟨z₀, hz₀⟩ ⟨z₁, hz₁⟩ hη p'
  let H : RigidifiedLineBundle.Classes (modulusBaseChange c (modulusCurveMap D) T.hom) →*
      RigidifiedLineBundle.Classes
        (modulusBaseChange c (modulusCurveMap D) (t ≫ specMap K Ω)) :=
    ((modulusPicardGroupPresheaf c (modulusCurveMap D)).map p'.op).hom
  change H (modulusDivisorFamilyClass c (modulusCurveMap D) E₀ hE₀ / e ^ n₀) =
    H (modulusDivisorFamilyClass c (modulusCurveMap D) E₁ hE₁ / e ^ n₁) at hraw
  have hraw₀ : H (modulusDivisorFamilyClass c (modulusCurveMap D) E₀ hE₀) =
      modulusDivisorFamilyClass c (modulusCurveMap D) E₀' hE₀' :=
    modulusDivisorFamilyClass_naturality c (modulusCurveMap D) E₀ hE₀
      p'.left (Over.w p')
  have hraw₁ : H (modulusDivisorFamilyClass c (modulusCurveMap D) E₁ hE₁) =
      modulusDivisorFamilyClass c (modulusCurveMap D) E₁' hE₁' :=
    modulusDivisorFamilyClass_naturality c (modulusCurveMap D) E₁ hE₁
      p'.left (Over.w p')
  have hrawε : H e = modulusAbelPointClass c (modulusCurveMap D) (bΩ ≫ ε) := by
    rw [he]
    change (modulusPicardGroupPresheaf c (modulusCurveMap D)).map p'.op
      (modulusAbelPointClass c (modulusCurveMap D) (b ≫ ε)) = _
    rw [modulusAbelPointClass_naturality, ← Category.assoc, hb]
  rw [map_div, map_div, map_pow, map_pow, hraw₀, hraw₁, hrawε] at hraw
  let cΩ := baseChange K c Ω
  let DΩ := D.changeBaseOfIdentity (specMap K Ω)
  let εΩ := modulusBasepointScalarExtension c D Ω ε
  let GΩ := (GroupSchemes.baseChange (specMap K Ω)).obj G
  have : IsSeparated GΩ.X.hom := by
    change IsSeparated (pullback.snd G.X.hom (specMap K Ω))
    infer_instance
  let qΩ := modulusGroupMapScalarExtension c D Ω G q
  let E₀Ω := (RelEffCartierDiv.changeBaseEquiv c (specMap K Ω) t n₀).symm E₀'
  let E₁Ω := (RelEffCartierDiv.changeBaseEquiv c (specMap K Ω) t n₁).symm E₁'
  let hE₀Ω := divisorScalarExtensionSupported c D Ω t E₀' hE₀'
  let hE₁Ω := divisorScalarExtensionSupported c D Ω t E₁' hE₁'
  have hεΩ : divisorScalarExtensionPoint c D Ω εΩ = bΩ ≫ ε :=
    divisorScalarExtensionPoint_lift c D Ω _
  let eΩ : RigidifiedLineBundle.Classes (modulusBaseChange cΩ (modulusCurveMap DΩ) t) :=
    modulusAbelPointClass cΩ (modulusCurveMap DΩ) (T := Over.mk t) εΩ
  have hclassΩ :
      modulusDivisorFamilyClass cΩ (modulusCurveMap DΩ) E₀Ω hE₀Ω /
          eΩ ^ n₀ =
        modulusDivisorFamilyClass cΩ (modulusCurveMap DΩ) E₁Ω hE₁Ω /
          eΩ ^ n₁ := by
    apply (divisorScalarExtensionClassesEquiv c D Ω t).injective
    dsimp only [eΩ]
    have hp := divisorScalarExtensionClassesEquiv_abelPoint c D Ω (T := Over.mk t) εΩ
    simp only [Over.mk_hom] at hp
    rw [map_div, map_div, map_pow, map_pow,
      divisorScalarExtensionClassesEquiv_divisorFamily,
      divisorScalarExtensionClassesEquiv_divisorFamily,
      hp, hεΩ]
    exact hraw
  let : Algebra Ω (pullback c (specMap K Ω)).functionField :=
    (AlgebraicCurve.baseToFunctionField cΩ).toAlgebra
  let MΩ := AlgebraicCurve.CurveModel.ofSmoothProperCurve cΩ
  have : GeometricallyIntegral MΩ.toBase := by
    change GeometricallyIntegral cΩ
    infer_instance
  have hmodΩ : MΩ.regularMapHasModulus DΩ GΩ ⟨qΩ.left, Over.w qΩ⟩ := hmod Ω
  have hsumΩ := MΩ.modulusFamilySum_eq_of_correctedClass DΩ
    ⟨εΩ.left, Over.w εΩ⟩ GΩ ⟨qΩ.left, Over.w qΩ⟩ hmodΩ
    E₀Ω hE₀Ω E₁Ω hE₁Ω hclassΩ
  have hsum :
      modulusFamilySum c D ε' (commGroupRelativeLaw G)
          (commGroupRelativeLaw_isCommutative G) q' E₀' hE₀' =
        modulusFamilySum c D ε' (commGroupRelativeLaw G)
          (commGroupRelativeLaw_isCommutative G) q' E₁' hE₁' := by
    apply (commGroupPointEquiv G (t ≫ specMap K Ω)).injective
    apply ((Over.mapPullbackAdj (specMap K Ω)).homEquiv (Over.mk t) G.X).injective
    exact (modulusFamilySum_scalarExtension_geometric c D ε G q Ω E₀' hE₀').trans
      ((congrArg (commGroupPointEquiv GΩ t) hsumΩ).trans
        (modulusFamilySum_scalarExtension_geometric c D ε G q Ω E₁' hE₁').symm)
  have hn₀ := modulusFamilySum_naturality c D ε' (commGroupRelativeLaw G)
    (commGroupRelativeLaw_isCommutative G) q' E₀ hE₀ p'.left (Over.w p')
  have hn₁ := modulusFamilySum_naturality c D ε' (commGroupRelativeLaw G)
    (commGroupRelativeLaw_isCommutative G) q' E₁ hE₁ p'.left (Over.w p')
  apply Over.OverMorphism.ext
  exact (congrArg Subtype.val hn₀).trans
    ((congrArg Subtype.val hsum).trans (congrArg Subtype.val hn₁).symm)

end AlgebraicGeometry.GeneralizedJacobian
