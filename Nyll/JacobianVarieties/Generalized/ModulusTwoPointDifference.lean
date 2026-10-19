/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelZeroClass

/-! # Algebraic triviality of two arbitrary points on the same test scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra Opposite
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- Any two actual points on the same field fibre have algebraically trivial difference. -/
theorem twoPointDifference_algEquivZero
    (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t c) :
    IsAlgEquivZero (pullback.snd c t)
      ((RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c y.1 y.2).idealModule) := by
  let a := pullback.snd c t
  let P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a :=
    ⟨graphOver c x.1 x.2, graphOver_snd c x.1 x.2⟩
  let Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a :=
    ⟨graphOver c y.1 y.2, graphOver_snd c y.1 y.2⟩
  let f := pullback.fst a (𝟙 (Spec (CommRingCat.of k)))
  have hpP : graphOver a P.1 P.2 ≫ f = graphOver c x.1 x.2 :=
    graphOver_fst _ _ _
  have hpQ : graphOver a Q.1 Q.2 ≫ f = graphOver c y.1 y.2 :=
    graphOver_fst _ _ _
  have hP : (graphOver c x.1 x.2).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c x.1 x.2)
  have hQ : (graphOver c y.1 y.2).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c y.1 y.2)
  have hP' : (graphOver a P.1 P.2).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint a P.1 P.2)
  have hQ' : (graphOver a Q.1 Q.2).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint a Q.1 Q.2)
  obtain ⟨eP⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    f (graphOver c x.1 x.2) (graphOver a P.1 P.2) hpP hP hP' 1).1
  obtain ⟨eQ⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    f (graphOver c y.1 y.2) (graphOver a Q.1 Q.2) hpQ hQ hQ' 1).2
  have eP' : (Scheme.Modules.pullback f).obj (graphOver c x.1 x.2).ker.invModule ≅
      (graphOver a P.1 P.2).ker.invModule :=
    (Scheme.Modules.pullback f).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _).symm)) ≪≫ eP ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _))
  have eQ' : (Scheme.Modules.pullback f).obj (graphOver c y.1 y.2).ker.module ≅
      (graphOver a Q.1 Q.2).ker.module :=
    (Scheme.Modules.pullback f).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _).symm)) ≪≫ eQ ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _))
  exact IsAlgEquivZero.of_iso_pointSubBasepoint P Q
    (Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ tensorIso eP' eQ')

/-- Actual rigidifications on two field-valued point bundles preserve algebraic triviality. -/
theorem rigidifiedTwoPointDifference_algEquivZero
    (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t c) {E : Scheme.{u}} (j : E ⟶ pullback c t)
    (M N : RigidifiedLineBundle j)
    (eM : M.L ≅ (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle)
    (eN : N.L ≅ (RelEffCartierDiv.ofPoint c y.1 y.2).lineBundle) :
    IsAlgEquivZero (pullback.snd c t) (M.tensor N.dual).L := by
  let E := RelEffCartierDiv.ofPoint c y.1 y.2
  have hE : E.I.IsInvertible := RelEffCartierDiv.isInvertible_I E
  have hInv : Nonempty (E.lineBundle ⊗ E.idealModule ≅ 𝟙_ (pullback c t).Modules) :=
    Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hE
  obtain ⟨eDual⟩ := MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
    eN ⟨N.evaluation⟩ hInv
  exact (twoPointDifference_algEquivZero c k t x y).of_iso (eM ⊗ᵢ eDual).symm

/-- The actual quotient of any two Abel point classes is a modulus Picard-zero class. -/
theorem modulusAbelPointClass_div_mem_zero
    {T : Over (Spec (CommRingCat.of R))}
    (P Q : T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    modulusAbelPointClass c i P / modulusAbelPointClass c i Q ∈
      modulusPicardZeroSubgroup c i T := by
  let x : SchemeHomOver T.hom ((modulusComplement i).ι ≫ c) := ⟨P.left, Over.w P⟩
  let y : SchemeHomOver T.hom ((modulusComplement i).ι ≫ c) := ⟨Q.left, Over.w Q⟩
  change RigidifiedLineBundle.classOf (modulusAbelBundleAt c i x) /
    RigidifiedLineBundle.classOf (modulusAbelBundleAt c i y) ∈ _
  rw [div_eq_mul_inv, ← RigidifiedLineBundle.classOf_dual]
  change RigidifiedLineBundle.classOf
    ((modulusAbelBundleAt c i x).tensor (modulusAbelBundleAt c i y).dual) ∈
      (modulusPicardZeroSubfunctor c i).obj (op T)
  intro k _ _ s
  let t := T.hom
  let ψ : SchemeHomOver (s ≫ t) t := ⟨s, rfl⟩
  let xk := postComp x ψ
  let yk := postComp y ψ
  let Mk := modulusAbelBundleAt c i xk
  let Nk := modulusAbelBundleAt c i yk
  let xc : SchemeHomOver (s ≫ t) c :=
    ⟨xk.1 ≫ (modulusComplement i).ι, (Category.assoc _ _ _).trans xk.2⟩
  let yc : SchemeHomOver (s ≫ t) c :=
    ⟨yk.1 ≫ (modulusComplement i).ι, (Category.assoc _ _ _).trans yk.2⟩
  have eM : Mk.L ≅ (RelEffCartierDiv.ofPoint c xc.1 xc.2).lineBundle :=
    modulusAbelBundlePullbackIso c i xk
  have eN : Nk.L ≅ (RelEffCartierDiv.ofPoint c yc.1 yc.2).lineBundle :=
    modulusAbelBundlePullbackIso c i yk
  have hfield : IsAlgEquivZero (pullback.snd c (s ≫ t)) (Mk.tensor Nk.dual).L :=
    rigidifiedTwoPointDifference_algEquivZero c k (s ≫ t) xc yc
      (modulusBaseChange c i (s ≫ t)) Mk Nk eM eN
  let M := modulusAbelBundleAt c i x
  let N := modulusAbelBundleAt c i y
  let f := baseChangeSnd c ψ
  have eM' : (Scheme.Modules.pullback f).obj M.L ≅ Mk.L :=
    modulusAbelBundleAtPullbackIso c i x ψ
  have eN' : (Scheme.Modules.pullback f).obj N.L ≅ Nk.L :=
    modulusAbelBundleAtPullbackIso c i y ψ
  have heval : (Scheme.Modules.pullback f).obj N.L ⊗
      (Scheme.Modules.pullback f).obj N.dual.L ≅ 𝟙_ (pullback c (s ≫ t)).Modules :=
    (Scheme.Modules.pullbackTensorObjIso f N.L N.dual.L).symm ≪≫
      (Scheme.Modules.pullback f).mapIso N.evaluation ≪≫ Scheme.Modules.pullbackUnitIso f
  obtain ⟨eDual⟩ := MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
    eN' ⟨heval⟩ ⟨Nk.evaluation⟩
  have epull : (Scheme.Modules.pullback f).obj (M.tensor N.dual).L ≅
      (Mk.tensor Nk.dual).L :=
    Scheme.Modules.pullbackTensorObjIso f M.L N.dual.L ≪≫ (eM' ⊗ᵢ eDual)
  let κ := pullbackLeftPullbackSndIso c t s
  have hκ : κ.hom ≫ f = pullback.fst (pullback.snd c t) s := by
    apply pullback.hom_ext
    · simp only [f, baseChangeSnd, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, pullbackLeftPullbackSndIso_hom_fst, Category.comp_id]
    · rw [Category.assoc, baseChangeSnd_snd, ← Category.assoc,
        pullbackLeftPullbackSndIso_hom_snd, pullback.condition]
  have hκsnd : κ.hom ≫ pullback.snd c (s ≫ t) = fibreAt c t s :=
    pullbackLeftPullbackSndIso_hom_snd c t s
  have efibre : (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj
      (M.tensor N.dual).L ≅
        (Scheme.Modules.pullback κ.hom).obj (Mk.tensor Nk.dual).L :=
    (Scheme.Modules.pullbackCongr hκ.symm).app (M.tensor N.dual).L ≪≫
      ((Scheme.Modules.pullbackComp κ.hom f).app (M.tensor N.dual).L).symm ≪≫
      (Scheme.Modules.pullback κ.hom).mapIso epull
  exact (hfield.pullback κ.hom hκsnd).of_iso efibre.symm

end AlgebraicGeometry.GeneralizedJacobian
