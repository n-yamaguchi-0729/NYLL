/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelPullback
import Nyll.JacobianVarieties.Generalized.ModulusPointDifference
import Nyll.JacobianVarieties.Generalized.PicardZeroGroupFunctor

/-! # Actual modulus Abel point differences lie in Picard-zero -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra Opposite
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

section

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]

/-- The actual Abel family evaluated at an arbitrary test point of the complement. -/
def modulusAbelBundleAt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t ((modulusComplement i).ι ≫ c)) :
    RigidifiedLineBundle (modulusBaseChange c i t) :=
  (modulusAbelBundle c i).pullback (baseChangeSnd c x) (baseChangeSnd (i ≫ c) x)
    (modulusBaseChange_naturality c i x)

/-- The moving line bundles commute with composition of test maps. -/
def modulusAbelBundleAtPullbackIso {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t ((modulusComplement i).ι ≫ c)) (s : SchemeHomOver t' t) :
    (Scheme.Modules.pullback (baseChangeSnd c s)).obj (modulusAbelBundleAt c i x).L ≅
      (modulusAbelBundleAt c i (postComp x s)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c s) (baseChangeSnd c x)).app
      (modulusAbelBundle c i).L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c x s)).app (modulusAbelBundle c i).L

/-- The constant test point determined by an actual point outside the modulus. -/
def modulusConstantPoint
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) ((modulusComplement i).ι ≫ c))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t ((modulusComplement i).ι ≫ c) :=
  ⟨t ≫ ε.1, (Category.assoc _ _ _).trans
    ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t))⟩

/-- The corresponding actual section of the whole curve. -/
def modulusComplementSection
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) ((modulusComplement i).ι ≫ c)) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c :=
  ⟨ε.1 ≫ (modulusComplement i).ι, (Category.assoc _ _ _).trans ε.2⟩

/-- The actual tensor quotient of moving and constant canonically rigidified point bundles. -/
def modulusAbelDifferenceBundle
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) ((modulusComplement i).ι ≫ c))
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t ((modulusComplement i).ι ≫ c)) :
    RigidifiedLineBundle (modulusBaseChange c i t) :=
  (modulusAbelBundleAt c i x).tensor
    (modulusAbelBundleAt c i (modulusConstantPoint c i ε t)).dual

private def pointLineBundleIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {x y : T ⟶ C} (h : x = y) (hx : x ≫ c = t) (hy : y ≫ c = t) :
    (RelEffCartierDiv.ofPoint c x hx).lineBundle ≅
      (RelEffCartierDiv.ofPoint c y hy).lineBundle := by
  cases h
  exact Iso.refl _

end

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- The modulus point-minus-basepoint family is algebraically trivial on every geometric fibre. -/
theorem modulusAbelDifference_mem_zero
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) ((modulusComplement i).ι ≫ c))
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t ((modulusComplement i).ι ≫ c)) :
    RigidifiedLineBundle.classOf (modulusAbelDifferenceBundle c i ε x) ∈
      (modulusPicardZeroSubfunctor c i).obj (op (Over.mk t)) := by
  intro k _ _ s
  let ψ : SchemeHomOver (s ≫ t) t := ⟨s, rfl⟩
  let xk := postComp x ψ
  let εk := postComp (modulusConstantPoint c i ε t) ψ
  let Mk := modulusAbelBundleAt c i xk
  let Nk := modulusAbelBundleAt c i εk
  let εC := modulusComplementSection c i ε
  let xc : SchemeHomOver (s ≫ t) c :=
    ⟨xk.1 ≫ (modulusComplement i).ι, (Category.assoc _ _ _).trans xk.2⟩
  have eM : Mk.L ≅ (RelEffCartierDiv.ofPoint c xc.1 xc.2).lineBundle :=
    modulusAbelBundlePullbackIso c i xk
  have eN : Nk.L ≅ (RelEffCartierDiv.ofPoint c ((s ≫ t) ≫ εC.1)
      ((Category.assoc _ _ _).trans
        ((congrArg ((s ≫ t) ≫ ·) εC.2).trans (Category.comp_id _)))).lineBundle := by
    refine modulusAbelBundlePullbackIso c i εk ≪≫ pointLineBundleIso c ?_ _ _
    simp only [εk, ψ, εC, postComp, modulusConstantPoint, modulusComplementSection,
      Category.assoc]
  have hfield : IsAlgEquivZero (pullback.snd c (s ≫ t)) (Mk.tensor Nk.dual).L :=
    rigidifiedPointDifference_algEquivZero c εC k (s ≫ t) xc
      (modulusBaseChange c i (s ≫ t)) Mk Nk eM eN
  let M := modulusAbelBundleAt c i x
  let N := modulusAbelBundleAt c i (modulusConstantPoint c i ε t)
  let f := baseChangeSnd c ψ
  have eM' : (Scheme.Modules.pullback f).obj M.L ≅ Mk.L :=
    modulusAbelBundleAtPullbackIso c i x ψ
  have eN' : (Scheme.Modules.pullback f).obj N.L ≅ Nk.L :=
    modulusAbelBundleAtPullbackIso c i (modulusConstantPoint c i ε t) ψ
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
