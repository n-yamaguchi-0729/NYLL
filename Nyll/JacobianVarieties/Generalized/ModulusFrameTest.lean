/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareFrameQuotient
import Nyll.JacobianVarieties.Generalized.RigidifiedLineBundle
import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.IsPullbackBaseChangeSnd

/-!
# Actual modulus frames on a parameter test scheme

The pullback square compares the intrinsic frame functor with frames of the
restricted, pulled-back line bundle on the actual curve family. All comparison
maps are geometric pullbacks, including the module pullback comparison.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual modulus inclusion commutes with parameter restriction. -/
theorem modulusFamilyInclusion_naturality {S T : Scheme.{u}}
    {s : S ⟶ Spec (CommRingCat.of K)} {t : T ⟶ Spec (CommRingCat.of K)}
    (g : SchemeHomOver t s) :
    modulusFamilyInclusion D t ≫ baseChangeSnd c g =
      baseChangeSnd (modulusBaseMap D) g ≫ modulusFamilyInclusion D s := by
  apply pullback.hom_ext
  · simp only [modulusFamilyInclusion, baseChangeSnd, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [modulusFamilyInclusion, baseChangeSnd, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc]

variable {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))

/-- The actual changed modulus is the pullback used by the intrinsic frame functor. -/
def modulusTestIso (T : Over S) :
    Over.mk (baseChangeSnd (modulusBaseMap D)
      (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)) ≅
        (Over.pullback (pullback.snd (modulusBaseMap D) s)).obj T :=
  Over.isoMk
    (isPullback_baseChangeSnd (modulusBaseMap D)
      (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)).flip.isoPullback
    (isPullback_baseChangeSnd (modulusBaseMap D)
      (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)).flip.isoPullback_hom_snd

/-- This comparison preserves the actual projection to the parameter test scheme. -/
theorem modulusTestIso_toParameter (T : Over S) :
    (modulusTestIso D s T).hom.left ≫
        modulusProjection (pullback.snd (modulusBaseMap D) s) T =
      pullback.snd (modulusBaseMap D) (T.hom ≫ s) :=
  (isPullback_baseChangeSnd (modulusBaseMap D)
    (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)).flip.isoPullback_hom_fst

/-- The scheme comparison pulls back the actual global units of the modulus. -/
def modulusTestUnitsEquiv (T : Over S) :
    ModulusUnits (pullback.snd (modulusBaseMap D) s) T ≃*
      Γ(pullback (modulusBaseMap D) (T.hom ≫ s), ⊤)ˣ :=
  Units.mapEquiv (Scheme.Γ.mapIso
    ((Over.forget (pullback (modulusBaseMap D) s)).mapIso
      (modulusTestIso D s T)).op).commRingCatIsoToRingEquiv.toMulEquiv

/-- The scheme comparison preserves precisely the actual parameter scalar. -/
theorem modulusTestUnitsEquiv_scalar (T : Over S) (a : Γ(T.left, ⊤)ˣ) :
    modulusTestUnitsEquiv D s T
        (Units.map
          (modulusProjection (pullback.snd (modulusBaseMap D) s) T).appTop.hom.toMonoidHom a) =
      Units.map (pullback.snd (modulusBaseMap D) (T.hom ≫ s)).appTop.hom.toMonoidHom a := by
  apply Units.ext
  exact congrArg (fun φ : Γ(T.left, ⊤) ⟶
    Γ(pullback (modulusBaseMap D) (T.hom ≫ s), ⊤) => φ (a : Γ(T.left, ⊤)))
      (congrArg Scheme.Hom.appTop (modulusTestIso_toParameter D s T))

variable (L : (pullback c s).Modules)

/-- The module comparison identifies intrinsic frames with frames of the pulled curve family. -/
def modulusFrameTestEquiv (T : Over S) :
    (relativeFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T) ≃
        ((Scheme.Modules.pullback (modulusFamilyInclusion D (T.hom ≫ s))).obj
          ((Scheme.Modules.pullback
            (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))).obj L) ≅
              𝟙_ (pullback (modulusBaseMap D) (T.hom ≫ s)).Modules) :=
  ((framePresheaf ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).mapIso
    (modulusTestIso D s T).op).toEquiv.trans
      (frameDomainEquiv ((RigidifiedLineBundle.restrictionComparison
        (i := modulusFamilyInclusion D s) (i' := modulusFamilyInclusion D (T.hom ≫ s))
        (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
        (baseChangeSnd (modulusBaseMap D) (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
        (modulusFamilyInclusion_naturality D
          (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))).app L))

/-- The ratio changes by restriction along the actual isomorphism of modulus schemes. -/
theorem frameRatio_modulusFrameTestEquiv (T : Over S)
    (e f : (relativeFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T)) :
    frameRatio (modulusFrameTestEquiv D s L T e) (modulusFrameTestEquiv D s L T f) =
      modulusTestUnitsEquiv D s T (frameRatio e f) := by
  exact (frameRatio_precomp _ _ _).trans
    (frameRatio_frameMap
      (M := (Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)
      (T := (Over.pullback (pullback.snd (modulusBaseMap D) s)).obj T)
      (T' := Over.mk (baseChangeSnd (modulusBaseMap D)
        (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)))
      (modulusTestIso D s T).hom e f)

/-- The actual frame comparison preserves the parameter-scalar relation in both directions. -/
theorem modulusFrameTestEquiv_scalarRel (T : Over S)
    (e f : (relativeFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T)) :
    (relativeScalarFrameSetoid (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L) T).r e f ↔
        (scalarFrameSetoid (pullback.snd (modulusBaseMap D) (T.hom ≫ s))
          ((Scheme.Modules.pullback (modulusFamilyInclusion D (T.hom ≫ s))).obj
            ((Scheme.Modules.pullback
              (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))).obj L))).r
                (modulusFrameTestEquiv D s L T e) (modulusFrameTestEquiv D s L T f) := by
  have hr := frameRatio_modulusFrameTestEquiv D s L T e f
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (modulusTestUnitsEquiv_scalar D s T a).symm.trans
      ((congrArg (modulusTestUnitsEquiv D s T) ha).trans hr.symm)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (modulusTestUnitsEquiv D s T).injective
      ((modulusTestUnitsEquiv_scalar D s T a).trans (ha.trans hr))⟩

/-- Intrinsic frame classes are the parameter-scalar classes on the actual changed modulus. -/
def modulusScalarFrameTestEquiv (T : Over S) :
    (scalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T) ≃
        ScalarFrameClasses (pullback.snd (modulusBaseMap D) (T.hom ≫ s))
          ((Scheme.Modules.pullback (modulusFamilyInclusion D (T.hom ≫ s))).obj
            ((Scheme.Modules.pullback
              (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))).obj L)) :=
  Quotient.congr (modulusFrameTestEquiv D s L T) (modulusFrameTestEquiv_scalarRel D s L T)

end AlgebraicGeometry.GeneralizedJacobian
