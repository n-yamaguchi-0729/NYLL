/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFrameSheaf
import Nyll.JacobianVarieties.Generalized.PicardZero

/-!
# Algebraic triviality of the actual modulus frame classes

A family algebraically trivial on geometric fibres supplies classes in the
existing modulus Picard-zero functor. The condition is verified on the actual
underlying pulled bundle and survives the modulus convention change.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual modulus convention change preserves geometric-fibre algebraic triviality. -/
theorem modulusFamilyClassEquiv_mem_zero {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (N : RigidifiedLineBundle (modulusFamilyInclusion D t))
    (hN : Unrigidified.FibrewiseZero
      (⟨N.L, N.isInvertible⟩ : Unrigidified.LineBundle c t)) :
    modulusFamilyClassEquiv D t (RigidifiedLineBundle.classOf N) ∈
      (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj (op (Over.mk t)) := by
  change Unrigidified.FibrewiseZero
    (⟨(Scheme.Modules.pullback (𝟙 (pullback c t))).obj N.L,
      N.isInvertible.pullback (𝟙 (pullback c t))⟩ : Unrigidified.LineBundle c t)
  intro k _ _ a
  exact (hN k a).of_iso
    ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) a)).mapIso
      ((Scheme.Modules.pullbackId (pullback c t)).app N.L).symm)

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) {L : (pullback c s).Modules}
  (hL : Scheme.Modules.IsInvertible L)
  (hzero : Unrigidified.FibrewiseZero (⟨L, hL⟩ : Unrigidified.LineBundle c s))

include hzero in
/-- Every actual frame class has the geometric-fibre zero condition of its underlying family. -/
theorem modulusFramePicardClass_mem_zero (T : Over S)
    (x : (scalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T)) :
    modulusFramePicardClass D s hL T x ∈
      (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj (op ((Over.map s).obj T)) := by
  induction x using Quotient.ind with
  | _ e =>
    change modulusFamilyClassEquiv D (T.hom ≫ s)
      (modulusFrameClass D s hL T (Quotient.mk _ e)) ∈ _
    rw [modulusFrameClass_mk s D hL T e]
    exact modulusFamilyClassEquiv_mem_zero D (T.hom ≫ s)
      (modulusFrameBundle s D hL T e)
      (Unrigidified.fibrewiseZero_pullback
        (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s) hzero)

/-- The actual natural frame comparison takes values in the modulus Picard-zero presheaf. -/
def modulusFramesToPicardZero :
    liftedScalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
        ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L) ⟶
      (Over.map s).op ⋙ modulusPicardZeroPresheaf c (modulusCurveMap D) where
  app T := TypeCat.ofHom (fun x => ⟨modulusFramePicardClass D s hL T.unop x.down,
    modulusFramePicardClass_mem_zero D s hL hzero T.unop x.down⟩)
  naturality {T T'} f := by
    apply TypeCat.homEquiv.injective
    funext x
    apply Subtype.ext
    exact (modulusFramePicardClass_naturality D s hL f.unop x.down).symm

/-- The zero condition restricts the target without introducing new frame identifications. -/
instance modulusFramesToPicardZero_mono : Mono (modulusFramesToPicardZero D s hL hzero) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro T
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y h
  apply ULift.ext
  exact modulusFramePicardClass_injective D s hL T.unop (congrArg Subtype.val h)

/-- The relative frame sheaf of an algebraically trivial family maps to the actual zero sheaf. -/
def modulusFrameSheafToPicardZero :
    scalarFrameSheaf (pullback.snd (modulusBaseMap D) s)
        ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L) ⟶
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) s).obj
        (modulusPicardZeroSheaf c (modulusCurveMap D)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
      (modulusFramesToPicardZero D s hL hzero) ≫
    ((Functor.pushforwardContinuousSheafificationCompatibility
      (G := Over.map s) (A := Type (u + 1))
      (J := Scheme.fppfTopology.over S)
      (K := Scheme.fppfTopology.over (Spec (CommRingCat.of K)))).app
        (modulusPicardZeroPresheaf c (modulusCurveMap D))).hom

/-- The geometric-fibre zero condition retains the embedding after fppf sheafification. -/
instance modulusFrameSheafToPicardZero_mono :
    Mono (modulusFrameSheafToPicardZero D s hL hzero) := by
  have hm : Mono ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
      (modulusFramesToPicardZero D s hL hzero)) := inferInstance
  let e := (Functor.pushforwardContinuousSheafificationCompatibility
    (G := Over.map s) (A := Type (u + 1))
    (J := Scheme.fppfTopology.over S)
    (K := Scheme.fppfTopology.over (Spec (CommRingCat.of K)))).app
      (modulusPicardZeroPresheaf c (modulusCurveMap D))
  exact mono_comp' hm (show Mono e.hom from inferInstance)

end AlgebraicGeometry.GeneralizedJacobian
