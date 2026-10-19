/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFrameClass
import Nyll.JacobianVarieties.Generalized.RigidifiedFrameNaturality

/-! Naturality of the actual modulus-frame classification under parameter restriction. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem framePresheaf_mapIso_apply {Y : Scheme.{u}} (M : Y.Modules)
    {T T' : Over Y} (a : T' ≅ T)
    (e : (framePresheaf M).obj (op T)) :
    ((framePresheaf M).mapIso a.op).toEquiv e = frameMap M a.hom e := rfl

private theorem frameDomainEquiv_trans_apply {Y : Scheme.{u}} {M N : Y.Modules}
    {A : Type u} (E : A ≃ (M ≅ 𝟙_ Y.Modules)) (a : N ≅ M) (x : A) :
    (E.trans (Scheme.Modules.frameDomainEquiv a)) x = a ≪≫ E x := rfl

variable {K : Type u} [Field K] {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))

/-- A parameter morphism viewed over the original field. -/
def parameterHom {T T' : Over S} (f : T' ⟶ T) :
    SchemeHomOver (T'.hom ≫ s) (T.hom ≫ s) :=
  ⟨f.left, (Category.assoc f.left T.hom s).symm.trans (congrArg (fun k => k ≫ s) f.w)⟩

/-- The actual restriction map of a family, viewed over its original parameter change. -/
def parameterFamilyMap {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of K))
    {T T' : Over S} (f : T' ⟶ T) :
    Over.mk (baseChangeSnd q (⟨T'.hom, rfl⟩ : SchemeHomOver (T'.hom ≫ s) s)) ⟶
      Over.mk (baseChangeSnd q (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)) :=
  Over.homMk (baseChangeSnd q (parameterHom s f))
    ((baseChangeSnd_comp q (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)
      (parameterHom s f)).trans (congrArg (baseChangeSnd q) (Subtype.ext f.w)))

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual modulus-scheme comparison commutes with restriction of parameters. -/
theorem modulusTestIso_naturality {T T' : Over S} (f : T' ⟶ T) :
    parameterFamilyMap s (modulusBaseMap D) f ≫ (modulusTestIso D s T).hom =
      (modulusTestIso D s T').hom ≫
        (Over.pullback (pullback.snd (modulusBaseMap D) s)).map f := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (parameterFamilyMap s (modulusBaseMap D) f).left ≫
        (modulusTestIso D s T).hom.left ≫ _ =
      ((modulusTestIso D s T').hom.left ≫
        ((Over.pullback (pullback.snd (modulusBaseMap D) s)).map f).left) ≫ _
    rw [modulusTestIso_toParameter]
    simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc, modulusTestIso_toParameter]
    exact RelPicard.BaseChange.baseChangeSnd_snd'
      (cc := modulusBaseMap D) (ψ := parameterHom s f)
  · exact ((parameterFamilyMap s (modulusBaseMap D) f ≫
      (modulusTestIso D s T).hom).w).trans
        (((modulusTestIso D s T').hom ≫
          (Over.pullback (pullback.snd (modulusBaseMap D) s)).map f).w).symm

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {L : (pullback c s).Modules} (hL : Scheme.Modules.IsInvertible L)

/-- The scalar comparison acts on representatives by the actual frame comparison. -/
theorem modulusAmbientFrameEquiv_mk (T : Over S)
    (e : (relativeFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T)) :
    modulusAmbientFrameEquiv D s L T (Quotient.mk _ e) =
      Quotient.mk _ (modulusFrameTestEquiv D s L T e) := rfl

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c] in
/-- Evaluation of the native frame comparison retains the actual restriction isomorphism. -/
theorem modulusFrameTestEquiv_apply (T : Over S)
    (e : (relativeFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T)) :
    modulusFrameTestEquiv D s L T e =
      (RigidifiedLineBundle.restrictionComparison
        (i := modulusFamilyInclusion D s) (i' := modulusFamilyInclusion D (T.hom ≫ s))
        (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
        (baseChangeSnd (modulusBaseMap D) (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
        (modulusFamilyInclusion_naturality D
          (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))).app L ≪≫
      frameMap ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)
        (T := (Over.pullback (pullback.snd (modulusBaseMap D) s)).obj T)
        (T' := Over.mk (baseChangeSnd (modulusBaseMap D)
          (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)))
        (modulusTestIso D s T).hom e := by
  have h := frameDomainEquiv_trans_apply
    (((framePresheaf ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).mapIso
      (modulusTestIso D s T).op).toEquiv)
    ((RigidifiedLineBundle.restrictionComparison
      (i := modulusFamilyInclusion D s) (i' := modulusFamilyInclusion D (T.hom ≫ s))
      (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
      (baseChangeSnd (modulusBaseMap D) (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
      (modulusFamilyInclusion_naturality D
        (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))).app L) e
  exact h.trans (congrArg
    (fun z => (RigidifiedLineBundle.restrictionComparison
      (i := modulusFamilyInclusion D s) (i' := modulusFamilyInclusion D (T.hom ≫ s))
      (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
      (baseChangeSnd (modulusBaseMap D) (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
      (modulusFamilyInclusion_naturality D
        (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))).app L ≪≫ z)
    (framePresheaf_mapIso_apply
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)
      (modulusTestIso D s T) e))

/-- The actual bundle underlying a native frame before passage to scalar classes. -/
def modulusFrameBundle (T : Over S)
    (e : (relativeFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T)) :
    RigidifiedLineBundle (modulusFamilyInclusion D (T.hom ≫ s)) :=
  RigidifiedLineBundle.fromRestrictionFrame (modulusFamilyInclusion D s) hL
    (Over.mk (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)))
    (Over.mk (baseChangeSnd (modulusBaseMap D)
      (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)))
    (modulusFamilyInclusion D (T.hom ≫ s))
    (modulusFamilyInclusion_naturality D
      (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
    (frameMap ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)
      (T := (Over.pullback (pullback.snd (modulusBaseMap D) s)).obj T)
      (T' := Over.mk (baseChangeSnd (modulusBaseMap D)
        (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)))
      (modulusTestIso D s T).hom e)

/-- The pointwise scalar quotient sends a frame to this same chosen-rigidified bundle. -/
theorem modulusFrameClass_mk (T : Over S)
    (e : (relativeFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T)) :
    modulusFrameClass D s hL T (Quotient.mk _ e) =
      RigidifiedLineBundle.classOf (modulusFrameBundle s D hL T e) := by
  have ha := congrArg
    (RigidifiedLineBundle.frameClass (modulusFamilyInclusion D (T.hom ≫ s))
      (hL.pullback (baseChangeSnd c
        (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))))
    (modulusAmbientFrameEquiv_mk s D T e)
  have hb := congrArg
    (fun z => RigidifiedLineBundle.classOf
      (RigidifiedLineBundle.withFrame (modulusFamilyInclusion D (T.hom ≫ s))
        (hL.pullback (baseChangeSnd c
          (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))) z))
    (modulusFrameTestEquiv_apply s D T e)
  exact ha.trans hb

/-- The pointwise classification preserves pullback of the whole chosen rigidification. -/
theorem modulusFrameClass_naturality {T T' : Over S} (f : T' ⟶ T)
    (x : (scalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T)) :
    RigidifiedLineBundle.classesPullback
        (baseChangeSnd c (parameterHom s f))
        (baseChangeSnd (modulusBaseMap D) (parameterHom s f))
        (modulusFamilyInclusion_naturality D (parameterHom s f))
        (modulusFrameClass D s hL T x) =
      modulusFrameClass D s hL T'
        ((scalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
          ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).map f.op x) := by
  induction x using Quotient.ind with
  | _ e =>
    change RigidifiedLineBundle.classesPullback _ _ _
        (modulusFrameClass D s hL T (Quotient.mk _ e)) =
      modulusFrameClass D s hL T' (Quotient.mk _
        ((relativeFramePresheaf (pullback.snd (modulusBaseMap D) s)
          ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).map f.op e))
    rw [modulusFrameClass_mk, modulusFrameClass_mk,
      relativeFramePresheaf_map_apply (pullback.snd (modulusBaseMap D) s)
        ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L) f e]
    let M := (Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L
    let V := Over.mk (baseChangeSnd (modulusBaseMap D)
      (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
    let V' := Over.mk (baseChangeSnd (modulusBaseMap D)
      (⟨T'.hom, rfl⟩ : SchemeHomOver (T'.hom ≫ s) s))
    let a := (modulusTestIso D s T).hom
    let a' := (modulusTestIso D s T').hom
    let g := parameterFamilyMap s (modulusBaseMap D) f
    let k := (Over.pullback (pullback.snd (modulusBaseMap D) s)).map f
    have he : frameMap M (T := V) (T' := V') g
        (frameMap M (T := (Over.pullback (pullback.snd (modulusBaseMap D) s)).obj T)
          (T' := V) a e) =
        frameMap M (T := (Over.pullback (pullback.snd (modulusBaseMap D) s)).obj T')
          (T' := V') a' (frameMap M k e) :=
      (frameMap_comp M a g e).trans
        ((congrArg (fun z => frameMap M z e) (modulusTestIso_naturality s D f)).trans
          (frameMap_comp M k a' e).symm)
    have hi := RigidifiedLineBundle.fromRestrictionFramePullbackIso
      (modulusFamilyInclusion D s) hL
      (modulusFamilyInclusion D (T.hom ≫ s))
      (modulusFamilyInclusion D (T'.hom ≫ s))
      (modulusFamilyInclusion_naturality D
        (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
      (modulusFamilyInclusion_naturality D
        (⟨T'.hom, rfl⟩ : SchemeHomOver (T'.hom ≫ s) s))
      (parameterFamilyMap s c f) g
      (modulusFamilyInclusion_naturality D (parameterHom s f))
      (frameMap M a e)
    have hz := congrArg
      (fun z : (Scheme.Modules.pullback V'.hom).obj M ≅ 𝟙_ V'.left.Modules =>
        RigidifiedLineBundle.classOf
        (RigidifiedLineBundle.fromRestrictionFrame (modulusFamilyInclusion D s) hL
          (Over.mk (baseChangeSnd c
            (⟨T'.hom, rfl⟩ : SchemeHomOver (T'.hom ≫ s) s))) V'
          (modulusFamilyInclusion D (T'.hom ≫ s))
          (modulusFamilyInclusion_naturality D
            (⟨T'.hom, rfl⟩ : SchemeHomOver (T'.hom ≫ s) s)) z)) he
    exact ((RigidifiedLineBundle.classOf_eq_iff _ _).mpr ⟨hi⟩).trans hz

end AlgebraicGeometry.GeneralizedJacobian
