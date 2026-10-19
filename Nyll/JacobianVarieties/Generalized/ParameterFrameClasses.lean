/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FixedBundleFrames
import Nyll.AlgebraicCurves.Geometry.Curves.BijectiveAppProper
import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Parameter scalars in the classification of modulus frames

A proper smooth family with geometrically connected fibres has the same global
functions as its parameter scheme. Thus ambient units in the fixed-bundle
classification are exactly parameter units. The hypotheses are supplied for
every base change of a proper smooth geometrically irreducible curve.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Geometry.Schemes.Proofs
  Smooth_isReduced_of_isReduced_of_isLocallyNoetherian

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X S D : Scheme.{u}} (p : X ⟶ S) (i : D ⟶ X)

/-- Restrictions of actual global units compose as the geometric maps do. -/
theorem unitRestriction_comp (a : Γ(S, ⊤)ˣ) :
    Units.map (i ≫ p).appTop.hom.toMonoidHom a =
      Units.map i.appTop.hom.toMonoidHom (Units.map p.appTop.hom.toMonoidHom a) := by
  apply Units.ext
  exact congrArg (fun φ : Γ(S, ⊤) ⟶ Γ(D, ⊤) => φ (a : Γ(S, ⊤)))
    (Scheme.Hom.comp_appTop i p)

/-- Surjectivity on actual units suffices to replace ambient by parameter scalars. -/
theorem scalarFrameSetoid_comp_iff
    (hp : Function.Surjective (Units.map p.appTop.hom.toMonoidHom))
    (L : D.Modules) (e f : L ≅ 𝟙_ D.Modules) :
    (scalarFrameSetoid (i ≫ p) L).r e f ↔ (scalarFrameSetoid i L).r e f := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Units.map p.appTop.hom.toMonoidHom a, (unitRestriction_comp p i a).symm.trans ha⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := hp a
    exact ⟨b, (unitRestriction_comp p i b).trans
      ((congrArg (Units.map i.appTop.hom.toMonoidHom) hb).trans ha)⟩

variable [IsProper p] [Smooth p] [GeometricallyConnected p]

/-- Proper smooth connected fibres supply the actual parameter-unit comparison. -/
def parameterUnitsEquiv : Γ(S, ⊤)ˣ ≃* Γ(X, ⊤)ˣ := by
  have : GeometricallyReduced p := REDsol.geometricallyReduced_of_smooth p
  exact Units.mapEquiv (RingEquiv.ofBijective p.appTop.hom
    (bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
      p ⊤)).toMulEquiv

theorem parameterUnitsEquiv_apply (a : Γ(S, ⊤)ˣ) :
    parameterUnitsEquiv p a = Units.map p.appTop.hom.toMonoidHom a := rfl

/-- The actual parameter-scalar relation equals the ambient-scalar relation. -/
theorem parameterScalarFrameSetoid_iff (L : D.Modules) (e f : L ≅ 𝟙_ D.Modules) :
    (scalarFrameSetoid (i ≫ p) L).r e f ↔ (scalarFrameSetoid i L).r e f := by
  apply scalarFrameSetoid_comp_iff p i _ L e f
  intro a
  obtain ⟨b, hb⟩ := (parameterUnitsEquiv p).surjective a
  exact ⟨b, (parameterUnitsEquiv_apply p b).symm.trans hb⟩

/-- The frame quotient can use parameter units without changing any classes. -/
def parameterFrameClassesEquiv (L : D.Modules) :
    ScalarFrameClasses (i ≫ p) L ≃ ScalarFrameClasses i L :=
  Quotient.congr (Equiv.refl _) (parameterScalarFrameSetoid_iff p i L)

variable {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)

/-- A parameter-scalar frame class determines an actual rigidified class. -/
def parameterFrameClass : ScalarFrameClasses (i ≫ p) ((Scheme.Modules.pullback i).obj M) →
    Classes i :=
  frameClass i hM ∘ parameterFrameClassesEquiv p i ((Scheme.Modules.pullback i).obj M)

theorem parameterFrameClass_injective : Function.Injective (parameterFrameClass p i hM) :=
  (frameClass_injective i hM).comp (parameterFrameClassesEquiv p i _).injective

/-- Parameter-frame classes have exactly the prescribed underlying line-bundle class. -/
theorem exists_parameterFrameClass_eq_iff (N : RigidifiedLineBundle i) :
    (∃ x : ScalarFrameClasses (i ≫ p) ((Scheme.Modules.pullback i).obj M),
      parameterFrameClass p i hM x = classOf N) ↔ Nonempty (M ≅ N.L) := by
  constructor
  · rintro ⟨x, hx⟩
    exact (exists_frameClass_eq_iff i hM N).mp
      ⟨parameterFrameClassesEquiv p i _ x, hx⟩
  · intro h
    obtain ⟨x, hx⟩ := (exists_frameClass_eq_iff i hM N).mpr h
    obtain ⟨y, hy⟩ :=
      (parameterFrameClassesEquiv p i ((Scheme.Modules.pullback i).obj M)).surjective x
    exact ⟨y, (congrArg (frameClass i hM) hy).trans hx⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))

/-- Every parameter change of the curve supplies the required unit comparison. -/
def curveParameterUnitsEquiv : Γ(T, ⊤)ˣ ≃* Γ(pullback c t, ⊤)ˣ := by
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have : GeometricallyConnected c := by
    constructor
    intro L _ y Z fst snd h
    have : IrreducibleSpace Z :=
      GeometricallyIrreducible.geometrically_irreducibleSpace (f := c) y fst snd h
    infer_instance
  exact RigidifiedLineBundle.parameterUnitsEquiv (pullback.snd c t)

/-- The curve comparison is restriction along the actual projection. -/
theorem curveParameterUnitsEquiv_apply (a : Γ(T, ⊤)ˣ) :
    curveParameterUnitsEquiv c t a =
      Units.map (pullback.snd c t).appTop.hom.toMonoidHom a := rfl

/-- Curve-family frame quotients can use ambient units or parameter units interchangeably. -/
def curveParameterFrameClassesEquiv {D' : Scheme.{u}} (i : D' ⟶ pullback c t)
    (L : D'.Modules) :
    ScalarFrameClasses (i ≫ pullback.snd c t) L ≃ ScalarFrameClasses i L := by
  apply Quotient.congr (Equiv.refl _)
  intro e f
  apply RigidifiedLineBundle.scalarFrameSetoid_comp_iff (pullback.snd c t) i _ L e f
  intro a
  obtain ⟨b, hb⟩ := (curveParameterUnitsEquiv c t).surjective a
  exact ⟨b, (curveParameterUnitsEquiv_apply c t b).symm.trans hb⟩

end AlgebraicGeometry.GeneralizedJacobian
