/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelCanonicalPoint
import Nyll.JacobianVarieties.Generalized.ModulusAbelZeroClass
import Nyll.JacobianVarieties.Generalized.ModulusRestrictionMap

/-! # Actual Abel classes commute with restriction of the whole modulus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  [IsClosedImmersion i] [IsClosedImmersion i'] (j : D' ⟶ D) (w : i' = j ≫ i)

include j w in
/-- Removing a larger modulus leaves an open subscheme of the smaller complement. -/
theorem modulusComplement_le_of_restriction : modulusComplement i ≤ modulusComplement i' := by
  intro x hx hx'
  apply hx
  have h : (i'.ker.support : Set C) ⊆ (i.ker.support : Set C) := by
    rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker]
    apply closure_mono
    rintro _ ⟨y, rfl⟩
    exact ⟨j y, by rw [w, Scheme.Hom.comp_apply]⟩
  exact h hx'

/-- The actual inclusion of open curves induced by a morphism of full moduli. -/
def modulusComplementRestriction :
    Over.mk ((modulusComplement i).ι ≫ c) ⟶
      Over.mk ((modulusComplement i').ι ≫ c) :=
  Over.homMk (C.homOfLE (modulusComplement_le_of_restriction j w)) (by
    change C.homOfLE (modulusComplement_le_of_restriction j w) ≫
      ((modulusComplement i').ι ≫ c) = (modulusComplement i).ι ≫ c
    rw [← Category.assoc, Scheme.homOfLE_ι])

variable [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- The canonical point frame restricts to the canonical frame for the smaller modulus. -/
def modulusCanonicalPointRestrictionIso {T : Over (Spec (CommRingCat.of R))}
    (x : T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    RigidifiedLineBundle.Iso
      ((modulusCanonicalPointBundle c i ⟨x.left, Over.w x⟩).pullback
        (𝟙 _) (modulusRestrictionPullback c j w T.hom)
        (modulusRestrictionPullback_square c j w T.hom))
      (modulusCanonicalPointBundle c i'
        ⟨(x ≫ modulusComplementRestriction c j w).left,
          Over.w (x ≫ modulusComplementRestriction c j w)⟩) := by
  let x₀ : SchemeHomOver T.hom ((modulusComplement i).ι ≫ c) := ⟨x.left, Over.w x⟩
  let x₁ : SchemeHomOver T.hom ((modulusComplement i').ι ≫ c) :=
    ⟨(x ≫ modulusComplementRestriction c j w).left,
      Over.w (x ≫ modulusComplementRestriction c j w)⟩
  let E := RelEffCartierDiv.ofPoint c (x₀.1 ≫ (modulusComplement i).ι)
    ((Category.assoc _ _ _).trans x₀.2)
  let E' := RelEffCartierDiv.ofPoint c (x₁.1 ≫ (modulusComplement i').ι)
    ((Category.assoc _ _ _).trans x₁.2)
  have hx : x₁.1 ≫ (modulusComplement i').ι = x₀.1 ≫ (modulusComplement i).ι := by
    change (x.left ≫ C.homOfLE (modulusComplement_le_of_restriction j w)) ≫
      (modulusComplement i').ι = _
    rw [Category.assoc, Scheme.homOfLE_ι]
  have he : E' = E := by
    dsimp [E', E]
    congr 1
  let M := modulusCanonicalPointBundle c i x₀
  have hI : E.I.IsInvertible := RelEffCartierDiv.isInvertible_I E
  exact RigidifiedLineBundle.zeroDivisorIso
    (M.pullback (𝟙 _) (modulusRestrictionPullback c j w T.hom)
      (modulusRestrictionPullback_square c j w T.hom))
    (Scheme.Modules.pullbackSection (𝟙 _) E.I.invModuleSection)
    (RigidifiedLineBundle.pullback_normalized_section _ _ _ M E.I.invModuleSection
      (RigidifiedLineBundle.ofInvertibleIdeal_section _ _ _ _))
    E'.I (RelEffCartierDiv.isInvertible_I E') (by
      exact (Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal (𝟙 _)
        hI.isInvertible_invModule E.I.invModuleSection).symm.trans
          ((congrArg (fun J => J.comap (𝟙 _)) hI.zeroSchemeIdeal_invModuleSection).trans
            ((Scheme.IdealSheafData.comap_id E.I).trans (congrArg RelEffCartierDiv.I he.symm))))
    (modulusPointDivisor_avoids c i' x₁)

/-- Equality of actual rigidified Abel classes, including their canonical modulus frames. -/
theorem modulusRestrictionClasses_abelPoint {T : Over (Spec (CommRingCat.of R))}
    (x : T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    modulusRestrictionClasses c j w T.hom (modulusAbelPointClass c i (T := T) x) =
      modulusAbelPointClass c i' (T := T) (x ≫ modulusComplementRestriction c j w) := by
  let x₀ : SchemeHomOver T.hom ((modulusComplement i).ι ≫ c) := ⟨x.left, Over.w x⟩
  let x₁ : SchemeHomOver T.hom ((modulusComplement i').ι ≫ c) :=
    ⟨(x ≫ modulusComplementRestriction c j w).left,
      Over.w (x ≫ modulusComplementRestriction c j w)⟩
  apply (RigidifiedLineBundle.classOf_eq_iff _ _).mpr
  exact ⟨((modulusAbelBundleAtCanonicalIso c i x₀).pullback _ _ _).trans
    ((modulusCanonicalPointRestrictionIso c j w x).trans
      (modulusAbelBundleAtCanonicalIso c i' x₁).symm)⟩

end AlgebraicGeometry.GeneralizedJacobian
