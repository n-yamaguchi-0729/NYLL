/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.EmptyModulusSheaf
import Nyll.JacobianVarieties.Generalized.PicardZeroForgetfulGroup

/-!
# The empty-modulus Picard-zero group sheaf

The zero condition is the condition on the actual underlying relative class.
Consequently the proved empty-modulus local bijection restricts to zero classes
and respects their tensor groups.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian.EmptyModulus

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsEmpty D]

/-- An ordinary zero class lifts to a zero class with the unique empty rigidification. -/
theorem forgetModulusZeroPresheaf_surjective (T : Over (Spec (CommRingCat.of R))) :
    Function.Surjective ((forgetModulusZeroPresheaf c i).app (op T)) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := forgetModulusClasses_surjective c i T.hom x
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  change RelPicard.Unrigidified.classesZero T.hom (forgetModulusClasses c i T.hom y)
  rw [hy]
  exact hx

/-- Equality of zero classes is detected locally by the actual forgetful map. -/
theorem forgetModulusZeroPresheaf_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (forgetModulusZeroPresheaf c i) := by
  have : Presheaf.IsLocallyInjective
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (forgetModulusPresheaf c i) :=
    forgetModulusPresheaf_isLocallyInjective c i
  constructor
  intro T x y hxy
  have he : (forgetModulusPresheaf c i).app T x.val =
      (forgetModulusPresheaf c i).app T y.val := congrArg Subtype.val hxy
  apply (Scheme.fppfTopology.over (Spec (CommRingCat.of R))).superset_covering ?_
    (Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (forgetModulusPresheaf c i) x.val y.val he)
  intro U f hf
  exact Subtype.ext hf

/-- The actual tensor-preserving empty-modulus comparison is an isomorphism of group sheaves. -/
theorem isIso_forgetModulusZeroGroupSheaf : IsIso (forgetModulusZeroGroupSheaf c i) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  have hi : Presheaf.IsLocallyInjective J (forgetModulusZeroPresheaf c i) :=
    forgetModulusZeroPresheaf_isLocallyInjective c i
  have hs : Presheaf.IsLocallySurjective J (forgetModulusZeroPresheaf c i) :=
    Presheaf.isLocallySurjective_of_surjective J _
      (fun T => forgetModulusZeroPresheaf_surjective c i T.unop)
  have : Presheaf.IsLocallyInjective J (forgetModulusZeroGroupPresheaf c i) :=
    (Presheaf.isLocallyInjective_forget_iff J
      (forgetModulusZeroGroupPresheaf c i)).mp hi
  have : Presheaf.IsLocallySurjective J (forgetModulusZeroGroupPresheaf c i) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J
      (forgetModulusZeroGroupPresheaf c i)).mpr hs
  exact (J.W_iff (forgetModulusZeroGroupPresheaf c i)).mp
    (J.W_of_isLocallyBijective (forgetModulusZeroGroupPresheaf c i))

/-- Empty-modulus zero tensor classes recover the ordinary relative Picard-zero group sheaf. -/
def ordinaryPicardZeroGroupSheafIso :
    modulusPicardZeroGroupSheaf c i ≅ ordinaryRelativePicardZeroGroupSheaf c := by
  let : IsIso (forgetModulusZeroGroupSheaf c i) := isIso_forgetModulusZeroGroupSheaf c i
  exact asIso (forgetModulusZeroGroupSheaf c i)

end AlgebraicGeometry.GeneralizedJacobian.EmptyModulus

