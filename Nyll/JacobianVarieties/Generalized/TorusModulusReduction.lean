/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.TorusRationalMapModulus
import Nyll.JacobianVarieties.Generalized.ModulusAbelTransition
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniquenessGeometric

/-! # Torus-valued group homomorphisms do not depend on modulus thickness

For two full moduli with the same support, precomposition with the actual
transition induces a bijection on homomorphisms to any torus. The proof uses
the original curve point, actual Abel maps and the torus modulus theorem.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d e : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (E : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of K))))
  (hDE : D.I ≤ E.I)
  (hU : modulusComplement (modulusCurveMap D) = modulusComplement (modulusCurveMap E))

include hU

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in
/-- Equal open complements make the canonical restriction an actual isomorphism. -/
theorem isIso_modulusComplementRestriction_of_eq :
    IsIso (modulusComplementRestriction c (Scheme.IdealSheafData.inclusion hDE)
      (modulusIdealInclusion_curve c D E hDE)) := by
  let r := modulusComplementRestriction c (Scheme.IdealSheafData.inclusion hDE)
    (modulusIdealInclusion_curve c D E hDE)
  let s : Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ c) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
    Over.homMk (C.homOfLE hU.symm.le) (by
      change C.homOfLE hU.symm.le ≫
        ((modulusComplement (modulusCurveMap D)).ι ≫ c) =
          (modulusComplement (modulusCurveMap E)).ι ≫ c
      rw [← Category.assoc, Scheme.homOfLE_ι])
  have hrs : r ≫ s = 𝟙 _ := by
    apply Over.OverMorphism.ext
    change C.homOfLE hU.le ≫ C.homOfLE hU.symm.le = 𝟙 _
    rw [Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl]
  have hsr : s ≫ r = 𝟙 _ := by
    apply Over.OverMorphism.ext
    change C.homOfLE hU.symm.le ≫ C.homOfLE hU.le = 𝟙 _
    rw [Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl]
  exact ⟨⟨s, hrs, hsr⟩⟩

/-- Thickening a modulus without changing its support does not change the
group homomorphisms to a torus. The bijection is precomposition with the
actual transition, over the original field. -/
theorem transition_torusHom_bijective
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (T : CommGrp (Over (Spec (CommRingCat.of K)))) [IsTorus T] :
    Function.Bijective
      (fun ψ : groupScheme c E ⟶ T => transition c D E hDE ≫ ψ) := by
  let r := modulusComplementRestriction c (Scheme.IdealSheafData.inclusion hDE)
    (modulusIdealInclusion_curve c D E hDE)
  have : IsIso r := isIso_modulusComplementRestriction_of_eq c D E hDE hU
  let εE := ε ≫ r
  let aD := modulusAbelMap c D ε
  let aE := modulusAbelMap c E εE
  have ha : aD ≫ (transition c D E hDE).hom.hom.hom = r ≫ aE :=
    modulusAbelMap_transitionAlong c D E (Scheme.IdealSheafData.inclusion hDE)
      (modulusIdealInclusion_curve c D E hDE) ε
  constructor
  · intro ψ χ h
    apply modulusAbel_groupHom_ext c E εE T ψ χ
    apply (cancel_epi r).mp
    have hh := congrArg (fun f : groupScheme c D ⟶ T => aD ≫ f.hom.hom.hom) h
    change aD ≫ (transition c D E hDE).hom.hom.hom ≫ ψ.hom.hom.hom =
      aD ≫ (transition c D E hDE).hom.hom.hom ≫ χ.hom.hom.hom at hh
    simpa only [← Category.assoc, ha] using hh
  · intro φ
    let q : Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ c) ⟶ T.X :=
      inv r ≫ aD ≫ φ.hom.hom.hom
    have hε : εE ≫ q = 1 := by
      change (ε ≫ r) ≫ (inv r ≫ aD ≫ φ.hom.hom.hom) = 1
      rw [Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc,
        modulusAbelMap_basepoint, MonObj.one_comp]
    obtain ⟨ψ, hψ, _⟩ := existsUnique_groupHom_torus c T E εE q hε
    refine ⟨ψ, ?_⟩
    apply modulusAbel_groupHom_ext c D ε T
    change aD ≫ (transition c D E hDE).hom.hom.hom ≫ ψ.hom.hom.hom =
      aD ≫ φ.hom.hom.hom
    rw [← Category.assoc, ha, Category.assoc, hψ]
    exact IsIso.hom_inv_id_assoc r (aD ≫ φ.hom.hom.hom)

/-- Every torus-valued group morphism kills the full transition kernel,
on every test scheme, when only the thickness of the modulus changes. -/
theorem torusHom_kills_transition_kernel
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (T : CommGrp (Over (Spec (CommRingCat.of K)))) [IsTorus T]
    (φ : groupScheme c D ⟶ T)
    {S : Over (Spec (CommRingCat.of K))} (x : S ⟶ (groupScheme c D).X)
    (hx : x ≫ (transition c D E hDE).hom.hom.hom = 1) :
    x ≫ φ.hom.hom.hom = 1 := by
  obtain ⟨ψ, hψ⟩ := (transition_torusHom_bijective c D E hDE hU ε T).surjective φ
  rw [← hψ]
  change x ≫ (transition c D E hDE).hom.hom.hom ≫ ψ.hom.hom.hom = 1
  rw [← Category.assoc, hx, MonObj.one_comp]

end AlgebraicGeometry.GeneralizedJacobian
