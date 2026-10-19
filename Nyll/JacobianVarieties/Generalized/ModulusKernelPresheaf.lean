/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitBoundaryInjective
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedBaseTwist
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # The actual forgetful kernel and its local scalar representatives -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)

/-- Actual modulus classes whose ordinary relative class is trivial. -/
def modulusForgetfulKernelPresheaf :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of ((forgetModulusZeroGroupPresheaf c i).app T).hom.ker
  map {T T'} f := CommGrpCat.ofHom
    ((((modulusPicardZeroGroupPresheaf c i).map f).hom.comp
      (((forgetModulusZeroGroupPresheaf c i).app T).hom.ker.subtype)).codRestrict
        (((forgetModulusZeroGroupPresheaf c i).app T').hom.ker) (fun x => by
          apply MonoidHom.mem_ker.mpr
          have h := ConcreteCategory.congr_hom
            ((forgetModulusZeroGroupPresheaf c i).naturality f) x.val
          exact h.trans (by
            change ((Unrigidified.zeroCommGrpPresheaf c).map f).hom
              (((forgetModulusZeroGroupPresheaf c i).app T).hom x.val) = 1
            rw [MonoidHom.mem_ker.mp x.property, map_one])))
  map_id T := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((modulusPicardZeroGroupPresheaf c i).map_id T) x.val
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((modulusPicardZeroGroupPresheaf c i).map_comp f g) x.val

/-- Inclusion of the genuine pointwise forgetful kernel. -/
def modulusForgetfulKernelInclusion :
    modulusForgetfulKernelPresheaf c i ⟶ modulusPicardZeroGroupPresheaf c i where
  app T := CommGrpCat.ofHom (((forgetModulusZeroGroupPresheaf c i).app T).hom.ker.subtype)
  naturality {_ _} _ := rfl

/-- The actual scalar boundary factors through the genuine forgetful kernel. -/
def modulusBoundaryToKernelPresheaf :
    liftedModulusUnitQuotientGroupPresheaf (i ≫ c) ⟶ modulusForgetfulKernelPresheaf c i where
  app T := CommGrpCat.ofHom (((modulusUnitBoundaryPresheaf c i).app T).hom.codRestrict
    (((forgetModulusZeroGroupPresheaf c i).app T).hom.ker) (fun a => by
      apply MonoidHom.mem_ker.mpr
      rcases a with ⟨a⟩
      refine QuotientGroup.induction_on a fun a => ?_
      exact modulusUnitsBoundary_forget c i T.unop a))
  naturality {T T'} f := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((modulusUnitBoundaryPresheaf c i).naturality f) a

variable {K : Type u} [Field K] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (i : D ⟶ C)
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

/-- The scalar boundary into the actual kernel is injective on every parameter scheme. -/
instance modulusBoundaryToKernelPresheaf_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusBoundaryToKernelPresheaf c i) := by
  apply Presheaf.isLocallyInjective_of_injective
  intro T a b h
  apply ULift.ext
  exact modulusUnitQuotientBoundary_injective c i T.unop (congrArg Subtype.val h)

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c] in
/-- Kernel classes admit actual scalar representatives on the open cover trivializing
its actual base twist; no rational curve section is used. -/
theorem modulusBoundaryToKernelPresheaf_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusBoundaryToKernelPresheaf c i) := by
  constructor
  intro T x
  rcases x with ⟨⟨x, hx⟩, hzero⟩
  induction x using Quotient.ind with
  | _ M =>
    let L : Unrigidified.LineBundle c T.hom := ⟨M.L, M.isInvertible⟩
    have hL : (Quot.mk _ L : Unrigidified.Classes c T.hom) =
        Quot.mk _ ⟨𝟙_ (pullback c T.hom).Modules, Scheme.Modules.isInvertible_unit _⟩ :=
      congrArg (fun a : (Unrigidified.zeroCommGrpPresheaf c).obj (op T) => a.val) hzero
    let V := (Unrigidified.zeroClassTrivializationCover c T.hom L hL).val
    let U (j : V.I₀) : Over (Spec (CommRingCat.of K)) := Over.mk (V.f j ≫ T.hom)
    let f (j : V.I₀) : U j ⟶ T := Over.homMk (V.f j) rfl
    have hcover : Sieve.ofArrows U f ∈
        (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) T := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      apply Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage
      exact V.mem_grothendieckTopology
    apply (Scheme.fppfTopology.over (Spec (CommRingCat.of K))).superset_covering ?_ hcover
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro j
    let s : SchemeHomOver (V.f j ≫ T.hom) T.hom := ⟨V.f j, rfl⟩
    let N := M.pullback (baseChangeSnd c s) (baseChangeSnd (i ≫ c) s)
      (modulusBaseChange_naturality c i s)
    let y := (modulusForgetfulKernelPresheaf c i).map (f j).op
      ⟨⟨RigidifiedLineBundle.classOf M, hx⟩, hzero⟩
    have hN : Nonempty (N.L ≅ 𝟙_ (pullback c (U j).hom).Modules) :=
      (Unrigidified.zeroClassTrivializationCover c T.hom L hL).property j
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp
      (modulusUnitQuotientBoundary_range c i (U j)) y.val).mpr hN
    exact ⟨ULift.up a, Subtype.ext ha⟩

/-- The fppf sheafification of the genuine pointwise kernel. -/
def modulusForgetfulKernelGroupSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) CommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    CommGrpCat.{u + 1}).obj (modulusForgetfulKernelPresheaf c i)

/-- The actual locally bijective scalar boundary identifies the intrinsic unit quotient
with the sheafified forgetful kernel, as commutative groups. -/
def modulusUnitKernelGroupSheafIso :
    modulusUnitQuotientGroupSheaf (i ≫ c) ≅ modulusForgetfulKernelGroupSheaf c i := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))
  have : Presheaf.IsLocallySurjective J (modulusBoundaryToKernelPresheaf c i) :=
    modulusBoundaryToKernelPresheaf_isLocallySurjective c i
  let m : modulusUnitQuotientGroupSheaf (i ≫ c) ⟶ modulusForgetfulKernelGroupSheaf c i :=
    (presheafToSheaf J CommGrpCat.{u + 1}).map (modulusBoundaryToKernelPresheaf c i)
  have hm : IsIso m := (J.W_iff (modulusBoundaryToKernelPresheaf c i)).mp
    (J.W_of_isLocallyBijective (modulusBoundaryToKernelPresheaf c i))
  exact ⟨m, Classical.choose hm.out, (Classical.choose_spec hm.out).1,
    (Classical.choose_spec hm.out).2⟩

end AlgebraicGeometry.GeneralizedJacobian
