/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusKernelPresheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Exactness at the actual modulus Picard-zero group sheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)

/-- The constant identity natural homomorphism on actual Picard-zero classes. -/
def modulusForgetfulIdentityPresheaf :
    modulusPicardZeroGroupPresheaf c i ⟶ RelPicard.Unrigidified.zeroCommGrpPresheaf c where
  app T := 1
  naturality {T T'} f := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact (((RelPicard.Unrigidified.zeroCommGrpPresheaf c).map f).hom.map_one).symm

/-- The literal forgetful kernel is an equalizer in commutative-group presheaves. -/
def modulusForgetfulKernelFork :
    Fork (forgetModulusZeroGroupPresheaf c i) (modulusForgetfulIdentityPresheaf c i) :=
  Fork.ofι (modulusForgetfulKernelInclusion c i) (by
    ext T x
    exact MonoidHom.mem_ker.mp x.property)

/-- Its universal property is supplied by codomain restriction to the actual group kernel. -/
def modulusForgetfulKernelForkIsLimit : IsLimit (modulusForgetfulKernelFork c i) := by
  apply Fork.IsLimit.mk'
  intro s
  let l : s.pt ⟶ modulusForgetfulKernelPresheaf c i :=
    { app T := CommGrpCat.ofHom ((s.ι.app T).hom.codRestrict
        (((forgetModulusZeroGroupPresheaf c i).app T).hom.ker) (fun x => by
          apply MonoidHom.mem_ker.mpr
          exact ConcreteCategory.congr_hom (NatTrans.congr_app s.condition T) x))
      naturality {T T'} f := by
        apply CommGrpCat.hom_ext
        apply MonoidHom.ext
        intro x
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (s.ι.naturality f) x }
  refine ⟨l, rfl, ?_⟩
  intro m hm
  ext T x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hm T) x

/-- The identity homomorphism on the actual sheaves. -/
def modulusForgetfulIdentitySheafFormula :
    modulusPicardZeroGroupSheaf c i ⟶ ordinaryRelativePicardZeroGroupSheaf c where
  hom :=
    { app T := 1
      naturality {T T'} f := by
        apply CommGrpCat.hom_ext
        apply MonoidHom.ext
        intro x
        exact (((ordinaryRelativePicardZeroGroupSheaf c).obj.map f).hom.map_one).symm }

/-- Sheafification sends the literal identity homomorphism to the actual identity map. -/
theorem sheafify_modulusForgetfulIdentity :
    (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      CommGrpCat.{u + 1}).map (modulusForgetfulIdentityPresheaf c i) =
        modulusForgetfulIdentitySheafFormula c i := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (ordinaryRelativePicardZeroGroupSheaf c).property
  calc
    _ = modulusForgetfulIdentityPresheaf c i ≫
        toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
          (RelPicard.Unrigidified.zeroCommGrpPresheaf c) :=
      (toSheafify_naturality (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusForgetfulIdentityPresheaf c i)).symm
    _ = _ := by
      ext T x
      exact ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (RelPicard.Unrigidified.zeroCommGrpPresheaf c)).app T).hom.map_one

/-- The identity sheaf map, kept in the same sheafification expression as the kernel fork. -/
def modulusForgetfulIdentitySheaf :
    modulusPicardZeroGroupSheaf c i ⟶ ordinaryRelativePicardZeroGroupSheaf c :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).map (modulusForgetfulIdentityPresheaf c i)

/-- This morphism has the literal constant identity formula on every section. -/
theorem modulusForgetfulIdentitySheaf_apply
    (T : (Over (Spec (CommRingCat.of R)))ᵒᵖ)
    (x : (modulusPicardZeroGroupSheaf c i).obj.obj T) :
    ((modulusForgetfulIdentitySheaf c i).hom.app T).hom x = 1 :=
  congrArg (fun f : modulusPicardZeroGroupSheaf c i ⟶
    ordinaryRelativePicardZeroGroupSheaf c => (f.hom.app T).hom x)
      (sheafify_modulusForgetfulIdentity c i)

variable {K : Type u} [Field K] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (i : D ⟶ C)
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c] in
/-- The actual boundary followed by forgetting is the identity element. -/
theorem modulusUnitBoundarySheaf_condition :
    modulusUnitBoundarySheaf c i ≫ forgetModulusZeroGroupSheaf c i =
      modulusUnitBoundarySheaf c i ≫ modulusForgetfulIdentitySheaf c i := by
  let S := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    CommGrpCat.{u + 1}
  change S.map (modulusUnitBoundaryPresheaf c i) ≫
      S.map (forgetModulusZeroGroupPresheaf c i) =
    S.map (modulusUnitBoundaryPresheaf c i) ≫
      S.map (modulusForgetfulIdentityPresheaf c i)
  rw [← S.map_comp, ← S.map_comp]
  apply congrArg S.map
  ext T a
  rcases a with ⟨a⟩
  refine QuotientGroup.induction_on a fun a => ?_
  exact modulusUnitsBoundary_forget c i T.unop a

/-- The actual scalar boundary has the kernel universal property after fppf sheafification. -/
def modulusUnitBoundarySheafIsKernel :
    IsLimit (Fork.ofι (modulusUnitBoundarySheaf c i)
      (modulusUnitBoundarySheaf_condition c i)) := by
  let S := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    CommGrpCat.{u + 1}
  have he : (modulusUnitKernelGroupSheafIso c i).hom ≫
      S.map (modulusForgetfulKernelInclusion c i) = modulusUnitBoundarySheaf c i := by
    change S.map (modulusBoundaryToKernelPresheaf c i) ≫
      S.map (modulusForgetfulKernelInclusion c i) = S.map (modulusUnitBoundaryPresheaf c i)
    rw [← S.map_comp]
    rfl
  let hK := isLimitForkMapOfIsLimit S
    (modulusForgetfulKernelFork c i).condition (modulusForgetfulKernelForkIsLimit c i)
  exact IsLimit.ofIsoLimit hK
    (Fork.ext (modulusUnitKernelGroupSheafIso c i).symm
      ((modulusUnitKernelGroupSheafIso c i).inv_comp_eq.mpr he.symm))

/-- Every section in the actual sheaf kernel is the boundary of a unique scalar-quotient section. -/
theorem modulusUnitBoundarySheaf_range (T : Over (Spec (CommRingCat.of K))) :
    Set.range ((modulusUnitBoundarySheaf c i).hom.app (op T)).hom =
      {x | ((forgetModulusZeroGroupSheaf c i).hom.app (op T)).hom x = 1} := by
  let E := sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    CommGrpCat.{u + 1} ⋙
      (evaluation _ CommGrpCat.{u + 1}).obj (op T) ⋙ forget CommGrpCat.{u + 1}
  let h := isLimitForkMapOfIsLimit E
    (modulusUnitBoundarySheaf_condition c i) (modulusUnitBoundarySheafIsKernel c i)
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    have hc := congrArg (fun f : modulusUnitQuotientGroupSheaf (i ≫ c) ⟶
        ordinaryRelativePicardZeroGroupSheaf c => (f.hom.app (op T)).hom a)
      (modulusUnitBoundarySheaf_condition c i)
    exact hc.trans (modulusForgetfulIdentitySheaf_apply c i (op T) _)
  · intro hx
    let k : PUnit.{u + 2} ⟶
        E.obj (modulusPicardZeroGroupSheaf c i) := TypeCat.ofHom (fun _ => x)
    have hk : k ≫ E.map (forgetModulusZeroGroupSheaf c i) =
        k ≫ E.map (modulusForgetfulIdentitySheaf c i) := by
      apply TypeCat.homEquiv.injective
      funext a
      exact hx.trans (modulusForgetfulIdentitySheaf_apply c i (op T) x).symm
    let a := (Fork.IsLimit.lift' h k hk).val PUnit.unit
    refine ⟨a, ?_⟩
    exact ConcreteCategory.congr_hom (Fork.IsLimit.lift' h k hk).property PUnit.unit

end AlgebraicGeometry.GeneralizedJacobian
