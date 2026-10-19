/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.OpenImmersion
import Nyll.JacobianVarieties.Generalized.PicardZeroLocalSums
import Nyll.JacobianVarieties.Generalized.PicardZeroGeometricEquality

/-! # Compatibility of the actual divisor atlas in the original zero sheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra

namespace AlgebraicGeometry.GeneralizedJacobian.ModulusDivisorAtlas

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)}
  [IsProper c] [SmoothOfRelativeDimension 1 c]
  {d : ℕ} {D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c)}
  {T : Over (Spec (CommRingCat.of K))}
  {x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)}
  (A : ModulusDivisorAtlas c D ε T x)

/-- The actual degree-zero class on a chart, before sheafification. -/
def rawClass (j : A.cover.I₀) :
    (modulusPicardZeroPresheaf c (modulusCurveMap D)).obj
      (op (Over.mk (A.cover.f j ≫ T.hom))) :=
  ⟨RigidifiedLineBundle.classOf (A.bundle j), A.degree_zero j⟩

/-- Pulling a raw chart representative back and then sheafifying gives the
restriction of the originally specified section along the composite map. -/
theorem rawClass_toSheafify_pullback {V : Over (Spec (CommRingCat.of K))}
    (j : A.cover.I₀) (f : V ⟶ Over.mk (A.cover.f j ≫ T.hom)) :
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroPresheaf c (modulusCurveMap D))).app (op V)
        ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map f.op (A.rawClass j)) =
      (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map
        (f ≫ (Over.homMk (A.cover.f j) : Over.mk (A.cover.f j ≫ T.hom) ⟶ T)).op x := by
  let η : modulusPicardZeroPresheaf c (modulusCurveMap D) ⟶
      (modulusPicardZeroSheaf c (modulusCurveMap D)).obj :=
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroPresheaf c (modulusCurveMap D))
  have hn := ConcreteCategory.congr_hom (η.naturality f.op) (A.rawClass j)
  change η.app (op V)
      ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map f.op (A.rawClass j)) =
    (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map f.op
      (η.app (op (Over.mk (A.cover.f j ≫ T.hom))) (A.rawClass j)) at hn
  exact hn.trans ((congrArg
    ((modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map f.op) (A.represents j)).trans
      (ConcreteCategory.congr_hom
        ((modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map_comp
          (Over.homMk (A.cover.f j) : Over.mk (A.cover.f j ≫ T.hom) ⟶ T).op f.op) x).symm)

/-- The actual raw chart representatives agree after sheafification on every overlap. -/
theorem rawClass_toSheafify_overlap {V : Over (Spec (CommRingCat.of K))}
    (i j : A.cover.I₀)
    (f : V ⟶ Over.mk (A.cover.f i ≫ T.hom))
    (g : V ⟶ Over.mk (A.cover.f j ≫ T.hom))
    (h : f ≫ (Over.homMk (A.cover.f i) : Over.mk (A.cover.f i ≫ T.hom) ⟶ T) =
      g ≫ (Over.homMk (A.cover.f j) : Over.mk (A.cover.f j ≫ T.hom) ⟶ T)) :
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroPresheaf c (modulusCurveMap D))).app (op V)
        ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map f.op (A.rawClass i)) =
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardZeroPresheaf c (modulusCurveMap D))).app (op V)
          ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map g.op (A.rawClass j)) := by
  rw [A.rawClass_toSheafify_pullback i f, A.rawClass_toSheafify_pullback j g, h]

/-- Every geometric test of an overlap identifies the original rigidified
classes, retaining the full modulus rather than only its reduced support. -/
theorem rawClass_overlap_geometricPoint {V : Over (Spec (CommRingCat.of K))}
    (i j : A.cover.I₀)
    (f : V ⟶ Over.mk (A.cover.f i ≫ T.hom))
    (g : V ⟶ Over.mk (A.cover.f j ≫ T.hom))
    (h : f ≫ (Over.homMk (A.cover.f i) : Over.mk (A.cover.f i ≫ T.hom) ⟶ T) =
      g ≫ (Over.homMk (A.cover.f j) : Over.mk (A.cover.f j ≫ T.hom) ⟶ T))
    {L : Type u} [Field L] [IsAlgClosed L]
    {s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)} (p : Over.mk s ⟶ V) :
    (modulusPicardPresheaf c (modulusCurveMap D)).map p.op
        ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map f.op (A.rawClass i)).val =
      (modulusPicardPresheaf c (modulusCurveMap D)).map p.op
        ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map g.op (A.rawClass j)).val :=
  modulusPicardZero_raw_eq_on_geometricPoint c (modulusCurveMap D) _ _
    (A.rawClass_toSheafify_overlap i j f g h) p

/-- Every field-valued point lifts to one actual affine chart of the atlas. -/
theorem exists_fieldPoint_lift
    {L : Type u} [Field L] {s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)}
    (p : Over.mk s ⟶ T) :
    ∃ (j : A.cover.I₀) (z : Over.mk s ⟶ Over.mk (A.cover.f j ≫ T.hom)),
      z ≫ (Over.homMk (A.cover.f j) : Over.mk (A.cover.f j ≫ T.hom) ⟶ T) = p := by
  have : Inhabited (Over.mk s).left :=
    inferInstanceAs (Inhabited (Spec (CommRingCat.of L)))
  have : Subsingleton (Over.mk s).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of L)))
  obtain ⟨j, y, hy⟩ := A.cover.openCover.exists_eq (p.left default)
  have : IsOpenImmersion (A.cover.f j) := A.cover.map_prop j
  have hrange : Set.range p.left ⊆ Set.range (A.cover.f j) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨y, hy.trans (congrArg p.left (Subsingleton.elim default z))⟩
  let ell : Spec (CommRingCat.of L) ⟶ Spec (A.cover.X j) :=
    IsOpenImmersion.lift (A.cover.f j) p.left hrange
  have hell : ell ≫ A.cover.f j = p.left :=
    IsOpenImmersion.lift_fac (A.cover.f j) p.left hrange
  have hel : ell ≫ (A.cover.f j ≫ T.hom) = s := by
    rw [← Category.assoc, hell]
    exact Over.w p
  refine ⟨j, Over.homMk ell hel, ?_⟩
  apply Over.OverMorphism.ext
  exact hell

end AlgebraicGeometry.GeneralizedJacobian.ModulusDivisorAtlas
