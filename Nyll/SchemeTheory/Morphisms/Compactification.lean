/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.ChowDatum
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Compactifications and their common refinements

A compactification is an actual factorization into an open immersion and a
proper morphism. Quasi-compact immersions into proper schemes give such
factorizations by taking their scheme-theoretic image. This constructs
compactifications of affine schemes of finite type over an affine base.

Two compactifications of a quasi-compact morphism admit a common proper
refinement, constructed as the image in their fiber product. These are
geometric inputs to compactly supported étale cohomology. Existence for
arbitrary separated finite-type schemes is not assumed here.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An open immersion into a proper scheme over the original base. -/
structure Compactification {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The proper ambient scheme. -/
  space : Scheme.{u}
  /-- The open inclusion of the original scheme. -/
  ι : X ⟶ space
  /-- The proper structure morphism. -/
  π : space ⟶ S
  /-- The first morphism is an open immersion. -/
  [isOpenImmersion : IsOpenImmersion ι]
  /-- The open immersion is quasi-compact. -/
  [quasiCompact : QuasiCompact ι]
  /-- The second morphism is proper. -/
  [isProper : IsProper π]
  /-- The factorization is over the specified base. -/
  fac : ι ≫ π = f

attribute [instance] Compactification.isOpenImmersion Compactification.quasiCompact
  Compactification.isProper

namespace Compactification

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Take the scheme-theoretic image of an immersion into a proper scheme. -/
def ofImmersion {P : Scheme.{u}} (i : X ⟶ P) [IsImmersion i] [QuasiCompact i]
    (p : P ⟶ S) [IsProper p] (h : i ≫ p = f) : Compactification f where
  space := i.image
  ι := i.toImage
  π := i.imageι ≫ p
  quasiCompact := by
    have : QuasiCompact (i.toImage ≫ i.imageι) := by
      rw [Scheme.Hom.toImage_imageι]
      infer_instance
    exact QuasiCompact.of_comp i.toImage i.imageι
  fac := by rw [← Category.assoc, Scheme.Hom.toImage_imageι, h]

/-- A proper scheme itself is a compactification with identity open inclusion. -/
def ofProper (f : X ⟶ S) [IsProper f] : Compactification f where
  space := X
  ι := 𝟙 X
  π := f
  fac := Category.id_comp f

/-- Pulling back the actual open/proper factorization gives a compactification
after any change of base. -/
def baseChange (C : Compactification f) {T : Scheme.{u}} (g : T ⟶ S) :
    Compactification (pullback.snd f g) := by
  let i : pullback f g ⟶ pullback C.π g :=
    pullback.lift (pullback.fst f g ≫ C.ι) (pullback.snd f g) (by
      rw [Category.assoc, C.fac]
      exact pullback.condition)
  have hi₁ : i ≫ pullback.fst C.π g = pullback.fst f g ≫ C.ι :=
    pullback.lift_fst _ _ _
  have hi₂ : i ≫ pullback.snd C.π g = pullback.snd f g := pullback.lift_snd _ _ _
  have hs : IsPullback (i ≫ pullback.snd C.π g) (pullback.fst f g) g (C.ι ≫ C.π) := by
    rw [hi₂, C.fac]
    exact (IsPullback.of_hasPullback f g).flip
  have hi : IsPullback i (pullback.fst f g) (pullback.fst C.π g) C.ι :=
    hs.of_right hi₁ (IsPullback.of_hasPullback C.π g).flip
  have : IsOpenImmersion i := MorphismProperty.of_isPullback hi.flip C.isOpenImmersion
  have : QuasiCompact i := MorphismProperty.of_isPullback hi.flip C.quasiCompact
  exact { space := pullback C.π g, ι := i, π := pullback.snd C.π g, fac := hi₂ }

/-- Two compactifications are dominated by an actual common compactification
whose maps to both ambient schemes are proper and preserve the open inclusions. -/
theorem exists_common_refinement (C D : Compactification f) :
    ∃ (E : Compactification f) (a : E.space ⟶ C.space) (b : E.space ⟶ D.space),
      IsProper a ∧ IsProper b ∧ E.ι ≫ a = C.ι ∧ E.ι ≫ b = D.ι ∧
        a ≫ C.π = E.π ∧ b ≫ D.π = E.π := by
  let P := pullback C.π D.π
  let p : P ⟶ S := pullback.fst C.π D.π ≫ C.π
  let i : X ⟶ P := pullback.lift C.ι D.ι (C.fac.trans D.fac.symm)
  have hiC : i ≫ pullback.fst C.π D.π = C.ι := pullback.lift_fst _ _ _
  have hiD : i ≫ pullback.snd C.π D.π = D.ι := pullback.lift_snd _ _ _
  have hip : i ≫ p = f := by
    rw [← Category.assoc, hiC, C.fac]
  have : IsProper p := inferInstanceAs (IsProper (pullback.fst C.π D.π ≫ C.π))
  have : IsImmersion (i ≫ pullback.fst C.π D.π) := by
    rw [hiC]
    infer_instance
  have : IsImmersion i := IsImmersion.of_comp i (pullback.fst C.π D.π)
  have : QuasiCompact (i ≫ pullback.fst C.π D.π) := by
    rw [hiC]
    infer_instance
  have : QuasiCompact i := QuasiCompact.of_comp i (pullback.fst C.π D.π)
  let E : Compactification f := ofImmersion i p hip
  let a : E.space ⟶ C.space := i.imageι ≫ pullback.fst C.π D.π
  let b : E.space ⟶ D.space := i.imageι ≫ pullback.snd C.π D.π
  have ha : IsProper a := by
    change IsProper (i.imageι ≫ pullback.fst C.π D.π)
    infer_instance
  have hb : IsProper b := by
    change IsProper (i.imageι ≫ pullback.snd C.π D.π)
    infer_instance
  refine ⟨E, a, b, ha, hb, ?_, ?_, ?_, ?_⟩
  · change i.toImage ≫ (i.imageι ≫ pullback.fst C.π D.π) = C.ι
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hiC]
  · change i.toImage ≫ (i.imageι ≫ pullback.snd C.π D.π) = D.ι
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hiD]
  · exact Category.assoc _ _ _
  · change (i.imageι ≫ pullback.snd C.π D.π) ≫ D.π =
      i.imageι ≫ (pullback.fst C.π D.π ≫ C.π)
    rw [Category.assoc, pullback.condition]

end Compactification

open AlgebraicCurves.Geometry.Schemes.Proofs.ChowDatum_nonempty.AlgebraicGeometry.ChowLemma

/-- An affine scheme of finite type over an affine base has an actual
compactification, via its closed embedding in an affine projective chart. -/
theorem exists_compactification_of_isAffine
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] :
    Nonempty (Compactification f) := by
  let W : X.Opens := ⊤
  have hW : IsAffineOpen W := isAffineOpen_top X
  have : IsAffine W.toScheme := hW
  let n := chartN f W hW
  let P : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  let p : P ⟶ Spec (.of R) := ProjSpace.π R n
  let i : W.toScheme ⟶ P := chartJ f W hW
  have hip : i ≫ p = W.ι ≫ f := chartJ_over f W hW
  have : IsImmersion i := IsImmersion.isImmersion_iff_exists.mpr
    ⟨_, chartJD f W hW, _, chartJD_closed f W hW, inferInstance, chartJD_ι f W hW⟩
  have : IsProper p := inferInstanceAs (IsProper (ProjSpace.π R n))
  have : QuasiCompact (i ≫ p) := by
    rw [hip]
    infer_instance
  have : QuasiCompact i := QuasiCompact.of_comp i p
  let j : X ⟶ P := X.topIso.inv ≫ i
  have hjp : j ≫ p = f := by
    change (X.topIso.inv ≫ i) ≫ p = f
    rw [Category.assoc, hip, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  exact ⟨Compactification.ofImmersion j p hjp⟩

end AlgebraicGeometry
