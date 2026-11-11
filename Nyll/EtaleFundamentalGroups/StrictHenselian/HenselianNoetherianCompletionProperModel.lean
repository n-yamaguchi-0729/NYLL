/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianCompletionImages
public import Nyll.SchemeTheory.Descent.FgSubalgebraProperFlatPullback
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.ProperFinitePresentationAmbient
public import Nyll.SchemeTheory.Descent.NoetherianImageResidueLimit

/-!
# Actual proper ambient models over completed image rings

Finite coefficients in the completion colimit lie in one actual complete
Noetherian image ring. Proper finite-presentation descent therefore supplies
a proper model over such an image. Applying this to a genuine proper
finite-presentation ambient gives an actual closed embedding of every
original proper scheme into the required image-limit ambient. Its structure
morphism is the original one, without a finite-presentation hypothesis.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits
open AlgebraicCurves.Geometry.Schemes.Proofs.ProperFlatFinitePresentationDescent.ApproxAux

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [IsNoetherianRing R]
  [CommRing A] [Algebra R A] [HenselianLocalRing A]

omit [IsNoetherianRing R] in
/-- A finite set of original colimit coefficients lies in one later complete image. -/
theorem exists_completionImageAlgebra_contains_finset (i₀ : FGSubalgebra R A)
    (s : Finset (completionColimit R A)) :
    ∃ i : completionImageIndex R A i₀,
      (↑s : Set (completionColimit R A)) ⊆ completionImagesAfter R A i₀ i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨⟨i₀, le_rfl⟩, ?_⟩
      intro x hx
      exact False.elim (Finset.notMem_empty x hx)
  | @insert a s _ ih =>
      obtain ⟨i, hi⟩ := completionImagesAfter_exhaustive R A i₀ a
      obtain ⟨j, hj⟩ := ih
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (completionImagesAfter R A i₀).monotone hik hi
      · exact (completionImagesAfter R A i₀).monotone hjk (hj hx)

omit [IsNoetherianRing R] in
/-- Every actual finitely generated coefficient algebra is contained in an
actual later complete image, using its finite generators. -/
theorem exists_completionImageAlgebra_contains_fg (i₀ : FGSubalgebra R A)
    (T : Subalgebra (completionImage R A i₀) (completionColimit R A)) (hT : T.FG) :
    ∃ i : completionImageIndex R A i₀, T ≤ completionImagesAfter R A i₀ i := by
  obtain ⟨s, hs⟩ := hT
  obtain ⟨i, hi⟩ := exists_completionImageAlgebra_contains_finset R A i₀ s
  refine ⟨i, ?_⟩
  rw [← hs]
  exact Algebra.adjoin_le hi

/-- The original proper finitely presented family descends to a complete
Noetherian image ring, preserving the actual Cartesian square and coefficients. -/
theorem exists_proper_completionImage_model (i₀ : FGSubalgebra R A)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (completionColimit R A))
    [IsProper g] [LocallyOfFinitePresentation g] (s : Finset (completionColimit R A)) :
    ∃ (i : completionImageIndex R A i₀),
      (↑s : Set (completionColimit R A)) ⊆ completionImage R A i.1 ∧
      ∃ (Y₀ : Scheme.{u}) (g₀ : Y₀ ⟶ Spec (CommRingCat.of (completionImage R A i.1)))
        (π : Y ⟶ Y₀), IsProper g₀ ∧ LocallyOfFinitePresentation g₀ ∧
          IsPullback π g g₀
            (Spec.map (CommRingCat.ofHom (completionImage R A i.1).subtype)) := by
  classical
  obtain ⟨T, hT, hs, Y₁, g₁, π₁, hprop₁, hlfp₁, sq₁⟩ :=
    @ProperFinitePresentationDescent (completionImage R A i₀) _ _
      (completionColimit R A) _
      (Algebra.ofSubsemiring (A := completionColimit R A) (completionImage R A i₀))
      Y g (inferInstance : IsProper g) (inferInstance : LocallyOfFinitePresentation g) s
  obtain ⟨i, hTi⟩ := exists_completionImageAlgebra_contains_fg R A i₀ T hT
  let κ : Spec (CommRingCat.of (completionImage R A i.1)) ⟶
      Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTi).toRingHom)
  let σ : Spec (completionColimit R A) ⟶
      Spec (CommRingCat.of (completionImage R A i.1)) :=
    Spec.map (CommRingCat.ofHom (completionImage R A i.1).subtype)
  have hκ : σ ≫ κ = Spec.map (CommRingCat.ofHom (algebraMap T (completionColimit R A))) := by
    dsimp only [σ, κ]
    exact (Spec.map_comp
      (CommRingCat.ofHom (Subalgebra.inclusion hTi).toRingHom)
      (CommRingCat.ofHom (completionImage R A i.1).subtype)).symm
  obtain ⟨π₀, sq₀⟩ := exists_isPullback_of_fac sq₁ κ σ hκ
  have : IsProper g₁ := hprop₁
  have : LocallyOfFinitePresentation g₁ := hlfp₁
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    locallyOfFinitePresentation_isStableUnderBaseChange
  have hlfp₀ : LocallyOfFinitePresentation (pullback.snd g₁ κ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback g₁ κ) hlfp₁
  exact ⟨i, fun _ ha => hTi (hs ha), pullback g₁ κ, pullback.snd g₁ κ,
    π₀, inferInstance, hlfp₀, sq₀⟩

/-- Every proper scheme over the constructed colimit has an actual closed
embedding into an image-limit ambient over one complete Noetherian image.
The original structure morphism is retained as an exact equation. -/
theorem exists_proper_completionImage_ambient
    {X : Scheme.{u}} (f : X ⟶ Spec (completionColimit R A)) [IsProper f] :
    ∃ (i₀ : FGSubalgebra R A) (X₀ : Scheme.{u})
      (f₀ : X₀ ⟶ Spec (CommRingCat.of (completionImage R A i₀))),
      IsProper f₀ ∧ LocallyOfFinitePresentation f₀ ∧
        ∃ j : X ⟶ (SubalgebraImageApproximation.ambientCone
            (completionImagesAfter R A i₀) f₀).pt,
          IsClosedImmersion j ∧
            SubalgebraImageApproximation.originalBaseMap
              (completionImagesAfter R A i₀) f₀ j = f := by
  obtain ⟨Y, i, g, hi, hg, hgfp, hig⟩ :=
    @exists_proper_finitePresentation_ambient (completionColimit R A) _ X f
      (inferInstance : IsProper f)
  have : IsClosedImmersion i := hi
  have : IsProper g := hg
  have : LocallyOfFinitePresentation g := hgfp
  let i₁ : FGSubalgebra R A := Classical.choice inferInstance
  obtain ⟨k, -, X₀, f₀, π, hf₀, hfp₀, sq⟩ :=
    @exists_proper_completionImage_model R A _ _ _ _ _ i₁ Y g hg hgfp ∅
  let e : Y ≅ (SubalgebraImageApproximation.ambientCone
      (completionImagesAfter R A k.1) f₀).pt := sq.isoPullback
  refine ⟨k.1, X₀, f₀, hf₀, hfp₀, i ≫ e.hom, inferInstance, ?_⟩
  change (i ≫ e.hom) ≫ pullback.snd f₀
    (Spec.map (CommRingCat.ofHom (completionImage R A k.1).subtype)) = f
  exact (Category.assoc i e.hom _).trans
    ((congrArg (fun a => i ≫ a) sq.isoPullback_hom_snd).trans hig)

end AlgebraicGeometry.HenselianNoetherianImageStages
