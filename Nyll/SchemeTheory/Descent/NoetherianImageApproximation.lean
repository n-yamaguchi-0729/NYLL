/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.AffineTransitionImageLimit
public import Nyll.SchemeTheory.Descent.FGSubalgebra
public import Nyll.SchemeTheory.Descent.SubalgebraStagesIsLimitCone
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.FiniteType

/-!
# Proper Noetherian images of a closed subscheme in a fixed ambient model

A closed subscheme of the base change of a proper scheme over a Noetherian
ring is recovered as the limit of its actual images over finitely generated
subalgebras. Every image is proper over its actual Noetherian stage ring.
No finite-presentation hypothesis is imposed on the closed subscheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SubalgebraImageApproximation

universe u

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
variable {ι : Type u} [Preorder ι] (S : ι →o Subalgebra A₀ A)

variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀))

/-- The actual ambient schemes over the original ordered subalgebras. -/
abbrev ambientDiagram : ιᵒᵖ ⥤ Scheme.{u} :=
  SubalgebraStages.diagram S f₀

/-- The actual ambient cone with vertex the base change to `A`. -/
abbrev ambientCone : Cone (ambientDiagram S f₀) :=
  SubalgebraStages.cone S f₀

/-- Exhaustiveness of the ring stages gives the actual ambient limit. -/
def ambientConeIsLimit [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (hS : ∀ a : A, ∃ i, a ∈ S i) : IsLimit (ambientCone S f₀) :=
  (SubalgebraStages.nonempty_isLimit_cone S
    hS f₀).some

variable {Z : Scheme.{u}} (j : Z ⟶ (ambientCone S f₀).pt)

/-- The proper approximation consists of the actual stage images of `j`. -/
abbrev diagram : ιᵒᵖ ⥤ Scheme.{u} :=
  AffineTransitionImage.diagram (ambientDiagram S f₀) (ambientCone S f₀) j

/-- The cone whose source is the original closed subscheme. -/
abbrev cone : Cone (diagram S f₀ j) :=
  AffineTransitionImage.cone (ambientDiagram S f₀) (ambientCone S f₀) j

/-- The actual map from a stage image to its original stage ring. -/
def baseMap (i : ιᵒᵖ) :
    (diagram S f₀ j).obj i ⟶ Spec (CommRingCat.of (S i.unop)) :=
  AffineTransitionImage.inclusion (ambientDiagram S f₀)
    (ambientCone S f₀) j i ≫
      pullback.snd f₀ (SubalgebraStages.specHom S i.unop)

/-- The actual stage maps commute with the inclusions of their base rings. -/
lemma transition_baseMap {i k : ιᵒᵖ} (f : i ⟶ k) :
    (diagram S f₀ j).map f ≫ baseMap S f₀ j k =
      baseMap S f₀ j i ≫
        (SubalgebraStages.specDiagram S).map f := by
  change AffineTransitionImage.transition (ambientDiagram S f₀)
      (ambientCone S f₀) j f ≫
        (AffineTransitionImage.inclusion (ambientDiagram S f₀)
          (ambientCone S f₀) j k ≫ _) = _
  rw [← Category.assoc, AffineTransitionImage.transition_inclusion,
    Category.assoc, SubalgebraStages.diagram_map_snd, ← Category.assoc]
  rfl

/-- The actual image diagram lies over the diagram of spectra of its stage rings. -/
def baseMaps : diagram S f₀ j ⟶
    SubalgebraStages.specDiagram S where
  app i := baseMap S f₀ j i
  naturality _ _ f := transition_baseMap S f₀ j f

instance [IsProper f₀] (i : ιᵒᵖ) :
    IsProper (baseMap S f₀ j i) := by
  dsimp only [baseMap]
  infer_instance

instance [IsProper f₀] (i : ιᵒᵖ) :
    CompactSpace ((diagram S f₀ j).obj i) :=
  QuasiCompact.compactSpace_of_compactSpace (baseMap S f₀ j i)

instance [IsProper f₀] (i : ιᵒᵖ) :
    QuasiSeparatedSpace ((diagram S f₀ j).obj i) :=
  quasiSeparatedSpace_of_quasiSeparated (baseMap S f₀ j i)

/-- Every image stage is an actual proper Noetherian scheme. -/
theorem stage_isNoetherian [IsProper f₀]
    (i : ιᵒᵖ) [IsNoetherianRing (S i.unop)] : IsNoetherian ((diagram S f₀ j).obj i) := by
  have : IsLocallyNoetherian ((diagram S f₀ j).obj i) :=
    LocallyOfFiniteType.isLocallyNoetherian (baseMap S f₀ j i)
  exact {}

/-- The original closed subscheme is the limit of the actual proper image stages. -/
def coneIsLimit [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (hS : ∀ a : A, ∃ i, a ∈ S i) [IsProper f₀] [IsClosedImmersion j] :
    IsLimit (cone S f₀ j) :=
  AffineTransitionImage.coneIsLimit (ambientDiagram S f₀)
    (ambientCone S f₀) (ambientConeIsLimit S f₀ hS) j

@[reassoc]
lemma cone_projection_baseMap (i : ιᵒᵖ) :
    (cone S f₀ j).π.app i ≫ baseMap S f₀ j i =
      j ≫ pullback.snd f₀ (SubalgebraStages.specHomTop (A₀ := A₀) (A := A)) ≫
        SubalgebraStages.specLeg S i.unop := by
  rw [baseMap, ← Category.assoc, AffineTransitionImage.cone_projection_inclusion,
    Category.assoc, SubalgebraStages.cone_π_app_snd]

end AlgebraicGeometry.SubalgebraImageApproximation

namespace AlgebraicGeometry.NoetherianImageApproximation

universe u

variable (A₀ A : Type u) [CommRing A₀] [CommRing A] [Algebra A₀ A]

/-- The exhaustive ordered family of actual finitely generated subalgebras. -/
@[reducible]
def subalgebras : FGSubalgebra A₀ A →o Subalgebra A₀ A where
  toFun B := B.1
  monotone' _ _ h := h

/-- Every element occurs in its actual singleton-generated subalgebra. -/
theorem exhaustive (a : A) : ∃ B, a ∈ subalgebras A₀ A B := by
  classical
  refine ⟨⟨Algebra.adjoin A₀ (↑({a} : Finset A) : Set A),
    Subalgebra.fg_adjoin_finset {a}⟩, ?_⟩
  exact Algebra.subset_adjoin (Finset.mem_singleton_self a)

variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀))

/-- The original finitely generated ambient diagram, using the general image construction. -/
abbrev ambientDiagram : (FGSubalgebra A₀ A)ᵒᵖ ⥤ Scheme.{u} :=
  SubalgebraImageApproximation.ambientDiagram (subalgebras A₀ A) f₀

/-- The original ambient cone. -/
abbrev ambientCone : Cone (ambientDiagram A₀ A f₀) :=
  SubalgebraImageApproximation.ambientCone (subalgebras A₀ A) f₀

/-- The existing exhaustive finitely generated family supplies the ambient limit. -/
def ambientConeIsLimit : IsLimit (ambientCone A₀ A f₀) :=
  SubalgebraImageApproximation.ambientConeIsLimit
    (subalgebras A₀ A) f₀ (exhaustive A₀ A)

variable {Z : Scheme.{u}} (j : Z ⟶ (ambientCone A₀ A f₀).pt)

/-- The original image diagram. -/
abbrev diagram : (FGSubalgebra A₀ A)ᵒᵖ ⥤ Scheme.{u} :=
  SubalgebraImageApproximation.diagram (subalgebras A₀ A) f₀ j

/-- The original image cone. -/
abbrev cone : Cone (diagram A₀ A f₀ j) :=
  SubalgebraImageApproximation.cone (subalgebras A₀ A) f₀ j

/-- The original stage structure map. -/
abbrev baseMap (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    (diagram A₀ A f₀ j).obj i ⟶ Spec (CommRingCat.of i.unop.1) :=
  SubalgebraImageApproximation.baseMap (subalgebras A₀ A) f₀ j i

lemma transition_baseMap {i k : (FGSubalgebra A₀ A)ᵒᵖ} (h : i ⟶ k) :
    (diagram A₀ A f₀ j).map h ≫ baseMap A₀ A f₀ j k =
      baseMap A₀ A f₀ j i ≫
        (SubalgebraStages.specDiagram (subalgebras A₀ A)).map h :=
  SubalgebraImageApproximation.transition_baseMap (subalgebras A₀ A) f₀ j h

/-- The original natural transformation to the stage spectra. -/
abbrev baseMaps : diagram A₀ A f₀ j ⟶
    SubalgebraStages.specDiagram (subalgebras A₀ A) :=
  SubalgebraImageApproximation.baseMaps (subalgebras A₀ A) f₀ j

/-- Every actual finitely generated ring stage is Noetherian. -/
theorem stageRing_isNoetherian [IsNoetherianRing A₀] (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    IsNoetherianRing i.unop.1 := by
  have : Algebra.FiniteType A₀ i.unop.1 :=
    (Subalgebra.fg_iff_finiteType i.unop.1).mp i.unop.2
  exact Algebra.FiniteType.isNoetherianRing A₀ i.unop.1

/-- The original stage images are proper Noetherian schemes. -/
theorem stage_isNoetherian [IsNoetherianRing A₀] [IsProper f₀]
    (i : (FGSubalgebra A₀ A)ᵒᵖ) : IsNoetherian ((diagram A₀ A f₀ j).obj i) := by
  have : IsNoetherianRing i.unop.1 := stageRing_isNoetherian A₀ A i
  exact SubalgebraImageApproximation.stage_isNoetherian (subalgebras A₀ A) f₀ j i

/-- The original closed subscheme is the limit of its finitely generated image stages. -/
def coneIsLimit [IsProper f₀] [IsClosedImmersion j] :
    IsLimit (cone A₀ A f₀ j) :=
  SubalgebraImageApproximation.coneIsLimit (subalgebras A₀ A) f₀ j (exhaustive A₀ A)

@[reassoc]
lemma cone_projection_baseMap (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    (cone A₀ A f₀ j).π.app i ≫ baseMap A₀ A f₀ j i =
      j ≫ pullback.snd f₀ (SubalgebraStages.specHomTop (A₀ := A₀) (A := A)) ≫
        SubalgebraStages.specLeg (subalgebras A₀ A) i.unop :=
  SubalgebraImageApproximation.cone_projection_baseMap (subalgebras A₀ A) f₀ j i

end AlgebraicGeometry.NoetherianImageApproximation
