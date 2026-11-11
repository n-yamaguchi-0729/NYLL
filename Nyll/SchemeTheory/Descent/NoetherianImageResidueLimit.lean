/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

module

public import Nyll.SchemeTheory.RingTheory.FinitePresentation.SubalgebraResidueFieldColimit
public import Nyll.SchemeTheory.Descent.NoetherianImageApproximation
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Actual residue fibers of the Noetherian image approximation

The fibers of the actual stage images over the contracted primes form an
inverse system. Its limit is the actual fiber of the original closed
subscheme. The three limits used here are supplied by the image construction,
the exhaustive subalgebra construction, and the residue-field colimit theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SubalgebraStages

universe u

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
variable {ι : Type u} [Preorder ι] (S : ι →o Subalgebra A₀ A)
variable (p : Ideal A) [p.IsPrime]

/-- The spectra of the actual residue fields at the contracted stage primes. -/
abbrev residueSpecDiagram : ιᵒᵖ ⥤ Scheme.{u} :=
  (residueDiagram S p).op ⋙ Scheme.Spec

instance (i : ιᵒᵖ) : IsAffine ((residueSpecDiagram S p).obj i) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (residuePrime S p i.unop).ResidueField)))

instance (i : ιᵒᵖ) : CompactSpace ((residueSpecDiagram S p).obj i) :=
  inferInstanceAs (CompactSpace (Spec (CommRingCat.of (residuePrime S p i.unop).ResidueField)))

instance (i : ιᵒᵖ) : QuasiSeparatedSpace ((residueSpecDiagram S p).obj i) :=
  inferInstanceAs
    (QuasiSeparatedSpace (Spec (CommRingCat.of (residuePrime S p i.unop).ResidueField)))

/-- The cone from the spectrum of the original residue field. -/
abbrev residueSpecCone : Cone (residueSpecDiagram S p) :=
  Scheme.Spec.mapCone (residueCocone S p).op

/-- The residue point of a stage is its actual algebra-map spectrum morphism. -/
abbrev residueSpecBase (i : ιᵒᵖ) :
    (residueSpecDiagram S p).obj i ⟶ (specDiagram S).obj i :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (S i.unop) (residuePrime S p i.unop).ResidueField))

/-- The original residue point, before approximation. -/
abbrev residueSpecBaseTop : Spec (CommRingCat.of p.ResidueField) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))

@[reassoc]
lemma residueSpecBase_naturality {i j : ιᵒᵖ} (h : i ⟶ j) :
    (residueSpecDiagram S p).map h ≫ residueSpecBase S p j =
      residueSpecBase S p i ≫ (specDiagram S).map h := by
  change Spec.map (CommRingCat.ofHom (residueTrans S p h.unop.le)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S j.unop) _)) =
    Spec.map (CommRingCat.ofHom (algebraMap (S i.unop) _)) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (S.mono h.unop.le)).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact residueTrans_algebraMap S p h.unop.le a

/-- The actual residue points constitute a natural transformation over the stage spectra. -/
def residueSpecBaseMaps : residueSpecDiagram S p ⟶ specDiagram S where
  app i := residueSpecBase S p i
  naturality _ _ h := residueSpecBase_naturality S p h

@[reassoc]
lemma residueSpecCone_projection_base (i : ιᵒᵖ) :
    (residueSpecCone S p).π.app i ≫ residueSpecBase S p i =
      residueSpecBaseTop p ≫ (specCone S).π.app i := by
  change Spec.map (CommRingCat.ofHom (residueLeg S p i.unop)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S i.unop) _)) =
    Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)) ≫
      Spec.map (CommRingCat.ofHom (S i.unop).val.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact residueLeg_algebraMap S p i.unop a

/-- Spectra turn the actual residue-field colimit into the actual residue-point limit. -/
def residueSpecConeIsLimit [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (hS : ∀ a : A, ∃ i, a ∈ S i) : IsLimit (residueSpecCone S p) :=
  isLimitOfPreserves Scheme.Spec (residueCoconeIsColimit S p hS).op

end AlgebraicGeometry.SubalgebraStages

namespace AlgebraicGeometry.SubalgebraImageApproximation

universe u

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
variable {ι : Type u} [Preorder ι] (S : ι →o Subalgebra A₀ A)
variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
variable {Z : Scheme.{u}} (j : Z ⟶ (ambientCone S f₀).pt)
variable (p : Ideal A) [p.IsPrime]

open SubalgebraStages in
/-- The actual fiber of a stage image at the contraction of the original prime. -/
abbrev residueFiberObj (i : ιᵒᵖ) : Scheme.{u} :=
  pullback (baseMap S f₀ j i) (residueSpecBase S p i)

instance (i : ιᵒᵖ) :
    IsAffineHom (pullback.fst (baseMap S f₀ j i)
      (SubalgebraStages.residueSpecBase S p i)) := by
  have : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom) :=
    isAffineHom_isStableUnderBaseChange
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback (baseMap S f₀ j i)
      (SubalgebraStages.residueSpecBase S p i)).flip
    (isAffineHom_of_isAffine (SubalgebraStages.residueSpecBase S p i))

open SubalgebraStages in
/-- The actual fiber transition induced by the image and residue-field maps. -/
def residueFiberTrans {i k : ιᵒᵖ} (h : i ⟶ k) :
    residueFiberObj S f₀ j p i ⟶ residueFiberObj S f₀ j p k :=
  pullback.map _ _ _ _ ((diagram S f₀ j).map h)
    ((residueSpecDiagram S p).map h)
    ((specDiagram S).map h)
    (transition_baseMap S f₀ j h).symm
    (residueSpecBase_naturality S p h).symm

@[reassoc]
lemma residueFiberTrans_fst {i k : ιᵒᵖ} (h : i ⟶ k) :
    residueFiberTrans S f₀ j p h ≫
        pullback.fst (baseMap S f₀ j k)
          (SubalgebraStages.residueSpecBase S p k) =
      pullback.fst (baseMap S f₀ j i)
        (SubalgebraStages.residueSpecBase S p i) ≫
          (diagram S f₀ j).map h :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma residueFiberTrans_snd {i k : ιᵒᵖ} (h : i ⟶ k) :
    residueFiberTrans S f₀ j p h ≫
        pullback.snd (baseMap S f₀ j k)
          (SubalgebraStages.residueSpecBase S p k) =
      pullback.snd (baseMap S f₀ j i)
        (SubalgebraStages.residueSpecBase S p i) ≫
          (SubalgebraStages.residueSpecDiagram S p).map h :=
  pullback.lift_snd _ _ _

/-- The inverse system of actual residue fibers of the actual image stages. -/
@[reducible] def residueFiberDiagram : ιᵒᵖ ⥤ Scheme.{u} where
  obj i := residueFiberObj S f₀ j p i
  map h := residueFiberTrans S f₀ j p h
  map_id i := by
    apply pullback.hom_ext
    · rw [residueFiberTrans_fst, CategoryTheory.Functor.map_id,
        Category.comp_id, Category.id_comp]
    · rw [residueFiberTrans_snd, CategoryTheory.Functor.map_id,
        Category.comp_id, Category.id_comp]
  map_comp h h' := by
    apply pullback.hom_ext
    · rw [residueFiberTrans_fst, Category.assoc, residueFiberTrans_fst,
        residueFiberTrans_fst_assoc, CategoryTheory.Functor.map_comp]
    · rw [residueFiberTrans_snd, Category.assoc, residueFiberTrans_snd,
        residueFiberTrans_snd_assoc, CategoryTheory.Functor.map_comp]
      simp only [SubalgebraStages.residueSpecDiagram, CategoryTheory.Functor.comp_map]

/-- Projection of the actual fiber system to the image system. -/
def residueFiberFst : residueFiberDiagram S f₀ j p ⟶ diagram S f₀ j where
  app i := pullback.fst (baseMap S f₀ j i)
    (SubalgebraStages.residueSpecBase S p i)
  naturality _ _ h := residueFiberTrans_fst S f₀ j p h

/-- Projection of the actual fiber system to the residue-field spectrum system. -/
def residueFiberSnd : residueFiberDiagram S f₀ j p ⟶
    SubalgebraStages.residueSpecDiagram S p where
  app i := pullback.snd (baseMap S f₀ j i)
    (SubalgebraStages.residueSpecBase S p i)
  naturality _ _ h := residueFiberTrans_snd S f₀ j p h

/-- The actual structure map of the original closed subscheme to the ambient ring. -/
abbrev originalBaseMap : Z ⟶ Spec (CommRingCat.of A) :=
  j ≫ pullback.snd f₀ (SubalgebraStages.specHomTop (A₀ := A₀) (A := A))

/-- The original fiber over the actual original residue field. -/
abbrev originalResidueFiber : Scheme.{u} :=
  pullback (originalBaseMap S f₀ j) (SubalgebraStages.residueSpecBaseTop p)

open SubalgebraStages in
/-- The original fiber maps to each actual stage fiber. -/
def residueFiberLeg (i : ιᵒᵖ) :
    originalResidueFiber S f₀ j p ⟶ residueFiberObj S f₀ j p i :=
  pullback.map _ _ _ _ ((cone S f₀ j).π.app i)
    ((residueSpecCone S p).π.app i)
    ((specCone S).π.app i)
    (cone_projection_baseMap S f₀ j i).symm
    (residueSpecCone_projection_base S p i).symm

@[reassoc]
lemma residueFiberLeg_fst (i : ιᵒᵖ) :
    residueFiberLeg S f₀ j p i ≫
        pullback.fst (baseMap S f₀ j i)
          (SubalgebraStages.residueSpecBase S p i) =
      pullback.fst (originalBaseMap S f₀ j) (SubalgebraStages.residueSpecBaseTop p) ≫
        (cone S f₀ j).π.app i :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma residueFiberLeg_snd (i : ιᵒᵖ) :
    residueFiberLeg S f₀ j p i ≫
        pullback.snd (baseMap S f₀ j i)
          (SubalgebraStages.residueSpecBase S p i) =
      pullback.snd (originalBaseMap S f₀ j) (SubalgebraStages.residueSpecBaseTop p) ≫
        (SubalgebraStages.residueSpecCone S p).π.app i :=
  pullback.lift_snd _ _ _

/-- The actual original fiber is a cone over the actual stage fibers. -/
@[reducible] def residueFiberCone : Cone (residueFiberDiagram S f₀ j p) where
  pt := originalResidueFiber S f₀ j p
  π :=
    { app i := residueFiberLeg S f₀ j p i
      naturality i k h := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        apply pullback.hom_ext
        · rw [Category.assoc, residueFiberTrans_fst, residueFiberLeg_fst_assoc,
            (cone S f₀ j).w h, residueFiberLeg_fst]
        · rw [Category.assoc, residueFiberTrans_snd, residueFiberLeg_snd_assoc,
            (SubalgebraStages.residueSpecCone S p).w h,
            residueFiberLeg_snd] }

/-- Each actual residue-fiber transition is affine. -/
instance {i k : ιᵒᵖ} (h : i ⟶ k) :
    IsAffineHom ((residueFiberDiagram S f₀ j p).map h) := by
  change IsAffineHom (residueFiberTrans S f₀ j p h)
  have : IsAffineHom ((ambientDiagram S f₀).map h) :=
    SubalgebraStages.isAffineHom_diagram_map S f₀ h
  have : IsAffineHom ((diagram S f₀ j).map h) :=
    inferInstanceAs (IsAffineHom ((AffineTransitionImage.diagram
      (ambientDiagram S f₀) (ambientCone S f₀) j).map h))
  have : IsAffineHom (residueFiberTrans S f₀ j p h ≫
      pullback.fst (baseMap S f₀ j k)
        (SubalgebraStages.residueSpecBase S p k)) := by
    rw [residueFiberTrans_fst]
    infer_instance
  exact IsAffineHom.of_comp _ (pullback.fst (baseMap S f₀ j k)
    (SubalgebraStages.residueSpecBase S p k))

instance [IsProper f₀] (i : ιᵒᵖ) :
    CompactSpace ((residueFiberDiagram S f₀ j p).obj i) :=
  QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd (baseMap S f₀ j i)
      (SubalgebraStages.residueSpecBase S p i))

instance [IsProper f₀] (i : ιᵒᵖ) :
    QuasiSeparatedSpace ((residueFiberDiagram S f₀ j p).obj i) :=
  quasiSeparatedSpace_of_quasiSeparated
    (pullback.snd (baseMap S f₀ j i)
      (SubalgebraStages.residueSpecBase S p i))

open AlgebraicCurves.Geometry.Schemes.Proofs.SubalgebraStages_nonempty_isLimit_cone in
open SubalgebraStages in
/-- The original residue fiber is the limit of the actual contracted residue fibers. -/
def residueFiberConeIsLimit [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (hS : ∀ a : A, ∃ i, a ∈ S i) [IsProper f₀] [IsClosedImmersion j] :
    IsLimit (residueFiberCone S f₀ j p) := by
  let hX : IsLimit (cone S f₀ j) := coneIsLimit S f₀ j hS
  let hK : IsLimit (residueSpecCone S p) :=
    residueSpecConeIsLimit S p hS
  let hB : IsLimit (specCone S) :=
    (LimBC.nonempty_isLimit_specCone S hS).some
  let leftCone : Cone (residueFiberDiagram S f₀ j p) → Cone (diagram S f₀ j) :=
    fun t => { pt := t.pt, π := t.π ≫ residueFiberFst S f₀ j p }
  let rightCone : Cone (residueFiberDiagram S f₀ j p) →
      Cone (residueSpecDiagram S p) :=
    fun t => { pt := t.pt, π := t.π ≫ residueFiberSnd S f₀ j p }
  let leftLift : ∀ t : Cone (residueFiberDiagram S f₀ j p), t.pt ⟶ Z :=
    fun t => hX.lift (leftCone t)
  let rightLift : ∀ t : Cone (residueFiberDiagram S f₀ j p),
      t.pt ⟶ Spec (CommRingCat.of p.ResidueField) :=
    fun t => hK.lift (rightCone t)
  have hleft (t : Cone (residueFiberDiagram S f₀ j p))
      (i : ιᵒᵖ) :
      leftLift t ≫ (cone S f₀ j).π.app i = t.π.app i ≫
        pullback.fst (baseMap S f₀ j i) (residueSpecBase S p i) :=
    hX.fac (leftCone t) i
  have hright (t : Cone (residueFiberDiagram S f₀ j p))
      (i : ιᵒᵖ) :
      rightLift t ≫ (residueSpecCone S p).π.app i = t.π.app i ≫
        pullback.snd (baseMap S f₀ j i) (residueSpecBase S p i) :=
    hK.fac (rightCone t) i
  have hbase (i : ιᵒᵖ) :
      (cone S f₀ j).π.app i ≫ baseMap S f₀ j i =
        originalBaseMap S f₀ j ≫ (specCone S).π.app i := by
    simpa only [originalBaseMap, Category.assoc] using cone_projection_baseMap S f₀ j i
  have hcompat (t : Cone (residueFiberDiagram S f₀ j p)) :
      leftLift t ≫ originalBaseMap S f₀ j = rightLift t ≫ residueSpecBaseTop p := by
    apply hB.hom_ext
    intro i
    calc
      (leftLift t ≫ originalBaseMap S f₀ j) ≫
          (specCone S).π.app i =
        leftLift t ≫ ((cone S f₀ j).π.app i ≫ baseMap S f₀ j i) := by
          rw [hbase, Category.assoc]
      _ = (t.π.app i ≫ pullback.fst _ _) ≫ baseMap S f₀ j i := by
          rw [← Category.assoc, hleft]
      _ = (t.π.app i ≫ pullback.snd _ _) ≫ residueSpecBase S p i := by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
      _ = rightLift t ≫ ((residueSpecCone S p).π.app i ≫
          residueSpecBase S p i) := by
          rw [← Category.assoc, hright]
      _ = (rightLift t ≫ residueSpecBaseTop p) ≫
          (specCone S).π.app i := by
          rw [residueSpecCone_projection_base, Category.assoc]
  refine
    { lift := fun t => pullback.lift (leftLift t) (rightLift t) (hcompat t)
      fac := ?_
      uniq := ?_ }
  · intro t i
    change pullback.lift (leftLift t) (rightLift t) (hcompat t) ≫
      residueFiberLeg S f₀ j p i = t.π.app i
    apply pullback.hom_ext
    · rw [Category.assoc, residueFiberLeg_fst, pullback.lift_fst_assoc]
      exact hleft t i
    · rw [Category.assoc, residueFiberLeg_snd, pullback.lift_snd_assoc]
      exact hright t i
  · intro t m hm
    have hm' (i : ιᵒᵖ) :
        m ≫ residueFiberLeg S f₀ j p i = t.π.app i := hm i
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply hX.hom_ext
      intro i
      rw [Category.assoc, ← residueFiberLeg_fst, ← Category.assoc, hm', hleft]
    · rw [pullback.lift_snd]
      apply hK.hom_ext
      intro i
      rw [Category.assoc, ← residueFiberLeg_snd, ← Category.assoc, hm', hright]

end AlgebraicGeometry.SubalgebraImageApproximation

namespace AlgebraicGeometry.NoetherianImageApproximation

universe u

variable (A₀ A : Type u) [CommRing A₀] [CommRing A] [Algebra A₀ A]
variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
variable {Z : Scheme.{u}} (j : Z ⟶ (ambientCone A₀ A f₀).pt)
variable (p : Ideal A) [p.IsPrime]

/-- The original residue fiber of a finitely generated image stage. -/
abbrev residueFiberObj (i : (FGSubalgebra A₀ A)ᵒᵖ) : Scheme.{u} :=
  SubalgebraImageApproximation.residueFiberObj (subalgebras A₀ A) f₀ j p i

/-- The original transitions, using the single general construction. -/
abbrev residueFiberTrans {i k : (FGSubalgebra A₀ A)ᵒᵖ} (h : i ⟶ k) :
    residueFiberObj A₀ A f₀ j p i ⟶ residueFiberObj A₀ A f₀ j p k :=
  SubalgebraImageApproximation.residueFiberTrans (subalgebras A₀ A) f₀ j p h

@[reassoc]
lemma residueFiberTrans_fst {i k : (FGSubalgebra A₀ A)ᵒᵖ} (h : i ⟶ k) :
    residueFiberTrans A₀ A f₀ j p h ≫
        pullback.fst (baseMap A₀ A f₀ j k)
          (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p k) =
      pullback.fst (baseMap A₀ A f₀ j i)
        (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i) ≫
          (diagram A₀ A f₀ j).map h :=
  SubalgebraImageApproximation.residueFiberTrans_fst (subalgebras A₀ A) f₀ j p h

@[reassoc]
lemma residueFiberTrans_snd {i k : (FGSubalgebra A₀ A)ᵒᵖ} (h : i ⟶ k) :
    residueFiberTrans A₀ A f₀ j p h ≫
        pullback.snd (baseMap A₀ A f₀ j k)
          (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p k) =
      pullback.snd (baseMap A₀ A f₀ j i)
        (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i) ≫
          (SubalgebraStages.residueSpecDiagram (subalgebras A₀ A) p).map h :=
  SubalgebraImageApproximation.residueFiberTrans_snd (subalgebras A₀ A) f₀ j p h

/-- The original residue-fiber diagram. -/
abbrev residueFiberDiagram : (FGSubalgebra A₀ A)ᵒᵖ ⥤ Scheme.{u} :=
  SubalgebraImageApproximation.residueFiberDiagram (subalgebras A₀ A) f₀ j p

/-- The original projection to the image diagram. -/
abbrev residueFiberFst : residueFiberDiagram A₀ A f₀ j p ⟶ diagram A₀ A f₀ j :=
  SubalgebraImageApproximation.residueFiberFst (subalgebras A₀ A) f₀ j p

/-- The original projection to the residue spectrum diagram. -/
abbrev residueFiberSnd : residueFiberDiagram A₀ A f₀ j p ⟶
    SubalgebraStages.residueSpecDiagram (subalgebras A₀ A) p :=
  SubalgebraImageApproximation.residueFiberSnd (subalgebras A₀ A) f₀ j p

/-- The original structure map, retaining its closed embedding. -/
abbrev originalBaseMap : Z ⟶ Spec (CommRingCat.of A) :=
  SubalgebraImageApproximation.originalBaseMap (subalgebras A₀ A) f₀ j

/-- The original residue fiber, retaining its original base morphism. -/
abbrev originalResidueFiber : Scheme.{u} :=
  SubalgebraImageApproximation.originalResidueFiber (subalgebras A₀ A) f₀ j p

/-- The original limit projection to a stage fiber. -/
abbrev residueFiberLeg (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    originalResidueFiber A₀ A f₀ j p ⟶ residueFiberObj A₀ A f₀ j p i :=
  SubalgebraImageApproximation.residueFiberLeg (subalgebras A₀ A) f₀ j p i

@[reassoc]
lemma residueFiberLeg_fst (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    residueFiberLeg A₀ A f₀ j p i ≫
        pullback.fst (baseMap A₀ A f₀ j i)
          (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i) =
      pullback.fst (originalBaseMap A₀ A f₀ j) (SubalgebraStages.residueSpecBaseTop p) ≫
        (cone A₀ A f₀ j).π.app i :=
  SubalgebraImageApproximation.residueFiberLeg_fst (subalgebras A₀ A) f₀ j p i

@[reassoc]
lemma residueFiberLeg_snd (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    residueFiberLeg A₀ A f₀ j p i ≫
        pullback.snd (baseMap A₀ A f₀ j i)
          (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i) =
      pullback.snd (originalBaseMap A₀ A f₀ j) (SubalgebraStages.residueSpecBaseTop p) ≫
        (SubalgebraStages.residueSpecCone (subalgebras A₀ A) p).π.app i :=
  SubalgebraImageApproximation.residueFiberLeg_snd (subalgebras A₀ A) f₀ j p i

/-- The original residue-fiber limit cone. -/
abbrev residueFiberCone : Cone (residueFiberDiagram A₀ A f₀ j p) :=
  SubalgebraImageApproximation.residueFiberCone (subalgebras A₀ A) f₀ j p

/-- The original finitely generated family supplies the general fiber limit. -/
def residueFiberConeIsLimit [IsProper f₀] [IsClosedImmersion j] :
    IsLimit (residueFiberCone A₀ A f₀ j p) :=
  SubalgebraImageApproximation.residueFiberConeIsLimit
    (subalgebras A₀ A) f₀ j p (exhaustive A₀ A)

end AlgebraicGeometry.NoetherianImageApproximation
