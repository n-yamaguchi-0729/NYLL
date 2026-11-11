/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.CurvePointFillingInertia
public import Nyll.AlgebraicCurves.Geometry.IsClosedSingletonNeGenericPoint
public import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Basic

/-!
# Filling the specified boundary point of an actual open curve

The intermediate open is the image of the original curve together with the
specified point. Its rational point is obtained by factoring the original
point morphism through this open. Removing its actual point divisor recovers
the original open curve, with the comparison over the original ambient curve.
Thus a single-point filling theorem applies without an assumed puncture model.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups.Cohomology

variable {k : Type uGeom} [Field k] {C U : Scheme.{uGeom}}
  [IsIntegral C] [Nonempty U]
  (c : C ⟶ Spec (.of k)) [QuasiCompact c] [SmoothOfRelativeDimension 1 c]
  (j : U ⟶ C) [IsOpenImmersion j]

include c in
/-- Removing one point from the finite boundary leaves a closed subset. -/
theorem isClosed_openBoundary_without_point (z : C) :
    IsClosed ((Set.range j)ᶜ \ {z}) := by
  let V := j.opensRange
  have hV : (V : Set C).Nonempty :=
    ⟨j (Classical.choice (inferInstance : Nonempty U)), Set.mem_range_self _⟩
  have hfinite : ((Set.range j)ᶜ \ {z}).Finite :=
    (AlgebraicCurve.finite_compl_of_isOpen c V hV).subset Set.sdiff_subset
  have hgeneric : genericPoint C ∈ V :=
    ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr
      (by simpa only [Set.inter_univ, Set.univ_inter] using hV)
  have hclosed : ∀ y ∈ (Set.range j)ᶜ \ {z}, IsClosed ({y} : Set C) := by
    intro y hy
    apply AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c y
    intro he
    exact hy.1 (he.symm ▸ hgeneric)
  have h := hfinite.isClosed_biUnion hclosed
  have hset : (⋃ y ∈ (Set.range j)ᶜ \ {z}, ({y} : Set C)) =
      (Set.range j)ᶜ \ {z} := by
    apply Set.ext
    intro y
    constructor
    · intro hy
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hwmem, hyw⟩ := Set.mem_iUnion.mp hw
      exact (Set.mem_singleton_iff.mp hyw).symm ▸ hwmem
    · intro hy
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, Set.mem_singleton y⟩⟩
  exact hset ▸ h

/-- The actual intermediate open restores only the selected boundary point. -/
def openCurvePointFillingOpen (z : C) : C.Opens :=
  ⟨((Set.range j)ᶜ \ {z})ᶜ, (isClosed_openBoundary_without_point c j z).isOpen_compl⟩

/-- Membership describes the original open and the one restored point. -/
theorem mem_openCurvePointFillingOpen (z y : C) :
    y ∈ openCurvePointFillingOpen c j z ↔ y ∈ Set.range j ∨ y = z := by
  classical
  change ¬ (¬ y ∈ Set.range j ∧ ¬ y = z) ↔ _
  simp only [not_and_or, not_not]

/-- The original open is contained in the actual one-point filling. -/
theorem opensRange_le_openCurvePointFillingOpen (z : C) :
    j.opensRange ≤ openCurvePointFillingOpen c j z := by
  intro y hy
  exact (mem_openCurvePointFillingOpen c j z y).mpr (Or.inl hy)

instance openCurvePointFillingOpen_nonempty (z : C) :
    Nonempty (openCurvePointFillingOpen c j z) :=
  ⟨⟨j (Classical.choice (inferInstance : Nonempty U)),
    opensRange_le_openCurvePointFillingOpen c j z (Set.mem_range_self _)⟩⟩

/-- The original inclusion, factored through the actual one-point filling. -/
def openCurvePointFillingInclusion (z : C) :
    U ⟶ openCurvePointFillingOpen c j z :=
  j.isoOpensRange.hom ≫ C.homOfLE (opensRange_le_openCurvePointFillingOpen c j z)

instance openCurvePointFillingInclusion_isOpenImmersion (z : C) :
    IsOpenImmersion (openCurvePointFillingInclusion c j z) := by
  unfold openCurvePointFillingInclusion
  infer_instance

/-- The intermediate map retains the original morphism into the compactification. -/
@[reassoc]
theorem openCurvePointFillingInclusion_comp (z : C) :
    openCurvePointFillingInclusion c j z ≫ (openCurvePointFillingOpen c j z).ι = j := by
  rw [openCurvePointFillingInclusion, Category.assoc, Scheme.homOfLE_ι,
    Scheme.Hom.isoOpensRange_hom_ι]

variable (P : Spec (.of k) ⟶ C)

/-- The selected rational point factors through its one-point filling open. -/
theorem rationalPoint_range_le_filling :
    Set.range P ⊆ Set.range (openCurvePointFillingOpen c j
      (P (IsLocalRing.closedPoint k))).ι := by
  rw [Scheme.Opens.range_ι]
  rintro y ⟨t, rfl⟩
  apply (mem_openCurvePointFillingOpen c j (P (IsLocalRing.closedPoint k)) (P t)).mpr
  exact Or.inr (congrArg P (Subsingleton.elim t _))

/-- The original rational point, lifted to the actual one-point filling. -/
def openCurvePointFillingSection :
    Spec (.of k) ⟶ openCurvePointFillingOpen c j (P (IsLocalRing.closedPoint k)) :=
  IsOpenImmersion.lift (openCurvePointFillingOpen c j (P (IsLocalRing.closedPoint k))).ι
    P (rationalPoint_range_le_filling c j P)

/-- The section is the specified original point after the original open inclusion. -/
@[reassoc]
theorem openCurvePointFillingSection_comp :
    openCurvePointFillingSection c j P ≫
        (openCurvePointFillingOpen c j (P (IsLocalRing.closedPoint k))).ι = P :=
  IsOpenImmersion.lift_fac _ _ _

/-- In the actual filling, the complement of the original open is exactly
the lifted original point. -/
theorem openCurvePointFillingInclusion_range
    (hboundary : P (IsLocalRing.closedPoint k) ∉ Set.range j) :
    Set.range (openCurvePointFillingInclusion c j (P (IsLocalRing.closedPoint k))) =
      ({openCurvePointFillingSection c j P (IsLocalRing.closedPoint k)} :
        Set (openCurvePointFillingOpen c j (P (IsLocalRing.closedPoint k))))ᶜ := by
  let V := openCurvePointFillingOpen c j (P (IsLocalRing.closedPoint k))
  let f := openCurvePointFillingInclusion c j (P (IsLocalRing.closedPoint k))
  let q := openCurvePointFillingSection c j P (IsLocalRing.closedPoint k)
  have hq : V.ι q = P (IsLocalRing.closedPoint k) :=
    congrArg (fun t : Spec (.of k) ⟶ C => t (IsLocalRing.closedPoint k))
      (openCurvePointFillingSection_comp c j P)
  have hf (u : U) : V.ι (f u) = j u :=
    congrArg (fun t : U ⟶ C => t u)
      (openCurvePointFillingInclusion_comp c j (P (IsLocalRing.closedPoint k)))
  ext v
  change v ∈ Set.range f ↔ v ≠ q
  constructor
  · rintro ⟨u, rfl⟩ he
    exact hboundary ⟨u, (hf u).symm.trans ((congrArg V.ι he).trans hq)⟩
  · intro hv
    rcases (mem_openCurvePointFillingOpen c j (P (IsLocalRing.closedPoint k)) v.val).mp
        v.property with h | h
    · obtain ⟨u, hu⟩ := h
      exact ⟨u, V.ι.isOpenEmbedding.injective ((hf u).trans hu)⟩
    · exact False.elim (hv (V.ι.isOpenEmbedding.injective (h.trans hq.symm)))

variable (hP : P ≫ c = 𝟙 _)

include hP in
/-- Rationality is inherited from the original section of the structural map. -/
theorem openCurvePointFillingSection_structure :
    openCurvePointFillingSection c j P ≫
      ((openCurvePointFillingOpen c j (P (IsLocalRing.closedPoint k))).ι ≫ c) = 𝟙 _ := by
  rw [← Category.assoc, openCurvePointFillingSection_comp, hP]

variable [IsSeparated c]

/-- The divisor complement in the constructed filling is the original open
curve. Both maps into the original compactification occur in the conclusion. -/
theorem exists_openCurvePointFillingPunctureIso
    (hboundary : P (IsLocalRing.closedPoint k) ∉ Set.range j) :
    let V := openCurvePointFillingOpen c j (P (IsLocalRing.closedPoint k))
    let : SmoothOfRelativeDimension 1 (V.ι ≫ c) :=
      smoothOfRelativeDimension_comp 0 1 V.ι c
    let D := curvePointDivisor (V.ι ≫ c) (openCurvePointFillingSection c j P)
      (openCurvePointFillingSection_structure c j P hP)
    ∃ e : U ≅ (D.1.supportComplement : Scheme.{uGeom}),
      e.hom ≫ D.1.supportComplement.ι ≫ V.ι = j := by
  intro V hSmooth D
  let f : U ⟶ (V : Scheme.{uGeom}) :=
    openCurvePointFillingInclusion c j (P (IsLocalRing.closedPoint k))
  let q : Spec (.of k) ⟶ (V : Scheme.{uGeom}) := openCurvePointFillingSection c j P
  have hsupport : (D.1.support : Set (V : Scheme.{uGeom})) =
      {q (IsLocalRing.closedPoint k)} :=
    curvePointDivisor_support (V.ι ≫ c) q
      (openCurvePointFillingSection_structure c j P hP)
  have hfrange : Set.range f =
      ({q (IsLocalRing.closedPoint k)} : Set (V : Scheme.{uGeom}))ᶜ :=
    openCurvePointFillingInclusion_range c j P hboundary
  have hDrange : Set.range D.1.supportComplement.ι =
      ({q (IsLocalRing.closedPoint k)} : Set (V : Scheme.{uGeom}))ᶜ :=
    (Scheme.Opens.range_ι D.1.supportComplement).trans (congrArg Set.compl hsupport)
  let e : U ≅ (D.1.supportComplement : Scheme.{uGeom}) :=
    IsOpenImmersion.isoOfRangeEq f D.1.supportComplement.ι (hfrange.trans hDrange.symm)
  refine ⟨e, ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t : U ⟶ (V : Scheme.{uGeom}) => t ≫ V.ι)
      (IsOpenImmersion.isoOfRangeEq_hom_fac f D.1.supportComplement.ι
        (hfrange.trans hDrange.symm))).trans
      (openCurvePointFillingInclusion_comp c j (P (IsLocalRing.closedPoint k))))

end EtaleFundamentalGroups.Cohomology
