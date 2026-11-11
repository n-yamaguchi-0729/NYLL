/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Tactic.Set
public import Nyll.AbelianVarieties.Geometry.PartialActions.Maximality
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AbelianVarieties.Geometry.PartialActions.Basic
public import Nyll.AbelianVarieties.Geometry.RelativeDimension
public import Nyll.AbelianVarieties.Geometry.SubgroupClosure
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.LocalGeometry.Dimension
public import Nyll.SchemeTheory.LocalGeometry.FormalNeighborhoods
public import Nyll.AbelianVarieties.Basic
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.GeometricallyConnectedIdentityComponent
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.AlgebraicCurves.Geometry.Schemes.LocalGeometry.IsIrreducibleTopologicalKrullDimAddOneLe
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.GeometricallyReducedReduced
public import Nyll.SchemeTheory.LocalGeometry.IntegralSmooth
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothOfRelativeDimensionLeTopologicalKrullDim
public import Nyll.SchemeTheory.Morphisms.SmoothRelativeDimension
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothSmoothOfRelativeDimension
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Closed subgroups, group-scheme images, and isotropy

Construct identity components and scheme-theoretic images of group homomorphisms,
prove closedness of their images, and obtain positive-dimensional isotropy groups.
Reduced subschemes and partial-action calculus use their existing owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry NeronModelInfra
open CategoryTheory.Limits hiding pair
open GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw TopologicalSpace Topology

universe u v w

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_preimage_range_eq_connectedComponent_of_isClosedImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.Subgroups

open CategoryTheory AlgebraicGeometry NeronModelInfra
open CategoryTheory.Limits hiding pair
open GoodReductionJacobian TopologicalSpace

noncomputable section

namespace ClosedFibreIdentity

section Maps

theorem one_coe_eq {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) :
    (L.one s).1 = s ≫ (L.one (𝟙 _)).1 := by
  have h := L.one_natural (𝟙 _) s s (Category.comp_id s)
  rw [← h, GoodReductionJacobian.schemeHomOverComp_coe]

theorem range_one_coe_subset {K : Type u} [Field K] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of K)} (L : RelativeGroupLaw K f) {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of K)) :
    Set.range (L.one s).1 ⊆ {(L.one (𝟙 _)).1 (fieldPoint K)} := by
  rw [one_coe_eq L s]
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply]
  rw [show s z = fieldPoint K from Subsingleton.elim _ _]
  exact Set.mem_singleton _

end Maps

section OpenSet

variable {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  [LocallyOfFiniteType g] [QuasiCompact g] (LB : RelativeGroupLaw R g)
  {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
  [IsClosedImmersion ι]

local notation "ptK" => 𝟙 (Spec (CommRingCat.of K))

/-- Projection from the base-changed group to the original group. -/
abbrev p : pullback g ι ⟶ B := pullback.fst g ι

/-- The group law after base change to the residue field. -/
abbrev Lι : RelativeGroupLaw K (pullback.snd g ι) := LB.baseChange ι

/-- The identity point of the base-changed group. -/
abbrev eι : ↥(pullback g ι) := ((Lι LB ι).one ptK).1 (fieldPoint K)

/-- The connected component of the identity in the base-changed group. -/
def idC : Set ↥(pullback g ι) := connectedComponent (eι LB ι)

omit [IsClosedImmersion ι] in
theorem exists_idComp :
    ∃ (G₀ : Scheme.{u}) (i₀ : G₀ ⟶ pullback g ι) (L₀ : RelativeGroupLaw K (i₀ ≫ pullback.snd g ι)),
      IsOpenImmersion i₀ ∧ Set.range i₀ = idC LB ι ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (i₀ ≫ pullback.snd g ι)),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y)
            (⟨i₀, rfl⟩ : SchemeHomOver (i₀ ≫ pullback.snd g ι) (pullback.snd g ι)) =
          (Lι LB ι).mul t
            (NeronModelInfra.schemeHomOverComp x
              (⟨i₀, rfl⟩ : SchemeHomOver (i₀ ≫ pullback.snd g ι) (pullback.snd g ι)))
            (NeronModelInfra.schemeHomOverComp y
              (⟨i₀, rfl⟩ : SchemeHomOver (i₀ ≫ pullback.snd g ι) (pullback.snd g ι)))) := by
  obtain ⟨G₀, i₀, L₀, hopen, -, -, -, -, hrange, -, hhom, -⟩ :=
    exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
      K (Lι LB ι)
  exact ⟨G₀, i₀, L₀, hopen, hrange, fun t x y => hhom t x y⟩

omit [IsClosedImmersion ι] in
theorem isOpen_idC : IsOpen (idC LB ι) := by
  obtain ⟨G₀, i₀, -, hopen, hrange, -⟩ := exists_idComp LB ι
  rw [← hrange]
  exact i₀.isOpenEmbedding.isOpen_range

omit [LocallyOfFiniteType g] [QuasiCompact g] [IsClosedImmersion ι] in
theorem eι_mem_idC : eι LB ι ∈ idC LB ι := mem_connectedComponent

/-- The complement of the image of the nonidentity components of the closed fibre. -/
def W : Set B := (p ι '' (idC LB ι)ᶜ)ᶜ

theorem isOpen_W : IsOpen (W LB ι) := by
  rw [W, isOpen_compl_iff]
  exact (p ι).isClosedMap _ (isOpen_idC LB ι).isClosed_compl

omit [LocallyOfFiniteType g] [QuasiCompact g] [IsClosedImmersion ι] in
theorem mem_W_iff (b : B) : b ∈ W LB ι ↔ ∀ c : ↥(pullback g ι), p ι c = b → c ∈ idC LB ι := by
  simp only [W, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
  exact ⟨fun h c hc => by_contra fun hn => h c hn hc, fun h c hn hc => hn (h c hc)⟩

omit [LocallyOfFiniteType g] [QuasiCompact g] in
theorem preimage_W : p ι ⁻¹' W LB ι = idC LB ι := by
  ext c
  rw [Set.mem_preimage, mem_W_iff]
  constructor
  · intro h; exact h c rfl
  · intro hc c' hc'
    rw [(p ι).isClosedEmbedding.injective hc']
    exact hc

omit [LocallyOfFiniteType g] [QuasiCompact g] [IsClosedImmersion ι] in
theorem compl_range_subset_W : (Set.range (p (g := g) ι))ᶜ ⊆ W LB ι := by
  intro b hb
  rw [mem_W_iff]
  intro c hc
  exact absurd ⟨c, hc⟩ hb

/-- The open set retaining the identity component in the closed fibre. -/
def U₀ : B.Opens := ⟨W LB ι, isOpen_W LB ι⟩

/-- The open subgroup obtained from the selected closed-fibre component. -/
abbrev U : Scheme.{u} := (U₀ LB ι : Scheme.{u})

/-- The inclusion of the open subgroup. -/
abbrev ιU : U LB ι ⟶ B := (U₀ LB ι).ι

/-- The structure morphism of the open subgroup. -/
abbrev gU : U LB ι ⟶ Spec (CommRingCat.of R) := ιU LB ι ≫ g

theorem range_ιU : Set.range (ιU LB ι) = W LB ι := (U₀ LB ι).range_ι

end OpenSet

section Stable

variable {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  [LocallyOfFiniteType g] [QuasiCompact g] (LB : RelativeGroupLaw R g)
  {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
  [IsClosedImmersion ι]

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

/-- Projection from the base change of a test scheme. -/
abbrev ψ : pullback t ι ⟶ T := pullback.fst t ι

/-- The residue-field structure morphism of the base-changed test scheme. -/
abbrev tι : pullback t ι ⟶ Spec (CommRingCat.of K) := pullback.snd t ι

omit [IsClosedImmersion ι] in
theorem ψ_t : ψ ι t ≫ t = tι ι t ≫ ι := pullback.condition

/-- Restrict a point of the original group to the base-changed test scheme. -/
def res (x : SchemeHomOver t g) : SchemeHomOver (tι ι t) (pullback.snd g ι) :=
  RelativeGroupLaw.baseChangePointOfBase ι
    (GoodReductionJacobian.schemeHomOverComp (ψ ι t) (ψ_t ι t) x)

omit [LocallyOfFiniteType g] [QuasiCompact g] [IsClosedImmersion ι] in
theorem res_coe_p (x : SchemeHomOver t g) : (res ι t x).1 ≫ p ι = ψ ι t ≫ x.1 := by
  rw [res, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst,
    GoodReductionJacobian.schemeHomOverComp_coe]

omit [LocallyOfFiniteType g] [QuasiCompact g] [IsClosedImmersion ι] in
theorem toBase_res (x : SchemeHomOver t g) :
    RelativeGroupLaw.baseChangePointToBase ι (res ι t x) =
      GoodReductionJacobian.schemeHomOverComp (ψ ι t) (ψ_t ι t) x :=
  RelativeGroupLaw.baseChangePointToBase_ofBase ι _

omit [LocallyOfFiniteType g] [QuasiCompact g] [IsClosedImmersion ι] in
theorem res_mul (x y : SchemeHomOver t g) :
    res ι t (LB.mul t x y) = (Lι LB ι).mul (tι ι t) (res ι t x) (res ι t y) := by
  apply (RelativeGroupLaw.baseChangePointEquiv ι (tι ι t)).injective
  change RelativeGroupLaw.baseChangePointToBase ι _ = RelativeGroupLaw.baseChangePointToBase ι _
  rw [RelativeGroupLaw.baseChangePointToBase_mul, toBase_res, toBase_res, toBase_res,
    LB.mul_natural]

omit [LocallyOfFiniteType g] [QuasiCompact g] [IsClosedImmersion ι] in
theorem res_one : res ι t (LB.one t) = (Lι LB ι).one (tι ι t) := by
  apply (RelativeGroupLaw.baseChangePointEquiv ι (tι ι t)).injective
  change RelativeGroupLaw.baseChangePointToBase ι _ = RelativeGroupLaw.baseChangePointToBase ι _
  rw [RelativeGroupLaw.baseChangePointToBase_one, toBase_res, LB.one_natural]

omit [LocallyOfFiniteType g] [QuasiCompact g] [IsClosedImmersion ι] in
theorem res_inv (x : SchemeHomOver t g) :
    res ι t (LB.inv t x) = (Lι LB ι).inv (tι ι t) (res ι t x) := by
  apply (RelativeGroupLaw.baseChangePointEquiv ι (tι ι t)).injective
  change RelativeGroupLaw.baseChangePointToBase ι _ = RelativeGroupLaw.baseChangePointToBase ι _
  rw [RelativeGroupLaw.baseChangePointToBase_inv, toBase_res, toBase_res, LB.inv_natural]

omit [LocallyOfFiniteType g] [QuasiCompact g] in
theorem range_subset_W_iff (x : SchemeHomOver t g) :
    Set.range x.1 ⊆ W LB ι ↔ Set.range (res ι t x).1 ⊆ idC LB ι := by
  constructor
  · intro h
    rintro _ ⟨w, rfl⟩
    have hw : p ι ((res ι t x).1 w) ∈ W LB ι := by
      rw [← Scheme.Hom.comp_apply, res_coe_p, Scheme.Hom.comp_apply]
      exact h ⟨_, rfl⟩
    exact (mem_W_iff LB ι _).mp hw _ rfl
  · intro h
    rintro _ ⟨z, rfl⟩
    rw [mem_W_iff]
    intro c hc
    have hz : z ∈ Set.range (ψ ι t) := by
      rw [Scheme.Pullback.range_fst]
      change t z ∈ Set.range ι
      have h1 : t z = g (x.1 z) := by rw [← Scheme.Hom.comp_apply, x.2]
      rw [h1, ← hc, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    obtain ⟨z', rfl⟩ := hz
    have h2 : p ι ((res ι t x).1 z') = x.1 (ψ ι t z') := by
      rw [← Scheme.Hom.comp_apply, res_coe_p, Scheme.Hom.comp_apply]
    rw [(p ι).isClosedEmbedding.injective (hc.trans h2.symm)]
    exact h ⟨z', rfl⟩

theorem range_mul_subset_W (x y : SchemeHomOver t g) (hx : Set.range x.1 ⊆ W LB ι)
    (hy : Set.range y.1 ⊆ W LB ι) : Set.range (LB.mul t x y).1 ⊆ W LB ι := by
  rw [range_subset_W_iff] at hx hy ⊢
  rw [res_mul]
  obtain ⟨G₀, i₀, L₀, hopen, hrange, hhom⟩ := exists_idComp LB ι
  have : IsOpenImmersion i₀ := hopen
  let a : SchemeHomOver (tι ι t) (i₀ ≫ pullback.snd g ι) :=
    ⟨IsOpenImmersion.lift i₀ (res ι t x).1 (by rw [hrange]; exact hx), by
      rw [IsOpenImmersion.lift_fac_assoc]; exact (res ι t x).2⟩
  let b : SchemeHomOver (tι ι t) (i₀ ≫ pullback.snd g ι) :=
    ⟨IsOpenImmersion.lift i₀ (res ι t y).1 (by rw [hrange]; exact hy), by
      rw [IsOpenImmersion.lift_fac_assoc]; exact (res ι t y).2⟩
  have ha : NeronModelInfra.schemeHomOverComp a
      (⟨i₀, rfl⟩ : SchemeHomOver (i₀ ≫ pullback.snd g ι) (pullback.snd g ι)) = res ι t x :=
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have hb : NeronModelInfra.schemeHomOverComp b
      (⟨i₀, rfl⟩ : SchemeHomOver (i₀ ≫ pullback.snd g ι) (pullback.snd g ι)) = res ι t y :=
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have h := hhom (tι ι t) a b
  rw [ha, hb] at h
  rw [← h, NeronModelInfra.schemeHomOverComp_coe, Scheme.Hom.comp_base, TopCat.coe_comp,
    ← hrange]
  exact Set.range_comp_subset_range _ _

omit [LocallyOfFiniteType g] [QuasiCompact g] in
theorem range_one_subset_W : Set.range (LB.one t).1 ⊆ W LB ι := by
  rw [range_subset_W_iff, res_one]
  exact (range_one_coe_subset (Lι LB ι) _).trans (Set.singleton_subset_iff.mpr (eι_mem_idC LB ι))

theorem range_inv_subset_W (x : SchemeHomOver t g) (hx : Set.range x.1 ⊆ W LB ι) :
    Set.range (LB.inv t x).1 ⊆ W LB ι := by
  rw [range_subset_W_iff] at hx ⊢
  rw [res_inv]
  obtain ⟨G₀, i₀, L₀, hopen, hrange, hhom⟩ := exists_idComp LB ι
  have : IsOpenImmersion i₀ := hopen
  let : Group (SchemeHomOver (tι ι t) (i₀ ≫ pullback.snd g ι)) := L₀.pointGroup (tι ι t)
  let : Group (SchemeHomOver (tι ι t) (pullback.snd g ι)) := (Lι LB ι).pointGroup (tι ι t)
  let a : SchemeHomOver (tι ι t) (i₀ ≫ pullback.snd g ι) :=
    ⟨IsOpenImmersion.lift i₀ (res ι t x).1 (by rw [hrange]; exact hx), by
      rw [IsOpenImmersion.lift_fac_assoc]; exact (res ι t x).2⟩
  let φ : SchemeHomOver (tι ι t) (i₀ ≫ pullback.snd g ι) →* SchemeHomOver (tι ι t) (pullback.snd g
    ι) :=
    MonoidHom.mk' (fun c => NeronModelInfra.schemeHomOverComp c
      (⟨i₀, rfl⟩ : SchemeHomOver (i₀ ≫ pullback.snd g ι) (pullback.snd g ι))) (fun c d => hhom _ c
        d)
  have ha : φ a = res ι t x := Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have h : φ a⁻¹ = (res ι t x)⁻¹ := by rw [map_inv, ha]
  change Set.range ((res ι t x)⁻¹).1 ⊆ idC LB ι
  rw [← h]
  change Set.range ((a⁻¹).1 ≫ i₀) ⊆ idC LB ι
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, ← hrange]
  exact Set.range_comp_subset_range _ _

end Stable

section Law

variable {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  [LocallyOfFiniteType g] [QuasiCompact g] (LB : RelativeGroupLaw R g)
  {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
  [IsClosedImmersion ι]

/-- Forget the factorization of a point through the open subgroup. -/
def toB {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t (gU LB ι)) :
    SchemeHomOver t g :=
  ⟨x.1 ≫ ιU LB ι, by rw [Category.assoc]; exact x.2⟩

@[scoped simp]
theorem toB_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t (gU LB ι)) : (toB LB ι x).1 = x.1 ≫ ιU LB ι := rfl

theorem toB_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} :
    Function.Injective (toB LB ι (T := T) (t := t)) := by
  intro x y h
  exact Subtype.ext ((cancel_mono (ιU LB ι)).mp (congrArg Subtype.val h))

theorem toB_transition {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (φ : T' ⟶ T) (hφ : φ ≫ t = t')
    (x : SchemeHomOver t (gU LB ι)) :
    toB LB ι (GoodReductionJacobian.schemeHomOverComp φ hφ x) =
      GoodReductionJacobian.schemeHomOverComp φ hφ (toB LB ι x) :=
  Subtype.ext (Category.assoc _ _ _)

theorem range_toB_subset {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t (gU LB ι)) : Set.range (toB LB ι x).1 ⊆ W LB ι := by
  rw [toB_coe, Scheme.Hom.comp_base, TopCat.coe_comp, ← range_ιU LB ι]
  exact Set.range_comp_subset_range _ _

/-- Lift a point into the subgroup constructed above. -/
def liftPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t g)
    (hy : Set.range y.1 ⊆ W LB ι) : SchemeHomOver t (gU LB ι) :=
  ⟨IsOpenImmersion.lift (ιU LB ι) y.1 (by rw [range_ιU]; exact hy), by
    rw [IsOpenImmersion.lift_fac_assoc]; exact y.2⟩

@[scoped simp]
theorem toB_liftPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t g)
    (hy : Set.range y.1 ⊆ W LB ι) : toB LB ι (liftPt LB ι y hy) = y :=
  Subtype.ext (IsOpenImmersion.lift_fac _ _ _)

/-- Multiply points of the constructed subgroup. -/
def mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (gU LB ι)) :
    SchemeHomOver t (gU LB ι) :=
  liftPt LB ι (LB.mul t (toB LB ι x) (toB LB ι y))
    (range_mul_subset_W LB ι t _ _ (range_toB_subset LB ι x) (range_toB_subset LB ι y))

/-- The identity point of the constructed subgroup. -/
def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t (gU LB ι) :=
  liftPt LB ι (LB.one t) (range_one_subset_W LB ι t)

/-- Invert a point of the constructed subgroup. -/
def invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t (gU LB ι)) :
    SchemeHomOver t (gU LB ι) :=
  liftPt LB ι (LB.inv t (toB LB ι x)) (range_inv_subset_W LB ι t _ (range_toB_subset LB ι x))

theorem toB_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t (gU LB ι)) :
    toB LB ι (mulPt LB ι t x y) = LB.mul t (toB LB ι x) (toB LB ι y) :=
  toB_liftPt _ _ _ _

theorem toB_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    toB LB ι (onePt LB ι t) = LB.one t :=
  toB_liftPt _ _ _ _

theorem toB_invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t (gU LB ι)) : toB LB ι (invPt LB ι t x) = LB.inv t (toB LB ι x) :=
  toB_liftPt _ _ _ _

/-- The relative group law on the selected open subgroup. -/
def lawU : RelativeGroupLaw R (gU LB ι) where
  mul t x y := mulPt LB ι t x y
  one t := onePt LB ι t
  inv t x := invPt LB ι t x
  mul_assoc t x y z := by
    apply toB_injective LB ι
    simp only [toB_mulPt]
    exact LB.mul_assoc t _ _ _
  one_mul t x := by
    apply toB_injective LB ι
    simp only [toB_mulPt, toB_onePt]
    exact LB.one_mul t _
  mul_one t x := by
    apply toB_injective LB ι
    simp only [toB_mulPt, toB_onePt]
    exact LB.mul_one t _
  inv_mul_cancel t x := by
    apply toB_injective LB ι
    simp only [toB_mulPt, toB_invPt, toB_onePt]
    exact LB.inv_mul_cancel t _
  mul_natural t t' φ hφ x y := by
    apply toB_injective LB ι
    rw [toB_transition]
    simp only [toB_mulPt]
    rw [LB.mul_natural t t' φ hφ, toB_transition, toB_transition]

theorem hom_ιU {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (gU LB
    ι)) :
    NeronModelInfra.schemeHomOverComp ((lawU LB ι).mul t x y)
        (⟨ιU LB ι, rfl⟩ : SchemeHomOver (gU LB ι) g) =
      LB.mul t (NeronModelInfra.schemeHomOverComp x (⟨ιU LB ι, rfl⟩ : SchemeHomOver (gU LB ι) g))
        (NeronModelInfra.schemeHomOverComp y (⟨ιU LB ι, rfl⟩ : SchemeHomOver (gU LB ι) g)) :=
  toB_mulPt LB ι t x y

theorem isCommutative_lawU (hc : LB.IsCommutative) : (lawU LB ι).IsCommutative := by
  intro T t x y
  apply toB_injective LB ι
  change toB LB ι (mulPt LB ι t x y) = toB LB ι (mulPt LB ι t y x)
  rw [toB_mulPt, toB_mulPt]
  exact hc t _ _

end Law

end ClosedFibreIdentity

end

end AbelianVarieties.NOSProofs.Subgroups

namespace GoodReductionJacobian.RelativeGroupLaw

open AbelianVarieties.NOSProofs.Subgroups.ClosedFibreIdentity

theorem
    exists_isOpenImmersion_preimage_range_eq_connectedComponent_of_isClosedImmersion
    {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    [LocallyOfFiniteType g] [QuasiCompact g] (LB : RelativeGroupLaw R g)
    {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [IsClosedImmersion ι] :
    ∃ (U : Scheme.{u}) (i : U ⟶ B) (LU : RelativeGroupLaw R (i ≫ g)),
      IsOpenImmersion i ∧
      Set.range i =
        (pullback.fst g ι ''
          (connectedComponent
            (((LB.baseChange ι).one (𝟙 (Spec (CommRingCat.of K)))).1
              (IsLocalRing.closedPoint K)))ᶜ)ᶜ ∧
      pullback.fst g ι ⁻¹' Set.range i =
        connectedComponent
          (((LB.baseChange ι).one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K)) ∧
      (Set.range (pullback.fst g ι))ᶜ ⊆ Set.range i ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ g)),
        NeronModelInfra.schemeHomOverComp (LU.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ g) g) =
          LB.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ g) g))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ g) g))) ∧
      (LB.IsCommutative → LU.IsCommutative) := by
  refine ⟨U LB ι, ιU LB ι, lawU LB ι, inferInstance, range_ιU LB ι, ?_, ?_,
    fun t x y => hom_ιU LB ι t x y, isCommutative_lawU LB ι⟩
  · rw [range_ιU]; exact preimage_W LB ι
  · rw [range_ιU]; exact compl_range_subset_W LB ι

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.Subgroups

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.TopologicalSpace
open _root_.Topology

noncomputable section

namespace ReducedIdentityComponent

open scoped
  AbelianVarieties.NOSProofs.ClosedSubgroups.GoodReductionJacobian.RelativeGroupLaw.ClosedSubmonoid
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section Reduced

open AlgebraicGeometry.Scheme.IdealSheafData

open
  AbelianVarieties.NOSProofs.ClosedSubgroups.GoodReductionJacobian.RelativeGroupLaw.ClosedSubmonoid
  (redSub redι redLift redLift_ι range_redι)

/-- The reduced closed subscheme with the whole underlying space. -/
abbrev Gr (G : Scheme.{u}) : Scheme.{u} := redSub (⊤ : Closeds G)

/-- The inclusion of the reduced subscheme. -/
abbrev ιr (G : Scheme.{u}) : Gr G ⟶ G := redι (⊤ : Closeds G)

theorem range_ιr (G : Scheme.{u}) : Set.range (ιr G) = Set.univ :=
  range_redι (⊤ : Closeds G)

theorem surjective_ιr (G : Scheme.{u}) : Function.Surjective (ιr G) :=
  Set.range_eq_univ.mp (range_ιr G)

theorem isHomeomorph_ιr (G : Scheme.{u}) : IsHomeomorph (ιr G) :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(ιr G).isClosedEmbedding.isEmbedding, surjective_ιr G⟩

/-- Factor a morphism from a reduced scheme through the reduction. -/
def liftr {G T : Scheme.{u}} [IsReduced T] (g : T ⟶ G) : T ⟶ Gr G :=
  redLift (⊤ : Closeds G) g (fun _ _ => trivial)

@[reassoc (attr := simp)]
theorem liftr_ι {G T : Scheme.{u}} [IsReduced T] (g : T ⟶ G) : liftr g ≫ ιr G = g :=
  redLift_ι (⊤ : Closeds G) g (fun _ _ => trivial)

end Reduced

section Law

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)

/-- The structure morphism of the reduced group. -/
abbrev fr (f : G ⟶ Spec (CommRingCat.of k)) : Gr G ⟶ Spec (CommRingCat.of k) := ιr G ≫ f

/-- Forget the factorization of a point through the reduced subscheme. -/
def toG {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (fr f)) :
    SchemeHomOver t f :=
  ⟨x.1 ≫ ιr G, by rw [Category.assoc]; exact x.2⟩

@[scoped simp]
theorem toG_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (fr f)) :
    (toG x).1 = x.1 ≫ ιr G := rfl

theorem toG_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (fr f)) :
    toG x = NeronModelInfra.schemeHomOverComp x (⟨ιr G, rfl⟩ : SchemeHomOver (fr f) f) := rfl

theorem toG_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (toG (f := f) (T := T) (t := t)) := by
  intro x y h
  exact Subtype.ext ((cancel_mono (ιr G)).mp (congrArg Subtype.val h))

theorem toG_transition {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t (fr f)) :
    toG (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (toG x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- Lift a point into the subgroup constructed above. -/
def liftPt {T : Scheme.{u}} [IsReduced T] {t : T ⟶ Spec (CommRingCat.of k)}
    (y : SchemeHomOver t f) : SchemeHomOver t (fr f) :=
  ⟨liftr y.1, by rw [liftr_ι_assoc]; exact y.2⟩

@[scoped simp]
theorem toG_liftPt {T : Scheme.{u}} [IsReduced T] {t : T ⟶ Spec (CommRingCat.of k)}
    (y : SchemeHomOver t f) : toG (liftPt y) = y :=
  Subtype.ext (liftr_ι _)

theorem toG_surjective {T : Scheme.{u}} [IsReduced T] {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Surjective (toG (f := f) (T := T) (t := t)) :=
  fun y => ⟨liftPt y, toG_liftPt y⟩

variable [PerfectField k] [LocallyOfFiniteType f]

theorem geometricallyReduced_fr : GeometricallyReduced (fr f) :=
  AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField (fr f)

theorem isReduced_pullback_fr : IsReduced (pullback (fr f) (fr f)) := by
  have : GeometricallyReduced (fr f) := geometricallyReduced_fr
  have : IsLocallyNoetherian (Gr G) := LocallyOfFiniteType.isLocallyNoetherian (fr f)
  infer_instance

/-- The multiplication morphism from the product of the reduced subscheme. -/
def M : pullback (fr f) (fr f) ⟶ G :=
  (L.mul (pullback.fst (fr f) (fr f) ≫ fr f)
    ⟨pullback.fst (fr f) (fr f) ≫ ιr G, by simp only [Category.assoc]⟩
    ⟨pullback.snd (fr f) (fr f) ≫ ιr G, by simpa only [Category.assoc] using
      pullback.condition.symm⟩).1

/-- The multiplication morphism factored through the reduction. -/
def Mr : pullback (fr f) (fr f) ⟶ Gr G :=
  have : IsReduced (pullback (fr f) (fr f)) := isReduced_pullback_fr
  liftr (M L)

@[reassoc]
theorem Mr_ι : Mr L ≫ ιr G = M L := by
  have : IsReduced (pullback (fr f) (fr f)) := isReduced_pullback_fr
  exact liftr_ι _

/-- Multiply points of the constructed subgroup. -/
def mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (fr f)) :
    SchemeHomOver t (fr f) :=
  ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ Mr L, by
    have h := (L.mul (pullback.fst (fr f) (fr f) ≫ fr f)
      ⟨pullback.fst (fr f) (fr f) ≫ ιr G, by simp only [Category.assoc]⟩
      ⟨pullback.snd (fr f) (fr f) ≫ ιr G, by simpa only [Category.assoc] using
        pullback.condition.symm⟩).2
    rw [Category.assoc, Mr_ι_assoc, M, h, pullback.lift_fst_assoc]
    exact x.2⟩

theorem toG_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (fr f)) :
    toG (mulPt L t x y) = L.mul t (toG x) (toG y) := by
  apply Subtype.ext
  rw [toG_coe]
  change (pullback.lift x.1 y.1 _ ≫ Mr L) ≫ ιr G = _
  rw [Category.assoc, Mr_ι, M]
  have hψ : pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ pullback.fst (fr f) (fr f) ≫ fr f = t := by
    rw [pullback.lift_fst_assoc]; exact x.2
  have h := L.mul_natural (pullback.fst (fr f) (fr f) ≫ fr f) t
    (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
    ⟨pullback.fst (fr f) (fr f) ≫ ιr G, by simp only [Category.assoc]⟩
    ⟨pullback.snd (fr f) (fr f) ≫ ιr G, by simpa only [Category.assoc] using
      pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
      (⟨pullback.fst (fr f) (fr f) ≫ ιr G, by simp only [Category.assoc]⟩ : SchemeHomOver _ f) =
        toG x :=
    Subtype.ext (by
      rw [GoodReductionJacobian.schemeHomOverComp_coe, toG_coe, pullback.lift_fst_assoc])
  have h2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
      (⟨pullback.snd (fr f) (fr f) ≫ ιr G, by simpa only [Category.assoc] using
        pullback.condition.symm⟩ :
        SchemeHomOver _ f) = toG y :=
    Subtype.ext (by
      rw [GoodReductionJacobian.schemeHomOverComp_coe, toG_coe, pullback.lift_snd_assoc])
  rw [h1, h2] at h
  exact congrArg Subtype.val h

/-- The identity section factored through the reduction. -/
def er : Spec (CommRingCat.of k) ⟶ Gr G := liftr (L.one (𝟙 _)).1

omit [PerfectField k] [LocallyOfFiniteType f] in
@[reassoc]
theorem er_ι : er L ≫ ιr G = (L.one (𝟙 _)).1 := liftr_ι _

/-- The identity point of the constructed subgroup. -/
def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : SchemeHomOver t (fr f) :=
  ⟨t ≫ er L, by
    rw [Category.assoc, er_ι_assoc, (L.one (𝟙 _)).2, Category.comp_id]⟩

omit [PerfectField k] [LocallyOfFiniteType f] in
theorem toG_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    toG (onePt L t) = L.one t := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id t)
  apply Subtype.ext
  rw [toG_coe]
  change (t ≫ er L) ≫ ιr G = _
  rw [Category.assoc, er_ι, ← h]
  rfl

/-- The inversion morphism factored through the reduction. -/
def jr : Gr G ⟶ Gr G := liftr (L.inv (fr f) ⟨ιr G, rfl⟩).1

omit [PerfectField k] [LocallyOfFiniteType f] in
@[reassoc]
theorem jr_ι : jr L ≫ ιr G = (L.inv (fr f) ⟨ιr G, rfl⟩).1 := liftr_ι _

/-- Invert a point of the constructed subgroup. -/
def invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (fr f)) :
    SchemeHomOver t (fr f) :=
  ⟨x.1 ≫ jr L, by
    rw [Category.assoc, jr_ι_assoc, (L.inv (fr f) ⟨ιr G, rfl⟩).2]
    exact x.2⟩

omit [PerfectField k] [LocallyOfFiniteType f] in
theorem toG_invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t (fr f)) : toG (invPt L t x) = L.inv t (toG x) := by
  have h := L.inv_natural (fr f) t x.1 x.2 ⟨ιr G, rfl⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (⟨ιr G, rfl⟩ : SchemeHomOver (fr f) f) =
      toG x := Subtype.ext rfl
  rw [h1] at h
  apply Subtype.ext
  rw [toG_coe, ← h]
  change (x.1 ≫ jr L) ≫ ιr G = _
  rw [Category.assoc, jr_ι]
  rfl

/-- The group law inherited by the reduced group. -/
def lawr : RelativeGroupLaw k (fr f) where
  mul t x y := mulPt L t x y
  one t := onePt L t
  inv t x := invPt L t x
  mul_assoc t x y z := by
    apply toG_injective
    simp only [toG_mulPt]
    exact L.mul_assoc t _ _ _
  one_mul t x := by
    apply toG_injective
    simp only [toG_mulPt, toG_onePt]
    exact L.one_mul t _
  mul_one t x := by
    apply toG_injective
    simp only [toG_mulPt, toG_onePt]
    exact L.mul_one t _
  inv_mul_cancel t x := by
    apply toG_injective
    simp only [toG_mulPt, toG_invPt, toG_onePt]
    exact L.inv_mul_cancel t _
  mul_natural t t' ψ hψ x y := by
    apply toG_injective
    rw [toG_transition]
    simp only [toG_mulPt]
    rw [L.mul_natural t t' ψ hψ, toG_transition, toG_transition]

theorem toG_lawr_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (fr f)) :
    toG ((lawr L).mul t x y) = L.mul t (toG x) (toG y) :=
  toG_mulPt L t x y

theorem toG_lawr_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    toG ((lawr L).one t) = L.one t :=
  toG_onePt L t

theorem hom_ιr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (fr f)) :
    NeronModelInfra.schemeHomOverComp ((lawr L).mul t x y) (⟨ιr G, rfl⟩ : SchemeHomOver (fr f) f) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (⟨ιr G, rfl⟩ : SchemeHomOver (fr f) f))
        (NeronModelInfra.schemeHomOverComp y (⟨ιr G, rfl⟩ : SchemeHomOver (fr f) f)) :=
  toG_lawr_mul L t x y

theorem isCommutative_lawr (hc : L.IsCommutative) : (lawr L).IsCommutative := by
  intro T t x y
  apply toG_injective
  rw [toG_lawr_mul, toG_lawr_mul, hc t]

theorem smooth_fr (L : RelativeGroupLaw k f) : Smooth (fr f) :=
  have : GeometricallyReduced (fr f) := geometricallyReduced_fr
  smooth_of_geometricallyReduced_of_locallyOfFiniteType (lawr L)

end Law

section Cast

variable {k : Type u} [Field k]

/-- Transport a relative group law along equality of its structure morphism. -/
def castLaw {X : Scheme.{u}} {f₁ f₂ : X ⟶ Spec (CommRingCat.of k)} (e : f₁ = f₂)
    (L : RelativeGroupLaw k f₁) : RelativeGroupLaw k f₂ := e ▸ L

theorem castLaw_mul_val {X : Scheme.{u}} {f₁ f₂ : X ⟶ Spec (CommRingCat.of k)} (e : f₁ = f₂)
    (L : RelativeGroupLaw k f₁) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t f₂) :
    ((castLaw e L).mul t x y).1 =
      (L.mul t ⟨x.1, by rw [e]; exact x.2⟩ ⟨y.1, by rw [e]; exact y.2⟩).1 := by
  subst e
  rfl

theorem isCommutative_castLaw {X : Scheme.{u}} {f₁ f₂ : X ⟶ Spec (CommRingCat.of k)} (e : f₁ = f₂)
    (L : RelativeGroupLaw k f₁) (hc : L.IsCommutative) : (castLaw e L).IsCommutative := by
  subst e
  exact hc

end Cast

section Topo

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

theorem image_connectedComponent_of_isHomeomorph {φ : α → β} (hφ : IsHomeomorph φ) (a : α) :
    φ '' connectedComponent a = connectedComponent (φ a) := by
  have h := (hφ.homeomorph φ).image_connectedComponentIn (s := Set.univ) (x := a) (Set.mem_univ a)
  rw [Set.image_univ, connectedComponentIn_univ] at h
  have hr : Set.range (hφ.homeomorph φ) = Set.univ := (hφ.homeomorph φ).surjective.range_eq
  rw [hr, connectedComponentIn_univ] at h
  exact h

end Topo

end ReducedIdentityComponent

end

end AbelianVarieties.NOSProofs.Subgroups

namespace GoodReductionJacobian.RelativeGroupLaw

open AbelianVarieties.NOSProofs.Subgroups.ReducedIdentityComponent

theorem
    exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
    (k : Type u) [Field k] [PerfectField k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f) :
    ∃ (G₀ : Scheme.{u}) (i : G₀ ⟶ G) (L₀ : RelativeGroupLaw k (i ≫ f)) (n : ℕ),
      IsClosedImmersion i ∧ IrreducibleSpace G₀ ∧ SmoothOfRelativeDimension n (i ≫ f) ∧
      GeometricallyIrreducible (i ≫ f) ∧
      IsOpen (Set.range i) ∧
      Set.range i =
        connectedComponent ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) ∧
      topologicalKrullDim G₀ = n ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      (L.IsCommutative → L₀.IsCommutative) ∧
      ∃ S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f), S.Finite ∧
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
          ∃ s ∈ S, ∃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f),
            x = L.mul (𝟙 (Spec (CommRingCat.of k))) s
              (NeronModelInfra.schemeHomOverComp a (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) := by
  have : Smooth (fr f) := smooth_fr L
  have : QuasiCompact (fr f) := inferInstance
  obtain ⟨G₀, i₀, L₀, hoi, hci, hirr, hgi, -, hrange, -, hhom, hcomm, S, hSfin, hS⟩ :=
    exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
      k (lawr L)
  have e : i₀ ≫ ιr G ≫ f = (i₀ ≫ ιr G) ≫ f := (Category.assoc _ _ _).symm
  have : Smooth ((i₀ ≫ ιr G) ≫ f) := by rw [Category.assoc]; infer_instance
  obtain ⟨n, hn⟩ :=
    AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace ((i₀ ≫ ιr G) ≫ f)
  have : Nonempty G₀ := inferInstance
  refine ⟨G₀, i₀ ≫ ιr G, castLaw e L₀, n, inferInstance, hirr, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact hgi
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (isHomeomorph_ιr G).isOpenMap _ i₀.isOpenEmbedding.isOpen_range
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange,
      image_connectedComponent_of_isHomeomorph (isHomeomorph_ιr G)]
    congr 1
    have h1 : ((lawr L).one (𝟙 _)).1 ≫ ιr G = (L.one (𝟙 _)).1 :=
      congrArg Subtype.val (toG_lawr_one L (𝟙 _))
    rw [← h1]
    rfl
  · have : SmoothOfRelativeDimension n ((i₀ ≫ ιr G) ≫ f) := hn
    exact le_antisymm
      (AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le ((i₀ ≫ ιr G) ≫ f) n)
      (AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim ((i₀ ≫ ιr G) ≫ f) n)
  · intro T t x y
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, castLaw_mul_val]
    set x' : SchemeHomOver t (i₀ ≫ ιr G ≫ f) := ⟨x.1, by rw [e]; exact x.2⟩ with hx'
    set y' : SchemeHomOver t (i₀ ≫ ιr G ≫ f) := ⟨y.1, by rw [e]; exact y.2⟩ with hy'
    have h1 := congrArg Subtype.val (hhom t x' y')
    have h2 := congrArg Subtype.val (hom_ιr L t
      (NeronModelInfra.schemeHomOverComp x' (⟨i₀, rfl⟩ : SchemeHomOver (i₀ ≫ fr f) (fr f)))
      (NeronModelInfra.schemeHomOverComp y' (⟨i₀, rfl⟩ : SchemeHomOver (i₀ ≫ fr f) (fr f))))
    simp only [NeronModelInfra.schemeHomOverComp_coe] at h1 h2
    rw [← Category.assoc, h1, h2]
    congr 2
  · intro hc
    exact isCommutative_castLaw e L₀ (hcomm (isCommutative_lawr L hc))
  · refine ⟨toG '' S, hSfin.image _, fun x => ?_⟩
    obtain ⟨x', hx'⟩ := toG_surjective (f := f) x
    obtain ⟨s, hs, a, ha⟩ := hS x'
    refine ⟨toG s, Set.mem_image_of_mem _ hs, ⟨a.1, by rw [← e]; exact a.2⟩, ?_⟩
    rw [← hx', ha, toG_lawr_mul]
    congr 1

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_of_flat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.Subgroups

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

namespace FlatImage
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section Represent

variable {k : Type u} [CommRing k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)

/-- The pair of test-scheme points as a morphism into the fibre product. -/
noncomputable def pair {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x y : SchemeHomOver t
    f) : T ⟶ pullback f f :=
  pullback.lift x.1 y.1 (x.2.trans y.2.symm)

@[scoped simp] theorem pair_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x y :
    SchemeHomOver t f) :
    pair x y ≫ pullback.fst f f = x.1 := pullback.lift_fst _ _ _
@[scoped simp] theorem pair_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x y :
    SchemeHomOver t f) :
    pair x y ≫ pullback.snd f f = y.1 := pullback.lift_snd _ _ _

/-- The scheme morphism representing inversion of group points. -/
noncomputable def invMor : J ⟶ J := (L.inv f ⟨𝟙 J, Category.id_comp f⟩).1

theorem invMor_over : invMor L ≫ f = f := (L.inv f ⟨𝟙 J, Category.id_comp f⟩).2

theorem inv_eq_comp_invMor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t
    f) :
    (L.inv t x).1 = x.1 ≫ invMor L := by
  have h := L.inv_natural f t x.1 x.2 ⟨𝟙 J, Category.id_comp f⟩
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (⟨𝟙 J, Category.id_comp f⟩ :
    SchemeHomOver f f) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]; rfl

/-- The identity section of the group scheme. -/
noncomputable def oneMor : Spec (CommRingCat.of k) ⟶ J := (L.one (𝟙 _)).1

theorem oneMor_over : oneMor L ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

theorem one_eq_comp_oneMor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    (L.one t).1 = t ≫ oneMor L := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← h]; rfl

end Represent

end FlatImage

namespace FlatImage
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section Image

variable {k : Type u} [CommRing k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)}
  {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} (σ : SchemeHomOver g f) [QuasiCompact σ.1]

theorem isSchemeTheoreticallyDominant_toImage : IsSchemeTheoreticallyDominant σ.1.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  let U : J.affineOpens → σ.1.image.affineOpens := fun V => ⟨σ.1.imageι ⁻¹ᵁ V.1, V.2.preimage
    σ.1.imageι⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U ?_ ?_
  · rw [← top_le_iff]
    intro b _
    obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ := J.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (σ.1.imageι b)) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hbV⟩
  · intro V
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← le_bot_iff]
    intro s hs
    exact (σ.1.toImage_app_injective V ((RingHom.mem_ker).mp hs |>.trans (map_zero _).symm) : _)

end Image

end FlatImage

namespace FlatImage
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section Closure

variable {k : Type u} [CommRing k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)
  {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} [Flat g] (LX : RelativeGroupLaw k g)
  (σ : SchemeHomOver g f) [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)]
  (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))

/-- The scheme-theoretic image inclusion as a morphism over the base. -/
noncomputable def imageιOver : SchemeHomOver (σ.1.imageι ≫ f) f := ⟨σ.1.imageι, rfl⟩

omit [Flat g] [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)] in
@[scoped simp] theorem imageιOver_coe : (imageιOver σ).1 = σ.1.imageι := rfl

/-- Multiplication on the product of the scheme-theoretic image. -/
noncomputable def mulJB : pullback (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ⟶ J :=
  (L.mul (pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f)
    ⟨pullback.fst _ _ ≫ σ.1.imageι, by rw [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ σ.1.imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩).1

omit [Flat g] [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)] in
theorem mulJB_over : mulJB L σ ≫ f = pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫
    f :=
  (L.mul _ _ _).2

/-- The product morphism induced by factorization through the image. -/
noncomputable def prodToImage : pullback g g ⟶ pullback (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) :=
  pullback.map g g (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) σ.1.toImage σ.1.toImage (𝟙 _)
    (by rw [Category.comp_id, ← Category.assoc, Scheme.Hom.toImage_imageι]; exact σ.2.symm)
    (by rw [Category.comp_id, ← Category.assoc, Scheme.Hom.toImage_imageι]; exact σ.2.symm)

omit [Flat g] [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)] in
@[scoped simp] theorem prodToImage_fst : prodToImage σ ≫ pullback.fst _ _ = pullback.fst g g ≫
    σ.1.toImage :=
  pullback.lift_fst _ _ _
omit [Flat g] [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)] in
@[scoped simp] theorem prodToImage_snd : prodToImage σ ≫ pullback.snd _ _ = pullback.snd g g ≫
    σ.1.toImage :=
  pullback.lift_snd _ _ _

include hσ in
omit [Flat g] [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)] in
theorem prodToImage_mulJB :
    prodToImage σ ≫ mulJB L σ = (LX.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
      ⟨pullback.snd g g, pullback.condition.symm⟩).1 ≫ σ.1 := by
  have hover : prodToImage σ ≫ pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f =
    pullback.fst g g ≫ g := by
    rw [← Category.assoc, prodToImage_fst, Category.assoc, ← Category.assoc σ.1.toImage,
      Scheme.Hom.toImage_imageι, σ.2]
  have h := L.mul_natural _ (pullback.fst g g ≫ g) (prodToImage σ) hover
    ⟨pullback.fst _ _ ≫ σ.1.imageι, by rw [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ σ.1.imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (prodToImage σ) hover
      (⟨pullback.fst _ _ ≫ σ.1.imageι, by rw [Category.assoc]⟩ : SchemeHomOver (pullback.fst
        (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f) f) =
      NeronModelInfra.schemeHomOverComp (⟨pullback.fst g g, rfl⟩ : SchemeHomOver (pullback.fst g g
        ≫ g) g) σ := by
    apply Subtype.ext
    change prodToImage σ ≫ pullback.fst _ _ ≫ σ.1.imageι = pullback.fst g g ≫ σ.1
    rw [← Category.assoc, prodToImage_fst, Category.assoc, Scheme.Hom.toImage_imageι]
  have h2 : GoodReductionJacobian.schemeHomOverComp (prodToImage σ) hover
      (⟨pullback.snd _ _ ≫ σ.1.imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩ :
        SchemeHomOver (pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f) f) =
      NeronModelInfra.schemeHomOverComp (⟨pullback.snd g g, pullback.condition.symm⟩ :
        SchemeHomOver (pullback.fst g g ≫ g) g) σ := by
    apply Subtype.ext
    change prodToImage σ ≫ pullback.snd _ _ ≫ σ.1.imageι = pullback.snd g g ≫ σ.1
    rw [← Category.assoc, prodToImage_snd, Category.assoc, Scheme.Hom.toImage_imageι]
  rw [h1, h2, ← hσ] at h
  exact congrArg Subtype.val h

theorem isSchemeTheoreticallyDominant_prodToImage : IsSchemeTheoreticallyDominant (prodToImage σ)
    := by
  have hdom : IsSchemeTheoreticallyDominant σ.1.toImage :=
    isSchemeTheoreticallyDominant_toImage σ
  have hqc : QuasiCompact σ.1.toImage := inferInstance
  have hπ : σ.1.toImage ≫ σ.1.imageι ≫ f = g := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact σ.2
  have t₁ := IsPullback.of_hasPullback (σ.1.imageι ≫ f) g
  have s₁ : IsPullback (pullback.fst g g) (pullback.snd g g) (σ.1.toImage ≫ σ.1.imageι ≫ f) g := by
    rw [hπ]; exact IsPullback.of_hasPullback g g
  have H₁ := IsPullback.of_bot' s₁ t₁
  have : IsSchemeTheoreticallyDominant (t₁.lift (pullback.fst g g ≫ σ.1.toImage) (pullback.snd g g)
      (by rw [Category.assoc, s₁.w])) := IsSchemeTheoreticallyDominant.of_isPullback H₁
  have t₂ := (IsPullback.of_hasPullback (σ.1.imageι ≫ f) (σ.1.imageι ≫ f)).flip
  have s₂ : IsPullback (pullback.snd (σ.1.imageι ≫ f) g) (pullback.fst (σ.1.imageι ≫ f) g)
      (σ.1.toImage ≫ σ.1.imageι ≫ f) (σ.1.imageι ≫ f) := by
    rw [hπ]; exact (IsPullback.of_hasPullback (σ.1.imageι ≫ f) g).flip
  have H₂ := IsPullback.of_bot' s₂ t₂
  have : IsSchemeTheoreticallyDominant (t₂.lift (pullback.snd (σ.1.imageι ≫ f) g ≫ σ.1.toImage)
      (pullback.fst (σ.1.imageι ≫ f) g) (by rw [Category.assoc, s₂.w])) :=
        IsSchemeTheoreticallyDominant.of_isPullback H₂
  have heq : prodToImage σ =
      t₁.lift (pullback.fst g g ≫ σ.1.toImage) (pullback.snd g g)
        (by rw [Category.assoc, s₁.w]) ≫
      t₂.lift (pullback.snd (σ.1.imageι ≫ f) g ≫ σ.1.toImage) (pullback.fst (σ.1.imageι ≫ f) g)
        (by rw [Category.assoc, s₂.w]) := by
    apply pullback.hom_ext
    · rw [prodToImage_fst, Category.assoc, t₂.lift_snd, t₁.lift_fst]
    · rw [prodToImage_snd, Category.assoc, t₂.lift_fst, t₁.lift_snd_assoc]
  rw [heq]; infer_instance

include hσ in
theorem ker_le_ker_mulJB : σ.1.ker ≤ (mulJB L σ).ker := by
  have hdom := isSchemeTheoreticallyDominant_prodToImage σ
  calc σ.1.ker = (⊥ : X.IdealSheafData).map σ.1 := (Scheme.IdealSheafData.map_bot _).symm
    _ ≤ ((LX.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g,
      pullback.condition.symm⟩).1.ker).map σ.1 :=
        Scheme.IdealSheafData.map_mono _ bot_le
    _ = ((LX.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g,
      pullback.condition.symm⟩).1 ≫ σ.1).ker :=
        (Scheme.Hom.ker_comp _ _).symm
    _ = (prodToImage σ ≫ mulJB L σ).ker := by rw [prodToImage_mulJB L LX σ hσ]
    _ = (prodToImage σ).ker.map (mulJB L σ) := Scheme.Hom.ker_comp _ _
    _ = (mulJB L σ).ker := by rw [hdom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- Inversion on the scheme-theoretic image followed by its inclusion. -/
noncomputable def invJB : σ.1.image ⟶ J := σ.1.imageι ≫ invMor L

include hσ in
omit [Flat g] [Flat (σ.1.imageι ≫ f)] in
theorem ker_le_ker_invJB : σ.1.ker ≤ (invJB L σ).ker := by
  have hdom : IsSchemeTheoreticallyDominant σ.1.toImage :=
    isSchemeTheoreticallyDominant_toImage σ
  have hcomp : σ.1.toImage ≫ invJB L σ = invMor LX ≫ σ.1 := by
    change σ.1.toImage ≫ σ.1.imageι ≫ invMor L = _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, ← inv_eq_comp_invMor L g σ]
    have h := AbelianVarieties.NOSProofs.KernelTorsor.Torsor.map_inv LX L σ hσ g ⟨𝟙 X,
      Category.id_comp g⟩
    have hx : NeronModelInfra.schemeHomOverComp (⟨𝟙 X, Category.id_comp g⟩ : SchemeHomOver g g) σ
      = σ :=
      Subtype.ext (Category.id_comp _)
    rw [hx] at h
    rw [← h]; rfl
  calc σ.1.ker = (⊥ : X.IdealSheafData).map σ.1 := (Scheme.IdealSheafData.map_bot _).symm
    _ ≤ ((invMor LX).ker).map σ.1 := Scheme.IdealSheafData.map_mono _ bot_le
    _ = (invMor LX ≫ σ.1).ker := (Scheme.Hom.ker_comp _ _).symm
    _ = (σ.1.toImage ≫ invJB L σ).ker := by rw [hcomp]
    _ = (σ.1.toImage).ker.map (invJB L σ) := Scheme.Hom.ker_comp _ _
    _ = (invJB L σ).ker := by rw [hdom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- Multiplication factored through the scheme-theoretic image. -/
noncomputable def mulB : pullback (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ⟶ σ.1.image :=
  IsClosedImmersion.lift σ.1.imageι (mulJB L σ) ((Scheme.IdealSheafData.ker_subschemeι _).trans_le
    (ker_le_ker_mulJB L LX σ hσ))

theorem mulB_imageι : mulB L LX σ hσ ≫ σ.1.imageι = mulJB L σ := IsClosedImmersion.lift_fac _ _ _

/-- Inversion factored through the scheme-theoretic image. -/
noncomputable def invB : σ.1.image ⟶ σ.1.image :=
  IsClosedImmersion.lift σ.1.imageι (invJB L σ) ((Scheme.IdealSheafData.ker_subschemeι _).trans_le
    (ker_le_ker_invJB L LX σ hσ))

omit [Flat g] [Flat (σ.1.imageι ≫ f)] in
theorem invB_imageι : invB L LX σ hσ ≫ σ.1.imageι = σ.1.imageι ≫ invMor L :=
    IsClosedImmersion.lift_fac _ _ _

/-- The identity section factored through the scheme-theoretic image. -/
noncomputable def oneB : Spec (CommRingCat.of k) ⟶ σ.1.image := oneMor LX ≫ σ.1.toImage

include hσ in
omit [Flat g] [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)] in
theorem oneB_imageι : oneB LX σ ≫ σ.1.imageι = oneMor L := by
  change (oneMor LX ≫ σ.1.toImage) ≫ σ.1.imageι = _
  rw [Category.assoc, Scheme.Hom.toImage_imageι]
  have h := AbelianVarieties.NOSProofs.KernelTorsor.Torsor.map_one LX L σ hσ (𝟙 _)
  exact congrArg Subtype.val h

end Closure

end FlatImage

namespace FlatImage
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section GroupLaw

variable {k : Type u} [CommRing k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} (L :
    RelativeGroupLaw k f)
  {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} [Flat g] (LX : RelativeGroupLaw k g)
  (σ : SchemeHomOver g f) [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)]
  (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))

/-- Include a point of the scheme-theoretic image in the target group. -/
noncomputable def incl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t
    (σ.1.imageι ≫ f)) :
    SchemeHomOver t f :=
  NeronModelInfra.schemeHomOverComp x (imageιOver σ)

omit [Flat g] [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)] in
@[scoped simp] theorem incl_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x :
    SchemeHomOver t (σ.1.imageι ≫ f)) :
    (incl σ x).1 = x.1 ≫ σ.1.imageι := rfl

omit [Flat g] [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)] in
theorem incl_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (incl σ (T := T) (t := t)) := fun _ _ h =>
  Subtype.ext ((cancel_mono σ.1.imageι).mp (congrArg Subtype.val h))

omit [Flat g] [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)] in
theorem incl_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec
    (CommRingCat.of k)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t (σ.1.imageι ≫ f)) :
    incl σ (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (incl σ x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- Multiply points of the constructed subgroup. -/
noncomputable def mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t
    (σ.1.imageι ≫ f)) :
    SchemeHomOver t (σ.1.imageι ≫ f) :=
  ⟨pair x y ≫ mulB L LX σ hσ, by
    rw [Category.assoc, ← Category.assoc (mulB L LX σ hσ), mulB_imageι, mulJB_over, ←
      Category.assoc, pair_fst]
    exact x.2⟩

theorem incl_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t
    (σ.1.imageι ≫ f)) :
    incl σ (mulPt L LX σ hσ t x y) = L.mul t (incl σ x) (incl σ y) := by
  have hψ : pair x y ≫ pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f = t := by
    rw [← Category.assoc, pair_fst]; exact x.2
  have h := L.mul_natural _ t (pair x y) hψ
    ⟨pullback.fst _ _ ≫ σ.1.imageι, by rw [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ σ.1.imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (pair x y) hψ
      (⟨pullback.fst _ _ ≫ σ.1.imageι, by rw [Category.assoc]⟩ :
        SchemeHomOver (pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f) f) = incl
          σ x := by
    apply Subtype.ext; change pair x y ≫ pullback.fst _ _ ≫ σ.1.imageι = x.1 ≫ σ.1.imageι
    rw [← Category.assoc, pair_fst]
  have h2 : GoodReductionJacobian.schemeHomOverComp (pair x y) hψ
      (⟨pullback.snd _ _ ≫ σ.1.imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩ :
        SchemeHomOver (pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f) f) = incl
          σ y := by
    apply Subtype.ext; change pair x y ≫ pullback.snd _ _ ≫ σ.1.imageι = y.1 ≫ σ.1.imageι
    rw [← Category.assoc, pair_snd]
  rw [h1, h2] at h
  rw [← h]
  apply Subtype.ext
  change (pair x y ≫ mulB L LX σ hσ) ≫ σ.1.imageι = pair x y ≫ mulJB L σ
  rw [Category.assoc, mulB_imageι]

/-- The identity point of the constructed subgroup. -/
noncomputable def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : SchemeHomOver t
    (σ.1.imageι ≫ f) :=
  ⟨t ≫ oneB LX σ, by
    rw [Category.assoc, ← Category.assoc (oneB LX σ), oneB_imageι L LX σ hσ, oneMor_over L,
      Category.comp_id]⟩

omit [Flat g] [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)] in
theorem incl_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : incl σ (onePt L LX σ hσ t)
    = L.one t := by
  apply Subtype.ext
  change (t ≫ oneB LX σ) ≫ σ.1.imageι = (L.one t).1
  rw [Category.assoc, oneB_imageι L LX σ hσ, one_eq_comp_oneMor L]

/-- Invert a point of the constructed subgroup. -/
noncomputable def invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t
    (σ.1.imageι ≫ f)) :
    SchemeHomOver t (σ.1.imageι ≫ f) :=
  ⟨x.1 ≫ invB L LX σ hσ, by
    rw [Category.assoc, ← Category.assoc (invB L LX σ hσ), invB_imageι, Category.assoc,
      invMor_over L]
    exact x.2⟩

omit [Flat g] [Flat (σ.1.imageι ≫ f)] in
theorem incl_invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t
    (σ.1.imageι ≫ f)) :
    incl σ (invPt L LX σ hσ t x) = L.inv t (incl σ x) := by
  apply Subtype.ext
  change (x.1 ≫ invB L LX σ hσ) ≫ σ.1.imageι = (L.inv t (incl σ x)).1
  rw [Category.assoc, invB_imageι, inv_eq_comp_invMor L, incl_coe, Category.assoc]

/-- The group law induced on the scheme-theoretic image. -/
noncomputable def lawB : RelativeGroupLaw k (σ.1.imageι ≫ f) where
  mul t x y := mulPt L LX σ hσ t x y
  one t := onePt L LX σ hσ t
  inv t x := invPt L LX σ hσ t x
  mul_assoc t x y z := incl_injective σ (by rw [incl_mulPt, incl_mulPt, incl_mulPt, incl_mulPt,
    L.mul_assoc])
  one_mul t x := incl_injective σ (by rw [incl_mulPt, incl_onePt, L.one_mul])
  mul_one t x := incl_injective σ (by rw [incl_mulPt, incl_onePt, L.mul_one])
  inv_mul_cancel t x := incl_injective σ (by rw [incl_mulPt, incl_invPt, incl_onePt,
    L.inv_mul_cancel])
  mul_natural t t' ψ hψ x y := incl_injective σ (by
    rw [incl_comp, incl_mulPt, incl_mulPt, incl_comp, incl_comp, L.mul_natural])

theorem lawB_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t
    (σ.1.imageι ≫ f)) :
    (lawB L LX σ hσ).mul t x y = mulPt L LX σ hσ t x y := rfl

include hσ in
theorem lawB_comm (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y :
    SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)) :
    (lawB L LX σ hσ).mul t x y = (lawB L LX σ hσ).mul t y x :=
  incl_injective σ (by rw [lawB_mul, lawB_mul, incl_mulPt, incl_mulPt, hcomm])

theorem lawB_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t
    (σ.1.imageι ≫ f)) :
    NeronModelInfra.schemeHomOverComp ((lawB L LX σ hσ).mul t x y) (imageιOver σ) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (imageιOver σ))
        (NeronModelInfra.schemeHomOverComp y (imageιOver σ)) :=
  incl_mulPt L LX σ hσ t x y

end GroupLaw

end FlatImage

end AbelianVarieties.NOSProofs.Subgroups

namespace GoodReductionJacobian.RelativeGroupLaw

open AbelianVarieties.NOSProofs.Subgroups.FlatImage

theorem
    exists_relativeGroupLaw_image_of_homomorphism_of_flat
    {R : Type u} [CommRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of R)} [Flat g] (LX : RelativeGroupLaw R g) (σ :
      SchemeHomOver g f)
    [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)]
    (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ)) :
    ∃ LB : RelativeGroupLaw R (σ.1.imageι ≫ f),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (σ.1.imageι ≫
        f)),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) (⟨σ.1.imageι, rfl⟩ : SchemeHomOver
          (σ.1.imageι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨σ.1.imageι, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨σ.1.imageι, rfl⟩)) ∧
      ((∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x
        y = L.mul t y x) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (σ.1.imageι ≫
          f)),
          LB.mul t x y = LB.mul t y x) :=
  ⟨lawB L LX σ hσ, fun t x y => lawB_hom L LX σ hσ t x y, fun hcomm _ t x y => lawB_comm L LX σ hσ
    hcomm t x y⟩

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.Subgroups

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.TopologicalSpace
open _root_.Topology

noncomputable section

namespace ClosedImage
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section Topology

variable {X : Type*} [TopologicalSpace X]

theorem denseOpen_union {s t U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUs : U ∩ closure s ⊆ s) (hs : closure s ⊆ closure (U ∩ closure s))
    (hVt : V ∩ closure t ⊆ t) (ht : closure t ⊆ closure (V ∩ closure t)) :
    ∃ W : Set X, IsOpen W ∧ W ∩ closure (s ∪ t) ⊆ s ∪ t ∧
      closure (s ∪ t) ⊆ closure (W ∩ closure (s ∪ t)) := by
  refine ⟨(U ∩ (closure t)ᶜ) ∪ (V ∩ (closure s)ᶜ) ∪ (U ∩ V),
    ((hU.inter isClosed_closure.isOpen_compl).union
      (hV.inter isClosed_closure.isOpen_compl)).union (hU.inter hV), ?_, ?_⟩
  · rintro p ⟨((⟨hpU, hpt⟩ | ⟨hpV, hps⟩) | ⟨hpU, hpV⟩), hpc⟩ <;>
      rw [closure_union] at hpc <;> rcases hpc with (hcs | hct)
    · exact Or.inl (hUs ⟨hpU, hcs⟩)
    · exact (hpt hct).elim
    · exact (hps hcs).elim
    · exact Or.inr (hVt ⟨hpV, hct⟩)
    · exact Or.inl (hUs ⟨hpU, hcs⟩)
    · exact Or.inr (hVt ⟨hpV, hct⟩)
  · have aux : ∀ {s' t' U' V' : Set X} (W : Set X), IsOpen U' →
        closure s' ⊆ closure (U' ∩ closure s') → closure t' ⊆ closure (V' ∩ closure t') →
        U' ∩ (closure t')ᶜ ⊆ W → U' ∩ V' ⊆ W →
        closure s' ⊆ closure (W ∩ closure (s' ∪ t')) := by
      intro s' t' U' V' W hU' hs' ht' h1 h2
      refine hs'.trans (closure_minimal ?_ isClosed_closure)
      rintro q ⟨hqU, hqs⟩
      by_cases hqt : q ∈ closure t'
      · have hq : q ∈ closure (U' ∩ (V' ∩ closure t')) :=
          hU'.inter_closure ⟨hqU, ht' hqt⟩
        refine closure_mono ?_ hq
        rintro z ⟨hzU, hzV, hzt⟩
        exact ⟨h2 ⟨hzU, hzV⟩, closure_mono Set.subset_union_right hzt⟩
      · exact subset_closure ⟨h1 ⟨hqU, hqt⟩, closure_mono Set.subset_union_left hqs⟩
    rw [closure_union]
    refine Set.union_subset ?_ ?_
    · rw [← closure_union]
      exact aux _ hU hs ht (fun z hz => Or.inl (Or.inl hz)) (fun z hz => Or.inr hz)
    · rw [← closure_union, Set.union_comm s t]
      exact aux _ hV ht hs (fun z hz => Or.inl (Or.inr hz)) (fun z hz => Or.inr ⟨hz.2, hz.1⟩)

theorem exists_isOpen_inter_closure_subset_of_isConstructible [CompactSpace X]
    [QuasiSeparatedSpace X] {ι : Type*} [Nonempty ι] (b : ι → Set X)
    (hb : IsTopologicalBasis (Set.range b)) (hbc : ∀ i, IsCompact (b i))
    {s : Set X} (hs : IsConstructible s) :
    ∃ U : Set X, IsOpen U ∧ U ∩ closure s ⊆ s ∧ closure s ⊆ closure (U ∩ closure s) := by
  induction s, hs using IsConstructible.induction_of_isTopologicalBasis b hb hbc with
  | sdiff i t ht =>
    refine ⟨b i, hb.isOpen ⟨i, rfl⟩, ?_, ?_⟩
    · rintro p ⟨hpi, hpc⟩
      refine ⟨hpi, ?_⟩
      have hcl : IsClosed (⋃ j ∈ t, b j)ᶜ :=
        (isOpen_biUnion fun j _ => hb.isOpen ⟨j, rfl⟩).isClosed_compl
      have : closure (b i \ ⋃ j ∈ t, b j) ⊆ (⋃ j ∈ t, b j)ᶜ :=
        closure_minimal (fun z hz => hz.2) hcl
      exact this hpc
    · exact closure_mono fun z hz => ⟨hz.1, subset_closure hz⟩
  | union s hs t ht Hs Ht =>
    obtain ⟨U, hU, hUs, hs'⟩ := Hs
    obtain ⟨V, hV, hVt, ht'⟩ := Ht
    exact denseOpen_union hU hV hUs hs' hVt ht'

theorem image_eq_of_image_subset [NoetherianSpace X] (r : X ≃ₜ X) {Z : Set X}
    (hZ : IsClosed Z) (h : r '' Z ⊆ Z) : r '' Z = Z := by
  by_contra hne
  let 𝒞 : Set (Closeds X) := {C | r '' (C : Set X) ⊂ C}
  have hZ𝒞 : (⟨Z, hZ⟩ : Closeds X) ∈ 𝒞 := LE.le.ssubset_of_ne h hne
  obtain ⟨C₀, hC₀, hmin⟩ := (wellFounded_lt (α := Closeds X)).has_min 𝒞 ⟨_, hZ𝒞⟩
  have hC₁ : (⟨r '' (C₀ : Set X), r.isClosedMap _ C₀.2⟩ : Closeds X) ∈ 𝒞 := by
    change r '' (r '' (C₀ : Set X)) ⊂ r '' (C₀ : Set X)
    refine ⟨Set.image_mono hC₀.1, fun hle => hC₀.2 ?_⟩
    exact (Set.image_subset_image_iff r.injective).mp hle
  refine hmin _ hC₁ ?_
  change (r '' (C₀ : Set X)) ⊂ (C₀ : Set X) at hC₀
  exact hC₀

end Topology

section Points

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k))

/-- The closed point determined by a rational group point. -/
abbrev pt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p) : X :=
  x.1 (fieldPoint k)

variable [LocallyOfFiniteType p]

theorem isClosed_pt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p) : IsClosed {pt p x} :=
  ((pointEquivClosedPoint p) ⟨x.1, x.2⟩).2

theorem exists_pt_eq_of_isClosed {c : X} (hc : IsClosed {c}) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p, pt p x = c := by
  refine ⟨⟨((pointEquivClosedPoint p).symm ⟨c, hc⟩).1,
    ((pointEquivClosedPoint p).symm ⟨c, hc⟩).2⟩, ?_⟩
  exact congrArg Subtype.val ((pointEquivClosedPoint p).apply_symm_apply ⟨c, hc⟩)

theorem exists_pt_mem_of_isLocallyClosed {C : Set X} (hC : IsLocallyClosed C)
    (hne : C.Nonempty) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p, pt p x ∈ C := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨c, hcC, hc⟩ := nonempty_inter_closedPoints hne hC
  obtain ⟨x, rfl⟩ := exists_pt_eq_of_isClosed p hc
  exact ⟨x, hcC⟩

theorem dense_range_pt :
    Dense (Set.range (pt p : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p → X)) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have h : closedPoints X ⊆ Set.range (pt p) := by
    intro c hc
    obtain ⟨x, rfl⟩ := exists_pt_eq_of_isClosed p hc
    exact ⟨x, rfl⟩
  exact Dense.mono h (dense_iff_closure_eq.mpr (closure_closedPoints (X := X)))

end Points

section Translations

variable {k : Type u} [Field k] {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)}

/-- The opposite relative group law. -/
def opLaw (M : RelativeGroupLaw k g) : RelativeGroupLaw k g where
  mul t x y := M.mul t y x
  one t := M.one t
  inv t x := M.inv t x
  mul_assoc t x y z := (M.mul_assoc t z y x).symm
  one_mul t x := M.mul_one t x
  mul_one t x := M.one_mul t x
  inv_mul_cancel t x := M.mul_inv_cancel t x
  mul_natural t t' ψ hψ x y := M.mul_natural t t' ψ hψ y x

@[scoped simp] theorem opLaw_mul (M : RelativeGroupLaw k g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g) :
    (opLaw M).mul t x y = M.mul t y x := rfl

variable (M : RelativeGroupLaw k g) (d : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g)

/-- The translation isomorphism determined by a rational group point. -/
def transIso : H ≅ H :=
  (RelativeGroupLaw.exists_iso_hom_comp_eq_and_comp_hom_eq_mul k M d).choose

theorem comp_transIso_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t g) :
    x.1 ≫ (transIso M d).hom =
      (M.mul t x (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) d)).1 :=
  (RelativeGroupLaw.exists_iso_hom_comp_eq_and_comp_hom_eq_mul k M d).choose_spec.2.2.1 t x

theorem schemeHomOverComp_id_eq :
    GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (CommRingCat.of k)))
      (Category.comp_id _) d = d :=
  Subtype.ext (Category.id_comp _)

theorem transIso_hom_pt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    (transIso M d).hom (pt g x) = pt g (M.mul (𝟙 _) x d) := by
  change (x.1 ≫ (transIso M d).hom) (fieldPoint k) = _
  rw [comp_transIso_hom, schemeHomOverComp_id_eq]

theorem transIso_hom_eq :
    (transIso M d).hom =
      (M.mul g (⟨𝟙 H, Category.id_comp g⟩ : SchemeHomOver g g)
        (GoodReductionJacobian.schemeHomOverComp g (Category.comp_id g) d)).1 := by
  rw [← comp_transIso_hom M d g ⟨𝟙 H, Category.id_comp g⟩]
  exact (Category.id_comp _).symm

variable {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  (φ : SchemeHomOver f g)
  (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
      M.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))

include hφ in
theorem hom_opLaw {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp ((opLaw L).mul t x y) φ =
      (opLaw M).mul t (NeronModelInfra.schemeHomOverComp x φ)
        (NeronModelInfra.schemeHomOverComp y φ) :=
  hφ t y x

include hφ in
theorem transIso_hom_comp (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    (transIso L a).hom ≫ φ.1 = φ.1 ≫ (transIso M (NeronModelInfra.schemeHomOverComp a φ)).hom := by
  have h1 : (transIso L a).hom ≫ φ.1 =
      (NeronModelInfra.schemeHomOverComp
        (L.mul f (⟨𝟙 G, Category.id_comp f⟩ : SchemeHomOver f f)
          (GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) a)) φ).1 := by
    rw [transIso_hom_eq]; rfl
  have h2 : NeronModelInfra.schemeHomOverComp (⟨𝟙 G, Category.id_comp f⟩ : SchemeHomOver f f) φ
      = φ := Subtype.ext (Category.id_comp _)
  have h3 : NeronModelInfra.schemeHomOverComp
      (GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) a) φ =
      GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f)
        (NeronModelInfra.schemeHomOverComp a φ) := Subtype.ext (Category.assoc _ _ _)
  rw [h1, hφ, comp_transIso_hom M _ f φ, h2, h3]

include hφ in
theorem apply_transIso_hom (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (z : G) :
    φ.1 ((transIso L a).hom z) = (transIso M (NeronModelInfra.schemeHomOverComp a φ)).hom (φ.1 z)
      := by
  rw [← Scheme.Hom.comp_apply, transIso_hom_comp M L φ hφ a, Scheme.Hom.comp_apply]

include hφ in
theorem image_transIso_hom_range (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    (transIso M (NeronModelInfra.schemeHomOverComp a φ)).hom '' Set.range φ.1 = Set.range φ.1 := by
  apply subset_antisymm
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨(transIso L a).hom z, apply_transIso_hom M L φ hφ a z⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨φ.1 ((transIso L a).inv z), ⟨_, rfl⟩, ?_⟩
    have hz : (transIso L a).hom ((transIso L a).inv z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    rw [← apply_transIso_hom M L φ hφ a, hz]

theorem pt_schemeHomOverComp (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pt g (NeronModelInfra.schemeHomOverComp a φ) = φ.1 (pt f a) := rfl

end Translations

section Homogeneity

variable {k : Type u} [Field k] [IsAlgClosed k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)

theorem iUnion_image_transIso_hom_eq_univ {V : Set G} (hV : IsOpen V) (hne : V.Nonempty) :
    ⋃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, (transIso L a).hom '' V = Set.univ := by
  by_contra hne'
  set W : Set G := ⋃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, (transIso L a).hom '' V
  have hW : IsOpen W :=
    isOpen_iUnion fun a => (Scheme.homeoOfIso (transIso L a)).isOpenMap V hV
  have hC : (Wᶜ).Nonempty := Set.nonempty_compl.mpr hne'
  obtain ⟨c₀, hc₀⟩ := exists_pt_mem_of_isLocallyClosed f hW.isClosed_compl.isLocallyClosed hC
  obtain ⟨v₀, hv₀⟩ := exists_pt_mem_of_isLocallyClosed f hV.isLocallyClosed hne
  apply hc₀
  let : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) := L.pointGroup (𝟙 _)
  refine Set.mem_iUnion.mpr ⟨v₀⁻¹ * c₀, pt f v₀, hv₀, ?_⟩
  rw [transIso_hom_pt]
  change pt f (v₀ * (v₀⁻¹ * c₀)) = pt f c₀
  rw [mul_inv_cancel_left]

end Homogeneity

section Main

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f] [QuasiCompact f]
  {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g] [QuasiCompact g]

theorem isClosed_range (L : RelativeGroupLaw k f) (M : RelativeGroupLaw k g)
    (φ : SchemeHomOver f g)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        M.mul t (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) :
    IsClosed (Set.range φ.1) := by
  classical
  have : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian G := ⟨⟩
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace H := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian H := ⟨⟩
  have : LocallyOfFiniteType φ.1 := by
    have : LocallyOfFiniteType (φ.1 ≫ g) := by rw [φ.2]; infer_instance
    exact locallyOfFiniteType_of_comp φ.1 g
  set S : Set H := Set.range φ.1 with hS
  set Z : Set H := closure S with hZ
  let cφ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g :=
    fun a => NeronModelInfra.schemeHomOverComp a φ
  have hSc : IsConstructible S := by
    have := φ.1.isConstructible_image IsConstructible.univ
    rwa [Set.image_univ] at this
  obtain ⟨U, hUo, hUS, hZU⟩ :
      ∃ U : Set H, IsOpen U ∧ U ∩ Z ⊆ S ∧ Z ⊆ closure (U ∩ Z) := by
    have : Nonempty H.affineOpens := ⟨⟨⊥, isAffineOpen_bot H⟩⟩
    refine exists_isOpen_inter_closure_subset_of_isConstructible
      (fun V : H.affineOpens => ((V : H.Opens) : Set H)) ?_ (fun V => V.2.isCompact) hSc
    have hb := H.isBasis_affineOpens
    rw [Opens.IsBasis, Set.image_eq_range] at hb
    convert hb using 2
  have hrS : ∀ a, (transIso M (cφ a)).hom '' S = S := image_transIso_hom_range M L φ hφ
  have hrZ : ∀ a, (transIso M (cφ a)).hom '' Z = Z := fun a => by
    change (Scheme.homeoOfIso (transIso M (cφ a))) '' closure S = closure S
    rw [Homeomorph.image_closure]
    exact congrArg closure (hrS a)
  let O : Set H := ⋃ a, (transIso M (cφ a)).hom '' U
  have hO : IsOpen O :=
    isOpen_iUnion fun a => (Scheme.homeoOfIso (transIso M (cφ a))).isOpenMap U hUo
  have hSO : S = O ∩ Z := by
    apply subset_antisymm
    · rintro _ ⟨x', rfl⟩
      refine ⟨?_, subset_closure ⟨x', rfl⟩⟩
      have hZne : (U ∩ Z).Nonempty := by
        by_contra h0
        rw [Set.not_nonempty_iff_eq_empty] at h0
        have := hZU (subset_closure ⟨x', rfl⟩)
        rw [h0, closure_empty] at this
        exact this
      obtain ⟨u, huU, huZ⟩ := hZne
      obtain ⟨x'', hx''⟩ := hUS ⟨huU, huZ⟩
      have hV : IsOpen (φ.1 ⁻¹' U) := hUo.preimage φ.1.continuous
      have hcov := iUnion_image_transIso_hom_eq_univ L hV ⟨x'', show φ.1 x'' ∈ U from hx'' ▸ huU⟩
      have hx' : x' ∈ ⋃ a, (transIso L a).hom '' (φ.1 ⁻¹' U) := by
        rw [hcov]; trivial
      obtain ⟨a, v, hv, rfl⟩ := Set.mem_iUnion.mp hx'
      refine Set.mem_iUnion.mpr ⟨a, φ.1 v, hv, ?_⟩
      rw [apply_transIso_hom M L φ hφ]
    · rintro p ⟨hpO, hpZ⟩
      obtain ⟨a, u', hu', rfl⟩ := Set.mem_iUnion.mp hpO
      have hu'Z : u' ∈ Z := by
        rw [← hrZ a] at hpZ
        obtain ⟨z, hz, hzu⟩ := hpZ
        rwa [← (Scheme.homeoOfIso (transIso M (cφ a))).injective hzu]
      rw [← hrS a]
      exact ⟨u', hUS ⟨hu', hu'Z⟩, rfl⟩
  suffices hZS : Z ⊆ S by
    have : S = Z := subset_antisymm subset_closure hZS
    rw [this]
    exact isClosed_closure
  by_contra hT
  obtain ⟨p₁, hp₁Z, hp₁S⟩ := Set.not_subset.mp hT
  have hTne : (Z \ S).Nonempty := ⟨p₁, hp₁Z, hp₁S⟩
  have hTc : IsClosed (Z \ S) := by
    have : Z \ S = Z \ O := by rw [hSO, Set.sdiff_inter_self_eq_sdiff]
    rw [this]
    exact isClosed_closure.sdiff hO
  obtain ⟨t₀, ht₀⟩ := exists_pt_mem_of_isLocallyClosed g hTc.isLocallyClosed hTne
  have hlS : ∀ a, (transIso (opLaw M) (cφ a)).hom '' S = S :=
    image_transIso_hom_range (opLaw M) (opLaw L) φ (fun t x y => hom_opLaw M L φ hφ t x y)
  have hlZ : ∀ a, (transIso (opLaw M) (cφ a)).hom '' Z = Z := fun a => by
    change (Scheme.homeoOfIso (transIso (opLaw M) (cφ a))) '' closure S = closure S
    rw [Homeomorph.image_closure]
    exact congrArg closure (hlS a)
  have hlT : ∀ a, (transIso (opLaw M) (cφ a)).hom '' (Z \ S) = Z \ S := fun a => by
    change (Scheme.homeoOfIso (transIso (opLaw M) (cφ a))) '' (Z \ S) = Z \ S
    rw [Set.image_sdiff (Scheme.homeoOfIso _).injective]
    exact congrArg₂ (· \ ·) (hlZ a) (hlS a)
  set r : H ≅ H := transIso M t₀ with hr
  have hkey : ∀ a, r.hom (pt g (cφ a)) ∈ Z \ S := fun a => by
    have h1 : r.hom (pt g (cφ a)) = (transIso (opLaw M) (cφ a)).hom (pt g t₀) := by
      rw [transIso_hom_pt, transIso_hom_pt]; rfl
    rw [h1, ← hlT a]
    exact ⟨_, ht₀, rfl⟩
  have hK : S ⊆ closure (Set.range fun a => pt g (cφ a)) := by
    rintro _ ⟨x', rfl⟩
    have hx' : x' ∈ closure (Set.range (pt f)) := by
      rw [(dense_range_pt f).closure_eq]; trivial
    have := image_closure_subset_closure_image φ.1.continuous ⟨x', hx', rfl⟩
    refine closure_mono ?_ this
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  have hrS' : r.hom '' S ⊆ Z \ S := by
    refine (Set.image_mono hK).trans ?_
    refine (image_closure_subset_closure_image r.hom.continuous).trans ?_
    refine closure_minimal ?_ hTc
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hkey a
  have hrZ' : r.hom '' Z ⊆ Z := by
    change r.hom '' closure S ⊆ closure S
    refine (image_closure_subset_closure_image r.hom.continuous).trans ?_
    exact closure_minimal (hrS'.trans Set.sdiff_subset) isClosed_closure
  have hrZeq : r.hom '' Z = Z :=
    image_eq_of_image_subset (Scheme.homeoOfIso r) isClosed_closure hrZ'
  have hrSeq : r.hom '' S = r.hom '' O ∩ Z := by
    conv_lhs => rw [hSO]
    change (Scheme.homeoOfIso r) '' (O ∩ Z) = (Scheme.homeoOfIso r) '' O ∩ Z
    rw [Set.image_inter (Scheme.homeoOfIso r).injective]
    exact congrArg _ hrZeq
  have hne1 : (closure S ∩ r.hom '' O).Nonempty := by
    have hmem : r.hom (φ.1 (pt f (L.one _))) ∈ r.hom '' S := ⟨_, ⟨_, rfl⟩, rfl⟩
    rw [hrSeq] at hmem
    exact ⟨_, hmem.2, hmem.1⟩
  have hrO : IsOpen (r.hom '' O) := (Scheme.homeoOfIso r).isOpenMap O hO
  rw [closure_inter_open_nonempty_iff hrO] at hne1
  obtain ⟨q, hqS, hqO⟩ := hne1
  have hq : q ∈ Z \ S := hrS' (hrSeq ▸ ⟨hqO, subset_closure hqS⟩)
  exact hq.2 hqS

end Main

end ClosedImage

end

end AbelianVarieties.NOSProofs.Subgroups

namespace GoodReductionJacobian.RelativeGroupLaw

theorem
    isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f] [QuasiCompact f]
    (L : RelativeGroupLaw k f)
    {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g] [QuasiCompact g]
    (M : RelativeGroupLaw k g)
    (φ : SchemeHomOver f g)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        M.mul t (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) :
    IsClosed (Set.range φ.1) :=
  AbelianVarieties.NOSProofs.Subgroups.ClosedImage.isClosed_range L M φ hφ

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_connectedSpace_lt_of_range_ne_univ.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.Subgroups

open CategoryTheory AlgebraicGeometry NeronModelInfra
open CategoryTheory.Limits hiding pair
open GoodReductionJacobian

end AbelianVarieties.NOSProofs.Subgroups

namespace GoodReductionJacobian.RelativeGroupLaw

theorem
    exists_isClosedImmersion_connectedSpace_lt_of_range_ne_univ
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f]
    {H : Scheme.{u}} (i : H ⟶ G) [IsClosedImmersion i] (LH : RelativeGroupLaw k (i ≫ f))
    (hi : (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))))
    (hne : Set.range i ≠ Set.univ)
    (hdim : 1 ≤ topologicalKrullDim
      ↥(connectedComponent ((LH.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint
        k)))) :
    ∃ (H' : Scheme.{u}) (i' : H' ⟶ G) (LH' : RelativeGroupLaw k (i' ≫ f)) (h : ℕ),
      IsClosedImmersion i' ∧ ConnectedSpace H' ∧ SmoothOfRelativeDimension h (i' ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i' ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH'.mul t x y) (⟨i', rfl⟩ : SchemeHomOver (i' ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i', rfl⟩ : SchemeHomOver (i' ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i', rfl⟩ : SchemeHomOver (i' ≫ f) f))) ∧
      1 ≤ h ∧ h < g := by
  classical
  have : PerfectField k := inferInstance
  have hsmf : Smooth f := SmoothOfRelativeDimension.smooth g f
  have : LocallyOfFiniteType (i ≫ f) := inferInstance
  have : QuasiCompact (i ≫ f) := inferInstance
  obtain ⟨G₀, i₀, L₀, n, hci, hirr, hsm, -, -, hrange, hdimG₀, hhom, -, -⟩ :=
    exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
      k LH
  have hdim₀ : topologicalKrullDim ↥(Set.range i₀) = topologicalKrullDim G₀ :=
    (IsHomeomorph.topologicalKrullDim_eq _
      (i₀.isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph).symm
  have hdim₁ : topologicalKrullDim ↥(Set.range (i₀ ≫ i)) = topologicalKrullDim G₀ :=
    (IsHomeomorph.topologicalKrullDim_eq _ ((i₀ ≫
      i).isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph).symm
  refine ⟨G₀, i₀ ≫ i, L₀, n, inferInstance, inferInstance, hsm, ?_, ?_, ?_⟩
  · intro T t x y
    change SchemeHomOver t (i₀ ≫ i ≫ f) at x y
    have e : ∀ z : SchemeHomOver t (i₀ ≫ i ≫ f),
        NeronModelInfra.schemeHomOverComp z (⟨i₀ ≫ i, rfl⟩ : SchemeHomOver (i₀ ≫ i ≫ f) f) =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z (⟨i₀, rfl⟩ :
            SchemeHomOver (i₀ ≫ i ≫ f) (i ≫ f)))
            (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) :=
      fun z => Subtype.ext (Category.assoc _ _ _).symm
    change NeronModelInfra.schemeHomOverComp (L₀.mul t x y) (⟨i₀ ≫ i, rfl⟩ : SchemeHomOver (i₀ ≫ i
      ≫ f) f) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i₀ ≫ i, rfl⟩ : SchemeHomOver (i₀ ≫ i ≫ f) f))
        (NeronModelInfra.schemeHomOverComp y (⟨i₀ ≫ i, rfl⟩ : SchemeHomOver (i₀ ≫ i ≫ f) f))
    rw [e, e, e, hhom, hi]
  · rw [← hrange, hdim₀, hdimG₀] at hdim
    exact_mod_cast hdim
  · have : Nonempty G := ⟨(L.one (𝟙 _)).1 (fieldPoint k)⟩
    have : IsIntegral G := AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace f
    have hY : IsClosed (Set.range (i₀ ≫ i)) := (i₀ ≫ i).isClosedEmbedding.isClosed_range
    have hYne : Set.range (i₀ ≫ i) ≠ Set.univ := by
      intro h
      apply hne
      apply Set.eq_univ_of_univ_subset
      rw [← h]
      rintro _ ⟨z, rfl⟩
      exact ⟨i₀ z, (Scheme.Hom.comp_apply _ _ _).symm⟩
    have h1 := IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne
      (IrreducibleSpace.isIrreducible_univ G) hY (Set.subset_univ _) hYne
    have h2 : topologicalKrullDim ↥(Set.univ : Set G) ≤ g :=
      (topologicalKrullDim_subspace_le G _).trans
        (AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le f g)
    rw [hdim₁, hdimG₀] at h1
    have h3 : ((n : ℕ∞) : WithBot ℕ∞) + 1 ≤ ((g : ℕ∞) : WithBot ℕ∞) := h1.trans h2
    have h4 : (n : ℕ∞) + 1 ≤ (g : ℕ∞) := by
      rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe] at h3
      exact h3
    have h5 : n + 1 ≤ g := by exact_mod_cast h4
    omega

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.Subgroups

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Limits hiding pair
open NeronModelInfra (SchemeHomOver)

namespace Isotropy

open GoodReductionJacobian.PartialAction

open
  AbelianVarieties.NOSProofs.PartialActionLaws.GoodReductionJacobian.PartialAction.ActionLaws
  (comp_comp comp_congr pair_comp defined_comp liftDom_eq liftDom_comp act_comp act_congr
    comp_mul const const_coe comp_const const_id range_kPoint kLift kLift_ι kLift_ι_assoc
    ltrans kpt_ltrans)
open
  AbelianVarieties.NOSProofs.PartialActionTransport.GoodReductionJacobian.PartialAction.OpTransport
  (geometricallyIrreducible)
open
  AbelianVarieties.NOSProofs.ClosedSubgroups.GoodReductionJacobian.RelativeGroupLaw.ClosedSubmonoid
  (exists_clpt_eq isClosed_clpt)

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

section Structure

variable (L : RelativeGroupLaw k f)

/-- Right translation by a rational group point. -/
def rtrans (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ⟶ G :=
  (L.mul f ⟨𝟙 G, Category.id_comp f⟩ (const f g)).1

theorem kpt_rtrans (g x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x.1 ≫ rtrans L g = (L.mul (𝟙 _) x g).1 := by
  have h : schemeHomOverComp x.1 x.2 (L.mul f ⟨𝟙 G, Category.id_comp f⟩ (const f g)) =
      L.mul (𝟙 _) x g := by
    rw [comp_mul, comp_const, const_id]
    congr 1
  exact congrArg Subtype.val h

end Structure

section Isotropy

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)
  (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)

/-- The identity morphism of the group as a point over the base. -/
def idG (f : G ⟶ Spec (CommRingCat.of k)) : SchemeHomOver f f := ⟨𝟙 G, Category.id_comp f⟩

/-- Pair the varying group point with the fixed point of the action space. -/
def sP : G ⟶ pullback f p := pair (idG f) (const f P₀)

theorem pair_kpt (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pair γ P₀ = γ.1 ≫ sP P₀ := by
  rw [sP, ← pair_comp γ.1 γ.2, comp_const, const_id]
  congr 1

/-- The open group locus where the fixed point can be acted on. -/
def Ω : G.Opens := sP P₀ ⁻¹ᵁ a.dom

theorem defined_iff_mem (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    a.Defined γ P₀ ↔ γ.1 (fieldPoint k) ∈ Ω a P₀ := by
  rw [Defined, pair_kpt, range_kPoint, Set.singleton_subset_iff, Scheme.Hom.comp_apply]
  rfl

/-- The tautological group point on the action domain of the fixed point. -/
def γΩ : SchemeHomOver ((Ω a P₀).ι ≫ f) f := ⟨(Ω a P₀).ι, rfl⟩

/-- The constant point on the action domain of the fixed point. -/
def PΩ : SchemeHomOver ((Ω a P₀).ι ≫ f) p := const _ P₀

theorem pair_Ω : pair (γΩ a P₀) (PΩ a P₀) = (Ω a P₀).ι ≫ sP P₀ := by
  rw [sP, PΩ, ← pair_comp (Ω a P₀).ι rfl, comp_const]
  rfl

theorem defined_Ω : a.Defined (γΩ a P₀) (PΩ a P₀) := by
  rintro _ ⟨ω, rfl⟩
  rw [pair_Ω, Scheme.Hom.comp_apply]
  exact ω.2

/-- The orbit morphism of the fixed point on its action domain. -/
def orb : ((Ω a P₀ : G.Opens) : Scheme.{u}) ⟶ P := (a.act (γΩ a P₀) (PΩ a P₀) (defined_Ω a P₀)).1

theorem orb_p : orb a P₀ ≫ p = (Ω a P₀).ι ≫ f := (a.act (γΩ a P₀) (PΩ a P₀) (defined_Ω a P₀)).2

/-- Lift a rational group point to the open locus where its action is defined. -/
def kΩ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    Spec (CommRingCat.of k) ⟶ (Ω a P₀ : G.Opens) :=
  kLift (Ω a P₀) γ.1 ((defined_iff_mem a P₀ γ).mp hγ)

@[reassoc (attr := simp)]
theorem kΩ_ι (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    kΩ a P₀ γ hγ ≫ (Ω a P₀).ι = γ.1 :=
  kLift_ι _ _ _

theorem kΩ_t (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    kΩ a P₀ γ hγ ≫ (Ω a P₀).ι ≫ f = 𝟙 _ := by
  rw [kΩ_ι_assoc]; exact γ.2

theorem act_kpt (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    a.act γ P₀ hγ = schemeHomOverComp (kΩ a P₀ γ hγ) (kΩ_t a P₀ γ hγ)
      (a.act (γΩ a P₀) (PΩ a P₀) (defined_Ω a P₀)) := by
  rw [← act_comp a _ _ _ _ _ (defined_comp a _ _ _ _ (defined_Ω a P₀))]
  refine act_congr a (Subtype.ext ?_) ?_ _ _
  · exact (kΩ_ι a P₀ γ hγ).symm
  · rw [PΩ, comp_const, const_id]

theorem act_kpt_coe (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    (a.act γ P₀ hγ).1 = kΩ a P₀ γ hγ ≫ orb a P₀ :=
  congrArg Subtype.val (act_kpt a P₀ γ hγ)

/-- The fibre of the orbit morphism over the fixed point. -/
def Hset : Set ↥((Ω a P₀ : G.Opens) : Scheme.{u}) := orb a P₀ ⁻¹' {P₀.1 (fieldPoint k)}

theorem isClosed_Hset [IsAlgClosed k] [LocallyOfFiniteType p] : IsClosed (Hset a P₀) :=
  (isClosed_clpt p P₀).preimage (orb a P₀).continuous

theorem mem_Hset_iff [IsAlgClosed k] [LocallyOfFiniteType p]
    (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    kΩ a P₀ γ hγ (fieldPoint k) ∈ Hset a P₀ ↔ a.act γ P₀ hγ = P₀ := by
  constructor
  · intro h
    apply Subtype.ext
    refine ext_of_apply_closedPoint_eq p (a.act γ P₀ hγ).2 P₀.2 ?_
    change (a.act γ P₀ hγ).1 (fieldPoint k) = P₀.1 (fieldPoint k)
    rw [act_kpt_coe, Scheme.Hom.comp_apply]
    exact h
  · intro h
    change orb a P₀ (kΩ a P₀ γ hγ _) = _
    rw [← Scheme.Hom.comp_apply, ← act_kpt_coe, h]

/-- The image in the group of the fixed-point fibre. -/
def Himg : Set ↥G := (Ω a P₀).ι '' Hset a P₀

theorem mem_Himg_iff [IsAlgClosed k] [LocallyOfFiniteType p]
    (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    γ.1 (fieldPoint k) ∈ Himg a P₀ ↔ ∃ hγ : a.Defined γ P₀, a.act γ P₀ hγ = P₀ := by
  constructor
  · rintro ⟨ω, hω, hωγ⟩
    have hγ : a.Defined γ P₀ := by
      rw [defined_iff_mem, ← hωγ]; exact ω.2
    refine ⟨hγ, (mem_Hset_iff a P₀ γ hγ).mp ?_⟩
    have : kΩ a P₀ γ hγ (fieldPoint k) = ω := by
      apply (Ω a P₀).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, kΩ_ι, hωγ]
    rw [this]; exact hω
  · rintro ⟨hγ, h⟩
    exact ⟨_, (mem_Hset_iff a P₀ γ hγ).mpr h, by rw [← Scheme.Hom.comp_apply, kΩ_ι]⟩

theorem one_mem_Himg [IsAlgClosed k] [LocallyOfFiniteType p] (hu : a.UnitActs L)
    (he : a.Defined (L.one (𝟙 _)) P₀) : (L.one (𝟙 _)).1 (fieldPoint k) ∈ Himg a P₀ :=
  (mem_Himg_iff a P₀ _).mpr ⟨he, hu _ _ he⟩

theorem mul_mem_Himg [IsAlgClosed k] [LocallyOfFiniteType p] (ha : a.Assoc L)
    (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hx : x.1 (fieldPoint k) ∈ Himg a P₀)
    (hy : y.1 (fieldPoint k) ∈ Himg a P₀) :
    (L.mul (𝟙 _) x y).1 (fieldPoint k) ∈ Himg a P₀ := by
  obtain ⟨hdx, ex⟩ := (mem_Himg_iff a P₀ x).mp hx
  obtain ⟨hdy, ey⟩ := (mem_Himg_iff a P₀ y).mp hy
  have hdx' : a.Defined x (a.act y P₀ hdy) := by rw [ey]; exact hdx
  obtain ⟨hd₃, e₃⟩ := ha _ x y P₀ hdy hdx'
  refine (mem_Himg_iff a P₀ _).mpr ⟨hd₃, ?_⟩
  rw [← e₃, act_congr a rfl ey hdx' hdx, ex]

theorem isLocallyClosed_Himg [IsAlgClosed k] [LocallyOfFiniteType p] :
    IsLocallyClosed (Himg a P₀) :=
  (isClosed_Hset a P₀).isLocallyClosed.image (Ω a P₀).ι.isOpenEmbedding.isInducing
    (by rw [Scheme.Opens.range_ι]; exact (Ω a P₀).2.isLocallyClosed)

/-- The closure of the fixed-point fibre in the group. -/
def Zset : Set ↥G := closure (Himg a P₀)

theorem Zset_eq [IsAlgClosed k] [LocallyOfFiniteType p] [LocallyOfFiniteType f] :
    Zset a P₀ = closure (Himg a P₀ ∩ closedPoints G) := by
  have : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
  exact (JacobsonSpace.closure_inter_closedPoints_eq_closure (isLocallyClosed_Himg a P₀)).symm

theorem ltrans_image_Zset [IsAlgClosed k] [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (ha : a.Assoc L) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hx : x.1 (fieldPoint k) ∈ Himg a P₀) :
    ltrans L x '' Zset a P₀ ⊆ Zset a P₀ := by
  rw [Zset_eq]
  refine (image_closure_subset_closure_image (ltrans L x).continuous).trans (closure_mono ?_)
  rintro _ ⟨s, ⟨hs, hsc⟩, rfl⟩
  obtain ⟨y, hpoint⟩ := exists_clpt_eq f hsc
  change y.1 (fieldPoint k) = s at hpoint
  subst s
  refine ⟨?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, kpt_ltrans]
    exact mul_mem_Himg L a P₀ ha x y hx hs
  · rw [← Scheme.Hom.comp_apply, kpt_ltrans]
    exact isClosed_clpt f _

theorem rtrans_image_Zset [IsAlgClosed k] [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (ha : a.Assoc L) (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hy : y.1 (fieldPoint k) ∈ Himg a P₀) :
    rtrans L y '' Zset a P₀ ⊆ Zset a P₀ := by
  rw [Zset_eq]
  refine (image_closure_subset_closure_image (rtrans L y).continuous).trans (closure_mono ?_)
  rintro _ ⟨s, ⟨hs, hsc⟩, rfl⟩
  obtain ⟨x, hpoint⟩ := exists_clpt_eq f hsc
  change x.1 (fieldPoint k) = s at hpoint
  subst s
  refine ⟨?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, kpt_rtrans]
    exact mul_mem_Himg L a P₀ ha x y hs hy
  · rw [← Scheme.Hom.comp_apply, kpt_rtrans]
    exact isClosed_clpt f _

theorem mul_mem_Zset [IsAlgClosed k] [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (ha : a.Assoc L) (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hx : x.1 (fieldPoint k) ∈ Zset a P₀)
    (hy : y.1 (fieldPoint k) ∈ Zset a P₀) :
    (L.mul (𝟙 _) x y).1 (fieldPoint k) ∈ Zset a P₀ := by
  have hsub : closure (Himg a P₀ ∩ closedPoints G) ⊆ ltrans L x ⁻¹' Zset a P₀ := by
    refine closure_minimal ?_ (isClosed_closure.preimage (ltrans L x).continuous)
    rintro s ⟨hs, hsc⟩
    obtain ⟨y', hpoint⟩ := exists_clpt_eq f hsc
    change y'.1 (fieldPoint k) = s at hpoint
    subst s
    change ltrans L x _ ∈ Zset a P₀
    rw [← Scheme.Hom.comp_apply, kpt_ltrans, ← kpt_rtrans, Scheme.Hom.comp_apply]
    exact rtrans_image_Zset L a P₀ ha y' hs ⟨_, hx, rfl⟩
  have := hsub (by rw [← Zset_eq]; exact hy)
  rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, kpt_ltrans] at this

theorem not_mem_Zset [IsAlgClosed k] [LocallyOfFiniteType p]
    (γ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ₀ : a.Defined γ₀ P₀)
    (hne : a.act γ₀ P₀ hγ₀ ≠ P₀) : γ₀.1 (fieldPoint k) ∉ Zset a P₀ := by
  intro h
  apply hne
  rw [← mem_Hset_iff, ← (isClosed_Hset a P₀).closure_eq,
    (Ω a P₀).ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image, Set.mem_preimage,
    ← Scheme.Hom.comp_apply, kΩ_ι]
  exact h

end Isotropy

section Assembly

theorem one_le_of_bounds {g : ℕ} {dZ dcl dW : WithBot ℕ∞} (h0 : 0 ≤ dZ)
    (hWg : dW + 1 ≤ (g : WithBot ℕ∞)) (hcl : dcl ≤ dW) (hdim : (g : WithBot ℕ∞) ≤ dZ + dcl) :
    1 ≤ dZ := by
  induction dZ using WithBot.recBotCoe with
  | bot => exact absurd (le_bot_iff.mp h0) WithBot.coe_ne_bot
  | coe n =>
    induction dcl using WithBot.recBotCoe with
    | bot => rw [WithBot.add_bot] at hdim; exact absurd (le_bot_iff.mp hdim) WithBot.coe_ne_bot
    | coe c =>
      induction dW using WithBot.recBotCoe with
      | bot => exact absurd (le_bot_iff.mp hcl) WithBot.coe_ne_bot
      | coe d =>
        have hWg' : d + 1 ≤ (g : ℕ∞) := by exact_mod_cast hWg
        have hcl' : c ≤ d := by exact_mod_cast hcl
        have hdim' : (g : ℕ∞) ≤ n + c := by exact_mod_cast hdim
        suffices h : (1 : ℕ∞) ≤ n by exact_mod_cast h
        induction n using ENat.recTopCoe with
        | top => exact le_top
        | coe n =>
          induction d using ENat.recTopCoe with
          | top =>
            rw [top_add] at hWg'
            exact (ENat.top_ne_natCast g (top_le_iff.mp hWg').symm).elim
          | coe d =>
            induction c using ENat.recTopCoe with
            | top => exact (ENat.top_ne_natCast d (top_le_iff.mp hcl').symm).elim
            | coe c =>
              have h1 : d + 1 ≤ g := by exact_mod_cast hWg'
              have h2 : c ≤ d := by exact_mod_cast hcl'
              have h3 : g ≤ n + c := by exact_mod_cast hdim'
              have : 1 ≤ n := by omega
              exact_mod_cast this

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)
  (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)

theorem range_orb_subset (W : Set ↥P) (hst : a.Stable W)
    (hP₀ : P₀.1 (fieldPoint k) ∈ W) : Set.range (orb a P₀) ⊆ W := by
  rintro _ ⟨ω, rfl⟩
  have h1 : a.liftDom (γΩ a P₀) (PΩ a P₀) (defined_Ω a P₀) ≫ a.dom.ι ≫ pullback.snd f p =
      ((Ω a P₀).ι ≫ f) ≫ P₀.1 := by
    rw [← Category.assoc, liftDom_ι, pair, pullback.lift_snd]; rfl
  have h2 : pullback.snd f p (a.dom.ι (a.liftDom (γΩ a P₀) (PΩ a P₀) (defined_Ω a P₀) ω)) ∈ W := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply]
    convert hP₀ using 2
    exact Subsingleton.elim _ _
  have := hst _ h2
  rwa [← Scheme.Hom.comp_apply] at this

theorem apply_one_eq {H : Scheme.{u}} (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f))
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    i ((LH.one (𝟙 _)).1 (fieldPoint k)) = (L.one (𝟙 _)).1 (fieldPoint k) := by
  have h := AbelianVarieties.NOSProofs.KernelTorsor.Torsor.map_one LH L
    (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) hhom (𝟙 _)
  exact congrArg (fun z : SchemeHomOver (𝟙 _) f => z.1 (fieldPoint k)) h

theorem main (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsSeparated p] [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (W : Set ↥P) (hW : IsClosed W) (hWg : topologicalKrullDim ↥W + 1 ≤ (g : WithBot ℕ∞))
    (hst : a.Stable W) (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hP₀ : P₀.1 (fieldPoint k) ∈ W) (he : a.Defined (L.one (𝟙 _)) P₀)
    (γ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ₀ : a.Defined γ₀ P₀)
    (hne : a.act γ₀ P₀ hγ₀ ≠ P₀) :
    ∃ (H : Scheme.{u}) (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      Set.range i ≠ Set.univ ∧
      1 ≤ topologicalKrullDim
        ↥(connectedComponent ((LH.one (𝟙 (Spec (CommRingCat.of k)))).1 (fieldPoint k))) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  obtain ⟨H, i, LH, hci, -, hrange, hhom⟩ :=
    RelativeGroupLaw.exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem k f L
      (Zset a P₀) isClosed_closure (subset_closure (one_mem_Himg L a P₀ hu he))
      (fun x y hx hy => mul_mem_Zset L a P₀ ha x y hx hy)
  refine ⟨H, i, LH, hci, hhom, ?_, ?_⟩
  · intro huniv
    have hmem : γ₀.1 (fieldPoint k) ∈ Set.range i := huniv ▸ Set.mem_univ _
    rw [hrange] at hmem
    exact not_mem_Zset a P₀ γ₀ hγ₀ hne hmem
  · have : GeometricallyIrreducible f := geometricallyIrreducible L
    have : IrreducibleSpace G := GeometricallyIrreducible.irreducibleSpace_of_subsingleton f
    have heΩ : (L.one (𝟙 _)).1 (fieldPoint k) ∈ Ω a P₀ := (defined_iff_mem a P₀ _).mp he
    have : Nonempty ((Ω a P₀ : G.Opens) : Scheme.{u}) := ⟨⟨_, heΩ⟩⟩
    have : IrreducibleSpace ((Ω a P₀ : G.Opens) : Scheme.{u}) :=
      (Ω a P₀).ι.isOpenEmbedding.irreducibleSpace
    have horb : orb a P₀ (kΩ a P₀ (L.one _) he (fieldPoint k)) =
        P₀.1 (fieldPoint k) := (mem_Hset_iff a P₀ _ he).mpr (hu _ _ he)
    obtain ⟨Z₁, heZ₁, hZ₁sub, hZ₁irr, -, hdim⟩ :=
      exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton
        ((Ω a P₀).ι ≫ f) p (orb a P₀) (orb_p a P₀) (isClosed_clpt p P₀) horb
    have : SmoothOfRelativeDimension g ((Ω a P₀).ι ≫ f) := by
      have : SmoothOfRelativeDimension (0 + g) ((Ω a P₀).ι ≫ f) := inferInstance
      rwa [zero_add] at this
    have hΩ : topologicalKrullDim ↥((Ω a P₀ : G.Opens) : Scheme.{u}) = g :=
      le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le ((Ω a P₀).ι ≫ f) g)
        (SmoothOfRelativeDimension.le_topologicalKrullDim ((Ω a P₀).ι ≫ f) g)
    have hcl : topologicalKrullDim ↥(closure (Set.range (orb a P₀))) ≤ topologicalKrullDim ↥W :=
      Topology.IsInducing.topologicalKrullDim_le
        (IsEmbedding.inclusion (closure_minimal (range_orb_subset a P₀ W hst hP₀) hW)).isInducing
    have h0 : 0 ≤ topologicalKrullDim ↥Z₁ := by
      have : IrreducibleSpace ↥Z₁ := Subtype.irreducibleSpace hZ₁irr
      have : Nonempty (TopologicalSpace.IrreducibleCloseds ↥Z₁) :=
        ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
      exact Order.krullDim_nonneg
    have h1 : 1 ≤ topologicalKrullDim ↥Z₁ := one_le_of_bounds h0 hWg hcl (hΩ ▸ hdim)
    let T₁ : Set ↥G := (Ω a P₀).ι '' Z₁
    have hT₁ : T₁ ⊆ Set.range i := by
      rw [hrange]
      rintro _ ⟨z, hz, rfl⟩
      exact subset_closure ⟨z, hZ₁sub hz, rfl⟩
    have hT₁irr : IsIrreducible T₁ := hZ₁irr.image _ (Ω a P₀).ι.continuous.continuousOn
    let φ₁ : ↥Z₁ → ↥T₁ := Set.codRestrict ((Ω a P₀).ι ∘ Subtype.val) T₁ (fun z => ⟨z.1, z.2, rfl⟩)
    have hφ₁ : IsInducing φ₁ :=
      ((Ω a P₀).ι.isOpenEmbedding.isInducing.comp IsInducing.subtypeVal).codRestrict _
    have hi := i.isClosedEmbedding
    let φ₂ : ↥T₁ → ↥H := fun t => hi.isEmbedding.toHomeomorph.symm ⟨t.1, hT₁ t.2⟩
    have hφ₂ : IsInducing φ₂ :=
      hi.isEmbedding.toHomeomorph.symm.isInducing.comp (IsEmbedding.inclusion hT₁).isInducing
    have hu₁ : φ₂ ⟨(L.one (𝟙 _)).1 (fieldPoint k),
        ⟨_, heZ₁, by rw [← Scheme.Hom.comp_apply, kΩ_ι]⟩⟩ =
        (LH.one (𝟙 _)).1 (fieldPoint k) := by
      change hi.isEmbedding.toHomeomorph.symm _ = _
      convert hi.isEmbedding.toHomeomorph_symm_apply ((LH.one (𝟙 _)).1 (fieldPoint k))
      exact (apply_one_eq L i LH hhom).symm
    have : ConnectedSpace ↥T₁ := isConnected_iff_connectedSpace.mp hT₁irr.isConnected
    have hsub : Set.range φ₂ ⊆
        connectedComponent ((LH.one (𝟙 _)).1 (fieldPoint k)) :=
      (isPreconnected_range hφ₂.continuous).subset_connectedComponent (hu₁ ▸ ⟨_, rfl⟩)
    have hψ : IsInducing (Set.codRestrict φ₂ _ (fun t => hsub ⟨t, rfl⟩)) := hφ₂.codRestrict _
    exact h1.trans ((Topology.IsInducing.topologicalKrullDim_le hφ₁).trans
      (Topology.IsInducing.topologicalKrullDim_le hψ))

end Assembly

end Isotropy

end

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

end AbelianVarieties.NOSProofs.Subgroups

namespace GoodReductionJacobian.PartialAction

theorem
    exists_isClosedImmersion_range_ne_univ_of_act_ne
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (W : Set ↥P) (hW : IsClosed W) (hWg : topologicalKrullDim ↥W + 1 ≤ (g : WithBot ℕ∞))
    (hst : a.Stable W)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hP₀ : P₀.1 (IsLocalRing.closedPoint k) ∈ W)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (γ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ₀ : a.Defined γ₀ P₀)
    (hne : a.act γ₀ P₀ hγ₀ ≠ P₀) :
    ∃ (H : Scheme.{u}) (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      Set.range i ≠ Set.univ ∧
      1 ≤ topologicalKrullDim
        ↥(connectedComponent ((LH.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint
          k))) :=
  AbelianVarieties.NOSProofs.Subgroups.Isotropy.main k f L g p a hu ha W hW hWg hst P₀ hP₀ he γ₀
    hγ₀ hne

end GoodReductionJacobian.PartialAction
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_of_mono_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.Subgroups

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.TopologicalSpace
open _root_.Topology

noncomputable section

namespace MonoClosedImmersion
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

open AbelianVarieties.NOSProofs.Subgroups.ClosedImage
  (pt exists_pt_eq_of_isClosed exists_pt_mem_of_isLocallyClosed transIso transIso_hom_comp
    iUnion_image_transIso_hom_eq_univ)

section Image

variable {k : Type u} [Field k]
  {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)} (M : RelativeGroupLaw k g)
  (φ : SchemeHomOver f g)

/-- The structure morphism of the scheme-theoretic image. -/
abbrev strC : φ.1.image ⟶ Spec (CommRingCat.of k) := φ.1.imageι ≫ g

/-- The image inclusion as a point over the base. -/
def ιPt : SchemeHomOver (strC φ) g := ⟨φ.1.imageι, rfl⟩

/-- The factorization to the image as a point over the base. -/
def ψPt : SchemeHomOver f (strC φ) :=
  ⟨φ.1.toImage, by rw [← Category.assoc, Scheme.Hom.toImage_imageι, φ.2]⟩

@[scoped simp] theorem ιPt_coe : (ιPt φ).1 = φ.1.imageι := rfl
@[scoped simp] theorem ψPt_coe : (ψPt φ).1 = φ.1.toImage := rfl

theorem comp_ψPt_ιPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (z : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z (ψPt φ)) (ιPt φ) =
      NeronModelInfra.schemeHomOverComp z φ :=
  Subtype.ext (by
    change (z.1 ≫ φ.1.toImage) ≫ φ.1.imageι = z.1 ≫ φ.1
    rw [Category.assoc, Scheme.Hom.toImage_imageι])

theorem injective_comp_ιPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    Function.Injective
      (fun z : SchemeHomOver t (strC φ) => NeronModelInfra.schemeHomOverComp z (ιPt φ)) := by
  intro a b h
  apply Subtype.ext
  exact (cancel_mono φ.1.imageι).mp (congrArg Subtype.val h)

variable
  (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
      M.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))

include hφ in
theorem exists_law_image [QuasiCompact φ.1] :
    ∃ LC : RelativeGroupLaw k (strC φ),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (strC φ)),
        NeronModelInfra.schemeHomOverComp (LC.mul t x y) (ιPt φ) =
          M.mul t (NeronModelInfra.schemeHomOverComp x (ιPt φ))
            (NeronModelInfra.schemeHomOverComp y (ιPt φ))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) (ψPt φ) =
          LC.mul t (NeronModelInfra.schemeHomOverComp x (ψPt φ))
            (NeronModelInfra.schemeHomOverComp y (ψPt φ))) := by
  obtain ⟨LC, hLC, -⟩ :=
    RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism_of_flat (R := k) M L φ hφ
  have hLC' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
      (x y : SchemeHomOver t (strC φ)),
      NeronModelInfra.schemeHomOverComp (LC.mul t x y) (ιPt φ) =
        M.mul t (NeronModelInfra.schemeHomOverComp x (ιPt φ))
          (NeronModelInfra.schemeHomOverComp y (ιPt φ)) := fun t x y => hLC t x y
  refine ⟨LC, fun t x y => hLC' t x y, fun t x y => ?_⟩
  apply injective_comp_ιPt φ t
  change NeronModelInfra.schemeHomOverComp
      (NeronModelInfra.schemeHomOverComp (L.mul t x y) (ψPt φ)) (ιPt φ) =
    NeronModelInfra.schemeHomOverComp (LC.mul t _ _) (ιPt φ)
  rw [hLC', comp_ψPt_ιPt, comp_ψPt_ιPt, comp_ψPt_ιPt, hφ]

theorem isReduced_image [IsReduced G] [QuasiCompact φ.1] : IsReduced φ.1.image := by
  have : IsSchemeTheoreticallyDominant φ.1.toImage :=
    AbelianVarieties.NOSProofs.Subgroups.FlatImage.isSchemeTheoreticallyDominant_toImage φ
  exact IsSchemeTheoreticallyDominant.isReduced φ.1.toImage

end Image

section Main

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f] [QuasiCompact f]
  {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g] [QuasiCompact g]

theorem isClosedImmersion [IsReduced G] (L : RelativeGroupLaw k f) (M : RelativeGroupLaw k g)
    (φ : SchemeHomOver f g) [Mono φ.1]
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        M.mul t (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) :
    IsClosedImmersion φ.1 := by
  classical
  have : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian G := ⟨⟩
  have : LocallyOfFiniteType φ.1 := by
    have : LocallyOfFiniteType (φ.1 ≫ g) := by rw [φ.2]; infer_instance
    exact locallyOfFiniteType_of_comp φ.1 g
  set ψ : G ⟶ φ.1.image := φ.1.toImage with hψdef
  have hψι : ψ ≫ φ.1.imageι = φ.1 := Scheme.Hom.toImage_imageι _
  have : Mono ψ := mono_of_mono_fac hψι
  have : LocallyOfFiniteType (strC φ) := inferInstance
  have : QuasiCompact (strC φ) := inferInstance
  have : IsLocallyNoetherian φ.1.image := LocallyOfFiniteType.isLocallyNoetherian (strC φ)
  have : IsReduced φ.1.image := isReduced_image φ
  have : LocallyOfFiniteType ψ := by
    have : LocallyOfFiniteType (ψ ≫ φ.1.imageι) := by rw [hψι]; infer_instance
    exact locallyOfFiniteType_of_comp ψ φ.1.imageι
  have hcl : IsClosed (Set.range φ.1) :=
    RelativeGroupLaw.isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed L M φ hφ
  have hsurj : Surjective ψ := by
    refine ⟨fun c => ?_⟩
    have hc : φ.1.imageι c ∈ Set.range φ.1 := by
      rw [← hcl.closure_eq, ← Scheme.Hom.support_ker, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨c, rfl⟩
    obtain ⟨x, hx⟩ := hc
    refine ⟨x, φ.1.imageι.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hψι, hx]
  have : Nonempty φ.1.image := ⟨ψ (pt f (L.one _))⟩
  obtain ⟨LC, -, hψhom⟩ := exists_law_image L M φ hφ
  obtain ⟨U₀, hU₀ne, hflat₀⟩ :=
    AlgebraicGeometry.exists_nonempty_flat_preimage_iota_comp_of_isReduced_of_locallyOfFiniteType ψ
  have : Flat ψ := by
    let V : G.Opens := ψ ⁻¹ᵁ U₀
    have hVne : (V : Set G).Nonempty := by
      obtain ⟨c, hc⟩ := hU₀ne
      obtain ⟨x, rfl⟩ := hsurj.1 c
      exact ⟨x, hc⟩
    let r : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f → (G ≅ G) := fun a => transIso L a
    have hcov := iUnion_image_transIso_hom_eq_univ L V.isOpen hVne
    have sourceLocal (P : MorphismProperty Scheme.{u})
        (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
        [HasRingHomProperty P Q] : IsZariskiLocalAtSource P := inferInstance
    have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
      sourceLocal _ RingHom.Flat
    apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat) (fun a => (r a).hom ''ᵁ V)
    · rw [eq_top_iff]
      rintro x -
      have hx : x ∈ ⋃ a, (transIso L a).hom '' (V : Set G) := by rw [hcov]; trivial
      obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hx
      exact Opens.mem_iSup.mpr ⟨a, hxa⟩
    · intro a
      have hint : (r a).hom ≫ ψ =
          ψ ≫ (transIso LC (NeronModelInfra.schemeHomOverComp a (ψPt φ))).hom :=
        transIso_hom_comp LC L (ψPt φ) hψhom a
      have e : ((r a).hom ''ᵁ V).ι ≫ ψ =
          ((r a).hom.isoImage V).inv ≫ (V.ι ≫ ψ) ≫
            (transIso LC (NeronModelInfra.schemeHomOverComp a (ψPt φ))).hom := by
        rw [Category.assoc, ← hint, ← Scheme.Hom.isoImage_inv_ι (r a).hom V]
        simp only [Category.assoc]
      rw [e]
      infer_instance
  have : IsIso ψ := Flat.isIso_of_surjective_of_mono ψ
  rw [← hψι]
  infer_instance

end Main

end MonoClosedImmersion

end

end AbelianVarieties.NOSProofs.Subgroups

namespace GoodReductionJacobian.RelativeGroupLaw

theorem
    isClosedImmersion_of_mono_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f] [QuasiCompact f]
    [IsReduced G] (L : RelativeGroupLaw k f)
    {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g] [QuasiCompact g]
    (M : RelativeGroupLaw k g)
    (φ : SchemeHomOver f g) [Mono φ.1]
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        M.mul t (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) :
    IsClosedImmersion φ.1 :=
  AbelianVarieties.NOSProofs.Subgroups.MonoClosedImmersion.isClosedImmersion L M φ hφ

end GoodReductionJacobian.RelativeGroupLaw
end
