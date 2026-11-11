/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.SplitIfs
public import Nyll.AbelianVarieties.Geometry.PartialActions.Basic
public import Nyll.AbelianVarieties.Geometry.PartialActions.Jets
public import Nyll.AbelianVarieties.Geometry.Subgroups
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver
public import Nyll.SchemeTheory.LocalGeometry.FormalNeighborhoods
public import Nyll.SchemeTheory.Morphisms.SectionRigidity
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced

/-! Affine group schemes from faithful representations and fixed partial actions. -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.AffineRepresentations

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.TopologicalSpace

universe u

noncomputable section

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw
namespace FaithfulAffine
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section Units

variable {X : Scheme.{u}}

theorem isUnit_of_basicOpen_eq_top {s : Γ(X, ⊤)} (h : X.basicOpen s = ⊤) : IsUnit s := by
  apply X.toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have : x ∈ X.basicOpen s := by rw [h]; trivial
  exact (X.mem_basicOpen_top s x).mp this

theorem basicOpen_eq_top_iff (s : Γ(X, ⊤)) : X.basicOpen s = ⊤ ↔ IsUnit s :=
  ⟨isUnit_of_basicOpen_eq_top, fun h => X.basicOpen_of_isUnit h⟩

theorem range_subset_basicOpen_iff {T : Scheme.{u}} (x : T ⟶ X) (s : Γ(X, ⊤)) :
    Set.range x ⊆ (X.basicOpen s : Set X) ↔ IsUnit (x.appTop s) := by
  rw [← basicOpen_eq_top_iff, ← Scheme.preimage_basicOpen_top]
  constructor
  · intro h
    rw [eq_top_iff]
    rintro p -
    exact h ⟨p, rfl⟩
  · intro h
    rintro _ ⟨p, rfl⟩
    have : p ∈ x ⁻¹ᵁ X.basicOpen s := by rw [h]; trivial
    exact this

end Units

section GeneralLinear

variable (d : ℕ) (R : Type u) [CommRing R]

/-- The affine space of square matrices over the base ring. -/
abbrev MatSp : Scheme.{u} := 𝔸(ULift.{u} (Fin d × Fin d); Spec (CommRingCat.of R))

/-- The universal matrix of coordinate sections. -/
def coordMatrix : Matrix (Fin d) (Fin d) Γ(MatSp d R, ⊤) :=
  Matrix.of fun i j => AffineSpace.coord (Spec (CommRingCat.of R)) (ULift.up (i, j))

/-- The determinant of the universal coordinate matrix. -/
def detSec : Γ(MatSp d R, ⊤) := (coordMatrix d R).det

/-- The open locus of invertible matrices. -/
abbrev GLOpen : (MatSp d R).Opens := (MatSp d R).basicOpen (detSec d R)

/-- The general linear scheme as a principal open of matrix space. -/
abbrev GLS : Scheme.{u} := GLOpen d R

/-- The structure morphism of the general linear scheme. -/
abbrev glStr : GLS d R ⟶ Spec (CommRingCat.of R) :=
  (GLOpen d R).ι ≫ (MatSp d R ↘ Spec (CommRingCat.of R))

variable {d R}

/-- The matrix of global sections determined by a map to matrix space. -/
def matOf {T : Scheme.{u}} (x : T ⟶ MatSp d R) : Matrix (Fin d) (Fin d) Γ(T, ⊤) :=
  Matrix.of fun i j => x.appTop (AffineSpace.coord (Spec (CommRingCat.of R)) (ULift.up (i, j)))

theorem matOf_apply {T : Scheme.{u}} (x : T ⟶ MatSp d R) (i j : Fin d) :
    matOf x i j = x.appTop (AffineSpace.coord (Spec (CommRingCat.of R)) (ULift.up (i, j))) := rfl

theorem matOf_eq_map {T : Scheme.{u}} (x : T ⟶ MatSp d R) :
    matOf x = x.appTop.hom.mapMatrix (coordMatrix d R) :=
  Matrix.ext fun _ _ => rfl

theorem appTop_detSec {T : Scheme.{u}} (x : T ⟶ MatSp d R) :
    x.appTop (detSec d R) = (matOf x).det := by
  rw [matOf_eq_map, detSec, ← RingHom.map_det]

theorem matOf_comp {T T' : Scheme.{u}} (ψ : T' ⟶ T) (x : T ⟶ MatSp d R) :
    matOf (ψ ≫ x) = ψ.appTop.hom.mapMatrix (matOf x) := by
  ext i j
  change (ψ ≫ x).appTop (AffineSpace.coord _ (ULift.up (i, j))) =
    ψ.appTop (x.appTop (AffineSpace.coord _ (ULift.up (i, j))))
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem matOf_homOfVector {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)) :
    matOf (AffineSpace.homOfVector t
      (fun ij : ULift.{u} (Fin d × Fin d) => m ij.down.1 ij.down.2)) = m := by
  ext i j
  rw [matOf_apply, AffineSpace.homOfVector_appTop_coord]

variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

theorem range_comp_ι_subset (x : SchemeHomOver t (glStr d R)) :
    Set.range (x.1 ≫ (GLOpen d R).ι) ⊆ (GLOpen d R : Set (MatSp d R)) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, ← Scheme.Opens.range_ι (GLOpen d R)]
  exact Set.range_comp_subset_range _ _

theorem isUnit_det_matOf (x : SchemeHomOver t (glStr d R)) :
    IsUnit (matOf (x.1 ≫ (GLOpen d R).ι)).det := by
  rw [← appTop_detSec, ← range_subset_basicOpen_iff]
  exact range_comp_ι_subset x

/-- The invertible matrix associated to a point of the general linear scheme. -/
def pts (x : SchemeHomOver t (glStr d R)) : GL (Fin d) Γ(T, ⊤) :=
  Matrix.GeneralLinearGroup.mk'' (matOf (x.1 ≫ (GLOpen d R).ι)) (isUnit_det_matOf x)

theorem coe_pts (x : SchemeHomOver t (glStr d R)) :
    ((pts x : GL (Fin d) Γ(T, ⊤)) : Matrix (Fin d) (Fin d) Γ(T, ⊤)) =
      matOf (x.1 ≫ (GLOpen d R).ι) :=
  rfl

/-- The map to matrix space defined by a matrix of sections. -/
def homOfMatrix (t : T ⟶ Spec (CommRingCat.of R)) (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)) :
    T ⟶ MatSp d R :=
  AffineSpace.homOfVector t (fun ij : ULift.{u} (Fin d × Fin d) => m ij.down.1 ij.down.2)

theorem homOfMatrix_over (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)) :
    homOfMatrix t m ≫ (MatSp d R ↘ Spec (CommRingCat.of R)) = t :=
  AffineSpace.homOfVector_over _ _

theorem matOf_homOfMatrix (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)) : matOf (homOfMatrix t m) = m :=
  matOf_homOfVector t m

theorem range_homOfMatrix_subset (m : GL (Fin d) Γ(T, ⊤)) :
    Set.range (homOfMatrix t (m : Matrix (Fin d) (Fin d) Γ(T, ⊤))) ⊆ Set.range (GLOpen d R).ι := by
  rw [Scheme.Opens.range_ι, range_subset_basicOpen_iff, appTop_detSec, matOf_homOfMatrix]
  exact Matrix.isUnits_det_units m

/-- The point of the general linear scheme defined by an invertible matrix. -/
def ofPts (t : T ⟶ Spec (CommRingCat.of R)) (m : GL (Fin d) Γ(T, ⊤)) :
    SchemeHomOver t (glStr d R) :=
  ⟨IsOpenImmersion.lift (GLOpen d R).ι (homOfMatrix t (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)))
      (range_homOfMatrix_subset m), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, homOfMatrix_over]⟩

theorem ofPts_comp_ι (m : GL (Fin d) Γ(T, ⊤)) :
    (ofPts t m).1 ≫ (GLOpen d R).ι = homOfMatrix t (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)) :=
  IsOpenImmersion.lift_fac _ _ _

theorem pts_ofPts (m : GL (Fin d) Γ(T, ⊤)) : pts (ofPts t m) = m := by
  apply Units.ext
  rw [coe_pts, ofPts_comp_ι, matOf_homOfMatrix]

theorem ofPts_pts (x : SchemeHomOver t (glStr d R)) : ofPts t (pts x) = x := by
  apply Subtype.ext
  rw [← cancel_mono (GLOpen d R).ι, ofPts_comp_ι, homOfMatrix]
  apply AffineSpace.hom_ext
  · rw [AffineSpace.homOfVector_over, Category.assoc]
    exact x.2.symm
  · intro ij
    rw [AffineSpace.homOfVector_appTop_coord]
    rfl

theorem pts_injective : Function.Injective (pts (d := d) (R := R) (t := t)) := by
  intro x y h
  rw [← ofPts_pts x, ← ofPts_pts y, h]

theorem pts_schemeHomOverComp {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t (glStr d R)) :
    pts (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      Matrix.GeneralLinearGroup.map ψ.appTop.hom (pts x) := by
  apply Units.ext
  change matOf ((ψ ≫ x.1) ≫ (GLOpen d R).ι) =
    ψ.appTop.hom.mapMatrix (matOf (x.1 ≫ (GLOpen d R).ι))
  rw [Category.assoc, matOf_comp]

theorem schemeHomOverComp_ofPts {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (m : GL (Fin d) Γ(T, ⊤)) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (ofPts t m) =
      ofPts t' (Matrix.GeneralLinearGroup.map ψ.appTop.hom m) := by
  apply pts_injective
  rw [pts_schemeHomOverComp, pts_ofPts, pts_ofPts]

variable (d R)

/-- The group law transported from invertible matrices through the point equivalence. -/
def glLaw : RelativeGroupLaw R (glStr d R) where
  mul t x y := ofPts t (pts x * pts y)
  one t := ofPts t 1
  inv t x := ofPts t (pts x)⁻¹
  mul_assoc t x y z := by simp only [pts_ofPts, _root_.mul_assoc]
  one_mul t x := by simp only [pts_ofPts, _root_.one_mul, ofPts_pts]
  mul_one t x := by simp only [pts_ofPts, _root_.mul_one, ofPts_pts]
  inv_mul_cancel t x := by simp only [pts_ofPts, _root_.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    rw [schemeHomOverComp_ofPts, map_mul, ← pts_schemeHomOverComp, ← pts_schemeHomOverComp]

variable {d R}

@[scoped simp] theorem pts_mul (x y : SchemeHomOver t (glStr d R)) :
    pts ((glLaw d R).mul t x y) = pts x * pts y := pts_ofPts _

end GeneralLinear

section Representation

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f) (d : ℕ)
  (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
    SchemeHomOver t f → GL (Fin d) Γ(T, ⊤))

/-- The matrix representing the identity-valued universal group point. -/
def univMatrix : GL (Fin d) Γ(G, ⊤) := ρ f ⟨𝟙 G, Category.id_comp f⟩

/-- The scheme morphism represented by the universal matrix. -/
def repPt : SchemeHomOver f (glStr d k) := ofPts f (univMatrix d ρ)

variable
  (hnat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f),
    ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x))

include hnat in
theorem rho_eq_map_univMatrix {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t f) :
    ρ t x = Matrix.GeneralLinearGroup.map x.1.appTop.hom (univMatrix d ρ) := by
  have h := hnat f t x.1 x.2 ⟨𝟙 G, Category.id_comp f⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 ⟨𝟙 G, Category.id_comp f⟩ = x :=
    Subtype.ext (Category.comp_id _)
  rw [h1] at h
  exact h

include hnat in
theorem pts_schemeHomOverComp_repPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t f) :
    pts (NeronModelInfra.schemeHomOverComp x (repPt d ρ)) = ρ t x := by
  have h : NeronModelInfra.schemeHomOverComp x (repPt d ρ) =
      GoodReductionJacobian.schemeHomOverComp x.1 x.2 (repPt d ρ) := rfl
  rw [h, repPt, schemeHomOverComp_ofPts, pts_ofPts, rho_eq_map_univMatrix d ρ hnat]

variable
  (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
    ρ t (L.mul t x y) = ρ t x * ρ t y)
  (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
    ρ t x = 1 → x = L.one t)

include hnat hmul in
theorem repPt_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.mul t x y) (repPt d ρ) =
      (glLaw d k).mul t (NeronModelInfra.schemeHomOverComp x (repPt d ρ))
        (NeronModelInfra.schemeHomOverComp y (repPt d ρ)) := by
  apply pts_injective
  rw [pts_mul, pts_schemeHomOverComp_repPt d ρ hnat, pts_schemeHomOverComp_repPt d ρ hnat,
    pts_schemeHomOverComp_repPt d ρ hnat, hmul]

include hmul hker in
theorem eq_of_rho_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) {x y : SchemeHomOver t f}
    (h : ρ t x = ρ t y) : x = y := by
  let : Group (SchemeHomOver t f) := L.pointGroup t
  have hone : ρ t (L.one t) = 1 := by
    have h1 : ρ t (L.one t) * ρ t (L.one t) = ρ t (L.one t) := by
      rw [← hmul, L.one_mul]
    exact mul_left_cancel (a := ρ t (L.one t)) (by rw [h1, _root_.mul_one])
  let φ : SchemeHomOver t f →* GL (Fin d) Γ(T, ⊤) :=
    { toFun := ρ t, map_one' := hone, map_mul' := hmul t }
  have hxy : φ (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, show φ x = φ y from h, _root_.mul_inv_cancel]
  have h2 : x * y⁻¹ = 1 := hker t _ hxy
  exact mul_inv_eq_one.mp h2

include hnat hmul hker in
theorem mono_repPt : Mono (repPt d ρ).1 := by
  refine ⟨fun {T} x y hxy => ?_⟩
  have ht : y ≫ f = x ≫ f := by
    rw [← (repPt d ρ).2, ← Category.assoc, ← hxy, Category.assoc]
  have h : ρ (x ≫ f) ⟨x, rfl⟩ = ρ (x ≫ f) ⟨y, ht⟩ := by
    rw [← pts_schemeHomOverComp_repPt d ρ hnat, ← pts_schemeHomOverComp_repPt d ρ hnat]
    congr 1
    exact Subtype.ext hxy
  exact congrArg Subtype.val (eq_of_rho_eq L d ρ hmul hker (x ≫ f) h)

end Representation

section BaseChange

variable {k : Type u} [Field k] {K : Type u} [Field K]
  (ι₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
  {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)} (M : RelativeGroupLaw k g)
  (φ : SchemeHomOver f g)
  (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
      M.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))

include hφ in
theorem hom_fibreRestrictAlong {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (baseChangeStr ι₀ f)) :
    NeronModelInfra.schemeHomOverComp ((L.baseChange ι₀).mul t x y) (fibreRestrictAlong ι₀ g f φ) =
      (M.baseChange ι₀).mul t
        (NeronModelInfra.schemeHomOverComp x (fibreRestrictAlong ι₀ g f φ))
        (NeronModelInfra.schemeHomOverComp y (fibreRestrictAlong ι₀ g f φ)) := by
  apply (baseChangePointEquiv ι₀ (f := g) t).injective
  change baseChangePointToBase ι₀ _ = baseChangePointToBase ι₀ _
  rw [baseChangePointToBase_comp_fibreRestrictAlong, baseChangePointToBase_mul, hφ,
    baseChangePointToBase_mul, baseChangePointToBase_comp_fibreRestrictAlong,
    baseChangePointToBase_comp_fibreRestrictAlong]

theorem mono_fibreRestrictAlong [Mono φ.1] : Mono (fibreRestrictAlong ι₀ g f φ).1 := by
  refine ⟨fun {Z} a b hab => ?_⟩
  apply pullback.hom_ext
  · rw [← cancel_mono φ.1, Category.assoc, Category.assoc,
      ← fibreRestrictAlong_coe_comp_fst ι₀ g f φ, reassoc_of% hab]
  · rw [← fibreRestrictAlong_coe_comp_snd ι₀ g f φ, reassoc_of% hab]

theorem isPullback_fibreRestrictAlong :
    IsPullback (fibreRestrictAlong ι₀ g f φ).1 (pullback.fst f ι₀) (pullback.fst g ι₀) φ.1 := by
  refine IsPullback.of_right ?_ (fibreRestrictAlong_coe_comp_fst ι₀ g f φ)
    (IsPullback.of_hasPullback g ι₀).flip
  rw [fibreRestrictAlong_coe_comp_snd, φ.2]
  exact (IsPullback.of_hasPullback f ι₀).flip

end BaseChange

section Main

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] [Smooth f]

theorem isAffine (L : RelativeGroupLaw k f) (d : ℕ)
    (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      SchemeHomOver t f → GL (Fin d) Γ(T, ⊤))
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      ρ t (L.mul t x y) = ρ t x * ρ t y)
    (hnat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
      (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f),
      ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
        Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ t x = 1 → x = L.one t) :
    IsAffine G := by
  let μ : SchemeHomOver f (glStr d k) := repPt d ρ
  have hμ := fun {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f) =>
    repPt_hom L d ρ hnat hmul t x y
  have : Mono μ.1 := mono_repPt L d ρ hnat hmul hker
  have : LocallyOfFiniteType μ.1 := by
    have : LocallyOfFiniteType (μ.1 ≫ glStr d k) := by rw [μ.2]; infer_instance
    exact locallyOfFiniteType_of_comp μ.1 (glStr d k)
  let K : Type u := AlgebraicClosure k
  let ι₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : Surjective ι₀ := ⟨fun s => ⟨(default : Spec (CommRingCat.of K)), Subsingleton.elim _ _⟩⟩
  let μ' := fibreRestrictAlong ι₀ (glStr d k) f μ
  have : Mono μ'.1 := mono_fibreRestrictAlong ι₀ μ
  have : IsReduced (pullback f ι₀) :=
    Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.snd f ι₀)
  have : IsClosedImmersion μ'.1 :=
    RelativeGroupLaw.isClosedImmersion_of_mono_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed
      (L.baseChange ι₀) ((glLaw d k).baseChange ι₀) μ'
      (hom_fibreRestrictAlong ι₀ L (glLaw d k) μ hμ)
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (pullback.fst (glStr d k) ι₀) := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed μ.1 :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (isPullback_fibreRestrictAlong ι₀ μ) hQ inferInstance
  have : IsProper μ.1 := {}
  have : IsClosedImmersion μ.1 :=
    (IsClosedImmersion.iff_isProper_and_mono μ.1).mpr ⟨inferInstance, inferInstance⟩
  exact isAffine_of_isAffineHom μ.1

end Main

end GoodReductionJacobian.RelativeGroupLaw.FaithfulAffine

end

end AbelianVarieties.NOSProofs.AffineRepresentations

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory AlgebraicGeometry NeronModelInfra
universe u

open AbelianVarieties.NOSProofs.AffineRepresentations.GoodReductionJacobian.RelativeGroupLaw in
theorem isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one
    {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [QuasiCompact f] [Smooth f] (L : RelativeGroupLaw k f) (d : ℕ)
    (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      SchemeHomOver t f → GL (Fin d) Γ(T, ⊤))
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      ρ t (L.mul t x y) = ρ t x * ρ t y)
    (hnat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
      (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f),
      ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
        Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ t x = 1 → x = L.one t) :
    IsAffine G :=
  FaithfulAffine.isAffine
    L d ρ hmul hnat hker

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_isAffine_of_forall_act_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.FixedPointAffineness

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open Topology

universe u

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace PartialAction
open _root_.GoodReductionJacobian.PartialAction
namespace FixedPointCriterion
open _root_.GoodReductionJacobian.PartialAction
open _root_.GoodReductionJacobian

section General

variable {k : Type u} [Field k]

theorem isNoetherian_of_locallyOfFiniteType {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [LocallyOfFiniteType f] : IsNoetherian G := by
  have : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

theorem tower_down {d : ℕ → ℕ} {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    (ρ : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      SchemeHomOver t f → GL (Fin (d n)) Γ(T, ⊤))
    (hmono : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ (n + 1) t x = 1 → ρ n t x = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
    (N : ℕ) (hN : ρ N t x = 1) : ∀ n ≤ N, ρ n t x = 1 := by
  induction N with
  | zero => intro n hn; obtain rfl : n = 0 := Nat.le_zero.mp hn; exact hN
  | succ N ih =>
    intro n hn
    rcases Nat.lt_or_eq_of_le hn with h | rfl
    · exact ih (hmono N t x hN) n (Nat.lt_succ_iff.mp h)
    · exact hN

theorem map_eq_one_iff {R S : Type u} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S)
    (c : GL (Fin n) R) :
    Matrix.GeneralLinearGroup.map φ c = 1 ↔
      ∀ i j : Fin n, φ (((c : Matrix (Fin n) (Fin n) R) - 1) i j) = 0 := by
  constructor
  · intro h i j
    have hij := congrArg (fun m : GL (Fin n) S => (m : Matrix (Fin n) (Fin n) S) i j) h
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at hij
    rw [Matrix.sub_apply, map_sub, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp only [map_one, map_zero, sub_self]
  · intro h
    apply Units.ext
    ext i j
    have hij := h i j
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at hij
    rw [Units.val_one, Matrix.GeneralLinearGroup.map_apply, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp only [map_one, map_zero]

end General

section Assembly

theorem isAffine
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L) (hc : a.Compatible L V ι hι)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (hfix : ∀ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hd : a.Defined γ P₀),
      a.act γ P₀ hd = P₀) :
    IsAffine G := by
  have hall : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
        a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀ :=
    fun t γ =>
      GoodReductionJacobian.PartialAction.exists_defined_act_eq_of_forall_act_eq
        k f L p a ha P₀ he hfix t γ
  obtain ⟨d, ρ, hmul, hnat, hmono, hfaith⟩ :=
    GoodReductionJacobian.PartialAction.exists_generalLinearGroup_jet_of_forall_defined_act_eq
      k f L p a hu ha P₀ hall
  have : IsNoetherian G := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨N, hN⟩ :=
    AlgebraicGeometry.exists_forall_generalLinearGroup_eq_one_of_forall_le_of_isNoetherian
      (G := G) d (fun n {T} (x : T ⟶ G) => ρ n (x ≫ f) ⟨x, rfl⟩)
      (fun n {T} {T'} ψ x => by
        have h := hnat n (x ≫ f) ((ψ ≫ x) ≫ f) ψ (Category.assoc ψ x f).symm ⟨x, rfl⟩
        exact h)
  have hallone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ N t x = 1 → ∀ n, ρ n t x = 1 := by
    intro T t x h n
    obtain ⟨x, rfl⟩ := x
    exact hN x (fun m hm => tower_down ρ hmono (x ≫ f) ⟨x, rfl⟩ N h m hm) n
  obtain ⟨u, hu_def⟩ : ∃ u : SchemeHomOver f f, u = ⟨𝟙 G, Category.id_comp f⟩ := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c : GL (Fin (d N)) Γ(G, ⊤), c = ρ N f u := ⟨_, rfl⟩
  obtain ⟨S, hS_def⟩ : ∃ S : Set Γ(G, ⊤), S =
      Set.range (fun ij : Fin (d N) × Fin (d N) =>
        (((c : Matrix (Fin (d N)) (Fin (d N)) Γ(G, ⊤)) - 1) ij.1 ij.2)) := ⟨_, rfl⟩
  have hρc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ N t x = Matrix.GeneralLinearGroup.map x.1.appTop.hom c := by
    intro T t x
    have h := hnat N f t x.1 x.2 u
    have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 u = x := by
      subst hu_def
      exact Subtype.ext (Category.comp_id x.1)
    rw [hx, ← hc_def] at h
    exact h
  have hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ N t x = 1 ↔ ∀ s ∈ S, x.1.appTop.hom s = 0 := by
    intro T t x
    rw [hρc, map_eq_one_iff, hS_def]
    constructor
    · rintro h s ⟨⟨i, j⟩, rfl⟩
      exact h i j
    · intro h i j
      exact h _ ⟨⟨i, j⟩, rfl⟩
  obtain ⟨e, he_def⟩ : ∃ e : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, e = L.one (𝟙 _) :=
    ⟨_, rfl⟩
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      (L.one t).1 = t ≫ e.1 := by
    intro T t
    have h := L.one_natural (𝟙 (Spec (CommRingCat.of k))) t t (Category.comp_id t)
    rw [he_def]
    exact (congrArg Subtype.val h).symm
  have hart : ∀ {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType t] (x : T ⟶ G), x ≫ f = t → (∀ s ∈ S, x.appTop.hom s = 0) →
      x = t ≫ e.1 := by
    intro T _ t _ x hx hs
    have h1 : ρ N t ⟨x, hx⟩ = 1 := (hker t ⟨x, hx⟩).mpr hs
    have hn : ∀ n, ρ n t ⟨x, hx⟩ = 1 := hallone t ⟨x, hx⟩ h1
    have hxe :=
      GoodReductionJacobian.PartialAction.eq_one_of_forall_act_jet_eq_of_subsingleton
        k f L p V ι hι a hc P₀ t ⟨x, hx⟩ (fun n jn hjn => hfaith n t ⟨x, hx⟩ jn hjn (hn n))
    rw [← hone t]
    exact congrArg Subtype.val hxe
  refine
    RelativeGroupLaw.isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one
      L (d N) (fun t x => ρ N t x) (fun t x y => hmul N t x y)
      (fun t t' ψ hψ x => hnat N t t' ψ hψ x) ?_
  intro T t x h1
  have hs : ∀ s ∈ S, x.1.appTop.hom s = 0 := (hker t x).mp h1
  have hx :=
    AlgebraicGeometry.eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton
      k f S e.1 (fun {T} _ t _ x hx hs => hart t x hx hs) t x.1 x.2 hs
  apply Subtype.ext
  rw [hx, hone t]

end Assembly

end GoodReductionJacobian.PartialAction.FixedPointCriterion

end AbelianVarieties.NOSProofs.FixedPointAffineness

namespace GoodReductionJacobian.PartialAction

open CategoryTheory AlgebraicGeometry NeronModelInfra
universe u

open AbelianVarieties.NOSProofs.FixedPointAffineness.GoodReductionJacobian.PartialAction in
theorem isAffine_of_forall_act_eq
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L) (hc : a.Compatible L V ι hι)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (hfix : ∀ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hd : a.Defined γ P₀),
      a.act γ P₀ hd = P₀) :
    IsAffine G :=
  FixedPointCriterion.isAffine k f L p V ι hι a hu ha hc P₀ he hfix

end GoodReductionJacobian.PartialAction
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_isAffine_of_forall_exists_defined_act_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.PartialAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem isAffine_of_forall_exists_defined_act_eq
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι hι) (hu : a.UnitActs L) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hfix : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
        a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) :
    IsAffine G := by
  have hP : GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (CommRingCat.of k)))
      (Category.comp_id (𝟙 (Spec (CommRingCat.of k)))) P₀ = P₀ :=
    Subtype.ext (Category.id_comp _)
  have key : ∀ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
      (X : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p), X = P₀ →
      (∃ hd : a.Defined γ X, a.act γ X hd = X) →
      a.Defined γ P₀ ∧ ∀ hd : a.Defined γ P₀, a.act γ P₀ hd = P₀ := by
    rintro γ X rfl ⟨hd', h'⟩
    exact ⟨hd', fun _ => h'⟩
  have hk : ∀ γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      a.Defined γ P₀ ∧ ∀ hd : a.Defined γ P₀, a.act γ P₀ hd = P₀ :=
    fun γ => key γ _ hP (hfix (𝟙 _) γ)
  exact GoodReductionJacobian.PartialAction.isAffine_of_forall_act_eq k f L p V ι hι a hu ha hc P₀
    (hk (L.one _)).1 (fun γ hd => (hk γ).2 hd)

end GoodReductionJacobian.PartialAction
end
