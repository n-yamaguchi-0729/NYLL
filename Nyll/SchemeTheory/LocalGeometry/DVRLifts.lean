/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sober
public import Mathlib.Tactic.Choose
public import Nyll.SchemeTheory.RingTheory.Ramification.UnramifiedDVR
public import Nyll.SchemeTheory.LocalGeometry.DVRStalks
public import Nyll.SchemeTheory.Etale.Neighborhoods
public import Nyll.SchemeTheory.LocalGeometry.OpenIrreducibleComponents
public import Nyll.SchemeTheory.Morphisms.SmoothSectionLifting
public import Nyll.SchemeTheory.LocalGeometry.SmoothDVRStalk
public import Nyll.SchemeTheory.LocalGeometry.SmoothNormalStalk
public import Nyll.SchemeTheory.RingTheory.Henselian.ModuleFinite

/-! # Affine neighborhoods and finite étale DVR lifts of smooth points -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace DVRNeighborhoods

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- A generic point of its fiber, characterized by specialization. -/
def FibreMax (x : X) : Prop := ∀ y : X, y ⤳ x → f.base y = f.base x → y = x

lemma eq_of_specializes_of_ne_closedPoint {p q : PrimeSpectrum R}
    (hq : q ≠ IsLocalRing.closedPoint R) (h : p ⤳ q) : p = q := by
  have hle : p.asIdeal ≤ q.asIdeal :=
    (PrimeSpectrum.asIdeal_le_asIdeal p q).mpr ((PrimeSpectrum.le_iff_specializes p q).mpr h)
  have hqbot : q.asIdeal = ⊥ := by
    by_contra hne
    apply hq
    have hmax : q.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot q.2 hne
    ext1
    exact IsLocalRing.eq_maximalIdeal hmax
  ext1
  apply le_antisymm
  · exact hqbot ▸ hle
  · rw [hqbot]; exact bot_le

lemma eq_of_specializes_of_fibreMax_of_ne {x : X} (hx : FibreMax f x)
    (hxs : f.base x ≠ IsLocalRing.closedPoint R) (y : X) (h : y ⤳ x) : y = x := by
  apply hx y h
  exact eq_of_specializes_of_ne_closedPoint hxs (h.map f.base.hom.continuous)

section Noetherian

variable [Smooth f] [IsSeparated f] [QuasiCompact f]
include f

omit [IsSeparated f] [QuasiCompact f] in
private lemma locallyNoetherian : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian f

omit [Smooth f] [IsSeparated f] in
lemma compactSpace : CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace f

omit [IsSeparated f] in
lemma isNoetherian : IsNoetherian X := by
  have : IsLocallyNoetherian X := locallyNoetherian f
  have : CompactSpace X := compactSpace f
  exact {}

omit [IsSeparated f] [QuasiCompact f] in
lemma isDomain_stalk (x : X) : IsDomain (X.presheaf.stalk x) :=
  (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
    R f x).1

omit [IsSeparated f] [QuasiCompact f] in
lemma isReduced : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x =>
    have : IsDomain (X.presheaf.stalk x) := isDomain_stalk f x
    inferInstance
  exact isReduced_of_isReduced_stalk X

omit [IsSeparated f] [QuasiCompact f] in
lemma isOpen_irreducibleComponent (x : X) :
    IsOpen (irreducibleComponent x) ∧
      ∀ Z ∈ irreducibleComponents X, x ∈ Z → Z = irreducibleComponent x := by
  have : IsLocallyNoetherian X := locallyNoetherian f
  exact AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk (isDomain_stalk f) x

omit [IsSeparated f] [QuasiCompact f] in
lemma isOpen_of_mem_irreducibleComponents {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    IsOpen Z := by
  obtain ⟨x, hx⟩ := hZ.1.nonempty
  rw [(isOpen_irreducibleComponent f x).2 Z hZ hx]
  exact (isOpen_irreducibleComponent f x).1

omit [IsSeparated f] [QuasiCompact f] in
lemma eq_of_mem_irreducibleComponents_of_mem {Z Z' : Set X} (hZ : Z ∈ irreducibleComponents X)
    (hZ' : Z' ∈ irreducibleComponents X) {x : X} (hx : x ∈ Z) (hx' : x ∈ Z') : Z = Z' := by
  rw [(isOpen_irreducibleComponent f x).2 Z hZ hx, (isOpen_irreducibleComponent f x).2 Z' hZ' hx']

omit [IsSeparated f] in
lemma finite_setOf_fibreMax_closed :
    {x : X | FibreMax f x ∧ f.base x = IsLocalRing.closedPoint R}.Finite := by
  classical
  have : IsNoetherian X := isNoetherian f
  let Xs : Closeds X := ⟨f.base ⁻¹' {IsLocalRing.closedPoint R},
    (IsLocalRing.isClosed_singleton_closedPoint R).preimage f.base.hom.continuous⟩
  obtain ⟨S, hSirr, hXs⟩ := NoetherianSpace.exists_finset_irreducible Xs
  have hXs' : (Xs : Set X) = ⋃ k ∈ S, (k : Set X) := by
    rw [hXs, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
    rfl
  let η : S → X := fun k => (hSirr k).genericPoint
  refine (Set.finite_range η).subset ?_
  rintro x ⟨hxmax, hxs⟩
  have hxXs : x ∈ (Xs : Set X) := hxs
  rw [hXs'] at hxXs
  obtain ⟨k, hkS, hxk⟩ := Set.mem_iUnion₂.mp hxXs
  have hk : IsGenericPoint (η ⟨k, hkS⟩) (k : Set X) :=
    (hSirr ⟨k, hkS⟩).isGenericPoint_genericPoint k.2
  refine ⟨⟨k, hkS⟩, ?_⟩
  have h1 : η ⟨k, hkS⟩ ⤳ x := hk.specializes hxk
  have h2 : f.base (η ⟨k, hkS⟩) = IsLocalRing.closedPoint R := by
    have hηk : η ⟨k, hkS⟩ ∈ (k : Set X) := hk.mem
    have : η ⟨k, hkS⟩ ∈ (Xs : Set X) := by
      rw [hXs']
      exact Set.mem_iUnion₂.mpr ⟨k, hkS, hηk⟩
    exact this
  exact hxmax _ h1 (h2.trans hxs.symm)

lemma component_case {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ (U : Set X) ⊆ Z ∧ ∀ x ∈ Z, FibreMax f x → x ∈ U := by
  classical
  have : IsNoetherian X := isNoetherian f
  have : IsReduced X := isReduced f
  let V : X.Opens := ⟨Z, isOpen_of_mem_irreducibleComponents f hZ⟩
  have hirr : IrreducibleSpace V := (isIrreducible_iff_irreducibleSpace (s := Z)).mp hZ.1
  have : IsIntegral V := isIntegral_of_irreducibleSpace_of_isReduced _
  let g : (V : Scheme.{u}) ⟶ Spec (CommRingCat.of R) := V.ι ≫ f
  have : LocallyOfFiniteType g := inferInstance
  have : IsSeparated g := inferInstance
  have hTfin := finite_setOf_fibreMax_closed f
  let T : Set V :=
    Subtype.val ⁻¹' {x : X | FibreMax f x ∧ f.base x = IsLocalRing.closedPoint R}
  have hT : T.Finite := hTfin.preimage Subtype.val_injective.injOn
  let S : Finset V := hT.toFinset
  have hS : ∀ v ∈ S, IsDiscreteValuationRing ((V : Scheme.{u}).presheaf.stalk v) := by
    intro v hv
    obtain ⟨hvmax, hvs⟩ := hT.mem_toFinset.mp hv
    obtain ⟨hdom, hdvr⟩ :=
      AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R f v.1 hvs
        (fun y hy hys => hvmax y hy (hys.trans hvs.symm))
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (V.stalkIso
      v).symm.commRingCatIsoToRingEquiv
  obtain ⟨U', hU'aff, hU'S⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isDiscreteValuationRing_stalk g S hS
  obtain ⟨U'', hU''aff, hU''S, hU''ne⟩ : ∃ U'' : (V : Scheme.{u}).Opens, IsAffineOpen U'' ∧
      (∀ v ∈ S, v ∈ U'') ∧ (U'' : Set V).Nonempty := by
    by_cases hne : (U' : Set V).Nonempty
    · exact ⟨U', hU'aff, hU'S, hne⟩
    · let v0 : V := genericPoint (V : Scheme.{u})
      obtain ⟨W, hW, hvW, -⟩ := exists_isAffineOpen_mem_and_subset
        (show v0 ∈ (⊤ : (V : Scheme.{u}).Opens) from trivial)
      refine ⟨W, hW, ?_, ⟨v0, hvW⟩⟩
      intro v hv
      exact absurd ⟨v, hU'S v hv⟩ hne
  refine ⟨V.ι ''ᵁ U'', hU''aff.image_of_isOpenImmersion V.ι, ?_, ?_⟩
  · intro y hy
    exact V.ι_image_le U'' hy
  · intro x hxZ hxmax
    let v : V := ⟨x, hxZ⟩
    suffices hv : v ∈ U'' by
      change x ∈ (V.ι ''ᵁ U'' : Set X)
      rw [Scheme.Hom.coe_image]
      exact ⟨v, hv, rfl⟩
    by_cases hxs : f.base x = IsLocalRing.closedPoint R
    · exact hU''S v (hT.mem_toFinset.mpr ⟨hxmax, hxs⟩)
    · have hgen : genericPoint (V : Scheme.{u}) = v := by
        have h1 : (genericPoint (V : Scheme.{u})) ⤳ v :=
          genericPoint_specializes (α := (V : Scheme.{u})) v
        have h2 : (genericPoint (V : Scheme.{u})).1 ⤳ x := h1.map continuous_subtype_val
        exact Subtype.ext (eq_of_specializes_of_fibreMax_of_ne f hxmax hxs _ h2)
      rw [← hgen]
      refine ((genericPoint_spec (V : Scheme.{u})).mem_open_set_iff U''.isOpen).mpr ?_
      simpa only [Set.univ_inter] using hU''ne

theorem main : ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x : X, FibreMax f x → x ∈ U := by
  classical
  have : IsNoetherian X := isNoetherian f
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have key : ∀ Z ∈ irreducibleComponents X, ∃ U : X.Opens, IsAffineOpen U ∧ (U : Set X) ⊆ Z ∧
      ∀ x ∈ Z, FibreMax f x → x ∈ U := fun Z hZ => component_case f hZ
  choose! UZ hUZaff hUZle hUZmem using key
  refine ⟨⨆ Z ∈ irreducibleComponents X, UZ Z, ?_, ?_⟩
  · apply IsAffineOpen.biSup_of_disjoint hfin hUZaff
    intro Z hZ Z' hZ' hne
    change Disjoint (UZ Z) (UZ Z')
    rw [← Opens.coe_disjoint, Set.disjoint_left]
    intro y hy hy'
    exact hne (eq_of_mem_irreducibleComponents_of_mem f hZ hZ' (hUZle Z hZ hy) (hUZle Z' hZ' hy'))
  · intro x hx
    have hZ := irreducibleComponent_mem_irreducibleComponents x
    have := hUZmem _ hZ x mem_irreducibleComponent hx
    exact Opens.mem_iSup.mpr ⟨_, Opens.mem_iSup.mpr ⟨hZ, this⟩⟩

end Noetherian

end DVRNeighborhoods

theorem exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] [IsSeparated f] [QuasiCompact f] :
    ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ x : X, (∀ y : X, y ⤳ x → f.base y = f.base x → y = x) → x ∈ U :=
  DVRNeighborhoods.main f

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem Smooth.exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (k' : Type u) [Field k'] [Algebra (IsLocalRing.ResidueField R) k']
    [FiniteDimensional (IsLocalRing.ResidueField R) k'] [Algebra.IsSeparable
      (IsLocalRing.ResidueField R) k']
    (x₀ : Spec (CommRingCat.of k') ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom
      ((algebraMap (IsLocalRing.ResidueField R) k').comp (IsLocalRing.residue R)))) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ :
      Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : HenselianLocalRing R')
      (φ : k' ≃ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R')
      (s : Spec (CommRingCat.of R') ⟶ X),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' ∧
      s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ∧
      Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) ≫ s =
        Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) ≫ x₀ := by
  obtain ⟨R', i1, i2, i3, i4, i5, i6, i7, i8, hmap, ⟨φ⟩⟩ :=
    IsDiscreteValuationRing.exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv R k'
  have i9 : HenselianLocalRing R' := HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := R) (S
    := R')
  have hring : (algebraMap R' (IsLocalRing.ResidueField R')).comp (algebraMap R R') =
      φ.toRingEquiv.toRingHom.comp ((algebraMap (IsLocalRing.ResidueField R) k').comp
        (IsLocalRing.residue R)) := by
    ext r
    change algebraMap R' (IsLocalRing.ResidueField R') (algebraMap R R' r) =
      φ (algebraMap (IsLocalRing.ResidueField R) k' (IsLocalRing.residue R r))
    rw [AlgEquiv.commutes, IsLocalRing.ResidueField.algebraMap_residue]
    rfl
  have hcomm : (Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) ≫ x₀) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [Category.assoc, hx₀, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hring]
  have hx₀' : pullback.lift _ _ hcomm ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R
    R'))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) :=
        pullback.lift_snd _ _ _
  obtain ⟨s', hs'₁, hs'₂⟩ :=
    AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) _ hx₀'
  have h₁ : (s' ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs'₁, Category.id_comp]
  have h₂ : Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) ≫
      (s' ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) =
        Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) ≫ x₀ := by
    rw [← Category.assoc, hs'₂]
    exact pullback.lift_fst _ _ _
  exact ⟨R', i1, i2, i3, i4, i5, i6, i7, i8, i9, φ, _, hmap, h₁, h₂⟩

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem Smooth.exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (V : X.Opens) (x : X) (hx : f.base x = IsLocalRing.closedPoint R) (hxV : x ∈ V) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ :
      Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : HenselianLocalRing R')
      (a : Spec (CommRingCat.of R') ⟶ X),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' ∧
      a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ∧
      a.base (IsLocalRing.closedPoint R') ∈ V := by
  classical
  let k : Type u := IsLocalRing.ResidueField R
  let ρ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue R))
  let j : pullback f ρ ⟶ X := pullback.fst f ρ
  let fk : pullback f ρ ⟶ Spec (CommRingCat.of k) := pullback.snd f ρ
  have : Smooth fk := inferInstance
  have hρ : ρ.base (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R := by
    change PrimeSpectrum.comap (IsLocalRing.residue R) _ = _
    exact IsLocalRing.PrimeSpectrum.comap_residue R _
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := ρ) x
    (IsLocalRing.closedPoint k)
    (hx.trans hρ.symm)
  let O : (pullback f ρ).Opens := j ⁻¹ᵁ V
  have hzO : z ∈ O := show j.base z ∈ V by rw [hz]; exact hxV
  have : Nonempty (O : Scheme.{u}) := ⟨⟨z, hzO⟩⟩
  have : Smooth (O.ι ≫ fk) := inferInstance
  obtain ⟨k', instF, instA, instFin, instSep, P, hP⟩ :=
    AlgebraicGeometry.exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty k (O.ι ≫ fk)
  let x₁ : Spec (CommRingCat.of k') ⟶ pullback f ρ := P ≫ O.ι
  have hx₁ : x₁ ≫ fk = Spec.map (CommRingCat.ofHom (algebraMap k k')) := by
    change (P ≫ O.ι) ≫ fk = _
    rw [Category.assoc, hP]
  let x₀ : Spec (CommRingCat.of k') ⟶ X := x₁ ≫ j
  have hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom
      ((algebraMap (IsLocalRing.ResidueField R) k').comp (IsLocalRing.residue R))) := by
    change (x₁ ≫ pullback.fst f ρ) ≫ f = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx₁, ← Spec.map_comp, ←
      CommRingCat.ofHom_comp]
  obtain ⟨R', instCR, instDom, instDVR, instAlg, instFinR, instEt, instFF, instLoc, instHens, φ,
    s, hmap, hs, hcl⟩ :=
    Smooth.exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing
      f k' x₀ hx₀
  refine ⟨R', instCR, instDom, instDVR, instAlg, instFinR, instEt, instFF, instLoc, instHens, s,
    hmap, hs, ?_⟩
  let q : Spec (CommRingCat.of (IsLocalRing.ResidueField R')) :=
    IsLocalRing.closedPoint (IsLocalRing.ResidueField R')
  let pt : Spec (CommRingCat.of k') := Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) q
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) q =
      (IsLocalRing.closedPoint R' : Spec (CommRingCat.of R')) := by
    change PrimeSpectrum.comap (algebraMap R' (IsLocalRing.ResidueField R')) _ = _
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.PrimeSpectrum.comap_residue R' _
  have h2 : s (IsLocalRing.closedPoint R' : Spec (CommRingCat.of R')) = x₀ pt :=
    (congrArg (fun r : Spec (CommRingCat.of R') => s r) h1).symm.trans
      (congrArg (fun t : Spec (CommRingCat.of (IsLocalRing.ResidueField R')) ⟶ X => t q) hcl)
  have hO : x₁ pt ∈ O := (P pt).property
  have hV : x₀ pt ∈ V := hO
  exact h2.symm ▸ hV

end AlgebraicGeometry
end
